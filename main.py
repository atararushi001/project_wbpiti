#!/usr/bin/env python3
import argparse
import csv
import json
import logging
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from urllib.parse import urljoin, urlparse, parse_qsl, urlencode
from urllib import robotparser
from threading import Lock
from html import escape

import requests
from bs4 import BeautifulSoup
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak

# --- Configuration ---
USER_AGENT = "edu-web-scanner/0.4 (educational)"
HEADERS = {"User-Agent": USER_AGENT}
REQUEST_DELAY = 0.5  # seconds
MAX_PAGES = 200
SMALL_WORDLIST = ["admin", "login", "config", "backup", "db", "uploads", "wp-admin", ".git", "robots.txt"]
SQL_ERROR_PATTERNS = [
    r"you have an error in your sql syntax",
    r"warning: mysql",
    r"unclosed quotation mark after the character string",
    r"quoted string not properly terminated",
    r"sqlstate",
]
XSS_TEST_PAYLOAD = "<script>alert('xss')</script>"
STATE_FILE = 'edu_scan_state.json'
LOG_FILE = 'edu_scanner.log'

# --- Utilities ---


def setup_logging(log_file=LOG_FILE):
    logging.basicConfig(filename=log_file, level=logging.INFO, format='%(asctime)s %(levelname)s: %(message)s')
    console = logging.StreamHandler()
    console.setLevel(logging.INFO)
    formatter = logging.Formatter('%(asctime)s %(levelname)s: %(message)s')
    console.setFormatter(formatter)
    logging.getLogger().addHandler(console)


def safe_get(session, url, params=None, allow_redirects=True, timeout=15, delay=REQUEST_DELAY, rp=None):
    """Fetch URL using given session, respect robots parser if provided."""
    try:
        if rp and not rp.can_fetch(HEADERS['User-Agent'], url):
            logging.info(f"Blocked by robots.txt: {url}")
            return None
        r = session.get(url, params=params, headers=HEADERS, allow_redirects=allow_redirects, timeout=timeout)
        time.sleep(delay)
        return r
    except Exception as e:
        logging.debug(f"Request error for {url}: {e}")
        return None


def is_same_domain(base, url):
    try:
        return urlparse(base).netloc == urlparse(url).netloc
    except Exception:
        return False


def dom_diff_score(html1, html2):
    """Rough similarity check between DOM trees (1.0 = identical-ish)."""
    try:
        soup1 = BeautifulSoup(html1 or "", "html.parser")
        soup2 = BeautifulSoup(html2 or "", "html.parser")
        tags1 = [t.name for t in soup1.find_all()]
        tags2 = [t.name for t in soup2.find_all()]
        overlap = len(set(tags1) & set(tags2))
        total = len(set(tags1) | set(tags2))
        if total == 0:
            return 1.0
        return overlap / total
    except Exception:
        return 1.0


def _snippet(text, marker, ctx=120):
    try:
        txt = text or ""
        idx = txt.lower().find(marker.lower())
        if idx == -1:
            return escape(txt[:ctx])
        start = max(0, idx - ctx // 2)
        return escape(txt[start:start + ctx].replace('\n', ' '))
    except Exception:
        return ''


def load_payloads(file_path, fallback):
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return [line.strip() for line in f if line.strip()]
    except Exception as e:
        logging.warning(f"Could not load payloads from {file_path}: {e} -- using fallback")
        return fallback
def load_payload_folder(folder_path="payloads"):
    """
    Auto-load all payload files inside payloads/ directory.
    Returns a dictionary:
    {
        'xss': [...],
        'sqli': [...],
        'lfi': [...],
        'custom': [...],
        ...
    }
    """
    payloads = {}

    if not os.path.isdir(folder_path):
        logging.warning(f"Payload folder not found: {folder_path}")
        return payloads

    for fname in os.listdir(folder_path):
        if not fname.endswith(".txt"):
            continue

        key = fname.replace(".txt", "").lower()
        fpath = os.path.join(folder_path, fname)

        try:
            with open(fpath, "r", encoding="utf-8") as f:
                items = [line.strip() for line in f if line.strip()]
                payloads[key] = items
                logging.info(f"Loaded {len(items)} payloads from {fname}")
        except Exception as e:
            logging.warning(f"Failed to load {fname}: {e}")

    return payloads


# --- Feature implementations ---


def crawl(session, start_url, max_pages=MAX_PAGES, delay=REQUEST_DELAY, rp=None):
    """Breadth-first crawl within same domain. Returns list of discovered pages."""
    to_visit = [start_url]
    visited = []
    seen = set()

    while to_visit and len(visited) < max_pages:
        url = to_visit.pop(0)
        if url in seen:
            continue
        r = safe_get(session, url, delay=delay, rp=rp)
        seen.add(url)
        if not r or r.status_code >= 400:
            continue
        visited.append(url)
        soup = BeautifulSoup(r.text, "html.parser")
        for tag, attr in (("a", "href"), ("form", "action"), ("link", "href")):
            for element in soup.find_all(tag):
                link = element.get(attr)
                if not link:
                    continue
                absolute = urljoin(url, link)
                absolute = absolute.split('#')[0]
                if is_same_domain(start_url, absolute) and absolute not in seen and absolute not in to_visit:
                    to_visit.append(absolute)
        logging.info(f"Crawled: {url} (total {len(visited)})")
    return visited


def enumerate_paths(session, base_url, wordlist, delay=REQUEST_DELAY, rp=None, max_workers=8):
    """Try a set of common paths and return those that exist (status < 400)."""
    found = []
    lock = Lock()

    def _check(word):
        target = urljoin(base_url, word)
        r = safe_get(session, target, delay=delay, rp=rp)
        if r and r.status_code < 400:
            with lock:
                found.append((target, r.status_code))
            logging.info(f"Found path: {target} (status {r.status_code})")

    with ThreadPoolExecutor(max_workers=min(max_workers, len(wordlist) or 1)) as ex:
        for w in wordlist:
            ex.submit(_check, w)
    return found


def analyze_headers(session, url, delay=REQUEST_DELAY, rp=None):
    r = safe_get(session, url, delay=delay, rp=rp)
    if not r:
        return {}, []
    server = r.headers.get("Server", "(none)")
    security_headers = {h: r.headers.get(h) for h in ["X-Frame-Options", "Content-Security-Policy", "X-Content-Type-Options", "Strict-Transport-Security"]}
    issues = []
    if re.search(r"\d+\.\d+", server):
        issues.append(f"Server header exposes version info: {server}")
    for name, val in security_headers.items():
        if not val:
            issues.append(f"Missing security header: {name}")
    return {'server': server, 'security_headers': security_headers}, issues


def extract_forms(session, url, delay=REQUEST_DELAY, rp=None):
    r = safe_get(session, url, delay=delay, rp=rp)
    forms = []
    if not r:
        return forms
    soup = BeautifulSoup(r.text, "html.parser")
    for form in soup.find_all("form"):
        f = {
            "action": urljoin(url, form.get("action", "")),
            "method": form.get("method", "get").lower(),
            "inputs": []
        }
        for inp in form.find_all(["input", "textarea", "select"]):
            name = inp.get("name")
            typ = inp.get("type", inp.name)
            value = inp.get('value') if inp.get('value') else ''
            f["inputs"].append({"name": name, "type": typ, "value": value})
        forms.append(f)
    return forms


def check_insecure_forms(session, urls, delay=REQUEST_DELAY, rp=None):
    issues = []
    for u in urls:
        forms = extract_forms(session, u, delay=delay, rp=rp)
        for f in forms:
            parsed = urlparse(f["action"] or u)
            if parsed.scheme != "https" and parsed.scheme != "":
                issues.append({'url': u, 'action': f['action'], 'method': f['method'], 'note': 'Form action is not HTTPS'})
            names = [i.get("name") or "" for i in f["inputs"]]
            csrf_like = any('csrf' in n.lower() or 'token' in n.lower() for n in names)
            if not csrf_like:
                issues.append({'url': u, 'action': f['action'], 'method': f['method'], 'note': 'Form has no CSRF-like field (heuristic)'})
    return issues


def check_sql_injection(cli, session, url, delay=REQUEST_DELAY, rp=None):

    """
    Enhanced SQL Injection check:
    - Tests multiple payloads
    - Logs parameter name, payload, and triggering evidence
    - Detects SQL error patterns and abnormal response length and DOM diff
    """
    parsed = urlparse(url)
    qs = dict(parse_qsl(parsed.query))
    if not qs:
        return []

    findings = []

 # AUTO-LOAD from payloads/sqli.txt, fallback to default list
    payloads = cli.payloads.get("sqli", [
        "'",
        "' OR '1'='1",
        "')--",
        "' UNION SELECT NULL--",
        '" OR "1"="1',
        "' OR 1=1--",
    ])

    baseline = safe_get(session, url, delay=delay, rp=rp)
    baseline_text = baseline.text if baseline else ''
    baseline_len = len(baseline_text)

    for name in qs.keys():
        for p in payloads:
            qs_copy = qs.copy()
            original_value = qs_copy[name] if qs_copy.get(name) else ''
            qs_copy[name] = original_value + p
            new_qs = urlencode(qs_copy)
            test_url = parsed._replace(query=new_qs).geturl()

            r = safe_get(session, test_url, delay=delay, rp=rp)
            if not r:
                continue

            body = r.text.lower()

            # Detect classic SQL error patterns
            for pattern in SQL_ERROR_PATTERNS:
                if re.search(pattern, body):
                    findings.append({
                        'url': test_url,
                        'param': name,
                        'payload': p,
                        'type': 'sql_error_pattern',
                        'pattern': pattern,
                        'evidence_snippet': _snippet(r.text, pattern)
                    })
                    logging.info(f"[SQLi] {name}={p} -> {pattern} @ {test_url}")

            # Detect large differences in response length
            if abs(len(r.text) - baseline_len) > 200:
                findings.append({
                    'url': test_url,
                    'param': name,
                    'payload': p,
                    'type': 'response_length_difference',
                    'len': len(r.text),
                    'baseline': baseline_len
                })
                logging.info(f"[SQLi-LEN] {name}={p} caused response size delta at {test_url}")

            # DOM diff check
            diff_score = dom_diff_score(baseline_text, r.text)
            if diff_score < 0.7:
                findings.append({
                    'url': test_url,
                    'param': name,
                    'payload': p,
                    'type': 'dom_difference',
                    'score': diff_score
                })
                logging.info(f"[SQLi-DOM] {name}={p} caused DOM diff score {diff_score} @ {test_url}")

    return findings

def test_post_sql(cli, session, page_url, form):
    """
    POST-based SQL Injection testing for forms.
    Injects SQL payloads into POST form fields and checks:
    - SQL error patterns
    - Response length anomalies
    - DOM differences
    """
    findings = []

    # Load SQL payloads from payloads/sqli.txt OR fallback
    payloads = cli.payloads.get("sqli", [
        "' OR 1=1--",
        "\" OR 1=1--",
        "' UNION SELECT NULL--"
    ])

    # Build baseline request
    baseline_data = {}
    for inp in form["inputs"]:
        name = inp.get("name")
        if not name:
            continue
        baseline_data[name] = inp.get("value", "")

    try:
        baseline_res = session.post(form["action"], data=baseline_data, timeout=10)
        baseline_text = baseline_res.text
        baseline_len = len(baseline_text)
    except:
        baseline_text = ""
        baseline_len = 0

    # Try each payload
    for pl in payloads:
        data = {}
        for inp in form["inputs"]:
            name = inp.get("name")
            if not name:
                continue
            data[name] = (inp.get("value") or "") + pl

        try:
            r = session.post(form["action"], data=data, timeout=10)
            body = r.text.lower()
        except:
            continue

        # SQL error checks
        for pattern in SQL_ERROR_PATTERNS:
            if pattern in body:
                findings.append({
                    "url": form["action"],
                    "type": "post_sql_error",
                    "payload": pl,
                    "pattern": pattern,
                    "evidence_snippet": _snippet(r.text, pattern)
                })

        # Response length anomaly
        if abs(len(r.text) - baseline_len) > 200:
            findings.append({
                "url": form["action"],
                "type": "post_sql_length_diff",
                "payload": pl,
                "len": len(r.text),
                "baseline": baseline_len
            })

        # DOM diff
        score = dom_diff_score(baseline_text, r.text)
        if score < 0.7:
            findings.append({
                "url": form["action"],
                "type": "post_sql_dom_diff",
                "payload": pl,
                "score": score
            })

    return findings

def check_reflected_xss(cli, session, url, delay=REQUEST_DELAY, rp=None):
    """
    Improved reflected XSS detection:
    - HTML-unescape response body
    - Partial payload matching (resistant to encoding)
    - Stronger evidence extraction
    """
    import html

    parsed = urlparse(url)
    qs = dict(parse_qsl(parsed.query))
    findings = []

    if not qs:
        return findings

    # load payloads
    payloads = cli.payloads.get("xss", [XSS_TEST_PAYLOAD])

    for param in qs.keys():
        for payload in payloads:

            qs_copy = qs.copy()
            original = qs_copy.get(param) or ""
            qs_copy[param] = original + payload

            new_qs = urlencode(qs_copy, doseq=True)
            test_url = parsed._replace(query=new_qs).geturl()

            r = safe_get(session, test_url, delay=delay, rp=rp)
            if not r:
                continue

            # normalize body (html-unescape)
            raw_body = r.text or ""
            body = html.unescape(raw_body).lower()

            # pick stable substring of payload
            marker = payload[0:10].lower()  # first 10 chars
            marker2 = payload[-10:].lower()  # last 10 chars

            reflected = False

            # check partial reflection
            if marker in body or marker2 in body:
                reflected = True

            # fallback: remove <script> tags when checking
            cleaned_body = re.sub(r"<script.*?>", "", body)
            if payload.replace("<script>", "").lower() in cleaned_body:
                reflected = True

            if reflected:
                findings.append({
                    "url": test_url,
                    "param": param,
                    "payload": payload,
                    "type": "reflected_xss_marker",
                    "evidence_snippet": _snippet(raw_body, marker)
                })

                logging.info(f"[XSS-REFLECT] {param}={payload} @ {test_url}")

    return findings

def check_stored_xss(cli, session, urls, delay=REQUEST_DELAY, rp=None):
    payload = cli.payloads.get("xss", [XSS_TEST_PAYLOAD])[0]

    findings = []
    injected_actions = []

    # Step 1: Inject payload
    for u in urls:
        r = safe_get(session, u, delay=delay, rp=rp)
        if not r:
            continue
        soup = BeautifulSoup(r.text, "html.parser")
        forms = soup.find_all("form")
        for form in forms:
            action = urljoin(u, form.get("action") or u)
            method = (form.get("method") or "get").lower()
            inputs = form.find_all(["input", "textarea", "select"])

            data = {}
            for inp in inputs:
                name = inp.get("name")
                if not name:
                    continue
                typ = (inp.get("type") or "").lower()
                if typ in ("text", "search", "email", "tel") or inp.name == "textarea":
                    data[name] = payload
                else:
                    data[name] = inp.get("value", "")

            try:
                if method == "post":
                    session.post(action, data=data, timeout=15)
                else:
                    session.get(action, params=data, timeout=15)

                injected_actions.append({
                    'action': action,
                    'method': method,
                    'data': data
                })
            except:
                pass

    # Step 2: Check if payload appears on any page
    for page in urls:
        r = safe_get(session, page, delay=delay, rp=rp)
        if not r:
            continue

        if payload.lower() in r.text.lower():
            findings.append({
                "url": page,
                "type": "stored_xss",
                "payload": payload,
                "evidence_snippet": _snippet(r.text, payload)
            })

    # REMOVE DEBUG NOISE
    findings = [f for f in findings if f.get("type") != "injection_attempt"]

    return findings


# --- Reporting ---


def generate_reports(report, target, output_dir='.', format='all'):
    """Generate JSON, CSV, HTML and PDF reports."""
    ts = datetime.utcnow().strftime('%Y%m%dT%H%M%SZ')
    base = os.path.join(output_dir, f"edu_scan_report_{ts}")
    os.makedirs(output_dir, exist_ok=True)
    paths = {}

    if format in ('json', 'all'):
        json_path = base + '.json'
        with open(json_path, 'w', encoding='utf-8') as jf:
            json.dump(report, jf, indent=2, ensure_ascii=False)
        paths['json'] = json_path

    if format in ('csv', 'all'):
        csv_path = base + '.csv'
        with open(csv_path, 'w', newline='', encoding='utf-8') as cf:
            writer = csv.writer(cf)
            writer.writerow(['target', 'type', 'detail'])
            writer.writerow([target, 'server', report.get('headers', {}).get('server')])
            for issue in report.get('header_issues', []):
                writer.writerow([target, 'header_issue', issue])
            for p in report.get('found_paths', []):
                writer.writerow([target, 'found_path', p[0] + ' (status ' + str(p[1]) + ')'])
            for f in report.get('form_issues', []):
                writer.writerow([target, 'form_issue', f.get('note') + ' @ ' + f.get('url')])
            for f in report.get('sqli', []):
                writer.writerow([target, 'sqli', json.dumps(f)])
            for f in report.get('xss', []):
                writer.writerow([target, 'xss', json.dumps(f)])
        paths['csv'] = csv_path

    if format in ('html', 'all'):
        html_path = base + '.html'
        with open(html_path, 'w', encoding='utf-8') as hf:
            hf.write('<!doctype html>\n')
            hf.write('<html lang="en">\n')
            hf.write('<head>\n')
            hf.write('  <meta charset="utf-8">\n')
            hf.write(f'  <title>Edu Scan Report - {target}</title>\n')
            hf.write('  <meta name="viewport" content="width=device-width,initial-scale=1">\n')
            hf.write('  <style>\n')
            hf.write("    body{font-family:Inter,Segoe UI,Roboto,Arial,sans-serif;margin:20px;color:#111}\n")
            hf.write("    h1{font-size:24px;margin-bottom:0.2em}\n")
            hf.write("    .muted{color:#555;font-size:0.95em}\n")
            hf.write("    .card{border-radius:8px;padding:12px;margin:12px 0;box-shadow:0 2px 6px rgba(0,0,0,0.06);background:#fff}\n")
            hf.write("    table{border-collapse:collapse;width:100%}th,td{padding:8px;border-bottom:1px solid #eee;text-align:left}th{background:#f7f7f7}pre{background:#f6f8fa;padding:10px;border-radius:6px;overflow:auto}\n")
            hf.write('  </style>\n')
            hf.write('</head>\n')
            hf.write('<body>\n')

            hf.write(f'<h1>Edu Scan Report</h1>\n')
            hf.write(f'<div class="muted">Target: {target} — Generated: {ts} UTC</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<strong>Summary</strong>\n')
            hf.write('<ul>\n')
            hf.write(f'<li>Pages crawled: {len(report.get("pages_crawled", []))}</li>\n')
            hf.write(f'<li>Found paths: {len(report.get("found_paths", []))}</li>\n')
            hf.write(f'<li>Form issues: {len(report.get("form_issues", []))}</li>\n')
            hf.write(f'<li>Potential SQLi findings: {len(report.get("sqli", []))}</li>\n')
            hf.write(f'<li>Potential XSS findings: {len(report.get("xss", []))}</li>\n')
            hf.write('</ul>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Server & Headers</h2>\n')
            hf.write('<pre>\n')
            hf.write(str(report.get('headers', {})) + '\n')
            hf.write('</pre>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Found Paths</h2>\n')
            hf.write('<table><thead><tr><th>Path</th><th>Status</th></tr></thead><tbody>\n')
            for p in report.get('found_paths', []):
                hf.write(f'<tr><td>{p[0]}</td><td>{p[1]}</td></tr>\n')
            hf.write('</tbody></table>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Form Issues</h2>\n')
            if report.get('form_issues'):
                hf.write('<table><thead><tr><th>URL</th><th>Action</th><th>Method</th><th>Note</th></tr></thead><tbody>\n')
                for f in report.get('form_issues', []):
                    hf.write(f'<tr><td>{f.get("url")}</td><td>{f.get("action")}</td><td>{f.get("method")}</td><td>{f.get("note")}</td></tr>\n')
                hf.write('</tbody></table>\n')
            else:
                hf.write('<div class="muted">No form issues detected.</div>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Potential SQL Injection Findings</h2>\n')
            if report.get('sqli'):
                hf.write('<ul>\n')
                for s in report.get('sqli'):
                    hf.write(f"<li><b>{s.get('param','(n/a)')}</b> = {escape(str(s.get('payload','')))} → {s.get('type')} @ {s.get('url')}<br/>Evidence: {s.get('evidence_snippet','(none)')}</li>\n")
                hf.write('</ul>\n')
            else:
                hf.write('<div class="muted">No SQLi-like findings.</div>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Potential XSS Findings</h2>\n')
            if report.get('xss'):
                hf.write('<ul>\n')
                for x in report.get('xss'):
                    # stored_xss entries may not have 'param'
                    if x.get('type') == 'stored_xss':
                        hf.write(f"<li><b>STORED XSS</b> @ {x.get('url')} - payload: {escape(str(x.get('payload','')))}<br/>Evidence: {x.get('evidence_snippet','(none)')}</li>\n")
                    elif x.get('type') == 'injection_attempt':
                        hf.write(f"<li><b>Injection Attempt</b> @ {x.get('url')} - method: {x.get('method')} - sample_data: {escape(json.dumps(x.get('sample_data',{})))}</li>\n")
                    else:
                        hf.write(f"<li>{x.get('type')} @ {x.get('url')} - param: {escape(str(x.get('param','')))} - payload: {escape(str(x.get('payload','')))}<br/>Evidence: {x.get('evidence_snippet','(none)')}</li>\n")
                hf.write('</ul>\n')
            else:
                hf.write('<div class="muted">No XSS detected.</div>\n')
            hf.write('</div>\n')

            # detailed pages section
            hf.write('<div class="card">\n')
            hf.write('<h2>Pages Crawled (detailed)</h2>\n')
            for p in report.get('pages_crawled', []):
                hf.write(f'<div style="margin-bottom:8px"><strong>{p}</strong></div>\n')
            hf.write('</div>\n')

            hf.write('</body>\n')
            hf.write('</html>\n')
        paths['html'] = html_path

    if format in ('pdf', 'all'):
        pdf_path = base + '.pdf'
        _make_pdf(report, target, pdf_path)
        paths['pdf'] = pdf_path

    return paths


def _make_pdf(report, target, pdf_path):
    """Generate a styled, well-formatted PDF report for scan results."""
    doc = SimpleDocTemplate(pdf_path, pagesize=A4)
    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name='MyHeading1', fontSize=18, spaceAfter=12, leading=22, textColor=colors.darkblue))
    styles.add(ParagraphStyle(name='MyHeading2', fontSize=14, spaceAfter=8, leading=18, textColor=colors.darkgreen))
    styles.add(ParagraphStyle(name='MyCode', fontName='Courier', fontSize=9, leading=10, textColor=colors.darkred))
    styles.add(ParagraphStyle(name='MySmall', fontSize=10, spaceAfter=6))

    story = []
    story.append(Paragraph(f"Edu Web Scanner Report - {target}", styles['MyHeading1']))
    story.append(Paragraph(f"Generated: {report.get('timestamp', '(unknown)')}", styles['MySmall']))
    story.append(Spacer(1, 10))

    story.append(Paragraph("Summary", styles['MyHeading2']))
    summary_data = [
        ['Pages Crawled', len(report.get('pages_crawled', []))],
        ['Found Paths', len(report.get('found_paths', []))],
        ['Form Issues', len(report.get('form_issues', []))],
        ['Potential SQLi Findings', len(report.get('sqli', []))],
        ['Potential XSS Findings', len(report.get('xss', []))]
    ]
    summary_table = Table(summary_data, hAlign='LEFT', colWidths=[200, 100])
    summary_table.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
        ('GRID', (0, 0), (-1, -1), 0.25, colors.grey),
        ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
        ('TEXTCOLOR', (0, 0), (-1, 0), colors.black),
    ]))
    story.append(summary_table)
    story.append(Spacer(1, 12))

    if report.get('sqli'):
        story.append(PageBreak())
        story.append(Paragraph("Potential SQL Injection Findings", styles['MyHeading2']))
        for f in report['sqli']:
            story.append(Paragraph(f"Type: {f.get('type')} | URL: {escape(f.get('url', ''))}", styles['MySmall']))
            snippet = escape(f.get('evidence_snippet', '(none)'))
            story.append(Paragraph(f"<b>Evidence:</b><br/><font face='Courier'>{snippet}</font>", styles['MyCode']))
            story.append(Spacer(1, 8))

    if report.get('xss'):
        story.append(PageBreak())
        story.append(Paragraph("Potential XSS Findings", styles['MyHeading2']))
        for x in report['xss']:
            story.append(Paragraph(f"Type: {x.get('type')} | URL: {escape(x.get('url', ''))}", styles['MySmall']))
            snippet = escape(x.get('evidence_snippet', '(none)'))
            story.append(Paragraph(f"<b>Evidence:</b><br/><font face='Courier'>{snippet}</font>", styles['MyCode']))
            story.append(Spacer(1, 8))

    if report.get('form_issues'):
        story.append(PageBreak())
        story.append(Paragraph("Form Security Issues", styles['MyHeading2']))
        for f in report['form_issues']:
            story.append(Paragraph(f"URL: {escape(f.get('url',''))}", styles['MySmall']))
            story.append(Paragraph(f"Issue: {escape(f.get('note',''))}", styles['MyCode']))
            story.append(Spacer(1, 8))

    doc.build(story)


def report_summary_lines(report):
    return [
        f"Pages crawled: {len(report.get('pages_crawled', []))}",
        f"Found paths: {len(report.get('found_paths', []))}",
        f"Form issues: {len(report.get('form_issues', []))}",
        f"Potential SQLi findings: {len(report.get('sqli', []))}",
        f"Potential XSS findings: {len(report.get('xss', []))}",
    ]


# --- CLI class ---


class EduScannerCLI:
    def __init__(self, proxy=None):
        self.session = requests.Session()
        self.session.headers.update(HEADERS)
        self.state_file = STATE_FILE
        # Auto-load payload sets
        self.payloads = load_payload_folder()

        # If proxy provided, set session.proxies so all requests use it.
        # Accepts full proxy URL, with optional credentials: http://user:pass@host:port or socks5://host:port
        if proxy:
            # requests expects proxies dict where same proxy used for http and https
            self.session.proxies = {'http': proxy, 'https': proxy}
            logging.info(f"Using proxy: {proxy}")

            # quick connectivity test for the proxy (best-effort)
            try:
                # httpbin returns the origin IP; won't work for socks5 unless requests[socks] installed.
                resp = self.session.get('https://httpbin.org/ip', timeout=8)
                if resp.status_code == 200:
                    logging.info(f"Proxy check OK: {resp.text.strip()}")
                else:
                    logging.warning(f"Proxy check returned status {resp.status_code}")
            except Exception as e:
                logging.warning(f"Proxy check failed: {e}\n(If you're using a SOCKS proxy, make sure 'requests[socks]' is installed.)")

    def load_wordlist(self, path):
        try:
            with open(path, 'r', encoding='utf-8') as f:
                return [l.strip() for l in f if l.strip()]
        except Exception as e:
            logging.warning(f"Could not open wordlist {path}: {e} -- falling back to builtin wordlist")
            return SMALL_WORDLIST

    def respect_robots(self, base_url):
        rp = robotparser.RobotFileParser()
        parsed = urlparse(base_url)
        robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"
        try:
            rp.set_url(robots_url)
            rp.read()
            return rp
        except Exception:
            return None

    def login_flow(self, login_url, username_field='username', password_field='password', username=None, password=None, extra=None):
        payload = {}
        if username is None or password is None:
            logging.warning('Username or password not provided for login')
            return False
        payload[username_field] = username
        payload[password_field] = password
        if extra:
            payload.update(extra)
        try:
            r = self.session.post(login_url, data=payload, timeout=15)
            time.sleep(REQUEST_DELAY)
            if r.status_code < 400 and self.session.cookies:
                logging.info(f"Logged in, cookies: {self.session.cookies.get_dict()}")
                return True
            logging.warning(f"Login response status: {r.status_code}")
            return False
        except Exception as e:
            logging.error(f"Login error: {e}")
            return False

    def save_state(self, state):
        try:
            with open(self.state_file, 'w', encoding='utf-8') as sf:
                json.dump(state, sf)
        except Exception as e:
            logging.error(f"Failed to save state: {e}")

    def load_state(self):
        try:
            with open(self.state_file, 'r', encoding='utf-8') as sf:
                return json.load(sf)
        except Exception:
            return {}
    def run_scan(self, target, wordlist_path=None, max_workers=4, delay=REQUEST_DELAY,
                respect_robots_flag=True, resume=False, output_dir='reports', report_format='all'):

        rp = None
        if respect_robots_flag:
            rp = self.respect_robots(target)

        pages = []
        found_paths = []
        header_issues = []
        form_issues = []
        sqli_findings = []
        xss_findings = []

        # Wordlist
        wordlist = SMALL_WORDLIST
        if wordlist_path:
            wordlist = self.load_wordlist(wordlist_path)

        # Resume state
        state = self.load_state() if resume else {}
        crawled = set(state.get('crawled', [])) if resume else set()

        # -----------------------
        # 1. Crawl the target
        # -----------------------
        pages = crawl(self.session, target, max_pages=MAX_PAGES, delay=delay, rp=rp)

        # -----------------------
        # 2. Analyze server headers
        # -----------------------
        hdrs, hdr_issues = analyze_headers(self.session, target, delay=delay, rp=rp)
        header_issues.extend(hdr_issues)

        # -----------------------
        # 3. Directory enumeration
        # -----------------------
        found_paths = enumerate_paths(self.session, target, wordlist,
                                    delay=delay, rp=rp, max_workers=max_workers)

        # -----------------------
        # 4. Form security issues
        # -----------------------
        for u in pages:
            forms = extract_forms(self.session, u, delay=delay, rp=rp)
            for f in forms:
                names = [i.get('name') or '' for i in f['inputs']]
                csrf_like = any('csrf' in n.lower() or 'token' in n.lower() for n in names)

                parsed_action = urlparse(f['action'] or u)
                if parsed_action.scheme not in ('https', ''):
                    form_issues.append({
                        'url': u,
                        'action': f['action'],
                        'method': f['method'],
                        'note': 'Form action not HTTPS'
                    })

                if not csrf_like:
                    form_issues.append({
                        'url': u,
                        'action': f['action'],
                        'method': f['method'],
                        'note': 'No CSRF-like field (heuristic)'
                    })

        # -----------------------
        # 5. GET-based SQLi + XSS on URLs WITH parameters
        # -----------------------
        for p in pages:
            if '?' not in p:
                continue

            logging.info(f"Testing GET parameters at: {p}")

            # GET SQL Injection
            sqli = check_sql_injection(self, self.session, p, delay=delay, rp=rp)
            if sqli:
                sqli_findings.extend(sqli)

            # Reflected GET XSS
            xss_ref = check_reflected_xss(self, self.session, p, delay=delay, rp=rp)
            if xss_ref:
                xss_findings.extend(xss_ref)

        # -----------------------
        # 6. AUTO-XSS for pages WITHOUT parameters (NEW)
        # -----------------------
        logging.info("Testing reflected XSS on pages without parameters...")
        for page in pages:
            if '?' in page:
                continue

            for payload in self.payloads.get("xss", [XSS_TEST_PAYLOAD]):
                test_url = page + "?x=" + payload
                r = safe_get(self.session, test_url, delay=delay, rp=rp)
                if not r:
                    continue

                if payload.lower() in r.text.lower():
                    xss_findings.append({
                        "url": test_url,
                        "param": "x",
                        "payload": payload,
                        "type": "reflected_xss_auto",
                        "evidence_snippet": _snippet(r.text, payload)
                    })
                    logging.info(f"[XSS-REFLECT-AUTO] payload reflected @ {test_url}")

        # -----------------------
        # 7. POST-based SQL Injection (always)
        # -----------------------
        logging.info("Testing POST-based SQL injection across ALL pages...")
        for page in pages:
            forms = extract_forms(self.session, page, delay=delay, rp=rp)
            for f in forms:
                if f["method"] == "post":
                    post_sqli = test_post_sql(self, self.session, page, f)
                    if post_sqli:
                        sqli_findings.extend(post_sqli)

        # -----------------------
        # 8. Stored XSS
        # -----------------------
        logging.info("Starting stored-XSS checks (this will submit data to forms).")
        stored = check_stored_xss(self, self.session, pages, delay=delay, rp=rp)
        if stored:
            xss_findings.extend(stored)

        # -----------------------
        # Save scan state
        # -----------------------
        state_out = {'crawled': pages, 'found_paths': found_paths}
        self.save_state(state_out)

        # -----------------------
        # Final report
        # -----------------------
        report = {
            'target': target,
            'headers': hdrs,
            'header_issues': header_issues,
            'found_paths': found_paths,
            'form_issues': form_issues,
            'sqli': sqli_findings,
            'xss': xss_findings,
            'pages_crawled': pages,
            'timestamp': datetime.utcnow().isoformat() + 'Z'
        }

        paths = generate_reports(report, target, output_dir=output_dir, format=report_format)
        logging.info(f"Reports generated: {paths}")

        return report, paths

    def interactive_menu(self):
        print('\n=== Edu Web Scanner - Interactive CLI ===')
        print('1) Quick scan (default settings)')
        print('2) Scan with options (wordlist, workers, delay)')
        print('3) Login & scan (authenticated)')
        print('4) Resume last scan state')
        print('5) Exit')

        choice = input('Choose an option: ').strip()

        if choice == '1':
            target = input('Target (include http:// or https://): ').strip()
            report, paths = self.run_scan(target)
            print('Done. Reports:', paths)

        elif choice == '2':
            target = input('Target: ').strip()
            wl = input('Wordlist file (leave blank to use builtin): ').strip() or None
            workers = int(input('Max workers (default 4): ').strip() or 4)
            delay = float(input('Delay between requests (default 0.5): ').strip() or 0.5)
            out = input('Output folder (default reports): ').strip() or 'reports'
            report, paths = self.run_scan(target, wordlist_path=wl, max_workers=workers, delay=delay, output_dir=out)
            print('Done. Reports:', paths)

        elif choice == '3':
            target = input('Target: ').strip()
            login_url = input('Login URL: ').strip()
            uname = input('Username: ').strip()
            pwd = input('Password: ').strip()

            if self.login_flow(login_url, username=uname, password=pwd):
                print('Login OK. Running scan...')
                report, paths = self.run_scan(target)
                print('Done. Reports:', paths)
            else:
                print('Login failed.')

        elif choice == '4':
            print('Loaded state:', self.load_state())
            target = input('Target to continue scanning: ').strip()
            report, paths = self.run_scan(target, resume=True)
            print('Done. Reports:', paths)

        else:
            print('Bye.')


# --- Entry point ---
if __name__ == '__main__':
    setup_logging()
    parser = argparse.ArgumentParser(description='Educational web scanner (improved)')
    parser.add_argument('--target', help='Target URL (include http:// or https://)')
    parser.add_argument('--wordlist', help='Path to wordlist file')
    parser.add_argument('--workers', type=int, default=4, help='Max concurrent workers')
    parser.add_argument('--delay', type=float, default=0.5, help='Delay between requests (seconds)')
    parser.add_argument('--no-robots', action='store_true', help='Do not respect robots.txt')
    parser.add_argument('--login-url', help='If provided, perform a login POST before scanning')
    parser.add_argument('--username', help='Username for login')
    parser.add_argument('--password', help='Password for login')
    parser.add_argument('--interactive', action='store_true', help='Run interactive CLI')
    parser.add_argument('--resume', action='store_true', help='Resume from last saved state')
    parser.add_argument('--outdir', default='reports', help='Output directory for reports')
    parser.add_argument('--format', default='all', help='Output format (json,csv,html,pdf,all)')
    parser.add_argument('--proxy', help='Proxy URL to use (e.g. http://127.0.0.1:8080 or socks5://127.0.0.1:9050)')

    args = parser.parse_args()

    # Create CLI with optional proxy
    cli = EduScannerCLI(proxy=args.proxy)

    if args.interactive:
        cli.interactive_menu()
        sys.exit(0)

    if args.login_url and args.username and args.password:
        ok = cli.login_flow(args.login_url, username=args.username, password=args.password)
        if not ok:
            print('Login failed; exiting.')
            sys.exit(1)

    if args.target:
        report, paths = cli.run_scan(args.target, wordlist_path=args.wordlist, max_workers=args.workers, delay=args.delay, respect_robots_flag=not args.no_robots, resume=args.resume, output_dir=args.outdir, report_format=args.format)
        print('Scan complete. Reports:', paths)
    else:
        print('No target provided. Launching interactive menu.')
        cli.interactive_menu()
