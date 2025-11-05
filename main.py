#!/usr/bin/env python3
"""
Edu Web Scanner v2 - Improved & Fixed

Changes made:
- Fixed truncated HTML writer and other bugs.
- Simpler, robust BFS crawler (single-threaded) to avoid race conditions during crawl.
- Concurrency used for path enumeration and request-heavy checks.
- Detailed vulnerability recording (type, page/url, evidence snippet).
- Added PDF report generation using reportlab.
- Better state save/load and output directory support.
- Improved logging and CLI options.

Ethics reminder: Only scan systems you own or have explicit permission to test.

Dependencies: requests, beautifulsoup4, reportlab
Install: pip install requests beautifulsoup4 reportlab

Author: Assistant (improved version)
"""

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
from html import escape
# PDF generation
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib import colors

# --- Configuration ---
USER_AGENT = "edu-web-scanner/0.3 (educational)"
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


def check_sql_injection(session, url, delay=REQUEST_DELAY, rp=None):
    parsed = urlparse(url)
    qs = dict(parse_qsl(parsed.query))
    if not qs:
        return []
    findings = []
    payloads = ["'", "' OR '1'='1", '"', '" OR "1"="1']
    baseline = safe_get(session, url, delay=delay, rp=rp)
    baseline_text = baseline.text if baseline else ''
    baseline_len = len(baseline_text)

    for name in qs.keys():
        for p in payloads:
            qs_copy = qs.copy()
            qs_copy[name] = qs_copy[name] + p
            new_qs = urlencode(qs_copy)
            test_url = parsed._replace(query=new_qs).geturl()
            r = safe_get(session, test_url, delay=delay, rp=rp)
            if not r:
                continue
            body = r.text.lower()
            evidence = ''
            for pattern in SQL_ERROR_PATTERNS:
                if re.search(pattern, body):
                    evidence = pattern
                    findings.append({'url': test_url, 'type': 'sql_error_pattern', 'pattern': pattern, 'evidence_snippet': _snippet(r.text, pattern)})
            if abs(len(r.text) - baseline_len) > 200:
                findings.append({'url': test_url, 'type': 'response_length_difference', 'len': len(r.text), 'baseline': baseline_len})
    return findings


def check_reflected_xss(session, url, delay=REQUEST_DELAY, rp=None):
    parsed = urlparse(url)
    qs = dict(parse_qsl(parsed.query))
    findings = []
    if not qs:
        return findings
    for name in qs.keys():
        qs_copy = qs.copy()
        qs_copy[name] = qs_copy[name] + XSS_TEST_PAYLOAD
        new_qs = urlencode(qs_copy)
        test_url = parsed._replace(query=new_qs).geturl()
        r = safe_get(session, test_url, delay=delay, rp=rp)
        if not r:
            continue
        if XSS_TEST_PAYLOAD in r.text:
            findings.append({'url': test_url, 'type': 'reflected_xss_marker', 'evidence_snippet': _snippet(r.text, XSS_TEST_PAYLOAD)})
    return findings


def _snippet(text, marker, ctx=120):
    try:
        idx = text.lower().find(marker.lower())
        if idx == -1:
            return escape(text[:ctx])
        start = max(0, idx - ctx // 2)
        return escape(text[start:start + ctx].replace('\n', ' '))
    except Exception:
        return ''

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
                    hf.write(f"<li>{s.get('type')} @ {s.get('url')} - evidence: {s.get('evidence_snippet','(none)')}</li>\n")
                hf.write('</ul>\n')
            else:
                hf.write('<div class="muted">No SQLi-like findings.</div>\n')
            hf.write('</div>\n')

            hf.write('<div class="card">\n')
            hf.write('<h2>Potential Reflected XSS Findings</h2>\n')
            if report.get('xss'):
                hf.write('<ul>\n')
                for x in report.get('xss'):
                    hf.write(f"<li>{x.get('type')} @ {x.get('url')} - snippet: {x.get('evidence_snippet','(none)')}</li>\n")
                hf.write('</ul>\n')
            else:
                hf.write('<div class="muted">No reflected XSS detected.</div>\n')
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


from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from html import escape

def _make_pdf(report, target, pdf_path):
    """Generate a styled, well-formatted PDF report for scan results."""
    doc = SimpleDocTemplate(pdf_path, pagesize=A4)
    styles = getSampleStyleSheet()
    # Custom style names to avoid conflicts
    styles.add(ParagraphStyle(name='MyHeading1', fontSize=18, spaceAfter=12, leading=22, textColor=colors.darkblue))
    styles.add(ParagraphStyle(name='MyHeading2', fontSize=14, spaceAfter=8, leading=18, textColor=colors.darkgreen))
    styles.add(ParagraphStyle(name='MyCode', fontName='Courier', fontSize=9, leading=10, textColor=colors.darkred))
    styles.add(ParagraphStyle(name='MySmall', fontSize=10, spaceAfter=6))

    story = []
    story.append(Paragraph(f"Edu Web Scanner Report - {target}", styles['MyHeading1']))
    story.append(Paragraph(f"Generated: {report.get('timestamp', '(unknown)')}", styles['MySmall']))
    story.append(Spacer(1, 10))

    # --- Summary ---
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

    # --- SQL Injection Findings ---
    if report.get('sqli'):
        story.append(PageBreak())
        story.append(Paragraph("Potential SQL Injection Findings", styles['MyHeading2']))
        for f in report['sqli']:
            story.append(Paragraph(f"Type: {f.get('type')} | URL: {escape(f.get('url', ''))}", styles['MySmall']))
            snippet = escape(f.get('evidence_snippet', '(none)'))
            story.append(Paragraph(f"<b>Evidence:</b><br/><font face='Courier'>{snippet}</font>", styles['MyCode']))
            story.append(Spacer(1, 8))

    # --- XSS Findings ---
    if report.get('xss'):
        story.append(PageBreak())
        story.append(Paragraph("Potential Reflected XSS Findings", styles['MyHeading2']))
        for x in report['xss']:
            story.append(Paragraph(f"Type: {x.get('type')} | URL: {escape(x.get('url', ''))}", styles['MySmall']))
            snippet = escape(x.get('evidence_snippet', '(none)'))
            story.append(Paragraph(f"<b>Evidence:</b><br/><font face='Courier'>{snippet}</font>", styles['MyCode']))
            story.append(Spacer(1, 8))

    # --- Form Issues ---
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
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update(HEADERS)
        self.state_file = STATE_FILE

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

    def run_scan(self, target, wordlist_path=None, max_workers=4, delay=REQUEST_DELAY, respect_robots_flag=True, resume=False, output_dir='reports', report_format='all'):
        rp = None
        if respect_robots_flag:
            rp = self.respect_robots(target)
        pages = []
        found_paths = []
        header_issues = []
        form_issues = []
        sqli_findings = []
        xss_findings = []

        wordlist = SMALL_WORDLIST
        if wordlist_path:
            wordlist = self.load_wordlist(wordlist_path)

        state = self.load_state() if resume else {}
        crawled = set(state.get('crawled', [])) if resume else set()

        # Crawl
        pages = crawl(self.session, target, max_pages=MAX_PAGES, delay=delay, rp=rp)

        # Header analysis
        hdrs, hdr_issues = analyze_headers(self.session, target, delay=delay, rp=rp)
        header_issues.extend(hdr_issues)

        # Path enumeration (concurrent)
        found_paths = enumerate_paths(self.session, target, wordlist, delay=delay, rp=rp, max_workers=max_workers)

        # Form analysis (per page)
        for u in pages:
            forms = extract_forms(self.session, u, delay=delay, rp=rp)
            for f in forms:
                names = [i.get('name') or '' for i in f['inputs']]
                csrf_like = any('csrf' in n.lower() or 'token' in n.lower() for n in names)
                parsed_action = urlparse(f['action'] or u)
                if parsed_action.scheme != 'https' and parsed_action.scheme != '':
                    form_issues.append({'url': u, 'action': f['action'], 'method': f['method'], 'note': 'Form action not HTTPS'})
                if not csrf_like:
                    form_issues.append({'url': u, 'action': f['action'], 'method': f['method'], 'note': 'No CSRF-like field (heuristic)'})

        # Parameter-based active checks (sequential to limit noisy traffic)
        for p in pages:
            if '?' not in p:
                continue
            logging.info(f"Testing parameters at: {p}")
            sqli = check_sql_injection(self.session, p, delay=delay, rp=rp)
            xss = check_reflected_xss(self.session, p, delay=delay, rp=rp)
            if sqli:
                sqli_findings.extend(sqli)
            if xss:
                xss_findings.extend(xss)

        # Save state for resume
        state_out = {'crawled': pages, 'found_paths': found_paths}
        self.save_state(state_out)

        report = {
            'target': target,
            'headers': hdrs,
            'header_issues': header_issues,
            'found_paths': found_paths,
            'form_issues': form_issues,
            'sqli': sqli_findings,
            'xss': xss_findings,
            'pages_crawled': pages
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
            delay = float(input('Delay between requests in seconds (default 0.5): ').strip() or 0.5)
            out = input('Output directory (default reports): ').strip() or 'reports'
            report, paths = self.run_scan(target, wordlist_path=wl, max_workers=workers, delay=delay, output_dir=out)
            print('Done. Reports:', paths)
        elif choice == '3':
            target = input('Target: ').strip()
            login_url = input('Login URL (form action): ').strip()
            uname = input('Username: ').strip()
            pwd = input('Password: ').strip()
            if self.login_flow(login_url, username_field='username', password_field='password', username=uname, password=pwd):
                print('Login succeeded (cookies stored). Starting scan...')
                report, paths = self.run_scan(target)
                print('Done. Reports:', paths)
            else:
                print('Login failed. Aborting.')
        elif choice == '4':
            state = self.load_state()
            print('Loaded state:', state)
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

    args = parser.parse_args()

    cli = EduScannerCLI()
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