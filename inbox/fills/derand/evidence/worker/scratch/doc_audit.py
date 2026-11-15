import json
from pathlib import Path
import runpy

tools = Path(__file__).parent
scanner = runpy.run_path(str(tools / 'frozen_headers.py'))
rows = json.loads(Path('evidence/clash/all-additions/results.json').read_text())['additions']
issues, record = [], []
for row in rows:
    source = Path(row['path']).read_text()
    declaration = next(item for item in scanner['extract'](source)
                       if item['name'] == row['name'].rsplit('.', 1)[-1])
    start = source.rfind('/--', 0, declaration['start'])
    end = source.find('-/', start) if start >= 0 else -1
    doc = source[start:end + 2] if end < declaration['start'] else ''
    header = declaration['header']
    if header.startswith('open '):
        header = header.split('\n', 1)[1]
    body = declaration['whole'][len(header):]
    proof_lines = sum(bool(line.strip()) for line in body.splitlines())
    sketch = '**Proof sketch' in doc
    if not row['private'] and not doc:
        issues.append((row['name'], 'missing docstring'))
    if row['kind'] in ['theorem', 'lemma'] and proof_lines >= 15 and not sketch:
        issues.append((row['name'], 'missing long-proof sketch', proof_lines))
    record.append(dict(name=row['name'], docstring=bool(doc), private=row['private'],
                       proof_nonblank_lines=proof_lines, sketch=sketch))
folder = Path('evidence/docs')
folder.mkdir(parents=True, exist_ok=True)
(folder / 'results.json').write_text(json.dumps(dict(declarations=record, issues=issues), indent=2) + '\n')
print(f'DOC AUDIT {"PASS" if not issues else "FAIL"}: {len(record)} additions; {len(issues)} issues')
for issue in issues:
    print(issue)
raise SystemExit(bool(issues))
