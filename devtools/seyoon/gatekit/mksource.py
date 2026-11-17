"""Gate 143: declaration inventory of the reader PR (SOURCE.json at head, SOURCE-base.json at the
campaign base), in the format the seal scripts read. Usage: mksource.py <head> <base> <outdir>"""
import hashlib, json, re, subprocess, sys
from pathlib import Path

head, base, out = sys.argv[1], sys.argv[2], Path(sys.argv[3])
import os as _os
_GATE = Path(_os.environ['GATE']); _CFG = json.loads((_GATE/'gate.json').read_text())
REPO = _CFG['repo']
decl = (Path(REPO)/'devtools/seyoon/declfreeze.py').read_text()
ns = {}
exec(compile(decl.split('a = chunks(open(sys.argv[1]).read())')[0], 'declfreeze', 'exec'), ns)
chunks = ns['chunks']
new_owners = set()
changed = [l for l in (_GATE/'CHANGED.txt').read_text().split() if l]


def show(rev, path):
    # Gate 149: a new owner (absent at base) reads as an empty file there.
    r = subprocess.run(['git', '-C', REPO, 'show', f'{rev}:{path}'], capture_output=True)
    if r.returncode and rev == base and path in new_owners:
        return ''
    r.check_returncode()
    return r.stdout.decode()


def kind(text):
    body = text.split('-/', 1)[1].lstrip() if text.startswith('/--') else text
    m = re.match(r'(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(\w+)', body)
    return m.group(1) if m else '?'


def statement(text):
    # Gate 144 G144-02: the declaration's own body delimiter is the first `:=` at bracket depth 0
    # that is followed by `by` or a line break (a `let x := e` inside the type is neither).
    body = text.split('-/', 1)[1] if text.startswith('/--') else text
    depth = 0
    for k, ch in enumerate(body):
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif depth == 0 and body.startswith(':=', k) and re.match(r':=[ \t]*(by\b|\n)', body[k:]):
            return re.sub(r'\s+', ' ', body[:k]).strip()
    return re.sub(r'\s+', ' ', body).strip()


rows_h, rows_b = [], []
added, removed, header_changed, definitions_changed = [], [], [], []
for path in changed:
    h, b = show(head, path), show(base, path)
    ch = {n: (p, t) for n, p, t in chunks(h)}
    cb = {n: (p, t) for n, p, t in chunks(b)}
    diff = [n for n in ch if n not in cb or cb[n][1] != ch[n][1]]
    gone = [n for n in cb if n not in ch]
    for n in diff:
        if n not in cb:
            if not ch[n][0]:
                added.append(n)
        else:
            if statement(cb[n][1]) != statement(ch[n][1]):
                header_changed.append(n)
            if kind(ch[n][1]) in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance'):
                definitions_changed.append(n)
    removed += gone
    rows_h.append({'path': path, 'sha256': hashlib.sha256(h.encode()).hexdigest(),
                   'total_changed_or_added_from_campaign': diff, 'removed_from_campaign': gone})
    rows_b.append({'path': path, 'sha256': hashlib.sha256(b.encode()).hexdigest(),
                   'total_changed_or_added_from_campaign': [n for n in diff if n in cb],
                   'removed_from_campaign': []})
common = {'head': head, 'base': base, 'added': added, 'removed': removed,
          'header_changed': header_changed, 'definitions_changed': definitions_changed}
(out / 'SOURCE.json').write_text(json.dumps(common | {'owner_source': rows_h}, ensure_ascii=False, indent=1) + '\n')
(out / 'SOURCE-base.json').write_text(json.dumps(common | {'owner_source': rows_b}, ensure_ascii=False, indent=1) + '\n')
print('owners', len(rows_h), 'changed-or-added', sum(len(r['total_changed_or_added_from_campaign']) for r in rows_h),
      'added', len(added), 'removed', removed, 'header_changed', header_changed,
      'definitions_changed', definitions_changed)
