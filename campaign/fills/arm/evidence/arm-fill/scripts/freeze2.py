"""Independent statement/body/docstring comparison for the modified files (complements
the maintainer's declfreeze.py).
usage: python3 -I freeze2.py <before-file> <after-file> [<name,name,...> to print docstring diffs]
Declarations are located on the comment-stripped text (line structure kept). For each one:
  doc   = the raw `/-- ... -/` block ending on the line just above the header (attributes skipped)
  stmt  = stripped text from the header to the first `:=` / `where` / `|` at bracket depth 0
  body  = stripped text after that, up to the next declaration or stop line
Prints: statement changes (exact and whitespace-normalized), body changes, docstring changes,
additions, removals, sorry status, and the [Tag, ...] citation sets of changed docstrings.
"""
import difflib, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines, DECL

STOP = re.compile(r'^(end\b|namespace\b|section\b|open\b|variable\b|set_option\b|#|attribute\b|'
                  r'universe\b|noncomputable section\b|import\b)')
TOK = re.compile(r'(?<![A-Za-z0-9_.\'])sorry(?![A-Za-z0-9_\'])')
TAG = re.compile(r'\[([A-Z][A-Za-z]+[0-9]{2}[a-z]?)((?:,|;)[^\]]*)?\]')

def split_stmt(s):
    """Split at the first depth-0 `:=`, depth-0 `where`, or a line starting with `|`."""
    d = 0; i = 0
    while i < len(s):
        ch = s[i]
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and s.startswith(':=', i): return s[:i], s[i:]
        elif (d == 0 and s.startswith('where', i) and (i == 0 or not (s[i-1].isalnum() or s[i-1] in '_.'))
              and (i + 5 == len(s) or not (s[i+5].isalnum() or s[i+5] in '_'))):
            return s[:i], s[i:]
        elif d == 0 and ch == '|' and s[:i].split('\n')[-1].strip() == '' and '\n' in s[:i]:
            return s[:i], s[i:]
        i += 1
    return s, ''

def comment_blocks(raw):
    """Map end line (0-based) -> (start line, opener) for every top-level block comment."""
    res = {}; i = 0; depth = 0; n = len(raw); line = 0; start = None
    while i < n:
        if raw.startswith('/-', i):
            if depth == 0:
                opener = '/--' if raw.startswith('/--', i) else ('/-!' if raw.startswith('/-!', i) else '/-')
                start = (line, opener)
            depth += 1; i += 2; continue
        if depth and raw.startswith('-/', i):
            depth -= 1; i += 2
            if depth == 0: res[line] = start
            continue
        if depth == 0 and raw.startswith('--', i):
            j = raw.find('\n', i)
            if j < 0: break
            i = j; continue
        if raw[i] == '\n': line += 1
        i += 1
    return res

def parse(path):
    raw = open(path, encoding='utf-8').read()
    rl = raw.split('\n'); st = strip_keep_lines(raw); sl = st.split('\n')
    blocks = comment_blocks(raw)
    heads = []
    for i, l in enumerate(sl):
        m = DECL.match(l)
        if m: heads.append((i, m))
    stops = [i for i, l in enumerate(sl) if STOP.match(l)]
    out = {}
    for k, (i, m) in enumerate(heads):
        nxt = [j for j in [h[0] for h in heads[k + 1:k + 2]] + [s for s in stops if s > i][:1]]
        end = min(nxt) if nxt else len(sl)
        # backtrack over trailing docstring/comment-only lines that belong to the next decl
        text = '\n'.join(sl[i:end]).rstrip()
        stmt, body = split_stmt(text)
        # docstring: raw lines above the header, skipping attribute-only lines
        j = i - 1
        while j >= 0 and (re.match(r'^\s*@\[[^\]]*\]\s*$', rl[j]) or rl[j].strip() == 'noncomputable'
                          or re.match(r'^\s*open\b.*\bin\s*$', rl[j])):
            j -= 1
        doc = ''
        if j >= 0 and rl[j].rstrip().endswith('-/') and j in blocks and blocks[j][1] == '/--':
            doc = '\n'.join(rl[blocks[j][0]:j + 1])
        name = m.group(3)
        out[name] = dict(kind=m.group(2), private='private' in m.group(1).split(), line=i + 1,
                         stmt=stmt.strip(), body=body.strip(), doc=doc,
                         sorry=len(TOK.findall(text)))
    return out

def norm(s): return ' '.join(s.split())
def tags(doc): return sorted({m.group(0) for m in TAG.finditer(doc)})

if __name__ == '__main__':
    a, b = parse(sys.argv[1]), parse(sys.argv[2])
    show = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else set()
    print(f'declarations before/after: {len(a)}/{len(b)}')
    for n in sorted(set(a) | set(b)):
        if n not in b: print(f'REMOVED  {n} (line {a[n]["line"]}, private={a[n]["private"]}, sorry {a[n]["sorry"]})'); continue
        if n not in a: print(f'ADDED    {n} (line {b[n]["line"]}, {b[n]["kind"]}, private={b[n]["private"]}, sorry {b[n]["sorry"]})'); continue
        x, y = a[n], b[n]
        flags = []
        if x['stmt'] != y['stmt']:
            flags.append('STATEMENT CHANGED (exact)' + ('' if norm(x['stmt']) != norm(y['stmt']) else ' — whitespace only'))
        if x['body'] != y['body']: flags.append('body changed')
        if x['doc'] != y['doc']: flags.append('docstring changed')
        if x['sorry'] != y['sorry']: flags.append(f'sorry {x["sorry"]} -> {y["sorry"]}')
        if flags: print(f'CHANGED  {n}: ' + '; '.join(flags))
    for n in sorted(show):
        if n in a and n in b:
            x, y = a[n], b[n]
            print(f'\n===== {n}: statement {"identical" if x["stmt"] == y["stmt"] else "DIFFERS"}; sorry {x["sorry"]} -> {y["sorry"]}')
            print('statement:\n' + y['stmt'])
            print(f'tags before: {tags(x["doc"])}')
            print(f'tags after:  {tags(y["doc"])}')
            print(f'tags dropped: {sorted(set(tags(x["doc"])) - set(tags(y["doc"])))}; added: {sorted(set(tags(y["doc"])) - set(tags(x["doc"])))}')
            sys.stdout.writelines(difflib.unified_diff((x['doc'] + '\n').splitlines(True), (y['doc'] + '\n').splitlines(True), f'before/{n}.doc', f'after/{n}.doc'))
