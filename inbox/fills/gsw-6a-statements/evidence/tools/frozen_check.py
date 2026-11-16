"""frozen_check.py <repo> <base> <head> <allowed.tsv> <file>... [--control-alter F:NAME] [--control-delete F:NAME]
Check 8 (frozen files): every declaration of each changed existing Lean file is extracted at <base> and
<head> with touched.py's declaration cutter (doc comment, attributes, statement and body; private ones
included) and compared byte for byte: (a) the header (doc comment through the statement, up to the
top-level `:=`/`where`/`|`) and (b) the whole declaration. Lines of <allowed.tsv> (`file<TAB>name<TAB>
what`, what in REMOVED / BODY) license O1's documented changes. Anything else is a VIOLATION.
--control-alter alters one character of NAME's header in the head text; --control-delete deletes NAME
from the head text (in memory only): the controls must report exactly one difference / one removal."""
import sys, re, subprocess
src = open('/home/user/work/tools/xr/touched.py', encoding='utf8').read()
code = src[src.index('def show('):src.index('report = {')]
repo, base, head, allowedf = sys.argv[1:5]
rest = sys.argv[5:]
ctrl_alter = ctrl_del = None
files = []
i = 0
while i < len(rest):
    if rest[i] == '--control-alter': ctrl_alter = rest[i + 1]; i += 2
    elif rest[i] == '--control-delete': ctrl_del = rest[i + 1]; i += 2
    else: files.append(rest[i]); i += 1
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\b\s*([^\s(:{\[]*)')
TOP = re.compile(r'^(namespace|end|section|open|variable|universe|set_option|attribute|noncomputable section|mutual|#|example|import|/-!)')
g = {'re': re, 'subprocess': subprocess, 'repo': repo, 'DECL': DECL, 'TOP': TOP}
exec(code, g)
decls, show = g['decls'], g['show']
allowed = {}
for l in open(allowedf, encoding='utf8'):
    if l.strip() and not l.startswith('#'):
        f, n, w = l.rstrip('\n').split('\t')[:3]; allowed[(f, n)] = w
def header(text):
    d = 0; k = text.find('-/') + 2 if text.lstrip().startswith('/--') else 0
    while k < len(text):
        ch = text[k]
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (text.startswith(':=', k) or re.match(r'\bwhere\b', text[k:]) or
                         (text[k] == '|' and text[k - 1] == '\n' + '' or text.startswith('\n  |', k))):
            return text[:k]
        k += 1
    return text
viol = 0; ndiff = 0; nrem = 0
for f in files:
    old, new = show(base, f), show(head, f)
    if ctrl_alter and ctrl_alter.split(':')[0] == f:
        name = ctrl_alter.split(':')[1]
        d = next(x for x in decls(new) if x['name'] == name)
        pos = new.index(d['text']) + d['text'].index('≤')   # one character of the statement: ≤ -> <
        new = new[:pos] + '<' + new[pos + 1:]
    if ctrl_del and ctrl_del.split(':')[0] == f:
        name = ctrl_del.split(':')[1]
        d = next(x for x in decls(new) if x['name'] == name)
        new = new.replace(d['text'], '', 1)
    a = {d['name']: d for d in decls(old)}
    b = {d['name']: d for d in decls(new)}
    print(f'== {f}: base {len(a)} declarations, head {len(b)}')
    for n in sorted(set(a) | set(b)):
        if n not in b:
            nrem += 1
            ok = allowed.get((f, n)) == 'REMOVED'
            print(f"{'REMOVED(allowed)' if ok else 'VIOLATION REMOVED'}\t{n}"); viol += not ok; continue
        if n not in a:
            print(f'VIOLATION ADDED\t{n}'); viol += 1; ndiff += 1; continue
        ha, hb = header(a[n]['text']), header(b[n]['text'])
        if ha != hb:
            print(f'VIOLATION HEADER\t{n}'); viol += 1; ndiff += 1; continue
        if a[n]['text'] != b[n]['text']:
            ok = allowed.get((f, n)) == 'BODY'
            print(f"{'BODY(allowed)' if ok else 'VIOLATION BODY'}\t{n}"); viol += not ok; ndiff += 1; continue
        print(f'IDENTICAL\t{n}')
print(f'RESULT violations={viol} differences={ndiff} removals={nrem}')
