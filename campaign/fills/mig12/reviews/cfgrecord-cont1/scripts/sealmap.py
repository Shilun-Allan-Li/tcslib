import sys, re, json
# usage: sealmap.py <seal out> <seal file .map.json> <original module> : map body diagnostics to original
# lines and declarations; count control diagnostics.
out, mp, orig = sys.argv[1:4]
ins = json.load(open(mp))
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)')
L = open(orig, encoding='utf-8').read().split('\n')
starts = [(i + 1, DECL.match(l).group(5)) for i, l in enumerate(L) if DECL.match(l)]
def decl(ln):
    n = '?'
    for s, d in starts:
        if s <= ln: n = d
        else: break
    return n
ctl = body = 0
for l in open(out, encoding='utf-8', errors='replace'):
    m = re.match(r'^\S+?\.lean:(\d+):(\d+): (error|warning)', l)
    if not m: continue
    o = ins[int(m.group(1)) - 1]
    if o is None: ctl += 1; continue
    body += 1
    print(f'BODY {m.group(3)} original line {o}:{m.group(2)} in {decl(o)}: {l.split(": ", 2)[-1].strip()[:90]}')
print(f'control diagnostics {ctl}; body diagnostics {body}')
