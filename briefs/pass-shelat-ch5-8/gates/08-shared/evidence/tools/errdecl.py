"""errdecl.py <sealed.lean> <sealed.out> <touched.txt>: the declaration enclosing each error, and
whether it is touched."""
import re, sys
src, out, tf = sys.argv[1:4]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example)\s*([^\s(:{\[]*)")
L = open(src, encoding='utf-8').read().split('\n')
touched = {l.strip() for l in open(tf) if l.strip()}
starts = [(i + 1, m.group(2)) for i, l in enumerate(L) if (m := DECL.match(l))]
seen = set()
for l in open(out):
    m = re.match(r'.*?\.lean:(\d+):\d+: error', l)
    if not m: continue
    ln = int(m.group(1))
    d = max((s for s in starts if s[0] <= ln), default=(0, '?'))
    if d in seen: continue
    seen.add(d)
    print(f"line {ln}: decl `{d[1]}` (starts {d[0]}) touched={d[1] in touched}")
