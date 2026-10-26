"""For each declaration in a line range of a Lean file: proof length (lines after ':=' / 'where' to the next declaration) and whether its docstring has a literal 'Proof sketch'.
Usage: sketches.py <file> <lo> <hi> [<lo> <hi> ...] (1-based, inclusive ranges of interest)"""
import re, sys
f = sys.argv[1]; L = open(f, encoding='utf-8').read().split('\n')
rngs = [(int(sys.argv[i]), int(sys.argv[i+1])) for i in range(2, len(sys.argv), 2)]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
starts = []
for i, l in enumerate(L):
    m = DECL.match(l)
    if m: starts.append((i, m.group(2)))
for idx, (i, name) in enumerate(starts):
    if not any(lo - 1 <= i <= hi - 1 for lo, hi in rngs): continue
    # docstring: scan back to '/--'
    j = i - 1; doc = ''
    if j >= 0 and L[j].rstrip().endswith('-/'):
        k = j
        while k >= 0 and '/--' not in L[k]: k -= 1
        doc = '\n'.join(L[k:j+1])
    end = starts[idx+1][0] if idx + 1 < len(starts) else len(L)
    # trim trailing blank lines and docstring of the next decl
    e = end - 1
    while e > i and (L[e].strip() == '' or L[e].strip().startswith('/-') or L[e].rstrip().endswith('-/') or (L[e].strip() and not L[e].startswith(' ') and not L[e].startswith('theorem') and not DECL.match(L[e]) and e > i and L[e][0] != ' ')):
        e -= 1
    # proof start: first line containing ':= by' or ':=' at end or ' where'
    p = None
    for t in range(i, e + 1):
        s = L[t]
        if re.search(r':=\s*by\s*$|:=\s*$|\bwhere\s*$|:= by\b', s) or (t > i and s.startswith('  ') and False):
            p = t; break
    plen = (e - p) if p is not None else 0
    print(f'{i+1:5d} {name:32s} proof {plen:4d} lines; docstring {"yes" if doc else "NO "}; Proof sketch {"yes" if "Proof sketch" in doc else "no"}{"  <-- >20 without sketch" if plen > 20 and "Proof sketch" not in doc else ""}')
