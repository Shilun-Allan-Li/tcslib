import sys, re, os
a_dir, b_dir = sys.argv[1], sys.argv[2]
def norm(p):
    L = open(p, 'rb').read().decode('utf-8', 'surrogateescape').split('\n')
    # drop the trailing "-- \n<version>\n" signature
    while L and L[-1] == '': L.pop()
    if len(L) >= 2 and L[-2] == '-- ': L = L[:-2]
    out = []
    for l in L:
        m = re.match(r'^index ([0-9a-f]+)\.\.([0-9a-f]+)(.*)$', l)
        if m: l = 'index %s..%s%s' % (m.group(1)[:7], m.group(2)[:7], m.group(3))
        out.append(l)
    return out
for f in sorted(os.listdir(a_dir)):
    pa, pb = os.path.join(a_dir, f), os.path.join(b_dir, f)
    if not os.path.exists(pb): print('MISSING', f); continue
    na, nb = norm(pa), norm(pb)
    if na == nb: print('EQUAL (index abbreviation, version trailer aside)', f)
    else:
        import difflib
        d = list(difflib.unified_diff(na, nb, lineterm='', n=0))
        print('DIFFER', f, len(d)); print('\n'.join(d[:20]))
