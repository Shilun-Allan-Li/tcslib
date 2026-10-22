import sys, re
# usage: spans.py file name1 name2 ...  -- span = attached docstring start .. last nonblank line before next blank-separated block/decl
path = sys.argv[1]; names = sys.argv[2:]
L = open(path, encoding='utf-8').read().split('\n')
decl = re.compile(r'^(private |protected )?(noncomputable )?(@\[[^\]]*\] )?(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)')
total = 0
for nm in names:
    idx = None
    for i, l in enumerate(L):
        m = decl.match(l)
        if m and m.group(5) == nm:
            idx = i; break
    assert idx is not None, nm
    # docstring start: walk back over the contiguous block above
    s = idx
    if idx > 0 and L[idx-1].rstrip().endswith('-/'):
        j = idx - 1
        while not L[j].lstrip().startswith('/--'):
            j -= 1
        s = j
    # end: last line before first blank line or next decl/docstring start at column 0
    e = idx
    j = idx + 1
    while j < len(L) and L[j].strip() != '' and not decl.match(L[j]) and not L[j].startswith('/--') and not L[j].startswith('end ') :
        e = j; j += 1
    n = e - s + 1
    total += n
    print(f"{nm}: lines {s+1}-{e+1} ({n})")
print("total", total)
