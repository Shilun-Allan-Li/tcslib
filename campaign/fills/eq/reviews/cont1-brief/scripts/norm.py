import re, sys
def norm(s):
    s = re.sub(r'[A-Za-z0-9_./-]*?(c1probe|rvprobe|eqprobe|probe)/', 'PROBE/', s)
    s = re.sub(r'_private\.[A-Za-z0-9_.]*?\.0\.', '_private.X.0.', s)
    return s
a = norm(open(sys.argv[1], encoding='utf-8').read()); b = norm(open(sys.argv[2], encoding='utf-8').read())
print("IDENTICAL" if a == b else "DIFFER")
if a != b:
    import difflib
    for l in difflib.unified_diff(a.splitlines(), b.splitlines(), lineterm='', n=0): print(l)
