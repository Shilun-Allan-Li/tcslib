import re, os, sys, functools
ROOT='/workspace/cp2/src'
@functools.lru_cache(None)
def imps(m):
    p=f'{ROOT}/{m.replace(".","/")}.lean'
    if not os.path.exists(p): return ()
    src=open(p).read()
    exec(open('/workspace/cp2/tools/chk.py').read().split('def header_imports')[1].split('imports = header_imports')[0].join(['def header_imports','']), globals())
    return tuple(x for x in header_imports(src) if x.startswith('TCSlib') or x.startswith('audits'))
@functools.lru_cache(None)
def clos(m):
    s=set()
    for x in imps(m): s.add(x); s|=clos(x)
    return frozenset(s)
if __name__=='__main__':
    tgt=sys.argv[1]
    for m in sys.argv[2:]:
        print(m, 'imports' if tgt in clos(m) else 'DOES NOT import', tgt)
