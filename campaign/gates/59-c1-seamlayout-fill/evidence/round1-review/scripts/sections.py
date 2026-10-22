import sys, hashlib
for d, bname, lean_rev, rec_rev in [
  ("59-c1-seamlayout-fill-gate","c1-seamlayout-bundle.md","126127b8959e4b64b37ac8ed15c0b1b05d747c9e","34af2e0f3bc984f336d08da42f55d448feb78a7b"),
  ("60-b6-f5-cont1-fill-gate","b6-f5-cont1-bundle.md","8114e482fcad1f1d07abdcc244ef74755b752b56","050d547e148dfbca2fc5a3b5846f0973644cb2c1"),
  ("61-s13d-g4-cont3-fill-gate","s13d-g4-cont3-bundle.md","13e1758929aa0eb3f298a8dd399e3dbc4bd809c0","050d547e148dfbca2fc5a3b5846f0973644cb2c1")]:
    base=sys.argv[1]+"/"+d
    data=open(base+"/"+bname,'rb').read()
    lines=data.decode('utf-8').split('\n')
    heads=[l[9:-6] for l in lines if l.startswith('## ===== ') and l.endswith(' =====')]
    lst=[l.strip() for l in open(base+"/BUNDLE-FILES.txt") if l.strip()]
    print(f"{d}: sha256 {hashlib.sha256(data).hexdigest()} bytes {len(data)}; section headers {len(heads)} (distinct {len(set(heads))}); list {len(lst)}; headers==list order: {heads[:len(lst)]==lst}")
