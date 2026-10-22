"""Union of rewindTM's stripped body covered by the tiles of its screen pairs (gate 55 review).
Usage: python3 -I rewind_cover.py <census_rw.py> <Rewind.lean> <Catalog.lean>"""
import sys, importlib.util, re
spec = importlib.util.spec_from_file_location('c', sys.argv[1])
src = open(sys.argv[1], encoding='utf-8').read()
ns = {}
exec(compile(src.split("rw_all = decls(")[0].replace("rw_path, outp, others = sys.argv[1], sys.argv[2], sys.argv[3:]", ""), 'c', 'exec'), ns)
rw = {d[1]: d for d in ns['decls'](sys.argv[2], 'Rewind.lean', keep_short=True)}
cat = {d[1]: d for d in ns['decls'](sys.argv[3], 'Catalog.lean')}
body = rw['rewindTM'][3]
cover = [False] * len(body)
for other in ['skipBackTM', 'seekStartTM', 'skipTM', 'seekEndTM']:
    ob = cat[other][3]
    for a, b in ((body, ob), (ob, body)):
        sh, tiles = ns['tiled'](a, b)
        for t in tiles:
            i = body.find(t)
            for j in range(i, i + len(t)): cover[j] = True
        print(f'{other}: tiled {sh}; tiles {[len(t) for t in tiles]}')
print(f'rewindTM body {len(body)}; covered by any pair {sum(cover)} ({sum(cover)/len(body):.0%})')
print('uncovered:', ''.join(c if not v else '.' for c, v in zip(body, cover)))
print('rewindTM body:', body)
print('skipBackTM body:', cat['skipBackTM'][3])
