import sys, importlib.util, json
spec = importlib.util.spec_from_file_location('df', sys.argv[1])
src_df = open(sys.argv[1], encoding='utf-8').read()
# load only the chunks() function from declfreeze (the module body runs on argv; avoid that)
ns = {}
code = src_df.split("a = chunks(open(sys.argv[1]).read())")[0]
exec(compile(code, 'declfreeze-head', 'exec'), ns)
chunks = ns['chunks']
A = {n: (p, t) for n, p, t in chunks(open(sys.argv[2], encoding='utf-8').read())}
B = {n: (p, t) for n, p, t in chunks(open(sys.argv[3], encoding='utf-8').read())}
new = [n for n in B if n not in A]
changed = [n for n in B if n in A and A[n][1] != B[n][1]]
removed = [n for n in A if n not in B]
json.dump({'new': new, 'changed': changed, 'removed': removed, 'all': list(B)}, open(sys.argv[4], 'w'), indent=0)
print('new', len(new), 'changed', len(changed), 'removed', len(removed), removed, 'all', len(B))
print('changed:', changed)
print('new non-private:', [n for n in new if not B[n][0]])
