import sys, re
# usage: bisect.py <src.lean> <outprefix> : writes one variant per theorem, all other proofs sorried
src = open(sys.argv[1]).read(); pre = sys.argv[2]
names = re.findall(r'^theorem (\S+)', src, re.M)
def sorry_all_but(s, keep):
    out = s
    for n in names:
        if n == keep: continue
        i = out.index('theorem ' + n + ' ') if ('theorem ' + n + ' ') in out else out.index('theorem ' + n + '\n')
        # find ':= by' or ':=\n' at top-level after statement: first occurrence of ':= by' or ' :=\n'
        cands = [x for x in [out.find(':= by', i), out.find(':=\n', i)] if x != -1]
        j = min(cands)
        k = out.find('\n\n', j)
        out = out[:j] + ':= by\n  sorry' + out[k:]
    return out
for idx, n in enumerate(names):
    open(f'{pre}{idx}.lean', 'w').write(sorry_all_but(src, n))
    print(idx, n)
