"""r3cross.py <r3 seal.py.txt> <candidate-dir>: every name of the r3 hand-picked seal table that is
not in the automatic candidate list of the same file."""
import sys
src = open(sys.argv[1]).read(); D = sys.argv[2]
G = "TCSlib.Cryptography.Games."; C = "TCSlib.Cryptography."
body = src[src.index('SEALS = {'):src.index('}\nenv') + 1]
SEALS = eval(body[len('SEALS = '):], {'G': G, 'C': C})
tot = miss = 0
for path, names in SEALS.items():
    mod = path[:-5].replace('/', '.')
    mine = {l.split('\t')[0].replace('# already-irreducible: ', '') for l in open(f'{D}/{mod}.txt')
            if l.strip() and (not l.startswith('#') or l.startswith('# already-irreducible:'))}
    for n in names:
        tot += 1
        if n not in mine:
            miss += 1; print('  not in the automatic list:', path, n)
print(f"{tot} names in the r3 table (13 files); {miss} not in the automatic lists")
