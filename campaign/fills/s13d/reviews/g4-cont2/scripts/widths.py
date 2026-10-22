import sys
for p in sys.argv[1:]:
    ls = open(p, encoding='utf-8').read().split('\n')
    w = [len(l) for l in ls]
    over = [(i + 1, n) for i, n in enumerate(w) if n > 100]
    print(f'{p.split("/")[-1]}: lines {len(ls) - (1 if ls[-1] == "" else 0)}, max width {max(w)}, over 100: {over}')
