import sys
for p in sys.argv[1:]:
    L = open(p, encoding='utf-8').read().split('\n')
    w = [(len(l), i + 1) for i, l in enumerate(L)]
    m = max(w)
    over = [i for n, i in w if n > 100]
    print(f'{p}: {len(L) - (1 if L[-1] == "" else 0)} lines, max {m[0]} chars (line {m[1]}), over 100: {over}')
