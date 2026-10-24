import re, sys
# usage: axcmp.py <mine> <worker's> : compare axiom prints by declaration short name
def prints(p):
    t = open(p, encoding='utf-8').read()
    d = {}
    for n, a in re.findall(r"'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)", t, re.S):
        short = n.split('.0.')[-1] if '_private' in n else n
        short = short.removeprefix('Turing.')
        d[short] = ' '.join(a.split())
    return d
a, b = prints(sys.argv[1]), prints(sys.argv[2])
print('mine', len(a), "worker's", len(b))
print('only mine:', sorted(set(a) - set(b))); print("only worker's:", sorted(set(b) - set(a)))
diff = [n for n in set(a) & set(b) if a[n] != b[n]]
print('different sets:', [(n, a[n], b[n]) for n in sorted(diff)])
