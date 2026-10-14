"""Import graph of a TCSlib worktree, from the `import` lines of every module. Read-only.
Usage: python3 -I importgraph.py <worktree> closure <Module> ...   (transitive TCSlib imports)
       python3 -I importgraph.py <worktree> replay <Module> ...    (modules equal to or importing any)
       python3 -I importgraph.py <worktree> importers <Module>     (direct and transitive importers)
"""
import sys, glob, os


def graph(root):
    G = {}
    for f in glob.glob(os.path.join(root, 'TCSlib', '**', '*.lean'), recursive=True):
        m = os.path.relpath(f, root)[:-5].replace(os.sep, '.')
        G[m] = [l.split()[1] for l in open(f, encoding='utf-8') if l.startswith('import ')]
    top = os.path.join(root, 'TCSlib.lean')
    if os.path.isfile(top):
        G['TCSlib'] = [l.split()[1] for l in open(top, encoding='utf-8') if l.startswith('import ')]
    return G


def clos(G, m):
    seen, st = set(), [m]
    while st:
        x = st.pop()
        for y in G.get(x, []):
            if y.startswith('TCSlib') and y not in seen:
                seen.add(y); st.append(y)
    return seen


if __name__ == '__main__':
    root, mode, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
    G = graph(root)
    mods_in = [m for m in G if m != 'TCSlib']
    if mode == 'closure':
        for m in mods:
            print(m, '->', ' '.join(sorted(clos(G, m))))
    elif mode == 'replay':
        S = set(mods)
        R = sorted(m for m in mods_in if m in S or clos(G, m) & S)
        print(f'modules: {len(mods_in)}; replay closure: {len(R)}')
        from collections import Counter
        c = Counter('.'.join(m.split('.')[:3]) for m in R)
        for k, v in sorted(c.items()):
            print(f'  {k}: {v}')
        for m in R:
            print('  ', m)
    elif mode == 'importers':
        for m in mods:
            d = sorted(x for x in mods_in if m in G[x])
            t = sorted(x for x in mods_in if m in clos(G, x))
            print(m, 'direct', len(d), 'transitive', len(t))
            for x in d:
                print('  direct', x)
