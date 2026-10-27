"""Extract the sealed bodies of the route probe and the review probe (between `attribute [local
irreducible] ...` and `end Sealed`), dropping the named declarations, and print them."""
import re, sys
def body(path, drop):
    t = open(path, encoding='utf-8').read()
    a = t.index('section Sealed')
    # skip the attribute block: up to the first blank line after it
    b = t.index('\n\n', t.index('attribute [local irreducible]', a)) + 2
    e = t.index('end Sealed', b)
    chunk = t[b:e]
    # split into blocks at blank lines followed by a doc comment / decl / section comment
    blocks = re.split(r'\n(?=/-[-!]|theorem |def |inductive |example )', chunk)
    out = []
    skip = False
    for blk in blocks:
        m = re.search(r'^(?:theorem|def|inductive)\s+(\S+)', blk, re.M)
        name = m.group(1) if m else None
        out.append((name, blk))
    # attach doc comments to the following declaration
    res, pending = [], ''
    for name, blk in out:
        if name is None and blk.lstrip().startswith('/--'):
            pending += blk + '\n'; continue
        if name in drop:
            pending = ''; continue
        res.append(pending + blk); pending = ''
    return '\n'.join(res)
route, review = sys.argv[1], sys.argv[2]
print(body(route, {'qy_guard'}))
print(body(review, set()))
