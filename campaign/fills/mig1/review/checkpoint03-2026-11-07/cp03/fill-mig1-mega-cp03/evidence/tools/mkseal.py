"""mkseal.py <src.lean> <out.lean> <decl names comma-separated> <irreducible names> <-simp names>
Write a sealed copy of a module: each named declaration chunk (docstring included, as chunked by
devtools/seyoon/declfreeze.py) is wrapped in its own section carrying
`attribute [local irreducible] ...` and `attribute [-simp] ...`. Everything else is verbatim."""
import sys, os
src, out, names, irr, nosimp = sys.argv[1:6]
repo = os.environ.get('TCSLIB_REPO', '.')
code = open(os.path.join(repo, 'devtools/seyoon/declfreeze.py'), encoding='utf-8').read()
code = code[:code.index('a = chunks(open(sys.argv[1])')]
ns = {}; exec(compile(code, 'declfreeze.py', 'exec'), ns)
text = open(src, encoding='utf-8').read()
want = [n for n in names.split(',') if n]
ch = {n: t for n, p, t in ns['chunks'](text)}
irr_l = ' '.join(x for x in irr.split(',') if x); ns_l = ' '.join(x for x in nosimp.split(',') if x)
done = []
for i, n in enumerate(want):
    key = [k for k in ch if k == n or k.endswith('.' + n)]
    assert len(key) == 1, (n, key)
    t = ch[key[0]]
    assert text.count(t) == 1, n
    hdr = f'section MIG1Seal{i}\nattribute [local irreducible] {irr_l}\n' + (f'attribute [-simp] {ns_l}\n' if ns_l else '')
    text = text.replace(t, hdr + t + f'\n\nend MIG1Seal{i}')
    done.append(key[0])
open(out, 'w', encoding='utf-8').write(text)
print('sealed', len(done), 'declarations:', ', '.join(done))
