import sys, subprocess
# usage: mkbundle-mixed.py <root> <lean-rev> <other-rev> <out> <orderfile> [--verify]
root, lrev, orev, out, order = sys.argv[1:6]
verify = '--verify' in sys.argv
paths = [l.strip() for l in open(order) if l.strip()]
def rev(p): return lrev if p.startswith('TCSlib/') else orev
def read(p):
    return subprocess.run(['git', 'show', f'{rev(p)}:{p}'], capture_output=True, text=True, cwd=root, check=True).stdout
def seg(p):
    c = read(p); c = c + ('' if c.endswith('\n') else '\n')
    if p.endswith('.lean') or p.endswith('.py'): c = '```\n' + c + '```\n'
    return f'## ===== {p} =====\n\n' + c
parts = [seg(p) for p in paths]
text = '\n'.join(parts)
if not verify:
    open(out, 'w', encoding='utf-8').write(text); print('wrote', len(paths), 'segments')
else:
    got = open(out, encoding='utf-8').read()
    assert got == text, 'bundle differs from a fresh rebuild'
    heads = [l[9:-6] for l in got.split('\n') if l.startswith('## ===== ') and l.endswith(' =====')]
    assert heads[:len(paths)] == paths or heads == paths, 'header order'
    print('verified', len(paths), 'segments; header lines', len(heads))
