r"""relational_headers.py <design-r1.md> <Relational.lean> (bb1-sim-statements, lead): the three
headers of design r1 §2.2 (from the line `theorem <name>` through the line ending in `:= by`, byte
for byte) against the module. Also lists the module's imports against the design's. PASS iff all
three headers and the import lines are identical. Exit 0 iff PASS."""
import sys, re
design, mod = sys.argv[1], sys.argv[2]
d = open(design, encoding='utf-8').read()
blk = d.split('### 2.2 Statement-phase text of the new module', 1)[1].split('```lean\n', 1)[1]
blk = blk.split('\n```\n', 1)[0]
m = open(mod, encoding='utf-8').read()
def header(src, name):
    ls = src.split('\n')
    i = next(k for k, l in enumerate(ls) if re.match(r'^theorem ' + re.escape(name) + r'\b', l))
    j = next(k for k in range(i, len(ls)) if ls[k].rstrip().endswith(':= by'))
    return '\n'.join(ls[i:j + 1])
ok = True
for n in ['expect_simulate_rel', 'prob_simulate_rel', 'expect_sample_rel']:
    a, b = header(blk, n), header(m, n)
    same = a == b
    ok &= same
    print(f'{n}: {"IDENTICAL" if same else "DIFFERENT"} ({len(b.splitlines())} lines)')
    if not same:
        print('--- design\n' + a + '\n--- module\n' + b)
imp = lambda s: [l for l in s.split('\n') if l.startswith('import ')]
si = imp(blk) == imp(m)
ok &= si
print('imports:', 'IDENTICAL' if si else 'DIFFERENT', imp(m))
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
