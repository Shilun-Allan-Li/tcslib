import sys, json
# usage: mkax.py <module .lean> <newchanged.json> <kit> <out .lean>
src = open(sys.argv[1], encoding='utf-8').read()
nc = json.load(open(sys.argv[2]))
kit = open(sys.argv[3], encoding='utf-8').read()
assert src.rstrip().endswith('end Turing'), src.rstrip()[-40:]
lines = src.split('\n')
last = max(k for k, l in enumerate(lines) if l.startswith('import '))
assert 'import Lean.Util.FoldConsts' not in src
lines.insert(last + 1, 'import Lean.Util.FoldConsts')
src2 = '\n'.join(lines).rstrip('\n') + '\n'
names = ['Turing.' + n for n in nc['all']]
assert len(names) == 872, len(names)
body = ''.join(f'#print axioms {n}\n' for n in names)
body += '#rv_sorry_sources Turing.exists_zoneRebalanceTM\n#rv_sorry_sources Turing.exists_zoneExtendTM\n'
body += ''.join(f'#rv_ext_check {n}\n' for n in names)
nchg = ['Turing.' + n for n in nc['new'] + nc['changed']]
body += '#rv_ext_list ' + ' '.join(nchg) + '\n'
body += '#rv_pub_consts\n'
out = src2 + kit + '\n' + body
open(sys.argv[4], 'w', encoding='utf-8').write(out)
assert out.count('#print axioms') == 872
print('prints', len(names), 'ext_list over', len(nchg), 'lines', out.count('\n'))
