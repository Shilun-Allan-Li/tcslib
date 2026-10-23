import sys, re
# usage: mkax2.py <module file> <out file> <decls file> <targets comma> <direct names comma>
# Appends to a copy of the module: #print axioms for every declaration; the admission walk for the
# targets; #ext_check (external constants, external privates, other modules' equation/unfold/match
# lemmas) for every declaration; #ext_list over all; #direct_uses for the listed declarations.
src, out, declf, targets, direct = sys.argv[1:6]
names = [l.split()[0] for l in open(declf, encoding='utf-8') if l.strip()]
targets = targets.split(','); direct = [d for d in direct.split(',') if d]
mkax = open(sys.argv[0].replace('mkax2.py', 'mkax_orig.py'), encoding='utf-8').read()
tail1 = mkax[mkax.index("tail = r'''") + len("tail = r'''"):mkax.index("'''\ncmds")]
mkd = open(sys.argv[0].replace('mkax2.py', 'mkdirect_orig.py'), encoding='utf-8').read()
tail2 = mkd[mkd.index("tail = r'''") + len("tail = r'''"):mkd.index("'''\ncmds")]
lines = open(src, encoding='utf-8').read().split('\n')
last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
lines.insert(last_import + 1, 'import Lean.Util.FoldConsts')
cmds = [f'#print axioms Turing.{t}' for t in names]
cmds += [f'#sorry_sources Turing.{t}' for t in targets]
cmds += [f'#ext_check Turing.{n}' for n in names]
cmds.append('#ext_list ' + ' '.join(f'Turing.{n}' for n in names))
cmds += [f'#direct_uses Turing.{n}' for n in direct]
assert len(names) >= 119
open(out, 'w', encoding='utf-8').write('\n'.join(lines).rstrip('\n') + '\n' + tail1 + '\n' + tail2 + '\n' + '\n'.join(cmds) + '\n')
print('declarations', len(names), 'commands', len(cmds))
