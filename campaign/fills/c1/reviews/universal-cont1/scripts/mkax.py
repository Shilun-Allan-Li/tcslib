"""mkax.py <head module> <model axiom probe> <out .lean> : head module + the admission/dependency-walk toolkit
(copied from the model review's probe, between its `end Turing` and its first `#print axioms`) + prints."""
import sys, re
head, model, out = sys.argv[1:4]
src = open(head, encoding='utf-8').read()
m = open(model, encoding='utf-8').read()
i = m.index('\nend Turing\n') + len('\nend Turing\n')
j = m.index('\n#print axioms ', i)
kit = m[i:j]
assert 'elab "#sorry_sources "' in kit and 'elab "#ext_check "' in kit and 'elab "#ext_list "' in kit
assert src.rstrip().endswith('end Complexity'), src.rstrip()[-40:]
assert 'import Lean.Util.FoldConsts' not in src
lines = src.split('\n')
# add the FoldConsts import after the last import line
last = max(k for k, l in enumerate(lines) if l.startswith('import '))
lines.insert(last + 1, 'import Lean.Util.FoldConsts')
src2 = '\n'.join(lines)
names = ['Turing.' + n for n in ['un_universal_of_setup', 'un_flatten', 'un_buffer_ge', 'un_step', 'un_canon_halt',
         'un_bankAct', 'un_bankAct_eq', 'un_bankTM', 'un_bank_run', 'un_inRewTM', 'un_inRew_run',
         'un_mapState_comp', "un_step'", 'un_setup', 'exists_timed_universal_NDTM',
         'exists_ndAcceptsWithin_decider', 'exists_ndInterpreterCore']] + \
        ['Complexity.ntime_hierarchy', 'Complexity.ntime_hierarchy_of_pos', 'Complexity.NTIME_linear_ssubset_square']
body = ''.join(f'#print axioms {n}\n' for n in names)
body += ''.join(f'#sorry_sources {n}\n' for n in names)
own = [n for n in names if '.un_' in n or n.endswith('exists_timed_universal_NDTM')]
body += ''.join(f'#ext_check {n}\n' for n in own)
body += '#ext_list ' + ' '.join(own) + '\n'
open(out, 'w', encoding='utf-8').write(src2.rstrip('\n') + '\n' + kit + '\n' + body)
print('prints', len(names), 'ext', len(own))
