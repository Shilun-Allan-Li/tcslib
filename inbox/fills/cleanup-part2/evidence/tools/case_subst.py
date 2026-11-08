#!/usr/bin/env python3
"""Replace foreign definitions with pattern-matching/structure bodies in simp/rw lists by their owner
case/field readers (cleanup-part2). python3 -I case_subst.py <scan.json> <root> [--apply]
Only list entries; `unfold X` tactics become `simp only [readers…]` with the other names kept."""
import sys, json, re, collections
MAP = {
 'TCSlib.Cryptography.PrivateKeyScheme.encodeList': ['encodeList_nil', 'encodeList_cons'],
 'Complexity.transduce': ['transduce_nil', 'transduce_cons'],
 'TCSlib.Cryptography.exec': ['exec_zero', 'exec_succ'],
 'BoolCircuit.decodeNat': ['decodeNat_nil', 'decodeNat_false_cons', 'decodeNat_true_cons'],
 'TCSlib.Cryptography.blockList': ['blockList_zero', 'blockList_succ'],
 'TCSlib.Cryptography.splitPair': ['splitPair_apply', 'splitPair_symm_apply'],
 'TCSlib.Cryptography.glPadDecode': ['glPadDecode_def'],
 'Complexity.NUPPT.inverter': ['inverter_def'],
 'Turing.Action.apply': ['apply_state', 'apply_output', 'apply_workTapes', 'apply_workTapePos', 'apply_inputPos'],
 'Turing.MultiTapeTM.step': ['step_def'],
 'Complexity.PolyExpr.eval': ['eval_const', 'eval_var', 'eval_add', 'eval_mul', 'eval_pow', 'eval_normal'],
}
scan = json.load(open(sys.argv[1])); root = sys.argv[2]
props = collections.defaultdict(list); left = collections.Counter()
for it in scan['items']:
    if not it['class'].startswith('FOREIGN_TCS_DEF'): continue
    r = it['resolved']
    if r not in MAP: left[r] += 1; continue
    qual = it['ident'][:-len(r.split('.')[-1])]   # keep the identifier's own qualification
    new = ', '.join(qual + x for x in MAP[r])
    props[it['file']].append((it['offset'], it['line'], it['tactic'], it['ident'], new))
for f, ps in props.items(): print(f, len(ps))
print('LEFT:', left.most_common())
if '--apply' in sys.argv:
    for f, ps in props.items():
        text = open(f'{root}/{f}').read()
        unf = collections.defaultdict(dict); other = []
        for off, ln, tac, ident, new in ps:
            if tac in ('unfold', 'delta'): unf[ln][ident] = new
            else: other.append((off, ident, new))
        for off, ident, new in sorted(other, reverse=True):
            assert text[off:off + len(ident)] == ident, (f, ident)
            text = text[:off] + new + text[off + len(ident):]
        lines = text.split('\n')
        for ln, mp in unf.items():
            line = lines[ln - 1]
            m = re.search(r'\b(unfold|delta)\s+([^;]*?)(\s+at\s+[^;]*)?(;.*)?$', line)
            if not m: continue
            names = [mp.get(x, x) for x in m.group(2).split()]
            lines[ln - 1] = line[:m.start()] + 'simp only [' + ', '.join(names) + ']' + (m.group(3) or '') + (m.group(4) or '')
        open(f'{root}/{f}', 'w').write('\n'.join(lines))
