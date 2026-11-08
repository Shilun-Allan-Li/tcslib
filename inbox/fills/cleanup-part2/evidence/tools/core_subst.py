#!/usr/bin/env python3
"""Replace Core/Mathlib definitions passed to simp/rw lists by their public lemmas (cleanup-part2).
python3 -I core_subst.py <scan.json> <root> [--apply]
Only list entries (not unfold/delta) of class CORE_MATHLIB_DEF whose resolved name is in MAP."""
import sys, json, collections
MAP = {'id': 'id_eq', 'Function.comp': 'Function.comp_apply', 'Prod.map': 'Prod.map_fst, Prod.map_snd',
       'Fin.tail': 'Fin.tail_def', 'Fin.castLE': 'Fin.coe_castLE', 'Fin.castAdd': 'Fin.coe_castAdd',
       'Fin.natAdd': 'Fin.coe_natAdd',
       'Equiv.sumArrowEquivProdArrow': 'Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd'}
scan = json.load(open(sys.argv[1])); root = sys.argv[2]
props = collections.defaultdict(list); left = collections.Counter()
for it in scan['items']:
    if not it['class'].startswith('CORE_MATHLIB_DEF'): continue
    r = it['resolved']
    if r in MAP and it['tactic'] not in ('unfold', 'delta'):
        props[it['file']].append((it['offset'], it['ident'], MAP[r]))
    else: left[(r, it['tactic'])] += 1
for f, ps in props.items(): print(f, len(ps))
print('LEFT:', left.most_common())
if '--apply' in sys.argv:
    for f, ps in props.items():
        text = open(f'{root}/{f}').read()
        for off, ident, new in sorted(ps, reverse=True):
            assert text[off:off + len(ident)] == ident, (f, ident)
            text = text[:off] + new + text[off + len(ident):]
        open(f'{root}/{f}', 'w').write(text)
