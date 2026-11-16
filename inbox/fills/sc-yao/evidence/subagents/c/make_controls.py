#!/usr/bin/env python3
"""Paired whole-closure seals detect one deliberate foreign definitional read."""
import ast
import json
from pathlib import Path
module=ast.parse(Path('evidence/subagents/c/make_seals.py').read_text())
preamble=next(ast.literal_eval(n.value)for n in module.body if isinstance(n,ast.Assign)
              and any(isinstance(t,ast.Name)and t.id=='preamble'for t in n.targets))
root=Path('evidence/subagents/c/seals/controls');root.mkdir(parents=True,exist_ok=True)
imports='import TCSlib.Cryptography.Foundations.Probability\nimport Lean\n'
body='''
/-- Deliberately read the foreign probability definition, for the seal control only. -/
example (p : Fin 1 → Prop) : TCSlib.Cryptography.uprob p =
    (Nat.card {a // p a} : ℝ) / Fintype.card (Fin 1) := by
  rfl
'''
rows=[]
for variant in ['A','B']:
 for coe in ['strict','coe']:
  for sealed in [False,True]:
   seal=preamble.replace('EVAL_NOTATION',str(variant=='A').lower())
   seal=seal.replace('COE_NOTATION',str(coe=='coe').lower())if sealed else ''
   p=root/f"Control_{variant}_{coe}_{'sealed'if sealed else 'unsealed'}.lean"
   p.write_text(imports+seal+body)
   rows.append(dict(probe=str(p),variant=variant,coercions=coe,sealed=sealed,
                    expected_errors=1 if sealed else 0))
(root/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
(root/'order.txt').write_text(''.join(r['probe'][:-5]+'\n'for r in rows))
print('Prepared eight paired controls')
