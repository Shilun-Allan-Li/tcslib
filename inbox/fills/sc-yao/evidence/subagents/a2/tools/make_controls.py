#!/usr/bin/env python3
"""Generate paired controls using the sc-garble seal preamble."""
import ast
import json
from pathlib import Path
source = Path('evidence/subagents/a2/tools/make_seals.py').read_text()
module = ast.parse(source)
preamble = next(ast.literal_eval(n.value) for n in module.body
                if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name)
                and t.id == 'preamble' for t in n.targets))
root = Path('evidence/subagents/a2/seals/controls')
root.mkdir(parents=True, exist_ok=True)
imports = 'import TCSlib.Cryptography.Foundations.Probability\nimport Lean\n'
body = '''
/-- Deliberate foreign definitional read for the seal control. -/
example (p : Fin 1 → Prop) : TCSlib.Cryptography.uprob p =
    (Nat.card {a // p a} : ℝ) / Fintype.card (Fin 1) := by
  rfl
'''
rows = []
for variant in ['A', 'B']:
    for coe in ['strict', 'coe']:
        for sealed in [False, True]:
            seal = preamble.replace('EVAL_NOTATION', str(variant == 'A').lower())
            seal = seal.replace('COE_NOTATION', str(coe == 'coe').lower()) if sealed else ''
            path = root / f"Control_{variant}_{coe}_{'sealed' if sealed else 'unsealed'}.lean"
            path.write_text(imports + seal + body)
            rows.append(dict(probe=str(path), variant=variant, coercions=coe,
                             sealed=sealed, expected_errors=1 if sealed else 0))
(root / 'manifest.json').write_text(json.dumps(rows, indent=2) + '\n')
