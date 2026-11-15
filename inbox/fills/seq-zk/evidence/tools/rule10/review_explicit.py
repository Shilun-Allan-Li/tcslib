"""Review scanner method/open aliases and retain local-proof-name context.

Prepare a precise native theorem-kind supplement; no Lean execution. Original
scanner results remain unchanged and the supplemental classification is separate.
"""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
p.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[2] / 'rule10/final')
args = p.parse_args()
ROOT, OUT = args.repo, args.out
SCAN = json.loads((OUT / 'explicit-final.json').read_text())
PREFIX = 'TCSlib.Cryptography.'
aliases = {
 'S.gen_uniform.runAtL_eq': 'Complexity.NUPPT.Uniform.runAtL_eq',
 'H.gen_uniform.runAtL_eq': 'Complexity.NUPPT.Uniform.runAtL_eq',
 'S.gen_uniform.runAt_eq': 'Complexity.NUPPT.Uniform.runAt_eq',
 'S.sign_uniform.runAt_eq': 'Complexity.NUPPT.Uniform.runAt_eq',
 'e.apply_symm_apply': 'Equiv.apply_symm_apply',
 'S.forgeGame_eq': PREFIX + 'Authentication.SignatureScheme.forgeGame_eq',
 'S.forgerCodec_eq_bitCodec': PREFIX + 'Authentication.SignatureScheme.forgerCodec_eq_bitCodec',
 'S.signImpl_eq': PREFIX + 'Authentication.SignatureScheme.signImpl_eq',
}
for name in ['rL_input', 'rU_input', 'rW_input', 'rX_input', 'rAns_input', 'rS_input',
             'rU_finInput', 'rW_finInput', 'finA_finInput']:
    aliases[name] = PREFIX + 'Games.InteractiveHandler.' + name
local_heads = {'hρ', 'h₁', 'h₂', 'hgen', 'hm₀', 'hlen', 'hfirst', 'hi', 'hσ', 'ht', 'payoff', 'win',
 'hrun', 'hcase', 'hw', 'hω', 'c', 'hinput', 'hnil', 'hp', 'hdecode', 'ha', 'hs', 'houter', 'hinner',
 'hout', 'hφ', 'hforward', 'he', 'hf'}
review = []
for item in SCAN['items']:
    if item['classification'] != 'LOCAL_OR_UNRESOLVED':
        continue
    row = dict(item)
    source = (ROOT / item['file']).read_text().splitlines()
    row['source_context'] = '\n'.join(source[max(0, item['line'] - 6): item['line'] + 1])
    if item['head'] in aliases:
        row['review_classification'] = 'PUBLIC_THEOREM_METHOD_OR_OPEN_ALIAS'
        row['native_target'] = aliases[item['head']]
    elif item['head'] in local_heads:
        row['review_classification'] = 'LOCAL_PROOF_BINDER_OR_LET'
        row['review_basis'] = 'Local hypothesis, chosen witness, case equation, or let within the enclosing declaration.'
    else:
        raise RuntimeError('unreviewed unresolved head: ' + item['head'])
    review.append(row)
targets = sorted({r['native_target'] for r in review if 'native_target' in r})
owners = (OUT / 'owners.txt').read_text().splitlines()
source = 'import Lean\n' + ''.join('import ' + owner + '\n' for owner in owners)
source += '\nset_option maxHeartbeats 0\nopen Lean Elab Command\n\nrun_cmd do\n'
source += '  let env ← getEnv\n  let names : Array Name := #[' + ', '.join('`' + n for n in targets) + ']\n'
source += '''  for n in names do
    match env.find? n with
    | some (.thmInfo _) => IO.println s!"EXPLICIT_ALIAS_THEOREM {n}"
    | _ => throwError "Explicit scan alias is not a theorem: {n}"
  IO.println s!"EXPLICIT_ALIAS_DONE {names.size}"
'''
module = '.lake/hash-sign-rule10/' + OUT.name + '/ExplicitAliases'
(ROOT / (module + '.lean')).write_text(source)
(OUT / 'sources/ExplicitAliases.lean').write_text(source)
result = {'original_unresolved_count': len(review), 'public_theorem_alias_items': sum('native_target' in r for r in review),
          'local_proof_items': sum('native_target' not in r for r in review), 'native_theorem_targets': targets,
          'native_probe_module': module, 'review': review,
          'limitation': 'The original scanner cannot follow method notation or an open resolved through another open. These aliases are explicitly mapped and separately verified as native theorem constants.'}
(OUT / 'explicit-review.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'review'}))
