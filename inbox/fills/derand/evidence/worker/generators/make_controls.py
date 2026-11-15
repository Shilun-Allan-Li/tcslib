import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location('derand_seals', Path('evidence/tools/make_seals.py'))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
root = Path('evidence/controls')
root.mkdir(parents=True, exist_ok=True)
sealed = Path('evidence/seals/controls')
sealed.mkdir(parents=True, exist_ok=True)
source = '''import TCSlib.Complexity.ClassP.DTIME

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DerandEvidence

-- This positive interface use must remain available when the definition is sealed.
example {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ Complexity.DTIME T ↔
      ∃ (c : ℕ) (M : Turing.FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Complexity.mem_DTIME_iff

-- The deliberate hidden-definition read must fail exactly once when sealed.
example {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ Complexity.DTIME T ↔
      ∃ (c : ℕ) (M : Turing.FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl

end DerandEvidence
'''
manifest, pairs, unsealed = [], [], []
for mode in ['A', 'B']:
    for coe in [False, True]:
        stem = mode + ('_coe' if coe else '_strict')
        original = root / (stem + '_unsealed.lean')
        original.write_text(source)
        label = 'controls_' + stem
        probe, mapping, offset = module.prepare(source, label, mode, coe)
        destination = sealed / (stem + '_sealed.lean')
        destination.write_text(probe)
        destination.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
        manifest.append(dict(source=str(original), probe=str(destination), label=label,
                             mode=mode, coe=coe, source_offset=offset))
        pairs.append(dict(mode=mode, coe=coe, unsealed=str(original), sealed=str(destination),
                          unsealed_expected_errors=0, sealed_expected_errors=1))
        unsealed.append(str(original.with_suffix('')))
(root / 'pairs.json').write_text(json.dumps(pairs, indent=2) + '\n')
(root / 'unsealed-order.txt').write_text('\n'.join(unsealed) + '\n')
(sealed / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(sealed / 'order.txt').write_text(''.join(item['probe'][:-5] + '\n' for item in manifest))
print('Prepared four paired controls: unsealed 0 errors, sealed exactly 1 error each')
