# Exact style-lint delta

The baseline is recovered verbatim from `evidence/initial-escalation.zip`, entry `dl-crh/evidence/logs/style-lint.log`.
`evidence/logs/style-base.log` retains all 109,997 original bytes; no baseline lint rerun is substituted.

- Archive SHA-256: `cbfd18e8dbddde11bee3d25e63552117c587c61990e72d0fb285fe8798c40965`.
- Baseline log SHA-256: `952fdf49768e45f34e4755b46a41b02e539f61b22804774e5867859276377fde`.
- Final log SHA-256: `89d59ed75ea288f34c53efddc9daae4a4618b71b8b1c1845f011259928df62a9`.

| Diagnostics | Baseline | Final | Delta |
|---|---:|---:|---:|
| FAIL | 216 | 222 | +6 |
| WARN | 102 | 102 | +0 |

## Added diagnostics

- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra` (count 1).
- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins` (count 1).
- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding` (count 1).
- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability` (count 1).
- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction` (count 1).
- FAIL `TCSlib/Cryptography/Hashing.lean`: facade does not import child module `TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling` (count 1).
- WARN `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: 1209 lines > 1000: policy requires a split or a recorded justification (escalation/decision log) (count 1).
- WARN `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: 5 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, dlDefaultIndex, expUnit (count 1).

## Removed diagnostics

- WARN `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: 1192 lines > 1000: policy requires a split or a recorded justification (escalation/decision log) (count 1).
- WARN `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: 6 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, dlDefaultIndex, expSampleRaw, expUnit (count 1).

The mechanical new-FAIL count is retained above. The user disposition for the six
ancestor-facade diagnostics is recorded separately in `facade-lint-exception.md`.
This comparison does not relabel those diagnostics as mechanical passes.
