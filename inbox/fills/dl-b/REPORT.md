# Fill dl-b: REPORT (checkpoint 1)

Unit **dl-b** of `briefs/pass-shelat-ch5-8/fills/dl-candidates/brief-issued.md`. Owned file:
`TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean`.

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (issue commit). Local branch `fill/dl-b`, never
  rebased, never pushed.
- **Head at this checkpoint:** `c47db33f48815ec1b67ce8bd1e4840bfafcc0543` (6 commits).
- **Environment:** internal worker under `issue/internal-env.md` (no preflight, cache or bootstrap
  step). At start: `nproc` 4, 15 GiB RAM, about 14 GiB available (`evidence/logs/start-resources.log`).

## Status at checkpoint 1

| Target | Status |
|---|---|
| `dlBits_pow` | filled |
| `uprob_trial_ge` | filled |
| `uprob_majOracle_ne_le` | filled |
| `invProb_shiftInverter_ge` | filled |
| `invProb_dlInverter_ge` | filled |
| `polyTimeComputable_halfStr` | filled |
| `fullDLCollection_hardCore` | in progress (still `sorry`) |

The owned file checks with 0 errors; the only warnings are the headline's `sorry` and an unused
`hg` in the frozen statement of `invProb_shiftInverter_ge` (the bound holds for every `g`).
Axiom prints: `evidence/logs/axioms.log` (the six filled targets print the standard triple).
The seal, sweep and lint are run at the final delivery.
