# Combined construction statement gate

This is the larger overnight draft authorized by the user on 2026-11-08.
Nontrivial new claims remain `sorry` for later proof fills. The morning external
reviewer is preselected as **Codex**; the user still dispatches that job.

| Item | Identity |
|---|---|
| Own worktree | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-construction-statements` |
| Own PR branch | `cryptography/lwe-sis-construction-statements` |
| Central target | `cryptography/lwe-sis-constructions` |
| Remote-verified central baseline | `2c37f3f486822a52f4a9e337c6b742e995ebb118` |
| Audited dependency stack and intake | `307cfdd1d6cadfda2ae9cca5367705ad770c5f42`, PRs #236/#237/#238/#239 |
| Last audited Lean dependency | `ec72ed773a690c17ac253707350935cc9e0acb34` |
| Frozen Lean/root (separate export commit) | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The source pin, checked inventory and execution totals are recorded in
`evidence/source-pin.txt` and `evidence/summary.json`.
`REPORT.md` distinguishes final evidence from development and earlier candidate sweeps.

## Combined scope

| Slice | Mathematical modules | Source declarations | Admissions |
|---|---:|---:|---:|
| Exact dyadic sampling and explicit bit-noise laws | 3 | 35 | 16 |
| Encoded dot products, matrix products and Boolean-vector expansion | 2 | 34 | 20 |
| SIS universality, evaluator, raw-output adapter and negligible collisions | 4 | 29 | 19 |
| Regev PKE algorithms, correctness and concrete security | 2 | 31 | 10 |
| Structured, encoded and single-word direct DLWE generators | 3 | 31 | 11 |
| Lossy and all-but-one secret-matrix trapdoor mathematics and DLWE hybrids | 5 | 60 | 25 |
| **Total** | **19** | **220** | **101** |

The source declarations are 57 definitions and 163 theorems. Sixty-two complete
equation/projection readers are `rfl`. Forty additional non-simp projection readers
are generated explicitly. Thirteen compiler auxiliaries are inventoried separately;
these are not handwritten public declarations. The earlier 302 owned constants
remain fixed. No old mathematical definition or theorem is edited.

## Ownership and coordination

Six existing Lean export files overlap with shared facades: `TCSlib.lean`, and
`Cryptography/Encoding.lean`, `LWE.lean`, `Encryption.lean`, `Hashing/SIS.lean`,
`Pseudorandom.lean`. Export wiring is isolated in a separate commit. All new
mathematics is in new problem/primitive children. No Asymptotic, Candidates,
Games, probability, PAC, Randomized owner or registry is edited.

Two additional exact proposals remain data only: the missing `Randomized.blockVal_eq`
reader and registration of the existing public counted loop. See `COORDINATION.md`.
Keep affected proof routes paused until the relevant owner/registry disposition.
The earlier probability-reader and source-registry proposals also remain unapplied.

No full primitive completion is claimed. SKE game/encoding bridges, full PKE CPA
integration, the standard exact-seed PRG compiler, efficient uniform noise schedules,
and full CCA2 with strong one-time signatures remain later consumers. SIS remains
independent of LWE. The trapdoor is an ordinary secret matrix; no short lattice basis,
Gaussian preimage sampler, search/decision bridge or worst-case lattice reduction
is introduced.

## Review and publication

The combined pack is `audits/lwe-sis-constructions-statements-pack.md`. The publisher
uses only the owned `lwe-sis-constructions/` exchange namespace in the private sparse
publisher, with immutable source/records pins and revision-qualified attachment indexes.
The user runs the client publication helper and pastes its printed prompt into a
fresh Codex auditor chat. The auditor reads GitHub directly and returns
`lwe-sis-constructions-statements-findings.md` as Markdown in chat. No ZIP is needed.
No external job is dispatched by preparing this gate; no central ref is pushed or merged.

**Not yet clear to merge — the combined statement audit, 101 proof fills,
source-policy work, applicable landing checks and user approval remain.**
