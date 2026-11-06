# Gate 07 (equation-lemma PR #210): round 1 resolutions (repair in progress)

- **Round 1:** findings `findings/gate07-eqlemmas-findings.md`, verbatim (delivered by upload; no
  copy in the exchange inbox), SHA-256 `d2fd7b754470e9922555507d02c1471225955a6b1cab20a34275005ca24b73bc`;
  head `fff0430c7c9db136e60ed14b069e972c2ea56fc8`. **Open: 0 blockers, 2 majors (F01, F02), 1 minor (F03).**
  The auditor found no counterexample to S1–S3 and confirmed the 183 additions, the three
  restatements and the domain equivalences against their definitions.
- **Repair** (follow-up commits on #210; with the fill-brief reviews' interface gaps, below).

| Finding | Severity | Resolution |
|---|---|---|
| F01 | major | **Confirmed.** The statement-level probes sealed a hand-picked candidate list, so `FunFamily.glPad`'s `inLen`/`outLen` reductions in `HardCorePermutation.lean` (`glHalf_f_even`, `glHalfBit_even`, `predProb_glHalf_even`, `invProb_glHalf_even`, `glHalf_f_odd`) and `HardCoreClaims.lean` (`thm_87_3_1/2/3`) were missed. **Repair:** a complete sweep replaces the list: every module of `Cryptography/` and `Checks`, statement-only copies with **every** foreign sealable definition in its declarations' types sealed, minimized per declaration, with controls (`sweep/`). Every read it finds is fixed by a published interface beside the definition (length equations or equivalences for `glPad`, etc.) and a restatement. |
| F02 | major | **Confirmed.** No sealed consumer exercises `PermCollection.glPad_domEquiv`/`_apply`/`glPad_perm`. **Repair:** a pass probe with `PermCollection.glPad` and `Collection.glPad` sealed and a paired control; the report maps every lemma group to its pass/control examples and logs. |
| F03 | minor | **Confirmed. Repair:** `polyTimeComputable_samplePrimeL`'s sketch restricts `natToList n 2 = 0^(n−2)10` to `n ≥ 2` and states the branches `[]` (`n = 0`) and `[false]` (`n = 1`). |

**Also in the repair (fill-brief reviews, `fills/*/review.md`):** #195's experiment equations
(`invProb_def`, `predProb_def`, `acceptProb_def`, `distAdv_def`, `uexp`'s; cherry-picked
byte-identical from `bd2e4d0f`), `expGen_coinsEquiv` with `expGen_runAt` and the three `_index`
statements restated through it, and `factoringAssumption_iff` (with a sweep for other `Prop`
definitions lacking an `_iff`).
