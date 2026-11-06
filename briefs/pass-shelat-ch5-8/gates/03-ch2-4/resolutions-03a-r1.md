# Gate 03a (machines and probability): round 1 resolutions

- **Round 1:** findings `findings/gate03a-findings.md`, verbatim, SHA-256
  `9dd9195111dfc8aca6748405f2730ca98c8f61f3ae51b2858b2fe87e8cfa5f92`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 0 majors, 13 minors, 13 notes.**
- **Review:** `review/gate03a-review.md`: 23 true, 3 partly true (#2, #20, #22), none false. Four
  severity changes: #4 and #8 minor → **major**; #2 and #6 minor → note. New tally **0 blockers,
  2 majors, 9 minors, 15 notes**. Eight items missed by the auditor (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`, decision log rows "Gate 03 rulings G3-5 to
  G3-8"**):** G3-5 (A), ledger the duplicates as DL-9 onward and clean them up in the gate 03
  clean-up PR (#4, #8); G3-6 (A), approve every listed `@[simp]` (#11); G3-7 (a), move
  `negligible_zero` to `Foundations/Negligible.lean`, overriding D2 for one lemma (#12). R-03l-1
  (gate 03l) widens the same clean-up PR; its part 1 also carries DL-11's first half (#4).
- **Repair:** commit `e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820` (on #198's head
  `c10ed6ace0b991146c0be769313fbbe52d36e25a`), merged with the ch. 2–4 head as
  `956c595f2584532899aac1fb6fbe3d0aab9fa370`, in PR #201 with 03c's
  `bc2aab59333e27729c9fbac3052cd650bf62c3aa`. #201's head is
  `0c348ff94cacf24d96d99078c9dd9e328530c8d2`, merged by `02951926d9c9cea1d3596afa71c252176ca9de1d`.
  Gate 03 clean-up part 1 is PR #203 (head `f29be161cd86cfc3a9c38bd203bfa095b4974086`, merged by
  `8ec28f130eaca5f7d7dc756953bde0807d41b7df`; evidence `evidence-repairs/03l-cleanup1/`). Evidence `evidence-repairs/03ac/` (replay of the 97 downstream modules
  plus `Checks`, the full `Checks` axiom print at #201's head, lint 0). Line numbers are at #201's
  head unless a row says otherwise; Lean paths are under `TCSlib/`.
- **Scheduled work** goes to the gate 03 clean-up: part 1 is merged (#203);
  part 2 follows #195 (`duplication-ledger.md` DL-9 to DL-15; `QUEUE.md:147`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | minor | **Fixed.** `NUPPT.Computes` (`Complexity/Randomized/PPT.lean:229–241`), the module docstring (:40–48, :89–90) and DESIGN D3 (`briefs/pass-shelat/DESIGN.md:64–67`) say that Def 24.6 proper is `A.Uniform ∧ A.Computes f` and that the non-uniform form holds for uncomputable `f`. No `PPT.Computes` wrapper (no consumer); the downstream check is clean (review: 0 uses in ch. 5–8). |
| 2 | note (was minor) | **Fixed** (docstring). `Ensemble.Indist.copies` (`Cryptography/Asymptotic/Ensembles.lean:456–460`) says the samplability hypotheses are [Gar26, Lemma 3.3]'s uniform reduction and can be dropped against non-uniform distinguishers (not proved, no consumer). D6 unchanged; the optional `Indist.copies'` is not added. |
| 3 | minor | **Fixed** (#203, item H; found missing while drafting these resolutions). `NUPPT.exists_compParam` (`Complexity/Randomized/Closure.lean:209`, at #203's head): closure under polynomial-time pre- and post-processing that see `1^n`, with the review's statement. `exists_comp` is re-derived as its special case (statement unchanged), and its Scope paragraph points to the new theorem; `Checks.lean` prints it (standard axioms). Its proof, like `exists_comp`'s, reads `PPT.lean`'s `runAtL` and `advInput` by `simp`; the equation lemmas `runAtL_eq` and `advInput_eq` are **scheduled** for part 2. |
| 4 | major (was minor) | **Fixed** in its first half (#203, item D): `Complexity.polyTimeComputable_stateFind` is public (`Complexity/Randomized/Repetition.lean:241`, at #203's head), with its statement unchanged, and the prose calling it private is fixed (`Repetition.lean`, `Build/StringLoops.lean`, `Asymptotic/HardCoreLoops.lean:68`). **Scheduled:** part 2 re-points the copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun` and the variant `stateIterate`, and their "private" docstrings (DL-11). Meanwhile `ThreeColoring/Machines.lean:126` names the `EncodingMachines` copy explicitly, since the public name made the call ambiguous. |
| 5 | minor | **Fixed.** `polyTimeComputable_runAtL` (`Complexity/Randomized/NonUniform.lean:122–128`), the module docstring (:33–37) and its main-results line (:61–62) say the machine's size and constants depend on `n`, and that Def 26.8's polynomial size comes from `advice_length`. |
| 6 | note (was minor, src) | **Fixed.** `pairwise_sampling_ineq`'s deviation (`Ensembles.lean:691–696`) states that `1/4 > 1 − p²` exactly when `p > √3/2`, and that the variance form implies both bounds. The review checked the source (p. 189). |
| 7 | minor | **Fixed.** `Ensemble`'s deviation (`Ensembles.lean:119–125`): rational laws (seeds `Fin 3` give mass `1/3`; the samplable ensembles are the dyadic ones, D6) on strings of the fixed length `ℓ(n)` (missed item M5). |
| 8 | major (was minor) | **Scheduled** (G3-5). Ledgered as DL-9 (`blocks`), DL-10 (`ptc_comp`), DL-11 (state loop), DL-12 (`abs_uexp_sub_le`), DL-13 (`negligible_const_zero`), DL-14 (`forall_of_uprob_eq_one`), all "accepted; scheduled"; clean-up part 2, except DL-11's first half (part 1). The copies are still in the tree, e.g. `Asymptotic/Adversary.lean:198`, `Ensembles.lean:199`, `Closure.lean:149`, `Asymptotic/Sampling.lean:198`, `ZeroKnowledge/Defs.lean:248`. |
| 9 | minor | **Fixed.** The catalogue tags read "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" (`Closure.lean:192, 219, 245, 283, 313, 338`); `exists_reparam_advice` gains its tag (:245, missed item M3); the inventory id is not renamed. |
| 10 | minor | **Fixed.** `StatClose` (`Asymptotic/Sampling.lean:104–114`) cites [PS10, Definition 181.1] in its sup-over-test-sets form; the module References list it (:91). |
| 11 | minor | **Recorded** (G3-6, `QUEUE.md:125`): the eleven attributes are approved and unchanged: `coins_ofPolyTime`, `adv_ofPolyTime`, `advice_ofPolyTime`, `coins_ofPolyTimeUniform` (`PPT.lean:275, 280, 285, 312`); `inParam_layout`, `inArg_layout`, `inAdvice_layout`, `inCoins_layout`, `pairFstD_combineAdvice`, `pairSndD_combineAdvice` (`Closure.lean:105, 109, 113, 117, 162, 170`); `bitsEquiv_val` (`Sampling.lean:364`). |
| 12 | minor | **Fixed**, with two items **Scheduled.** Precise imports replace the facade in `Ensembles.lean:6–11`, `Asymptotic/EnsemblesLemmas.lean:6–7` and `Candidates/DiscreteLog.lean:6–8` (missed item M2); `negligible_zero` is in `Cryptography/Foundations/Negligible.lean:164` under its full name (G3-7 (a); D2's exception at `DESIGN.md:47–51`). Scheduled: `ThreeColoring/SimulatorMachine` is to import `NonUniform` itself so that `Ensembles` can drop it (`QUEUE.md:147`), and the copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean:248`) goes as DL-13 (part 2). |
| 13 | minor | **Fixed.** `Asymptotic/SamplingFinDist.lean:4` (`Authors:`), :9 (`maxHeartbeats 0`), :23–25 (`## Main definitions`: None). |
| 14 | note | **Fixed** (docstring). `IndistLit.toIndist` (`Ensembles.lean:349–354`), the module docstring (:41–42, :52–54), DESIGN D5 (`DESIGN.md:96–98`) and register item 5 (:1003–1004) say the two forms coincide for every `PolyExpr ℓ` (constant case by point tests, not formalized). `hℓ` is kept (no consumer). |
| 15 | note | **Fixed.** The wrong-length cost is stated on `NUPPT.inverter` (`Asymptotic/Adversary.lean:102–108`) and on `FunFamily.ofString` (`Asymptotic/OneWay.lean:198–206`), as routed with 03b #2. |
| 16 | note | **Fixed.** `hybrid_lemma` (`Ensembles.lean:426–428`): one seed type; other shapes embed into a product seed. |
| 17 | note | **Fixed.** `PolyExpr` (`Complexity/Randomized/PolyExpr.lean:68–72`): `n − 1`, `⌊n/2⌋`, `n(n−1)/2`, `⌈log₂ n⌉` not expressible; pad or use `exists_reparam_advice`. |
| 18 | note | **Fixed.** `Ensemble.push` (`Ensembles.lean:189–192`): padding is lossless only for exact `ℓ'(n)`-bit outputs. No `EnsembleL` (no consumer). |
| 19 | note | **Fixed.** The eleven prints and `negligible_zero`'s are in `audits/pass-shelat/Checks.lean:454–467`; all twelve print `[propext, Classical.choice, Quot.sound]` at #201's head (`evidence-repairs/03ac/checks-axioms.log:471–482`). |
| 20 | note (partly true) | **Fixed.** DESIGN D11 (`DESIGN.md:172–177`) names the real admission, `NUPPT.decides_of_decidesWithAdviceInTime`, and says `ofPartial` was never written; §8 Q5 (:1283–1285) cites the ruling of 2026-10-27. |
| 21 | note | **Fixed.** `PassShelatChecks.zeros` and `not_indist_uniform_zeros` (first-bit distinguisher) in `audits/pass-shelat/Checks.lean:475, 507`; its print is standard (`checks-axioms.log:483`). |
| 22 | note (partly true) | **Fixed in the closing-round pack** (pack erratum): `EnsemblesLemmas.lean` is context for 03a and audited in 03i. |
| 23 | note | **Fixed.** Banners "superseded by DESIGN D3–D6" on `inventory-ch2.md:255, 265` (Def-23.4, Def-26.8) and `inventory-ch3.md:38, 195, 204` (Machine-NUPPT, Def-69.3, Def-69.4); the erratum to the pack's stale Q1 is in the closing-round pack. |
| 24 | note | **Fixed.** (a) `PPT.lean:68–70`: (i) holds by `runLit`'s definition, no ill-typed `φ := length`. (b) `Indist.push`'s sketch cites gate 03a finding 3, not "P2-4" (`Ensembles.lean:402`). |
| 25 | note | **No change.** Resolved by the review: the source is in the tree; #6 checked against p. 189; Defs 23.4, 23.5, 24.6, 26.8, 69.3, 69.4 and Lemmas 71.5, 71.6, 73.8 read, no new daylight. |
| 26 | note | **Fixed.** `StatClose` (`Sampling.lean:115–118`): on an empty seed type the law is the zero measure; every use has nonempty seeds. |
| M1 | (review) duplication wider | **Scheduled** with #4 and #8 (DL-9 to DL-14). |
| M2 | (review) facade imports elsewhere | **Fixed** with #12 (`EnsemblesLemmas.lean:6–7`, `DiscreteLog.lean:6–8`). |
| M3 | (review) `exists_reparam_advice` untagged | **Fixed** (`Closure.lean:245`). |
| M4 | (review) `Samplable` misattributed | **Fixed.** `Ensemble.Samplable` (`Ensembles.lean:157–158`) cites [PS10, p. 72, Example] and [Gar26, Lemma 3.3] for the multicopy lemma. |
| M5 | (review) fixed length not declared | **Fixed** with #7 (`Ensembles.lean:122–123`). |
| M6 | (review) prose calls `stateFind` private | **Fixed** (#203, item D); see #4. |
| M7 | (review) 03b #12b's `NUPPT` helpers | **Fixed** in #198: moved to `Cryptography/Asymptotic/CollectionsHelpers.lean:58–115` (not 03a's directory) with the full names `Complexity.NUPPT.*` unchanged, so 03a's closing diff does not include them. |
| M8 | (review) downstream check for #1 | **No change:** clean (no ch. 5–8 use of `NUPPT.Computes`). |
