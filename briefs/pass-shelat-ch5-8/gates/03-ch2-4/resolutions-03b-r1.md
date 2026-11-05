# Gate 03b (one-wayness and collections): round 1 resolutions

- **Round 1:** findings `findings/gate03b-findings.md`, verbatim, SHA-256
  `0d3a1f038c63a13cfc0f7484832049d5559790e84f6d19935a2241716b01bbb6`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 3 minors,
  10 notes.**
- **Review:** `review/gate03b-review.md`: 12 true, 1 partly true (#1), 1 true and resolved by the
  review (#14), none false. #1 stays a major, not a blocker (the formal Algorithm 104.3 takes a
  `PredEvaluator`). One severity change: #12 is split, and (c) (unledgered copies) goes from note to
  **minor**; (a), (b), (d) stay notes. #7 is a note here but, in the review, a blocker for gate 06B.
  New tally **0 blockers, 1 major, 4 minors, the rest notes**. Eight items missed by the auditor
  (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-1 (A), canonical decoding `Collection.encD_decD` (#1); G3-5
  (A), ledger and clean up the duplicates (#12c, M6: DL-10, DL-15); G3-6 (A), approve the listed
  `@[simp]` (#12a); G3-8 (A), an enhanced hard-core hypothesis for Prop 161.5 in prong B (#7, M1).
  G3-7 (c) (03c #3, the cost of `henc`) was applied in the same commit and closes M2's overclaim.
- **Repair:** PR #198, head `c10ed6ace0b991146c0be769313fbbe52d36e25a` (one commit on
  `a3c5fa8b…`), merged into `cryptography/pass-shelat-ch2-4` by
  `cdff8890ee4af8eec7d6682963c02041390f52f2`. Maintainer re-check recorded in the decision log
  (#198 row: 62 downstream modules plus `Checks`, no `sorry` change, lint 0); the prints below are
  in the `Checks` axiom print at #201's head (`evidence-repairs/03ac/checks-axioms.log`). Line
  numbers are at #201's head (`0c348ff94cacf24d96d99078c9dd9e328530c8d2`, which contains #198);
  Lean paths are under `TCSlib/Cryptography/`.
- **Prong B** (outside ch. 2–4): G3-8 is commit `587843c76f95f10056c9ddc9174da9dc8fba8b54` on
  `cryptography/pass-shelat-ch5-8-prong-b`.

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major (not blocker) | **Fixed** (G3-1). The field `encD_decD` (`Asymptotic/Collections.lean:141–147`) is proved for every instance (`Collections.lean:420`; `Asymptotic/HardCoreCollection.lean:103–107`; `Candidates/DiscreteLog.lean:571`, `Factoring.lean:585`, `RSA.lean:648`, `Rabin.lean:476, 855`), with the derived `decD_eq_some_iff` … `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv` (`Collections.lean:258–289, 362, 373`), `HardCore.nonempty_predEvaluator` and the evaluator-free `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` (`Asymptotic/PublicKey.lean:549, 973`), DESIGN §2.10 and §5 item 24 (`briefs/pass-shelat/DESIGN.md:587, 630–640, 1064–1067`); prints standard (`checks-axioms.log:424–433`). **Scheduled:** prong B still carries `hcanon : SamplerCanonical T` and `hspec`; dropping them is in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md:58–59`). |
| 2 | minor | **Fixed** (docstrings). The `LengthRegular` proviso is in DESIGN D5 (`DESIGN.md:87–88`), `OneWay.lean`'s module docstring (:29–31) and `FunFamily` (:92–93). `ofString` keeps its padding (marker padding not recommended: it would change `fUniversal`). |
| 3 | minor | **Fixed.** `OneWayPermutation` cites [PS10, §2.10, Definition 55.1, single-function form, as used in Theorems 79.4 and 126.4] (`Asymptotic/OneWay.lean:916`); Thm 126.4 is dropped from `Collection.HardCore`'s consumers and the two lists agree (`Collections.lean:25–26, 221`). |
| 4 | minor | **Fixed.** `owfFamily_strongOneWay`'s sketch (`Collections.lean:926–953`) describes `padStr` and the reduction without a length check (and why none is needed); `weak_to_strong`'s (`OneWay.lean:603–641`) describes `OneWay.exists_yaoReduction` with advice `⟨A'.advice n, 1^{kk}⟩`, the "Implementation" paragraph folded in. |
| 5 | note | **Fixed** (optional docstring): `PermCollection` (`Collections.lean:300–303`) says junk indices may have a one-element domain. |
| 6 | note | **Fixed.** `TrapdoorCollection`'s P3-5 deviation (`Collections.lean:326–334`) and DESIGN §5 item 17 (`DESIGN.md:1031–1035`) give the general argument (`t' := ⟨i, t⟩`; the classes coincide). |
| 7 | note (blocker for 06B, review) | **No change** in ch. 2–4. G3-8 is applied in prong B (`587843c7…`): `EnhancedHardCore` (`SecureComputation/ObliviousTransfer.lean:149` there), taken by `otProtocol_simulators` and `otProtocol_hbcSecure` (:420, :452); gate 06B audits it. |
| 8 | note | **Fixed.** DESIGN §5 item 23 (`DESIGN.md:1058–1063`): parameter-`n` adversaries for Thms 35.1, 35.2, and Claim 38.2's `T` and threshold. The optional bridge lemma is deferred (review) and not added. |
| 9 | note | **Fixed.** `WorstCaseOneWayLit`'s deviation (`OneWay.lean:175–182`) and DESIGN §5 item 16 (`DESIGN.md:1025–1030`), with the review's correction ("can hold" for constant `outLen`; `f n b = b ⊕ [n odd]`). |
| 10 | note | **Fixed.** "for `n ≥ 1`" at the three places (`Asymptotic/Permutations.lean:28, 78, 426`). |
| 11 | note | **No change** (true; the review proposes none). |
| 12a | note | **Recorded** (G3-6, `QUEUE.md:125`): the 15 attributes are approved and unchanged: `prod_inLen`, `prod_outLen`, `eval_yaoBlocks`, `eval_yaoRounds`, `PermFamily.toFunFamily_f` (`OneWay.lean`), `NUPPT.coins_withIndexParam` (now `Asymptotic/CollectionsHelpers.lean:68`), `liftSucc_zero`, `liftSucc_succ` (`Permutations.lean`), `length_natToList`, `mulStr_`, `addStr_`, `subStr_`, `leStr_`, `modExpStr_pairEncode`, `length_sizeStr` (`Candidates/Arithmetic.lean`). No repair added an attribute. |
| 12b | note | **Fixed** (the review's option): `NUPPT.withIndexParam`, `length_runAt_le`, `runLenPoly` and their lemmas moved, names unchanged, to `Asymptotic/CollectionsHelpers.lean:58–115`, which `Collections.lean` imports. The file is still in the crypto layer, as the review allowed. |
| 12c | minor (was note) | **Scheduled** (G3-5, clean-up part 2). `ptc_comp` (`Collections.lean:644`, private) is DL-10; `decodeFin_eq_some_iff` (`Collections.lean:472`, private; `Asymptotic/GGMReductionEval.lean:163`, public) is DL-15, together with #198's new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean:189`). G3-5 supersedes the review's "inline `ptc_comp` now". |
| 12d | note | **Fixed.** `Collections.lean` was split upstream first and is 982 lines with the new field. |
| 13 | note | **Fixed.** `not_weakOneWay_id`, `not_worstCaseOneWay_id` (`OneWay.lean:870, 887`) and `FunFamily.not_toCollection_oneWay_id` (`Collections.lean:545`), through `FunFamily.invProbAt_ofString_id_eq_one` (`OneWay.lean:836`); printed with `TrapdoorCollection.eval_inv` in `audits/pass-shelat/Checks.lean:404–416`, all standard (`checks-axioms.log:424–436`). |
| 14 | note | **No change:** resolved by the review (`samplePairOut_eq_encode`; the default pair is the canonical encoding). Under G3-1 `factoringCollection` discharges `encD_decD` (`Candidates/Factoring.lean:585`). |
| M1 | (review) Prop 161.5 unprovable as stated | **Fixed** outside ch. 2–4 (G3-8, prong B `587843c7…`); see #7. |
| M2 | (review) `PredEvaluator`; GL docstring overclaims | **Fixed.** Under canonical decoding the evaluator is derivable (`PublicKey.lean:549`) and Thm 104.4's text reading is evaluator-free (:973); "from trapdoor permutations alone" is replaced (`Asymptotic/HardCoreCollection.lean:344–347`, `PublicKey.lean:809–812`; G3-7 (c)). |
| M3 | (review) the lenient fix breaks GL for collections | **No change:** the lenient alternative was not adopted. |
| M4 | (review) the infidelity is in Def 41.1 (2), 56.1 (6) | **Recorded** here and in the field docstring (`Collections.lean:141–146`) and DESIGN §5 item 24: the auditor's inventory row Def-41.1 should read "(2) and Def 56.1 (6) were decode-level only; repaired by `encD_decD`", and (3) was faithful. |
| M5 | (review) `fUniversal` is the in-repo instance of #2 | **No change:** the lossy padding is harmless there; a pointer for 03h. |
| M6 | (review) third copy of `decodeFin_eq_some_iff` | **Scheduled:** DL-15 (part 2). The ledger row calls the `GGMRed` copy private; it is public (`GGMReductionEval.lean:163`), which is what makes the namespace collision. |
| M7 | (review) split `Collections.lean` first | **Fixed:** the split precedes the field (#12b, #12d). |
| M8 | (review) the † items | **No change:** resolved by the review against the extract (#3, #8, #11). |
