# Chapter 7 completeness grade (printed AB09, pp. 123–143)

Independent grader pass, 2026-10-14, worktree `tcstcslib-ch7`. I read the printed chapter text
(`ch7_book_pp123-143.txt`) start to finish, including the "What have we learned" box, the chapter
notes and all exercises. For each item I found the Lean declaration myself (a namespace-aware index
of every `theorem`/`lemma`/`def`/`structure` under `TCSlib/`) and read its statement.

**Name check.** All 160 qualified names cited in `SURVEY.md`, plus its 20 unqualified names, exist,
in the namespace and file SURVEY gives. Some of its line numbers are off by 1–4 lines (see P10).

**Sorry check.** No `sorry`, `admit` or `native_decide`, and no `axiom`/`unsafe`/`implemented_by`,
in `Randomized/*.lean`, `ClassP/BinaryArith/*.lean`, `SpaceComplexity/Machines/*.lean` or
`TuringMachine/Build/ND*.lean`. None of the 129 added lines of `ClassNP/Nondeterminism.lean`
adds one. The pre-existing sorried lemmas `NDTM.runWith_eq_fixChoice_runFrom`
(Nondeterministic.lean:290) and `spaceUsedWith_eq_fixChoice_spaceUsed`
(NondeterministicSpace.lean:182) are not referenced by any chapter-7 file. Axiom probe: see the
end of this file.

Verdict key: OK · UNFAITHFUL (formalized, but the statement is weaker than the book's or narrower
in scope, and nothing records or justifies that) · MISSING · SORRY · EXCLUSION-OK (legitimately
not formalized) · EXCLUSION-NOT-OK (not formalized, and either not legitimate or not listed in
`NOT_FORMALIZED.md`).
Paths are relative to `TCSlib/Complexity/`.

## 1. Body items

| Item | Lean name(s) | File | Verdict | Note |
|---|---|---|---|---|
| Def 7.1 PTM, runs in T(n) | `Turing.FinNDTM.RunsInTime`, `outputWith`, `outputProb` | Randomized/PTM.lean:112–122 | OK | coin per step = choice word; 0/1-output convention recorded (:40-48) |
| §7.1 "Pr = fraction of branches" | `outputProb` (counting ratio `randProb`) | PTM.lean:121 | OK | |
| Def 7.2 BPTIME, BPP | `FinNDTM.BPDecidesInTime`, `Randomized.BPTIME`, `BPP_PTM` | PTM.lean:126, 268, 273 | OK | `c·T`, `n^c+1` padding recorded |
| p.126 P ⊆ BPP | `DTIME_subset_BPTIME`, `P_subset_BPP_PTM` | Randomized/Inclusions.lean:89,103 | OK | |
| Def 7.3 BPP (certificate) | `InBPP`, `polyTimeModel`, `polyLen` | Randomized/Classes.lean:276; PolyTimeModel.lean:75 | OK | `polyLen` schedules justified; Eff = both answer sets in `P` (tags say "Def 7.4", see P8) |
| p.126 Def 7.2 ≡ Def 7.3 | `mem_BPP_PTM_iff`, `BPP_PTM_eq` | Randomized/PTMEquiv.lean:300,304 | OK | genuine two-way equivalence |
| p.126 BPP ⊆ EXP | `BPP_PTM_subset_EXP`, `mem_EXP_of_inBPP_polyTimeModel` | PTMEquiv.lean:394; Inclusions.lean:207 | OK | |
| §7.2.1 median, FindKthElement correct | `IsMedian`, `findKthElement`, `findKthElement_correct`, `_isMedian` | Randomized/Median.lean:234,259,304 | OK | strict-partition repair justified (printed algorithm loops on `[a,a]`) |
| Claim 7.4 T(n)=O(n) | `maxExpectedComparisons_le` (`≤ 10n`) | Median.lean:511 | OK | the book's own constant |
| Footnote 2 (unit cost) | — | — | EXCLUSION-OK | cost-model aside, no claim |
| §7.2.2 PRIMES, QR_N | `PRIMES`, `qrSymbol`, `qrSymbol_trichotomy` | Randomized/PrimalityMath.lean:77–86 | OK | |
| §7.2.2 fact 1 (Euler) | `qrSymbol_eq_pow` | PrimalityMath.lean:131 | OK | |
| §7.2.2 fact 2 (Jacobi def + time) | `jacobiSym_eq_prod_qrSymbol`; `BinArith.polyTimeComputable_jacobiAlg`, `_jacobiModAlg` | PrimalityMath.lean; ClassP/BinaryArith/Jacobi.lean:295,389 | OK | poly time instead of `O(log A·log N)`; recorded (Jacobi.lean:32); a cited fact |
| §7.2.2 fact 3 | `two_mul_card_eulerLiarSubgroup_le`, `two_mul_card_filter_isEulerLiar_le` | PrimalityMath.lean:373,389 | OK | |
| §7.2.2 Solovay–Strassen: PRIMES ∈ coRP ⊆ BPP | `inCoRP_PRIMESBin`, `PRIMESBin_mem_coRP_PTM`, `PRIMESBin_mem_BPP_PTM` | Randomized/Primality.lean:231–273 | OK | |
| Footnotes 3, 4; AKS04; factoring (Ch.10) | — | — | EXCLUSION-OK | anecdotes / cited / deferred; not listed in NOT_FORMALIZED (P7) |
| §7.2.3 algebraic circuits, polynomial computed | `AlgCircuit`, `toMvPolynomial` | Randomized/AlgCircuit.lean:85,156 | OK | single sink recorded |
| §7.2.3 ZEROP; PIT ≤ ZEROP via C−C′ | `ZEROP`, `subCircuit`, `toMvPolynomial_eq_iff_subCircuit`, `PITLang_le_ZEROP` | AlgCircuit.lean:338,403,533; Randomized/ZeroPReduce.lean:386 | OK | |
| p.129 ∏(1+xᵢ): circuit size 2n, 2ⁿ terms | — | — | MISSING | concrete claim, not formalized, not listed (P4) |
| Footnotes 5, 6 | `MvPolynomial.totalDegree` | — | OK | definitional |
| Lemma 7.5 Schwartz–Zippel | `schwartz_zippel` | Randomized/SchwartzZippel.lean:66 | OK | |
| p.130 size m ⇒ degree ≤ 2^m; values ≤ (10·2^m)^{2^m} | `totalDegree_toMvPolynomial_le`, `abs_eval_le_pow` | AlgCircuit.lean:259,304 | OK | |
| p.130 naive test rejects w.p. ≥ 9/10 | `AlgCircuit.prob_eval_ne_zero` (15/16 over `[2^{m+4}]`) | Randomized/Fingerprint.lean:271 | OK | range change recorded (Fingerprint.lean:41) |
| p.130 fingerprinting Pr[k∤y] ≥ 1/(4m) | `fingerprint` (M ≥ 12, Chebyshev instead of PNT) | Fingerprint.lean:164 | OK | "sufficiently large m" made explicit |
| p.130 ZEROP ∈ coRP | `inCoRP_ZEROP_polyTime`, `ZEROP_mem_coRP_PTM`, `ZEROP_mem_BPP_PTM`; `PITLang_mem_coRP_PTM` | Randomized/ZeroP.lean:498–510; ZeroPPIT.lean:291 | OK | |
| §7.2.4 PM ⇔ det(X) ≢ 0 | `Matching.det_edmondsMatrix_ne_zero_iff` | Randomized/MatchingMath.lean:248 | OK | |
| §7.2.4 Lovász's algorithm | `lovasz_test`, `lovasz_test_zmod`, `BipartitePerfectMatching_mem_RP_PTM` | MatchingMath.lean:388,406; Matching.lean:507 | OK | values from `[2^k] ⊇ [2n]`, mod-p determinant recorded |
| p.131 NC parallel implementation (Ex 6.16) | — | — | EXCLUSION-NOT-OK | legitimate (Ch. 6 material) but not listed (P7) |
| Def 7.6 RTIME, RP | `FinNDTM.RDecidesInTime`, `RTIME`, `RP_PTM`; `InRP` | PTM.lean:133,277,281; Classes.lean:285 | OK | |
| p.131 RP ⊆ NP | `RP_PTM_subset_NP` | Inclusions.lean:112 | OK | |
| p.131 coRP | `coRP_PTM`, `InCoRP` | PTM.lean:284; Classes.lean:295 | OK | |
| §7.3 T_{M,x}, expected running time | `notHaltedProb`, `ExpTimeLe`, `FinNDTM.ExpTimeLe` | Randomized/ExpectedTime.lean:159,163,329 | OK | tail-sum form of E[T], prefix-stable runs |
| Def 7.7 ZTIME, ZPP | `FinNDTM.ZDecidesInTime`, `ZTIME`, `ZPP_PTM` | ExpectedTime.lean:407,546,550 | OK | every halted branch correct; E[T] ≤ c·T |
| Thm 7.8 ZPP = RP ∩ coRP | `ZPP_PTM_eq_RP_PTM_inter_coRP_PTM`; `zpp_eq_rp_inter_corp_polyTime`; `inZPP_iff_inRP_and_inCoRP` | Randomized/ZPPHostsClasses.lean:375; PolyTimeModel.lean:539; Classes.lean:897 | OK | proved for Def 7.7's expected-time ZPP |
| p.132 RP, coRP ⊆ BPP | `RP_PTM_subset_BPP_PTM`, `coRP_PTM_subset_BPP_PTM` | Inclusions.lean:117,121 | OK | |
| Lemma 7.9 BPP_{1/2+n^{-c}} = BPP | `inBPPWeak_iff_inBPP` (abstract `E`, `ClosedUnderMajority` hypothesis) | Classes.lean:1315 | UNFAITHFUL | stated for a polynomial-time PTM. The repo has only the abstract certificate form: no `polyTimeModel` instance, no PTM form (P1) |
| Thm 7.10 error reduction | `bpp_error_reduction` (abstract); `majority_error_le` | Classes.lean:1181; ErrorReduction.lean:330 | UNFAITHFUL | same gap as Lemma 7.9 (P1). The bound is stronger than the book's, which is fine |
| p.133 RP/coRP error reduction (→ Ex 7.4) | see Ex 7.4 | | OK | |
| p.133 randomness-efficient O(m+k) coins | — | — | EXCLUSION-OK | the book defers it to Ch. 21 §21.2.5; listed |
| §7.4.2 expected time ≡ worst-case, for BPTIME | `haltProb_le_truncate`, `BPP_ExpPTM_eq_BPP_PTM` | ExpectedTime.lean:391; Randomized/ZPPEquiv.lean:303 | OK | |
| §7.4.2 the same, for RTIME | — | — | MISSING | the book says it for "RTIME(T(n)) and BPTIME(T(n))"; only BPP is done (P3) |
| §7.4.3 ρ-coin setting | `biasedProb`, `FinNDTM.biasedOutputProb`, `biasedBPP` | Randomized/Coins.lean:291; BiasedCoin.lean:209–231 | OK | |
| Note 7.11 Chernoff / estimation, O(log(1/δ)/ε²) | `iid_bernoulli_avg_concentration(_of_le)`, `exists_sample_count` | ErrorReduction.lean:251,363,386 | OK | its "Erratum" is mis-attributed (P8) |
| Lemma 7.12 ρ-coin from fair coins, expected O(1) | `rhoCoinRun`, `expTimeLe_rhoCoinRun`, `exists_expCost_rhoCoinRun_le`, `tendsto_randProb_rhoCoinRun`, `randProb_rhoCoinRun_binDigit` | Coins.lean:69–261 | OK | coin-level procedure with poly(i) cost per bit; divergence recorded (Coins.lean:42-47) |
| Lemma 7.13 von Neumann | `vonNeumann_heads_eq_tails`, `tendsto_vonNeumann_heads`, `vonNeumann_expected_pairs` | Coins.lean:419–435 | OK | the book's bound `1/(2ρ(1−ρ))` exactly |
| p.135 weak random sources (Ch. 21) | — | — | EXCLUSION-OK | announcement only, no claim |
| p.135 P ⊆ BPP ⊆ P/poly; P=NP ⇒ BPP=P | `BPP_PTM_eq_P_of_P_eq_NP` | PTMEquiv.lean:398 | OK | |
| p.135 "BPP=P ⇒ BPP ⊊ DTIME(n^{log n})" (time hierarchy) | — | — | EXCLUSION-NOT-OK | stated consequence; not formalized, not listed (P5) |
| §7.5.1 3SAT ∈ BPP ⇒ PH collapses | `PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM` | PTMEquiv.lean:415 | OK | |
| Thm 7.14 Adleman | `BPP_PTM_subset_PPoly`, `adleman_polyTime`, `adleman` | PTMEquiv.lean:402; PolyTimeModel.lean:476; Adleman.lean:87 | OK | statement faithful; tags say "Thm 7.17" (P8) |
| p.136 BPP = coBPP | `compl_mem_BPP_PTM`, `InBPP.compl` | PTM.lean:320; Classes.lean:723 | OK | |
| Thm 7.15 Sipser–Gács | `BPP_PTM_subset_SigmaP_two_inter_PiP_two`, `sipser_gacs_polyTime`, `sipser_gacs` | PTMEquiv.lean:406; PolyTimeModel.lean:552; SipserGacs.lean:672 | OK | uses the library's `SigmaP`/`PiP`; tags say "Thm 7.18" (P8) |
| Claim 1 / Claim 2 (p.137) | inside `bpp_subset_sigma2`, via `shift_count_lt_two_pow`, `exists_notMem_of_card_lt`, `randProb_xor_right`, `randProb_blockCount` | SipserGacs.lean:111,174,362,388 | OK | proved as steps of the theorem's proof. `k` is balanced against the amplified error, since the book's `k = m/n+1` fails at small n (recorded) |
| §7.5.3 BPTIME property undecidable | — | — | EXCLUSION-OK | the book asserts it as motivation without proof; false for the repo's non-effective codes; listed |
| §7.5.3 ⟨M,x,1^t⟩ language is BPP-hard | `probAccept_bppHard` | Randomized/BPPHard.lean:250 | OK | holds for every lawful code scheme (recorded) |
| §7.5.3 that language is #P-complete (Ch. 17) | — | — | EXCLUSION-NOT-OK | legitimate (deferred to Ch. 17) but not listed (P7) |
| §7.5.3 BPP=P ⇒ BPP has a complete problem | — | — | EXCLUSION-NOT-OK | one-line conditional; not formalized, not listed (P5) |
| §7.5.3 BPTIME hierarchy open | — | — | EXCLUSION-OK | open problem, no claim |
| Def 7.16 randomized reduction | `RandReducible` (`≤ᵣ`) | Randomized/Reductions.lean:169 | OK | printed B/C swap recorded; certificate-form transducer |
| p.138 "not transitive" | — | Reductions.lean:42 | OK | the repo claims no transitivity (recorded) |
| p.138 C ∈ BPP, B ≤ᵣ C ⇒ B ∈ BPP | `InBPP.of_randReducible` | Reductions.lean:289 | OK | |
| Def 7.17 BP·NP | `BPNP`, `NP_subset_BPNP` | Reductions.lean:354,359 | OK | |
| p.138 Valiant–Vazirani (Ch. 17) | — | — | EXCLUSION-OK | forward reference only |
| §7.7 PTM space S(n) | `FinNDTM.UsesSpace` | Randomized/Space.lean:102 | OK | counts visited cells (recorded) |
| Def 7.18 BPL, RL | `BPDecidesInSpace`, `RDecidesInSpace`, `BPSPACE`, `RSPACE`, `BPL`, `RL` | Space.lean:108,115,230–242 | OK | requires every branch to halt by some T, as Def 7.1 does (recorded); this forces poly time |
| p.139 error reduction in log space | `mem_RSPACE_of_pos`, `mem_BPSPACE_of_advantage`, `BPL_error_reduction`, `RL_error_reduction` | Space.lean:489,500; SpaceAmplifyPoly.lean:378,423 | OK | |
| p.139 RL ⊆ NL ⊆ P | `RL_subset_NL`, `RL_subset_P` | Space.lean:268,271 | OK | |
| §7.7 UPATH | `Complexity.UPATH`, `mem_UPATH_iff` | Randomized/UPath.lean:51,174 | OK | symmetric adjacency matrix |
| Thm 7.19 UPATH ∈ RL | `Complexity.UPATH_mem_RL` via `LogProg.narm_mem_RL` | Randomized/UPathRL.lean:172; SpaceComplexity/Machines/NARMLogspace.lean:174 | OK | genuine logspace PTM, `100n⁴` walk |
| p.139 E[hit] ≤ 10n⁴, accept ≥ 3/4 | `hitTime_le_ten_mul_pow_four`, `three_quarters_le_hitProb` | Randomized/RandomWalkHitting.lean:370,383 | OK | |
| p.139 deterministic logspace UPATH (Ch. 21 §21.4) | — | — | EXCLUSION-NOT-OK | legitimate (deferred) but not listed (P7) |
| p.139 BPL ⊆ SPACE(log^{3/2} n) | — | — | EXCLUSION-OK | cited [SZ99]; listed |
| Footnote 7 cover time, lollipop | — | — | EXCLUSION-OK | cited [Fei95]; listed |
| "What have we learned" box | as above | | OK | |
| Notes: BP·P = BPP (p.141) | — | — | EXCLUSION-NOT-OK | concrete claim; easy with `RandReducible`; not formalized, not listed (P5) |
| Notes: [Can96, RS95], BPP/1 hierarchies, promise problems | — | — | EXCLUSION-NOT-OK | legitimate (cited) but not listed (P7) |

## 2. Exercises

| Item | Lean name(s) | File | Verdict | Note |
|---|---|---|---|---|
| Ex 7.1 | `uniformSample_spec` | Randomized/UniformSample.lean:339 | OK | poly-time in `⟨N, 1^k⟩`, `k = ⌈log(1/δ)⌉`; failure ≤ δ; uniform given not `?` |
| Ex 7.2 | `exists_sum_rpow_div_two_pow_le` | Coins.lean:453 | OK | holds for every real c |
| Ex 7.3 | `BinArith.polyTimeComputable_powMod` | ClassP/BinaryArith/ModPow.lean:214 | OK | `powMod` is `a^n mod p` on the decoded triple |
| Ex 7.4 | `RP_PTMWith_error_reduction`, `rp_error_reduction_polyTime`, `inRPWeak_iff_inRP` | PTMEquiv.lean:421; Inclusions.lean:367,435,440 | OK | PTM form; hypothesis weaker and conclusion stronger than the book's |
| Ex 7.5 | `exists_biasedBPP_not_computablePred` | Randomized/BiasedCoinHalting.lean:582 | OK | ρ-coin PTMs (`biasedBPP`), non-computable language |
| Ex 7.6(a) | `ZPPAbort_PTM_eq_ZPP_PTM`, `ZDecidesInTime.abort`, `AbortDecidesInTime.restart` | ZPPHostsClasses.lean:365; ExpectedTime.lean:454,512 | OK | machine-level equality of the classes |
| Ex 7.6(b) | `ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` | ZPPHostsClasses.lean:375 | OK | |
| Ex 7.7 | `Language.InNPPoly`, `BPNP_subset_NPPoly` | Randomized/NPPoly.lean:125,260 | OK | |
| Ex 7.8 | `PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP` (+ Yap `PH_eq_SigmaP_three_of_coNP_subset_NPPoly`) | Randomized/Yap.lean:578,593 | OK | hypothesis `3SATᶜ ∈ BP·NP`, the correct reading of the lost overbar |
| Ex 7.9 | `BPL_subset_P` | Randomized/BPLInP.lean:437 | OK | DP over configurations, threshold test in P |
| Ex 7.10 | `hitProb_chainDigraph_le`, `hitTime_chainDigraph_ge`, `chainDigraph_reachable` | Randomized/DirectedWalk.lean:158,182 | OK | `n+1` vertices, `E[τ] ≥ (2ⁿ−1)/2` |
| Ex 7.11(a) | `RegularMultigraph.uniform_stationary` | Randomized/RandomWalk.lean:155 | OK | |
| Ex 7.11(b) contraction | `exists_uniformExcess_walkDist_le`, `uniformExcess_walkDist_two_mul_le` | Randomized/RandomWalkMixing.lean:337,374 | OK | ∃k ∀p (stronger) |
| Ex 7.11(b)(a) uniqueness | `isStationary_iff_eq_uniform` | RandomWalkMixing.lean:403 | OK (minor) | only ℚ-valued distributions; not recorded (P9) |
| Ex 7.11(b)(b) visit frequency | `exists_le_expVisits` | RandomWalkMixing.lean:433 | OK | |
| Ex 7.11(c) E_u ≤ 10n | `returnTime_le_card` (E_u ≤ n) | RandomWalkHitting.lean:167 | OK | sharper |
| Ex 7.11(d) E_{u,v} ≤ 100kn²; 1000n³ walk misses w.p. ≤ 1/10 | `hitTime_le` (`2Dn³`), `one_sub_le_hitProb` | RandomWalkHitting.lean:313,359 | UNFAITHFUL | weaker bound, recorded (:43-48); neither of the exercise's two conclusions is proved (P2) |
| Ex 7.11(e) | `half_le_hitProb_padGraph`, `half_le_hitProb_padDegree` | Randomized/RandomWalkMixingPad.lean:267,284 | OK | `G` irregular via `Digraph.mk`, `G′` = padding with `n ≤ D ≤ 4n²` |

## 3. Exclusions in NOT_FORMALIZED.md

| Row | Verdict | Reason |
|---|---|---|
| BPL ⊆ SPACE(log^{3/2} n) [SZ99] | EXCLUSION-OK | the book cites it and defers it to §21.6 |
| Footnote 7 cover time / lollipop [Fei95] | EXCLUSION-OK | cited without proof |
| §7.5.3 BPTIME property undecidable | EXCLUSION-OK | asserted as motivation without proof, nothing depends on it, and no effective PTM code scheme exists to state it (the statement is false for lawful non-effective schemes) |
| p.133 O(m+k)-coin repetition | EXCLUSION-OK | the book defers it to Ch. 21 §21.2.5 |
| Web-draft expander appendix (incl. `Expander.walk_visits_concentration` sorry) | EXCLUSION-OK | not in printed Ch. 7 |

## 4. Problems found

- **P1 — Lemma 7.9 and Thm 7.10 exist only in abstract certificate form.** The book states
  both for polynomial-time PTMs. The repo proves them only for an arbitrary `VerifierModel E`
  with `ClosedUnderMajority E` (`Classes.lean:1134` `InBPPWeak`, `:1154` `InBPPStrong`,
  `:1181` `bpp_error_reduction`, `:1315` `inBPPWeak_iff_inBPP`). There is no `polyTimeModel`
  corollary (SURVEY row 29 admits this), and no PTM form. Exercise 7.4 has a PTM form
  (`RP_PTMWith`, `mem_RP_PTMWith_iff`, `RP_PTMWith_error_reduction`, `PTMEquiv.lean:317–425`);
  BPP has no analogue. **Needed:** `BPDecidesInTimeWith` / `BPP_PTMWith p`, its equivalence with
  the threshold-`p` certificate class over `polyTimeModel`, and PTM-form statements of Lemma 7.9
  (`BPP_PTMWith (1/2 + weakAdv c) = BPP_PTM`) and Thm 7.10 (`BPP_PTMWith (1/2 + weakAdv c) ⊆
  BPP_PTMWith (1 − 2^{-((n+1)^d+1)})`).
- **P2 — Exercise 7.11(d) is weakened.** The exercise asks for `E_{u,v} ≤ 100kn²` when `u` and
  `v` are joined by a path of length `≤ k`, and for "a `1000n³`-step walk misses `t` with
  probability `≤ 1/10`". `hitTime_le` (`RandomWalkHitting.lean:313`) proves only `2·D·n³`. For
  `D ≤ n` that is `2n⁴`. With this bound, `one_sub_le_hitProb` (`:359`) gives a miss
  probability of about `n/500` at `L = 1000n³`, which is not `≤ 1/10` once `n > 50`. The
  divergence is recorded (`:43-48`), but it leaves the exercise unproved, while SURVEY marks it
  "proved". The source of the loss is the energy argument's `k²·2Dn`
  (`RandomWalkHitting.lean` ≈ `:300`), which should be linear in `k`. The commute-time
  argument gives `E_{u,v} ≤ D·n·k`: each edge has effective resistance `≤ 1`, and `2|E| = Dn`.
  **Needed:** `E_{u,v} ≤ D·n·k` (hence `≤ 100kn²` for `D ≤ 100n`, which covers simple graphs),
  and the `1000n³ ⇒ ≤ 1/10` corollary. (Theorem 7.19 itself is unaffected.)
- **P3 — §7.4.2 for RTIME is missing.** The book: "When defining RTIME(T(n)) and BPTIME(T(n))
  … we could have used expected running time instead … this yields an equivalent definition."
  Only `BPP_ExpPTM_eq_BPP_PTM` exists (`ZPPEquiv.lean:303`). The `RP_ExpPTM = RP_PTM` analogue
  was flagged as cheap (CRITIQUE_LOG, U8 round 2) and never done. **Needed:** the RP (and coRP)
  expected-time class equality. The truncation must output 0 on timeout to keep one-sided
  error.
- **P4 — p.129 example missing.** "`∏ᵢ(1+xᵢ)` can be computed using a circuit of size `2n` but
  has `2ⁿ` terms." This is a concrete, easily formalized claim: an `AlgCircuit` of size `O(n)`
  whose `toMvPolynomial` has support of size `2ⁿ`. It is neither formalized nor listed.
- **P5 — provable remarks neither formalized nor listed in NOT_FORMALIZED.md.** Each must be
  formalized or given an explicit exclusion row with a reason:
  (a) chapter notes p.141, "`BP·P = BPP`": immediate from `RandReducible` and
  `InBPP.of_randReducible`;
  (b) p.135, "if BPP = P then BPP ⊊ DTIME(n^{log n})" (time hierarchy; the repo has
  `TimeHierarchy.lean`);
  (c) p.138, "if BPP = P then BPP has a complete problem (since P does)".
- **P6 — sorry status: no problem.** No sorry, admit or native_decide; every declaration
  probed uses only the standard axioms (§5).
- **P7 — NOT_FORMALIZED.md is not exhaustive.** It says the listed rows are all the cited,
  deferred or informal items. These are also not formalized and legitimately excluded, but
  unlisted: Lovász test in NC (p.131, Ex 6.16); #P-completeness of the `⟨M,x,1^t⟩` language
  (p.138, Ch. 17); Valiant–Vazirani (p.138, Ch. 17); deterministic logspace UPATH (p.139,
  §21.4); [AKS04] PRIMES ∈ P (p.128); factoring on quantum computers (p.129, Ch. 10); BPP = P
  under hardness assumptions (Ch. 19–20); chapter-notes results [Can96, RS95], BPP/1 hierarchy
  theorems [Bar02, FS04, GST04], and the promise-problem remark. **Needed:** add rows (one
  grouped "forward references / cited results" row is acceptable).
- **P8 — attribution errors (policy §2).** The References sections cite the printed 2009 book,
  but the tags still use web-draft numbering:
  `Classes.lean:28,41,53,61,71,109,244,251,256,275,716` ("Def 7.4" means printed Def 7.3;
  "Thm 7.18" means 7.15); `Adleman.lean:16,30,71` ("Thm 7.17" means 7.14);
  `SipserGacs.lean:15,25,33,59,60,76,230,370,647` ("Thm 7.18"/"Def 7.4");
  `PolyTimeModel.lean:46,55,73,473,544`; `ErrorReduction.lean:28,44,55,59,85,238`
  ("Cor 7.11", which does not exist in print).
  `ErrorReduction.lean:59-68` is the most serious. It attributes a false "Erratum" bound and a
  `1/n` normalisation typo to "[AB09, Cor 7.11]". Printed Thm 7.10 cites Cor A.15 with the
  multiplicative bound `e^{−δ²pk/4}`, which is correct, and printed Note 7.11 contains no such
  statement. The docstring therefore asserts an error in the printed book that the printed
  book does not contain. `Classes.lean:66-69` also still describes the poly-time
  instantiation as future work, though `polyTimeModel` exists.
- **P9 — Ex 7.11(b)(a) ℚ-only (minor).** `isStationary_iff_eq_uniform`
  (`RandomWalkMixing.lean:403`) quantifies over `p : V → ℚ`. The module's Divergences block
  (`:41-47`) does not record the restriction to rational distributions. Record it, or state it
  for ℝ (the kernel of a rational matrix has the same dimension over ℚ and ℝ).
- **P10 — stale campaign documents.**
  - SURVEY row 15 says the poly-time `code(C−C′)` map "is in NOT_FORMALIZED.md". It is
    actually proved (`PITLang_le_ZEROP`, ZeroPReduce.lean:386) and is not listed there.
  - SURVEY row 50 says the `2^{-n^d}` log-space version is in NOT_FORMALIZED.md. It is proved
    (`BPL_error_reduction` and `RL_error_reduction`, SpaceAmplifyPoly.lean:378,423).
  - Several SURVEY line numbers are off (e.g. rows 16, 29, 30: `:64` is really `:66`, `:1314`
    is `:1315`, `:1180` is `:1181`, `:1153` is `:1154`; `ErrorReduction.lean:326` is `:330`).
  - CRITIQUE_LOG has no U11 or U17 section. The "axiom sweep clean" claim is recorded only in
    PLAN.md:111.

## 5. Axiom probe

I ran `#print axioms` on 32 headline declarations through `lb.sh` (build
`build-163207-69803.log`, EXIT 0); the probe file has since been deleted. All 32 depend only on
`[propext, Classical.choice, Quot.sound]`. The declarations: `mem_BPP_PTM_iff`, `bpp_error_reduction`,
`BPP_PTM_subset_PPoly`, `BPP_PTM_subset_SigmaP_two_inter_PiP_two`,
`ZPP_PTM_eq_RP_PTM_inter_coRP_PTM`, `ZPPAbort_PTM_eq_ZPP_PTM`, `BPP_ExpPTM_eq_BPP_PTM`,
`RL_subset_P`, `BPL_subset_P`, `UPATH_mem_RL`, `PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP`,
`exists_biasedBPP_not_computablePred`, `PRIMESBin_mem_coRP_PTM`, `ZEROP_mem_coRP_PTM`,
`PITLang_mem_coRP_PTM`, `BipartitePerfectMatching_mem_RP_PTM`, `probAccept_bppHard`,
`exists_le_expVisits`, `half_le_hitProb_padDegree`, `uniformSample_spec`,
`maxExpectedComparisons_le`, `RP_PTMWith_error_reduction`, `BPL_error_reduction`,
`hitTime_chainDigraph_ge`, `vonNeumann_expected_pairs`, `exists_expCost_rhoCoinRun_le`,
`exists_sample_count`, `polyTimeComputable_powMod`, `polyTimeComputable_jacobiAlg`,
`InBPP.of_randReducible`, `fingerprint`, `two_mul_card_filter_isEulerLiar_le`.
Lint noise in chapter files, not a grading issue: an unused simp argument `hp` at
`Classes.lean:1216` and at `SipserGacs.lean:289`.

GRADE: INCOMPLETE
1. P1 — PTM-form (or at least `polyTimeModel`) statements of Lemma 7.9 and Theorem 7.10.
2. P2 — Exercise 7.11(d): `E_{u,v} ≤ 100kn²` (via `≤ D·n·k`) and the `1000n³ ⇒ miss ≤ 1/10` corollary.
3. P3 — §7.4.2 for RTIME/RP: expected-time RP equals RP.
4. P4 — the p.129 `∏(1+xᵢ)` example (size-`O(n)` circuit, `2ⁿ` monomials).
5. P5 — formalize or explicitly exclude: BP·P = BPP (notes); BPP = P ⇒ BPP ⊊ DTIME(n^{log n}); BPP = P ⇒ BPP has a complete problem.
6. P7 — list the remaining cited/deferred items in NOT_FORMALIZED.md.
7. P8 — retag draft-numbered `[AB09, …]` citations to printed numbering and remove the false "Erratum" attributed to the printed book (ErrorReduction.lean:55-68).
8. P9 — record (or remove) the ℚ-only restriction in Ex 7.11(b)(a).
9. P10 — correct the stale SURVEY rows 15/50 and line numbers; record the U11/U17 axiom sweep in CRITIQUE_LOG.
