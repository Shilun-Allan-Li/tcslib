# Chapter 7 (printed AB09, pp. 123–143) — formalization survey

Read-only survey of worktree `tcstcslib-ch7` (branch `complexity/arora-barak-ch7-cont`) against
`ch7/ch7_book_pp123-143.txt`. Numbering is the **printed** book's. The existing Lean cites the 2007
web draft; the translation used here: draft "Def 7.4" = printed Def 7.3; draft "Thm 7.17" = printed
Thm 7.14 (Adleman); draft "Thm 7.18" = printed Thm 7.15 (Sipser–Gács); draft "Cor 7.11" (Chernoff) has
no printed ch. 7 counterpart (printed Thm 7.10 cites Cor A.15; printed Note 7.11 is the
statistical-estimation note); draft §7.A/7.B expanders (Def 7.25, Lem 7.37/7.40, Thm 7.38/7.41) are
**not in printed ch. 7** (printed p.133 defers them to Ch. 21, §21.2.5).

Status key: **proved** (Lean name, file:line, fidelity), **def** (definition present), **partial**,
**sorried**, **missing**. All paths are relative to `TCSlib/Complexity/`. "Abstract" = stated over
`Randomized.VerifierModel E` (Randomized/Classes.lean:259) with closure hypotheses; "poly-time" = the
instance `polyTimeModel` (Randomized/PolyTimeModel.lean:75), i.e. verifiers whose `some true` /
`some false` sets on `Turing.pairEncode x r` are in `Complexity.P`. Probabilities are ℚ counting
ratios `randProb` (Classes.lean:110); random lengths are `polyLen a k n = a·(n+1)^k` (Classes.lean:248).

**Status column updated in U11 (cross-track pass, 2026-10-14)** to the Lean names that now
cover each row (unit in parentheses); §§3–4 below are the original pre-campaign analysis.

## 1. Body items

| # | Item (page) | Statement (short) | Status in repo |
|---|---|---|---|
| 1 | Def 7.1 (p.125) | PTM = TM with δ₀, δ₁ chosen by fair coins; runs in T(n) time if halts within T(|x|) on every branch | **def** (U1) `Turing.FinNDTM` read probabilistically: `Turing.FinNDTM.outputProb`, `Turing.FinNDTM.RunsInTime` (Randomized/PTM.lean) |
| 2 | Def 7.2 (p.125) | BPTIME(T): PTM halting in T(|x|) with Pr[M(x)=L(x)] ≥ 2/3; BPP = ∪_c BPTIME(n^c) | **def** (U1) `Turing.FinNDTM.BPDecidesInTime`, `Randomized.BPTIME`, `Randomized.BPP_PTM` (Randomized/PTM.lean) |
| 3 | Remark (p.126) | P ⊆ BPP (a TM is a PTM with δ₀=δ₁) | **proved** (U1) `Randomized.DTIME_subset_BPTIME`, `Randomized.P_subset_BPP_PTM`; certificate form `Randomized.inBPP_polyTimeModel_of_mem_P` (Randomized/Inclusions.lean) |
| 4 | Def 7.3 (p.126) | BPP alt.: poly-time TM M, poly p, Pr_{r∈{0,1}^{p(|x|)}}[M(x,r)=L(x)] ≥ 2/3 | **def** `Randomized.InBPP` Classes.lean:276; instantiated by `polyTimeModel` PolyTimeModel.lean:75. Faithful modulo: p restricted to `polyLen` schedules; "poly-time TM" = both answer sets of `pairEncode x r` in `P` |
| 5 | Remark (p.126) | BPP ⊆ EXP (enumerate coins) | **proved** (U1/U2) `Randomized.mem_EXP_of_inBPP_polyTimeModel` (Randomized/Inclusions.lean), `Randomized.BPP_PTM_subset_EXP` (Randomized/PTMEquiv.lean) |
| 6 | Remark (p.126, "alternative definition") | Def 7.2 ≡ Def 7.3 | **proved** (U2) `Randomized.mem_BPP_PTM_iff`, `Randomized.BPP_PTM_eq`, `Randomized.mem_RP_PTM_iff`, `Randomized.mem_coRP_PTM_iff` (Randomized/PTMEquiv.lean) |
| 7 | §7.2.1 (pp.126–127) | median def; FindKthElement outputs the k-th smallest | **proved** (U3) `Randomized.findKthElement` (a `PMF` over runs), `Randomized.findKthElement_correct`, `Randomized.findKthElement_isMedian` (Randomized/Median.lean); strict-partition divergence recorded |
| 8 | Claim 7.4 (p.127) | expected running time T(n) = O(n) | **proved** (U3) `Randomized.maxExpectedComparisons_le` (`T(n) ≤ 10n`), `Randomized.expectedComparisons_le` (Randomized/Median.lean) |
| 9 | §7.2.2 (p.128) | PRIMES; QR_N(A) ∈ {0,±1} | **def** (U5) `Randomized.PRIMES`, `Randomized.qrSymbol`, `Randomized.qrSymbol_trichotomy` (Randomized/PrimalityMath.lean) |
| 10 | §7.2.2 fact 1 | odd prime N: QR_N(A) ≡ A^{(N−1)/2} (Euler) | **proved** (U5) `Randomized.qrSymbol_eq_pow` (Randomized/PrimalityMath.lean) |
| 11 | §7.2.2 fact 2 | Jacobi symbol computable in O(log A · log N) | **proved** (U4) `Complexity.BinArith.polyTimeComputable_jacobiAlg`, `Complexity.BinArith.polyTimeComputable_jacobiModAlg` (ClassP/BinaryArith/Jacobi.lean); polynomial time, not the book's `O(log A · log N)` |
| 12 | §7.2.2 fact 3 | odd composite N: ≤ half of units A satisfy (A/N) ≡ A^{(N−1)/2} | **proved** (U5) `Randomized.two_mul_card_eulerLiarSubgroup_le`, `Randomized.two_mul_card_filter_isEulerLiar_le` (Randomized/PrimalityMath.lean) |
| 13 | §7.2.2 (p.128) | Solovay–Strassen: PRIMES ∈ coRP (hence BPP) | **proved** (U5) `Randomized.inCoRP_PRIMESBin`, `Randomized.inBPP_PRIMESBin`, `Randomized.PRIMESBin_mem_coRP_PTM`, `Randomized.PRIMESBin_mem_BPP_PTM` (Randomized/Primality.lean) |
| 14 | §7.2.3 (p.129) | algebraic circuits over {+,−,×}; compute an integer polynomial | **def** (U6) `Randomized.AlgCircuit`, `Randomized.AlgCircuit.toMvPolynomial` (Randomized/AlgCircuit.lean) |
| 15 | §7.2.3 (p.129) | ZEROP; PIT reduces to ZEROP via C − C′ | **def/proved** (U6) `Randomized.ZEROP`, `Randomized.AlgCircuit.subCircuit`, `Randomized.AlgCircuit.toMvPolynomial_eq_iff_subCircuit` (Randomized/AlgCircuit.lean); `Randomized.PITLang` (Randomized/ZeroPPIT.lean); poly-time map and reduction (U16) `Randomized.PITLang_le_ZEROP`, `Randomized.PITLang_mem_coRP_PTM_of_reduction` (Randomized/ZeroPReduce.lean) |
| 16 | Lemma 7.5 (p.129) | Schwartz–Zippel: p ≠ 0, deg ≤ d, S ⊂ ℤ finite ⇒ Pr[p(a) ≠ 0] ≥ 1 − d/|S| | **proved** `Randomized.schwartz_zippel` Randomized/SchwartzZippel.lean:64 — faithful (ℚ≥0 counting over `piFinset`, explicit `p ≠ 0`, `S` nonempty), via Mathlib `schwartz_zippel_totalDegree` |
| 17 | §7.2.3 (p.130) | size-m circuit has degree ≤ 2^m | **proved** (U6) `Randomized.AlgCircuit.totalDegree_toMvPolynomial_le`, value bound `Randomized.AlgCircuit.abs_eval_le_pow` (Randomized/AlgCircuit.lean) |
| 18 | §7.2.3 (p.130) | fingerprinting: k ∈_R [2^{2m}], y ≠ 0 ⇒ Pr[k ∤ y] ≥ 1/(4m) (uses PNT) | **proved** (U6) `Randomized.fingerprint` (for `M ≥ 12`, via the Chebyshev bound `Randomized.two_pow_le_mul_primeCounting` instead of the PNT; Randomized/Fingerprint.lean) |
| 19 | §7.2.3 (p.130) | ZEROP has a one-sided poly-time algorithm, i.e. ZEROP ∈ coRP | **proved** (U6) `Randomized.inCoRP_ZEROP_polyTime`, `Randomized.ZEROP_mem_coRP_PTM`, `Randomized.ZEROP_mem_BPP_PTM` (Randomized/ZeroP.lean); PIT: `Randomized.PITLang_mem_coRP_PTM` (Randomized/ZeroPPIT.lean) |
| 20 | §7.2.4 (pp.130–131) | bipartite G has a perfect matching ⇔ det(X) ≢ 0 (Edmonds matrix) | **proved** (U7) `Randomized.Matching.det_edmondsMatrix_ne_zero_iff` (Randomized/MatchingMath.lean) |
| 21 | §7.2.4 (p.131) | Lovász: random values from [2n], accept iff det ≠ 0; one-sided error | **proved** (U7) `Randomized.Matching.lovasz_test`, `Randomized.Matching.lovasz_test_zmod` (Randomized/MatchingMath.lean); `Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM` (Randomized/Matching.lean); determinant over `ZMod p` (divergence recorded) |
| 22 | Def 7.6 (p.131) | RTIME(T), RP = ∪ RTIME(n^c) | **def** (U1) `Turing.FinNDTM.RDecidesInTime`, `Randomized.RTIME`, `Randomized.RP_PTM` (Randomized/PTM.lean); certificate form `Randomized.InRP` Classes.lean |
| 23 | Remark (p.131) | RP ⊆ NP | **proved** (U1) `Randomized.RP_PTM_subset_NP`, `Randomized.mem_NP_of_inRP_polyTimeModel` (Randomized/Inclusions.lean) |
| 24 | Remark (p.131) | coRP = {L : L̄ ∈ RP} | **def** `Randomized.InCoRP` Classes.lean; PTM form `Randomized.coRP_PTM` (Randomized/PTM.lean) |
| 25 | §7.3 (p.131) | T_{M,x} running-time random variable; expected running time | **def** (U8) `Randomized.notHaltedProb`, `Randomized.ExpTimeLe`, `Turing.FinNDTM.ExpTimeLe` (finite tail sums; Randomized/ExpectedTime.lean) |
| 26 | Def 7.7 (p.131) | ZTIME(T): expected time O(T), output always correct when it halts; ZPP = ∪ ZTIME(n^c) | **def/proved** (U8, U8b) `Turing.FinNDTM.ZDecidesInTime`, `Randomized.ZTIME`, `Randomized.ZPP_PTM` (Randomized/ExpectedTime.lean); `Randomized.ZPP_PTM_eq_setOf_inZPP`, `Randomized.ZPPAbort_PTM_eq_ZPP_PTM` (Randomized/ZPPHostsClasses.lean) |
| 27 | Thm 7.8 (p.132) | ZPP = RP ∩ coRP | **proved** abstract `Randomized.inZPP_iff_inRP_and_inCoRP` Classes.lean; poly-time `zpp_eq_rp_inter_corp_polyTime` PolyTimeModel.lean; for Def 7.7's ZPP (U8b) `Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` (Randomized/ZPPHostsClasses.lean) |
| 28 | Display (p.132) | RP ⊆ BPP, coRP ⊆ BPP | **proved** (U1) `Randomized.RP_PTM_subset_BPP_PTM`, `Randomized.coRP_PTM_subset_BPP_PTM`, `Randomized.InRP.inBPP`, `Randomized.InCoRP.inBPP` (Randomized/Inclusions.lean) |
| 29 | Lemma 7.9 (p.132) | BPP_{1/2+n^{−c}} = BPP | **proved** abstract `Randomized.inBPPWeak_iff_inBPP` (Classes.lean; advantage `weakAdv c n = min(1/6, (n+1)^{−c})` because the literal 1/2+|x|^{−c} > 1 at |x| ≤ 1); poly-time `Randomized.inBPPWeak_polyTimeModel_iff_inBPP` and PTM form `Randomized.BPP_PTMWith_weakAdv_eq_BPP_PTM` (U18, Randomized/BPPAmplify.lean; threshold-generic `BPP_PTMWith`, `mem_BPP_PTMWith_iff` in Randomized/PTMEquiv.lean); p.132 "any constant > 1/2": `Randomized.BPP_PTMWith_const_eq_BPP_PTM` |
| 30 | Thm 7.10 (p.132) | error reduction: 1/2+|x|^{−c} ⇒ 1−2^{−|x|^d} | **proved** abstract `Randomized.bpp_error_reduction` Classes.lean:1180 (to `InBPPStrong` :1153, bound 2^{−((n+1)^d+1)}, stronger). Probability by exact ℚ binomial tail (`randProb_tail_le`), not the book's Chernoff (Cor A.15). Real-analytic Hoeffding version of the calculation: `Randomized.majority_error_le` Randomized/ErrorReduction.lean (standalone, not used by the classes); poly-time `Randomized.bpp_error_reduction_polyTime` and PTM form `Randomized.BPP_PTMWith_error_reduction` (U18, Randomized/BPPAmplify.lean) |
| 31 | Remark (p.133) | O(m+k)-coin error reduction (deferred to Ch. 21 §21.2.5) | **not formalized** (deferred by the book to Ch. 21; NOT_FORMALIZED.md); related draft-expander results exist (`Expander.walk_all_mem_le` Expanders/Walks.lean:700), see §4 |
| 32 | §7.4.2 (p.133) | expected-time PTM ⇒ worst-case 100T by Markov truncation | **proved** (U8, U8b) `Turing.FinNDTM.haltProb_le_truncate`, `Turing.FinNDTM.ZDecidesInTime.truncate` (Randomized/ExpectedTime.lean); machine level `Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime` (Randomized/ZPPHostsClasses.lean); `Randomized.BPP_ExpPTM_eq_BPP_PTM` (Randomized/ZPPEquiv.lean); class level: `Randomized.BPP_ExpPTM_eq_BPP_PTM` (ZPPEquiv.lean), `Randomized.RP_ExpPTM_eq_RP_PTM`, `Randomized.coRP_ExpPTM_eq_coRP_PTM` (U18, Randomized/RPExpected.lean) |
| 33 | Note 7.11 (p.134) | Chernoff / statistical estimation: O(log(1/δ)/ε²) samples | **proved** `Randomized.iid_bernoulli_avg_concentration` ErrorReduction.lean; sample-count corollary (U13a) `Randomized.iid_bernoulli_avg_concentration_of_le`, `Randomized.exists_sample_count` (O(log(1/δ)/ε²) samples) |
| 34 | Lemma 7.12 (p.134) | ρ-coin simulated in expected O(1) time if bits of ρ poly-time | **proved** (U8) `Randomized.expTimeLe_rhoCoinRun` (expected ≤ 2 coins), `Randomized.exists_expCost_rhoCoinRun_le` (cost `(i+1)^c` per bit), `Randomized.tendsto_randProb_rhoCoinRun`, `Randomized.randProb_rhoCoinRun_binDigit` (Randomized/Coins.lean); coin-level (divergence recorded) |
| 35 | Lemma 7.13 (p.135) | von Neumann: fair coin from ρ-coins in expected O(1/(ρ(1−ρ))) | **proved** (U8) `Randomized.vonNeumann_heads_eq_tails`, `Randomized.tendsto_vonNeumann_heads`, `Randomized.vonNeumann_expected_pairs` (Randomized/Coins.lean) |
| 36 | §7.5.1 remark (p.135) | BPP ⊆ P/poly + Thm 6.19 ⇒ 3SAT ∉ BPP unless PH collapses | **proved** (U1/U2) `Randomized.InBPP.of_polyTimeReducible`, `Randomized.PH_eq_SigmaP_two_of_inBPP_SAT3` (Randomized/Inclusions.lean), `Randomized.PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM` (Randomized/PTMEquiv.lean) |
| 37 | Thm 7.14 (p.136) | Adleman: BPP ⊆ P/poly | **proved** abstract `Randomized.adleman` Adleman.lean; poly-time `adleman_polyTime` PolyTimeModel.lean; PTM form (U2) `Randomized.BPP_PTM_subset_PPoly` (Randomized/PTMEquiv.lean) |
| 38 | Remark (p.136) | BPP = coBPP | **proved** `Randomized.InBPP.compl` Classes.lean:723 |
| 39 | Thm 7.15 (p.136) | Sipser–Gács: BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ | **proved** abstract `Randomized.sipser_gacs` SipserGacs.lean; poly-time `sipser_gacs_polyTime` PolyTimeModel.lean; PTM form (U2) `Randomized.BPP_PTM_subset_SigmaP_two_inter_PiP_two` (Randomized/PTMEquiv.lean) |
| 40 | Claim 1 (p.137) | |S| ≤ 2^{m−n} ⇒ k shifts never cover {0,1}^m | **proved inline** in `bpp_subset_sigma2` SipserGacs.lean:388 (via `shift_count_lt_two_pow` :174, `exists_notMem_of_card_lt` :362); not a standalone lemma; k is a `polyLen` schedule, not ⌈m/n⌉+1 (book's k fails at small n) |
| 41 | Claim 2 (p.137) | |S| ≥ (1−2^{−n})2^m ⇒ some k shifts cover | **proved inline** in `bpp_subset_sigma2` (via `randProb_xor_right` :111, `randProb_blockCount` Classes.lean:463) |
| 42 | §7.5 / "learned" box (p.135, p.140) | NP = P ⇒ BPP = P | **proved** (U1/U2) `Randomized.inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP` (Randomized/Inclusions.lean), `Randomized.BPP_PTM_eq_P_of_P_eq_NP` (Randomized/PTMEquiv.lean) |
| 43 | §7.5.3 (p.137) | testing the BPTIME (2/3-or-1/3) property of a TM is undecidable | **not formalized** (informal remark; NOT_FORMALIZED.md) |
| 44 | §7.5.3 (p.138) | {⟨M,x,1^t⟩ : Pr[M(x)=1 in t steps] ≥ 2/3} is BPP-hard | **proved** (U13b) `Randomized.probAccept_bppHard` (Randomized/BPPHard.lean) |
| 45 | Def 7.16 (p.138) | B ≤_r C: PTM M with Pr[B(x) = C(M(x))] ≥ 2/3 | **def** (U9) `Randomized.RandReducible` (`≤ᵣ`; printed B/C swap recorded) (Randomized/Reductions.lean) |
| 46 | Remark (p.138) | C ∈ BPP ∧ B ≤_r C ⇒ B ∈ BPP | **proved** (U9) `Randomized.InBPP.of_randReducible` (Randomized/Reductions.lean) |
| 47 | Def 7.17 (p.138) | BP·NP = {L : L ≤_r 3SAT} | **def** (U9) `Randomized.BPNP`, `Randomized.NP_subset_BPNP` (Randomized/Reductions.lean) |
| 48 | §7.7 (p.139) | PTM space S(n): every branch uses O(S(n)) cells | **def** (U10a) `Turing.FinNDTM.UsesSpace` (every branch; Randomized/Space.lean) |
| 49 | Def 7.18 (p.139) | BPL, RL (O(log n)-space PTM, two-/one-sided) | **def** (U10a) `Turing.FinNDTM.BPDecidesInSpace`, `Turing.FinNDTM.RDecidesInSpace`, `Randomized.BPSPACE`, `Randomized.RSPACE`, `Randomized.BPL`, `Randomized.RL` (Randomized/Space.lean) |
| 50 | Remark (p.139) | error reduction in log space | **proved** (U10a, U16) constant repetitions `Randomized.mem_RSPACE_of_pos`, `Randomized.mem_BPSPACE_of_advantage` (Randomized/Space.lean; machine `Randomized.Amplify.amp`, Randomized/SpaceAmplify*.lean); error `2^{-n^d}`: `Randomized.BPL_error_reduction`, `Randomized.RL_error_reduction` (Randomized/SpaceAmplifyPoly.lean) |
| 51 | Remark (p.139) | RL ⊆ NL, hence RL ⊆ P | **proved** (U10a) `Randomized.RL_subset_NL`, `Randomized.RL_subset_P`, `Randomized.RL_subset_BPL` (Randomized/Space.lean) |
| 52 | §7.7 (p.139) | UPATH (PATH on undirected graphs) | **def** (U10d) `Complexity.UPATH`, `Complexity.mem_UPATH_iff` (Randomized/UPath.lean) |
| 53 | Thm 7.19 (p.139) | UPATH ∈ RL (random walk of length 100n⁴) | **proved** (U10d) `Complexity.UPATH_mem_RL` (Randomized/UPathRL.lean), via the probabilistic NARM transfer `Complexity.LogProg.narm_mem_RL` (SpaceComplexity/Machines/NARMLogspace.lean; semantics `PSem` in NARMPSem.lean) and `Complexity.LogProg.narm_randProb` (SpaceComplexity/Machines/NARMProb.lean) |
| 54 | §7.7 (p.139) | connected s,t ⇒ expected hitting time ≤ 10n⁴, so Pr[accept] ≥ 3/4 | **proved** (U10b) `Randomized.RegularMultigraph.hitTime_le_ten_mul_pow_four`, `Randomized.RegularMultigraph.three_quarters_le_hitProb` (Randomized/RandomWalkHitting.lean); padded walk `Randomized.three_quarters_le_randProb_padWalk` (Randomized/RandomWalkPad.lean) |
| 55 | §7.7 (p.139, cited) | BPL ⊆ SPACE(log^{3/2} n) | **not formalized** (cited only; NOT_FORMALIZED.md) |
| 56 | Footnote 7 (p.139, cited) | cover time ≤ (4/27)n³ + o(n³), tight (lollipop) | **not formalized** (cited only; NOT_FORMALIZED.md) |

"What have we learned" box (p.140): its formal content is rows 3, 5, 27–30, 37–39, 42.

**Body totals (56 rows), after Phase 2 (U12–U16):** every row is proved or defined except 31 (deferred by the book to Ch. 21), 43 (informal aside, infeasible without effective machine codes), 55 and 56 (cited research results) — all four in NOT_FORMALIZED.md. Missing 0, sorried 0.

## 2. Exercises (pp.141–142)

| Ex | Content | Status |
|---|---|---|
| 7.1 | uniform sample from [N] with ≤ δ failure, poly(log N log 1/δ) | **proved** (U13a) `Randomized.uniformSample_spec` (Randomized/UniformSample.lean) |
| 7.2 | Σ_{i≥1} i^c/2^i bounded | **proved** (U8, U13a) general form `Randomized.exists_sum_rpow_div_two_pow_le` (Randomized/Coins.lean); form used by Lemma 7.12 `Randomized.exists_expCost_rhoCoinRun_le` |
| 7.3 | a^n mod p in poly time | **proved** (U4) `Complexity.BinArith.polyTimeComputable_powMod` (ClassP/BinaryArith/ModPow.lean) |
| 7.4 | RP error reduction n^{−c} → 1−2^{−n^d} | **proved** (U1/U2) `Randomized.rp_error_reduction`, `Randomized.rp_error_reduction_polyTime`, `Randomized.inRPWeak_iff_inRP` (Randomized/Inclusions.lean); PTM form `Randomized.RP_PTMWith_error_reduction` (Randomized/PTMEquiv.lean) |
| 7.5 | uncomputable ρ-coin decides undecidable language | **proved** (U13a) `Randomized.exists_biasedBPP_not_computablePred` (Randomized/BiasedCoinHalting.lean; ρ-coin classes in Randomized/BiasedCoin.lean) |
| 7.6(a) | ZPP ⇔ poly-time {0,1,?} machine, Pr[?] ≤ 1/2 | **proved** (U8, U8b) `Turing.FinNDTM.ZDecidesInTime.abort`, `Turing.FinNDTM.AbortDecidesInTime.restart` (Randomized/ExpectedTime.lean); `Randomized.ZPPAbort_PTM_eq_ZPP_PTM`, `Randomized.mem_ZPP_PTM_iff` (Randomized/ZPPHostsClasses.lean) |
| 7.6(b) | Thm 7.8 | **proved** (row 27); for Def 7.7's ZPP `Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` (Randomized/ZPPHostsClasses.lean) |
| 7.7 | BP·NP ⊆ NP/poly | **proved** (U9) `Language.InNPPoly`, `Randomized.BPNP_subset_NPPoly` (Randomized/NPPoly.lean) |
| 7.8 | 3SAT ∈ BP·NP ⇒ PH = Σ₃ᵖ | **proved** (U9, U12) first step `Randomized.coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP` (Randomized/NPPoly.lean); collapse `Randomized.PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP` via Yap's theorem `Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly` (Randomized/Yap.lean) |
| 7.9 | BPL ⊆ P | **proved** (U14) `Randomized.BPL_subset_P` (Randomized/BPLInP.lean), via `Randomized.BPLInP.haltsWithin_of_codes`, `Randomized.BPLInP.dpVal_init` (Randomized/BPLInPCount.lean) |
| 7.10 | random walk fails on digraphs (Ω(2ⁿ) hitting time) | **proved** (U13b) `Randomized.hitProb_chainDigraph_le`, `Randomized.hitTime_chainDigraph_ge` (Randomized/DirectedWalk.lean) |
| 7.11(a) | uniform distribution stationary on regular G | **proved** (U10b) `Randomized.RegularMultigraph.uniform_stationary` (Randomized/RandomWalk.lean) |
| 7.11(b) | Δ(p^k) contraction for connected non-bipartite G; uniqueness; visit frequency | **proved** (U15) `Randomized.RegularMultigraph.exists_uniformExcess_walkDist_le`, `uniformExcess_walkDist_two_mul_le` (k = 2n for D ≤ n⁵), `isStationary_iff_eq_uniform` (ℝ version `isStationary_real_iff_eq_uniform`, U19), `exists_le_expVisits` (Randomized/RandomWalkMixing.lean; double cover in RandomWalkCover.lean) |
| 7.11(c) | return time E_u ≤ 10n | **proved** (U10b) `Randomized.RegularMultigraph.returnTime_le_card` (Randomized/RandomWalkHitting.lean) |
| 7.11(d) | E_{u,v} ≤ 100kn²; 1000n³ walk misses t w.p. ≤ 1/10 | **proved** (U19) `Randomized.RegularMultigraph.hitTime_le_hundred_mul`, `Randomized.RegularMultigraph.missProb_thousand_mul_pow_three_le` (Randomized/RandomWalkHitting.lean), under degree D ≤ 100n (recorded divergence; simple graphs with loops and the padded UPATH graphs satisfy it); helpers `hitTime_le_add` (triangle inequality), `hitTime_le_length_mul`. The cruder `hitTime_le`, `one_sub_le_hitProb` serve the p.139 route (row 54). |
| 7.11(e) | self-loop regularization | **proved** (U10b, U15) padding `Randomized.padGraph` (Randomized/RandomWalkPad.lean); transfer `Randomized.half_le_hitProb_padGraph`, `Randomized.half_le_hitProb_padDegree` (Randomized/RandomWalkMixingPad.lean) |

**Exercise totals (16 items), after Phase 2 (U12–U16):** proved 16 (7.1, 7.2, 7.3, 7.4, 7.5, 7.6(a), 7.6(b), 7.7, 7.8, 7.9, 7.10, 7.11(a), (b), (c), (d), (e)); partial 0, not formalized 0, missing 0, sorried 0. (Original survey: proved 1, partial 1, missing 14.)

## 3. Machine-model gap

*(Pre-campaign analysis, kept for the record; the gap is closed by `Randomized/PTM.lean`,
`Randomized/PTMEquiv.lean`, `Randomized/Space.lean` and `SpaceComplexity/Machines/NARMProb.lean`.)*

**No genuine PTM model exists.** Grep for `PTM`, `BPTIME`, `RTIME`, `ZTIME`, `BPL`, `RL`, `UPATH`
over `TCSlib/` finds no such definition (only the certificate-form `InBPP`/`InRP`/`InZPP` names and docstrings). All four classes are certificate-form predicates over
`VerifierModel` (Classes.lean:259–310), deliberately (plan `AroraBarakChapter7Plan.md` §1 defers
"Tier C — PTMs proper, BPL/RL, UPATH ∈ RL").

**`Turing.FinNDTM` as the PTM of Def 7.1.** `Turing.NDTM` (TuringMachine/Nondeterministic.lean:103)
has `tr : Bool → …` (δ₀ = `tr false`, δ₁ = `tr true`), `runWith` over a choice word, one bit per step
(:133), halting absorbing under every choice (`runWith_of_halt` :180), and all-branch halting
`HaltsWithin x t` = every length-t word halts (:192) — exactly "halts within T(|x|) regardless of its
random choices". The bundled `FinNDTM` (:219) is what `NTIME` uses. It can serve directly; only the
*reading* changes (fraction of branches vs. existence, as the book says on p.125). Suggested statement:

```
def FinNDTM.BPDecidesInTime (N : FinNDTM Bool) (L) (T : ℕ → ℕ) : Prop :=
  ∀ x, N.tm.HaltsWithin x (T x.length) ∧
    2/3 ≤ Randomized.randProb (T x.length) fun w =>
      (N.tm.runWith w (N.tm.initCfg x)).output = [MultiTapeTM.indicator L x]
def BPTIME T := {L | ∃ c N, N.BPDecidesInTime L (fun n => c * T n)}
def BPP' := ⋃ c, BPTIME (fun n => n ^ c + 1)      -- same `+1` padding as NTIME/P
```

Output-tape acceptance mirrors `FinNDTM.AcceptsWithin` (ClassNP/NTIME.lean:93). T-invariance past the
halting time follows from `runWith_of_halt` + `randProb_take` (Classes.lean:232) — no new probability
needed. `RTIME`/`RP` analogously (acceptance on members ≥ 2/3, every branch on non-members outputs ≠
`[true]`); then RP ⊆ NTIME-poly ⊆ NP is immediate by `NP_eq_iUnion_NTIME`
(ClassNP/Nondeterminism.lean:2339). Def 7.7 (expected time) is **not** expressible over this model:
all-branch `HaltsWithin` forbids unbounded runs; a stream/`PMF` semantics would be needed (or keep the
abort form and prove Ex 7.6(a) via §7.4.2 truncation).

**Equivalence Def 7.2 ≡ Def 7.3 (the book's "alternative definition").** Nothing proves it, but
Theorem 2.6's machinery is the template:
* 7.2 ⇒ 7.3: the verifier "run N on x with choice word u" is the private `choiceVerifier`
  (Nondeterminism.lean:132), with `cont_choiceVerifier_mem_P` (:947) putting it in `P`. The coin→
  certificate map is the identity on words, so it is measure-preserving for free. Remaining work: export
  the private lemmas; convert the `x ++ u` (split-search) encoding to `pairEncode x u` (PolyTimePairing
  infra); pad `c·(n^k+1)` to a `polyLen` length (`choiceBudget_le` TuringMachine/ChoiceWords.lean:92,
  `randProb_take`); supply the `some false` set (complement — `polyTimeModel_closedUnderNot`
  PolyTimeModel.lean:346 shows how).
* 7.3 ⇒ 7.2: the reverse compiler `b2_compile` (Nondeterminism.lean:2233) guesses certificate bits at
  scheduler emissions (`contGuessTM` :1125) after a startup phase, then runs the decider. Its contract
  `b2_host_contract` (:2143) is **existential only** (∀ branch ∃ certificate; ∀ certificate ∃ branch).
  For BPP one needs the quantitative version: the branch→certificate map is a fixed coordinate
  projection (positions determined by |x|), every other bit ignored, so the uniform measure pushes
  forward to uniform. No `randProb` lemma for coordinate-subset projections exists (only prefixes
  `randProb_take` and block splits `randProb_split` :198). This is the main new proof obligation.
* P ⊆ BPP over FinNDTM is free from `MultiTapeTM.toNDTM_runWith` (Nondeterministic.lean:253); note the
  related slice lemma `NDTM.runWith_eq_fixChoice_runFrom` (:285) is **sorried** (:290), as is
  `spaceUsedWith_eq_fixChoice_spaceUsed` (TuringMachine/NondeterministicSpace.lean:182).

**BPL / RL.** `NSPACE` (SpaceComplexity/NSPACE.lean:95; `DecidesInSpace` :78) is built on the same
`FinNDTM`: choice bits come from the external word, one per step, never stored on a tape; only work
tapes count (`spaceUsedWith` NondeterministicSpace.lean:70). So the model **is read-once** in AB's sense
(re-reading a coin requires writing it to a work tape, which is charged). BPL/RL can be stated by
replacing the acceptance clause of `DecidesInSpace` with `randProb T` thresholds (T existential per
input, invariant past halting by `runWith_of_halt`/`spaceUsedWith_append_of_halt` :117); all-branch
halting with log space bounds running time by configuration counting (SpaceComplexity/ConfigCount.lean).
RL ⊆ NL is then immediate (Pr ≥ 2/3 ⇒ ∃ accepting branch) and RL ⊆ P follows from `NL_subset_P`.
Caveat for algorithms: the NARM layer (`NIns.choose` SpaceComplexity/Machines/NARM.lean:61, compiled by
`ncompileFinNDTM` Machines/NARMCompile.lean:197, bridged by `narm_decides` Machines/NARMProof.lean:195)
only transfers existential acceptance (`NAns`/`NHalts`); a probabilistic transfer (one physical coin per
`choose`) is unproved, and UPATH's uniform-neighbour step needs Ex 7.1-style sampling (truncated, since
branches must all halt) or a power-of-two-degree normalization.

## 4. The intentional sorry (expander Chernoff)

`Expander.walk_visits_concentration`, Expanders/Chernoff.lean:70, body `sorry` at :77 — web-draft
"Theorem 7.41" (sign-corrected 2·exp(−(1−λ)δ²(k+1)/60); proof omitted in the draft, plan cites Gillman
1998). It is the only `sorry` under `Randomized/` and `Expanders/`. **It is not in printed Chapter 7**:
the printed chapter has no expander material at all; p.133 ("Randomness-efficient repetitions") only
announces the O(m+k)-coin transformation and defers it to Chapter 21, §21.2.5, and p.141 defers the
random-walk analysis to Ch. 21. The same holds for the proved draft items `Expanders/Basic.lean`
(λ(G), draft Def 7.25), `Mixing.lean` (`inner_indicator_mulVec_le` :84, draft Lem 7.37), `Walks.lean`
(`exists_decomposition` :101, draft Lem 7.40; `walk_all_mem_le` :700, draft Thm 7.38). Likewise the
"Cor 7.11 erratum" in ErrorReduction.lean concerns the draft's normalized form; printed Thm 7.10 uses
the multiplicative Cor A.15 form `Pr[|ΣXᵢ − pk| > δpk] < e^{−δ²pk/4}`. These belong to a printed-Ch. 21
campaign; they are neither needed nor sufficient for any printed ch. 7 item except as optional
infrastructure for Ex 7.11.

## Items added after completeness-grader round 1

| # | Book | Item | Status |
|---|---|---|---|
| G1 | §7.2.3 (p.129) | `∏(1+xᵢ)` has a circuit with 2n operations but 2ⁿ monomials | **proved** (U20) `Randomized.AlgCircuit.countP_isOp_prodOnePlus`, `Randomized.AlgCircuit.toMvPolynomial_prodOnePlus`, `Randomized.AlgCircuit.card_support_toMvPolynomial_prodOnePlus` (Randomized/AlgCircuitExample.lean) |
| G2 | §7.5 (p.135) | if BPP = P then BPP ⊊ DTIME(n^{log n}) | **proved** (U20) `Randomized.P_ssubset_DTIME_pow_log` (Randomized/QuasiPolyHierarchy.lean), `Randomized.BPP_PTM_ssubset_DTIME_pow_log_of_eq_P` (Randomized/BPPEqP.lean) |
| G3 | §7.5.3 (p.138) | if BPP = P then BPP has a complete problem | **proved** (U20) `Randomized.exists_BPPHard_mem_BPP_PTM_of_eq_P`, `polyTimeReducible_of_mem_P` (Randomized/BPPEqP.lean) |
| G4 | Chapter notes (p.141) | BP·P = BPP | **proved** (U18) `Randomized.BPdot_P_eq_BPP_PTM`, `Randomized.BPdot_P_eq_BPP`, consistency `Randomized.BPdot_NP_eq_BPNP` (Randomized/BPOperator.lean) |
| G5 | §7.4.1 (p.132) | any constant > 1/2 gives BPP | **proved** (U18) `Randomized.BPP_PTMWith_const_eq_BPP_PTM` (Randomized/BPPAmplify.lean) |
