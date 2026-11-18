# io-sprg: duplication sweep r2 (Phase A)

Static sweep (no Lean run) of TCSlib and Mathlib for anything the sPRG Phase A job might otherwise
re-prove, refreshed for r2. **Base**: `foundations/subexp` head
`cbce64d1c135c710b7c036968ed9d4f21414aa72` (draft PR #374). Its `TCSlib/` tree differs from r1's
sweep commit `0fec25892d5aea3acde4908d94451f24b3c23b79` only by
`Foundations/Subexponential.lean` (+300) and `Foundations.lean` (+3)
(`git diff --stat 0fec25892 cbce64d1c -- TCSlib`), so every r1 file:line below is valid at the
base; the rows new in r2 were read at `cbce64d1` with `git show`/`git grep` (spot-checked:
`Games/Advantage.lean:63, 72, 111, 122`, `Games/Hopping.lean:127`, `Games/Probability.lean:393,
409`, `Lamport/Averaging.lean:114, 129`, `LWE/Assumption.lean:65, 117, 136, 141`,
`LWE/Encoding.lean:42–72`, `Foundations/Negligible.lean:74, 86, 153, 169, 237`,
`Asymptotic/ReductionSupport.lean:200, 267`, `Asymptotic/UniversalLemmas.lean:79, 125`,
`Encoding/Modular.lean:51, 65, 79, 101`). Mathlib as pinned by `lake-manifest.json`, read in
`.lake/packages/mathlib`. Paths without a root are under `TCSlib/Cryptography/`. If `<BASE>` is a
later stacked head, re-check the line numbers there. The brief carries this file as the
**must-reuse list**; r1's `duplication-sweep.md` is superseded.

**Rule (binding).** Any undisclosed re-proof of a public TCSlib or Mathlib lemma, including an
inline re-derivation inside a proof, is a **major**. Before every helper, search (name search in
TCSlib and Mathlib sources, `exact?`/`apply?` on the statement in a scratch probe, grep for the
conclusion's shape) and record the search in REPORT.md § *Overlap and reuse*. A helper with no
public equivalent is allowed when disclosed with its search.

Legend: **MR** must reuse (do not restate or re-derive); **R** reuse if the route needs it;
**NR** nearest relative only (cite in the disclosure, do not copy); **X** do not use (reason given);
**B** Phase B only (appendix; not used by this job).

**What changed from r1.** §C now names the Foundations/Subexponential API with its real names and
lines (MR). §D is new: adversaries, realisation, uniform efficiency forms. §E is new: encodings with
explicit equivalences (C13). The machine-building rows of r1 §D (mod-p arithmetic on encodings,
`matVecPoly`, `BinArith`, the H16 loop, `NUPPT.wrap` hop machines) moved to the **Phase B
appendix**. r1 §E–§G are now §F–§H.

Searches with **no hit** (so the job may add them, disclosed): any LPN definition or game (every
branch, `git grep -i 'LPN'`); any structured-seed, local or Goldreich PRG; `weightedTotalDegree`
add/mul/sum/prod/C/X closure lemmas in Mathlib; a `ProbComp` union bound over a `Finset` of events;
a public C(n, k) ≤ (e n / k)^k; balls-in-bins tails for a uniform random function; a constructive
sparse matrix factorization; **a generic "machine realises a function on encoded challenges"
predicate** (`Lamport/Realization.lean` is a specific T1 realisation, NR; `git grep -n Realiz` finds
nothing generic); **a string encoding of `MvPolynomial` or of a polynomial term list**
(`git grep -i 'encodeMvPoly\|encodePoly'`: none); **a prime-parameter structure** (κ-bit prime with
proofs) in `Cryptography/` (the pairing generators carry their own order, NR).

## A. Assumptions and their experiments (LPN is an LWE family; r1 §A, three rows revised, one added)

| Name | File:line | Use |
|---|---|---|
| `LWE.Noise` (finite uniform-seed scalar law) | `TCSlib/Cryptography/LWE/Noise.lean:41` | **MR**: `lpnNoise` is an `LWE.Noise` |
| `LWE.Parameters`, `noisyValues`, `noisyValues_apply`, `LWE.sample`, `sample_fst/_snd` | `LWE/Basic.lean:44, 59, 67, 101, 109, 116` | **MR** (the LPN sample map is `LWE.sample` with `lpnNoise`) |
| `LWE.Family`, `Family.advantageAt` (+`_eq`), `DLWEAssumption`, `dlweAssumption_iff` | `LWE/Assumption.lean:65, 117, 136, 141` | **MR**: `LPNFamily.toLWE`, `LPNFamily.Assumption := DLWEAssumption …` |
| `Family.inputBitsBound`, `Family.encodeChallenge_length_le` | `LWE/Assumption.lean:88, 102` | **MR** where a length bound of `lpnEnc` is needed (M6) |
| `LWE.decisionAdvantage` (+`_eq`) | `LWE/Experiments.lean:44` | **MR** |
| `LWE.encodeChallenge` (+`_eq`, `_length`, `_injective`) | `LWE/Encoding.lean:42, 49, 60, 72` | **MR**: `lpnEnc` is exactly this string (§E); Phase A never parses it |
| `Family.withSamples`, `multiMessageSamples` | `LWE/SampleSchedules.lean:64, 82` | R (only if a schedule is rewritten) |
| `bitNoise`, `centeredNoise`, `sampleFromBits`, `uniformFromBits` | `LWE/BitNoise.lean:40, 78`; `LWE/Sampling.lean:48, 116` | **X**: dyadic samplers; samplers are out of scope (S2) |
| `Pairing.BilinearGen.dbdhGame` (uniform ℤ_p exponents as `ProbComp.sample (ZMod p)`) | `Pairing/Assumptions.lean:225` | NR: the precedent for exact ℤ_p laws in a game |
| `Candidates.ArithmeticFP` | `Candidates/Arithmetic.lean:314` | **X** (Q-S6 superseded: no assumed arithmetic; Phase A has no machines) |
| `Complexity.BinArith` prime search (`ClassP/BinaryArith/PrimeFind.lean`) | `TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean` | **X**: p is an input (S12); no definition computes a prime (it covers only O(log n)-bit primes from unary input anyway) |

## B. Games, probability, hybrids (unchanged from r1)

| Name | File:line | Use |
|---|---|---|
| `ProbComp`, `sample`, `expect`, `prob` | `Games/Probability.lean:78, 93, 107, 113` | **MR** |
| `expect_bind`, `expect_map`, `expect_sample`, `expect_add`, `expect_const_mul`, `expect_const`, `expect_sum`, `expect_mono`, `expect_nonneg`, `expect_sub` | `Games/Probability.lean:128, 135, 147, 158, 165, 174, 184, 193, 202, 340` | **MR** |
| `prob_eq_expect`, `prob_bind`, `prob_mono`, `prob_congr`, `prob_or_le`, `prob_not`, `prob_le_one` | `Games/Probability.lean:208, 224, 244, 254, 259, 267, 236` | **MR** (`prob_or_le` is the two-event union bound) |
| `expect_sample_equiv`, `expect_sample_comm`, `expect_expect_sample`, `expect_sample_update`, `expect_sample_coord` | `Games/Probability.lean:304, 313, 326, 355, 383` | **MR** (Fubini, reordering, coordinate updates) |
| `abs_expect_sub_le`, `abs_expect_sub_le_expect` | `Games/Probability.lean:393, 409` | **MR** (the averaging step of §4.8) |
| `ProbComp.dist` (+`dist_apply`) | `Games/Probability.lean:280, 291` | R |
| `OracleComp.AllOutputs`, `allOutputs_pure/_query`, `AllOutputs.mono`, `AllOutputs.bind` | `Games/OracleComp.lean:292, 297, 303, 316, 324` | **MR** (support statements: `HasComplexity`, `G4_eval_eq`) |
| `accept`, `advantage` (+`_eq`), `advantage_comm`, `advantage_triangle`, `advantage_le_one` | `Games/Advantage.lean:63, 72, 89, 103, 96` | **MR** |
| `advantage_hybrid`, `exists_advantage_hybrid_gap` | `Games/Advantage.lean:111, 122` | **MR** (Lemma 4.2's chain; the machine's hop choice) |
| `abs_prob_sub_le_of_agree` | `Games/Hopping.lean:127` | **MR**: H₀ ≈ H₁ and H₂ ≈ H₃ (differ only when err = 1) |
| `prob_split`, `expect_congr_of_allOutputs`, `prob_eq_zero_of_allOutputs` | `Games/Hopping.lean:77, 101, 116` | R |
| `Bridge.prob_sample_eq_uprob`, `expect_sample_eq_uexp`, `expect_sample_pair`, `prob_sample_pair` | `Games/Bridges/Experiments.lean:66, 74, 80, 89` | **MR** (ProbComp ↔ `uprob`) |
| `Bridge.acceptGame` (+`_eq`), `acceptProb_eq`, `distAdv_eq` | `Games/Bridges/Experiments.lean:114, 121, 128, 139` | **MR**: the LWE advantage inside a ProbComp proof |
| `uprob`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le` (finite union bound), `uprob_prod`, `uprob_comp_equiv`, `uprob_not` | `Foundations/Probability.lean:59, 120, 127, 137, 153, 165, 109` | **MR** (route union bounds through `uprob`; no new `ProbComp` union bound without disclosure) |
| `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `half_le_uprob_good` | `Foundations/Probability.lean:218, 230, 190` | R |
| Markov: `LamportReduction.expect_favourable_of_success` (`b * prob c P ≤ expect c q`) | `Authentication/Signatures/Lamport/Averaging.lean:129` | **MR** for Cond₁; if `<BASE>` already has Stage 2's `ProbComp.mul_prob_le_expect` (`Games/Probability.lean`, S2-DL-16), use that instead |
| averaging: `LamportReduction.exists_expect_sample_le` | `…/Lamport/Averaging.lean:114` | **MR** (fix the best ω*) |
| `multicopyHybrid`, `multicopyRed`, `acceptProb_multicopyRed_left` [Gar26, Lemma 3.3] | `Pseudorandom/Indistinguishability.lean:198, 211, 247` | NR: independent copies; Lemma 4.2's instances share A, so it does not apply |
| `StatClose`, `distAdv_le_of_statClose`, `rejectionSample`, `statClose_getD_of_uniform_of_some`, `one_sub_inv_pow_le_half` | `Asymptotic/Sampling.lean:126, 278, 732, 913, 828` | **X** for sampling (S2: no approximate samplers, no sampler bridge); `one_sub_inv_pow_le_half` R |
| `InformationTheory.statDist`, `statDist_triangle`, `FinDist`, `FinDist.map`, `distAdv_le_statDist`, `abs_sum_sub_le_statDist` | `InformationTheory/StatisticalDistance.lean:46, 60`; `InformationTheory/FinDist.lean:52, 105`; `Foundations/Experiments.lean:173, 152` | R (not needed on the agree-lemma route; never re-derive) |

## C. Negligibility and subexponential smallness

| Name | File:line | Use |
|---|---|---|
| `SubexpSmall c μ` (eventually `\|μ n\| ≤ 2^(−n^c)`), `subexpSmall_iff`, `subexpSmall_iff_eventually` | `Foundations/Subexponential.lean:71, 76, 81` (namespace `TCSlib.Cryptography`; at `<BASE>`) | **MR**: every subexponential statement; **no subexponential notion of the job's own** (a one-line wrapper `SPRG.SubexpSecure := SubexpHard S.adv` with `_iff` is the only allowed form) |
| `SubexpHard adv := ∃ c > 0, ∀ D, SubexpSmall c (adv D)` (any adversary type `α`; instantiate `α := NUPPT`), `subexpHard_iff` | `Foundations/Subexponential.lean:274, 279` | **MR**: the hypotheses and conclusion of `jls_subexpSecure`, `theorem41_subexp`, `exists_sprg_subexp` |
| `eventually_const_mul_rpow_mul_two_rpow_neg_le` (eventually `A n^s 2^(−n^c) ≤ 2^(−n^c')`, `c' < c`, `0 < c`) | `:132` | **MR** for any direct estimate of an explicit-slack term |
| `SubexpSmall.mono`, `.mono_exponent` | `:152, 163` | **MR** (domination by the core inequality; common exponent) |
| `SubexpSmall.add`, `.const_mul`, `.mul_pow` (each to any `c' < c`, needs `0 < c`) | `:176, 190, 204` | **MR** (the `2κ` factor and the sum of three terms) |
| `SubexpSmall.negligible`, `SubexpHard.negligible` | `:218, 286` | R (the negligible corollary goes through `Negligible` directly) |
| `SubexpSmall.comp_of_rpow_le` (re-index by `ℓ n ≥ n^a`: exponent `a·c`), `SubexpHard.comp_of_rpow_le` | `:238, 293` | **MR**: the LPN term along `ℓ κ = κ^E` (`a = E`), the PRG term along `n κ = κ^{E·D}` (`a = E·D`); use the `SubexpSmall` form, since the realisers depend on `A` |
| `subexpSmall_zero`, `subexpSmall_two_pow_neg` (`2^(−n)` is `SubexpSmall 1`) | `:253, 258` | **MR** (the `2·errProb` slack via `claim42`) |
| `Randomness.subexpBound` (⌈2^(n^ε)⌉ as a time bound) | `TCSlib/Randomness/Derandomization.lean:74` | **X** (running-time bound; subexponential-time adversaries out of scope) |
| `Negligible`, `negligible_iff`, `.mono`, `.add`, `.mul`, `.mul_pow`, `.const_mul`, `negligible_two_pow_neg`, `negligible_zero`, `.comp_of_le` | `Foundations/Negligible.lean:57, 62, 74, 86, 110, 126, 143, 153, 169, 237` | **MR** (`comp_of_le` moves the LPN term along `ℓ κ ≥ κ`, the PRG term along `n κ ≥ κ`) |
| `Negligible.polyExpr_mul` | `Asymptotic/ReductionSupport.lean:267` | **MR** (the `2κ` factor) |

## D. Adversaries, realisation, uniform efficiency forms (Phase A)

| Name | File:line | Use |
|---|---|---|
| `Complexity.NUPPT` (fields `M`, `coins`, `adv`, `advice`, `halts`), `advInput` (`⟨1^n, y⟩`) | `TCSlib/Complexity/Randomized/PPT.lean:137, 210` | **MR** |
| `NUPPT.runAt`, `runAtL`, `runAtL_eq`, `runAt_eq`, `Coins`, `coinLen` | `PPT.lean:235, 240, 245, 249, 223, 168` | **MR** (the reduction functions call `A.runAtL`; `RealizesOn` is stated with `runAtL`) |
| `NUPPT.coinsEquivPoly` (+`_ofFn`) | `PPT.lean:274, 280` | **MR** (a realiser's coins as `A.coins.subst .var` bits) |
| `NUPPT.Uniform`, `uniform_iff`, `Computes`, `computes_iff`, `ofPolyTimeUniform`, `runAtL_ofPolyTimeUniform`, `exists_uniform_computes` | `PPT.lean:301, 305, 328, 332, 406, 437, 448` | **MR** wherever an honest-algorithm efficiency form is not `PolyTimeComputable` itself: it is `A.Uniform ∧ A.Computes f` (S11), **never a bare `∃ A : NUPPT, A.Computes f`** (the docstring of `Computes`, `:309–327`, says why) |
| `NUPPT.Computes.polyTimeComputable` (needs `A.Uniform`) | `TCSlib/Complexity/Randomized/Closure.lean:458` | R (converse of the above) |
| `PolyTimeComputable` | `TCSlib/Complexity/ClassNP/PolyTime.lean:73` | **MR**: the form of every efficiency target (§4.10) |
| `NUPPT.distinguisherL` (+`_eq`), `NUPPT.computes_iff_uprob` | `Asymptotic/Adversary.lean:381, 386, 470` | **MR** (verdicts; the realiser's verdict lemma) |
| `NUPPT.exists_reparam_pre_post` (`B.runAtL m y r = post (A.runAtL (φ m) (pre ⟨β m, y⟩) (r.take (A.coinLen (φ m))))`, `B.coins = A.coins.subst p`) | `Asymptotic/UniversalLemmas.lean:79` | **MR** for `realizable_of_targets` (Q-S11 A), with `post := id`; the reduction functions are written in its conclusion shape (§4.8). Phase A uses it only with `PolyTimeComputable` **hypotheses** (the targets), never proving them |
| `NUPPT.exists_reparam_pre_post_adv` | `Asymptotic/UniversalLemmas.lean:125` | R (only if a post-processing must read the advice; the r2 shape does not) |
| `PolyExpr` (`.var`, `.subst`, `eval_subst`, `eval_mono`) | `TCSlib/Complexity/Randomized/PolyExpr.lean:73, 99, 134, 142` | **MR** (coin polynomial `A.coins.subst .var`; advice and encoding length bounds) |
| `acceptProb_coins_equiv`, `prgAdv_coins_equiv`, `takeLen_poly`, `dropLen_poly`, `finCastEquiv` | `Asymptotic/ReductionSupport.lean:221, 229, 248, 256, 79` | R (uniform coin prefix, `r.take`) |
| `Signatures.Lamport.Realization` (`exists_realization_machine`) | `Authentication/Signatures/Lamport/Realization.lean:91` | NR (a specific realisation; not the generic predicate) |
| The shared realisation file (Q-S9 A: `Asymptotic/Realization.lean`, `NUPPT.RealizesOn`) | only if present at `<BASE>` | **MR** when present; otherwise the job writes `StructuredSeed/Realization.lean` (design-r2 §4.8) |
| `Games.NUPPT.toComp`, `MachineCodec` | `Games/Machines.lean:233, 79` | **X** (oracle machines; no oracle here) |

## E. Encodings and explicit equivalences (C12, C13)

| Name | File:line | Use |
|---|---|---|
| `Encoding.Modular.encodeVector`, `encodeMatrix` (+`_length`, `_injective`) | `Encoding/Modular.lean:51, 65, 79, 89, 101, 126` | **MR**: public seed, private seed, `A`, the reductions' advice residues |
| `LWE.encodeChallenge` (+`_eq`, `_length`, `_injective`); `Family.encodeChallenge_length_le` | `LWE/Encoding.lean:42, 49, 60, 72`; `LWE/Assumption.lean:102` | **MR**: `lpnEnc` is exactly this string |
| `Candidates.natToBits`, `natToList`, `listToNat_natToList`; `bitsToNat` | `Candidates/Arithmetic.lean:97, 100, 143`; `Asymptotic/Sampling.lean:393` | **MR** (`PrimeParam.enc`, `SPRG.encPP`, fixed-width indices) |
| `pairEncode`, `length_pairEncode`; `pairFstD`, `pairSndD` | `TCSlib/Complexity/TuringMachine/Encoding.lean:136`; `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:207, 210` | **MR** (`pairEncode` for every layout); the decoders R (Phase A needs no parsing) |
| `BoolCircuit.encodeList` (element encoder, `1`-prefixed, `0`-terminated) | `TCSlib/Complexity/CircuitComplexity/Uniform.lean:91` | R for `encTerms` (a list of terms); if not used, say why |
| `PrivateKey.encodeList` (nested pairs of strings) | `Encryption/PrivateKey/EnsembleSecurity.lean:103` | NR |
| `finSumFinEquiv`, `finProdFinEquiv` | `Mathlib/Logic/Equiv/Fin/Basic.lean:219, 325` | **MR** (C13: `privEquiv`, public-seed layout `Fin (κ * n + 1)`) |
| `finFunctionFinEquiv` (`(Fin n → Fin m) ≃ Fin (m ^ n)`) | `Mathlib/Algebra/BigOperators/Fin.lean:555` | **MR** (the tensor index `Fin D → Fin (ℓ + 1)`) |
| `finCongr`, `Equiv.sumCongr`, `Equiv.prodCongr` | Mathlib `Logic/Equiv` | **MR** (casts between `Fin (L ^ D)` and `Fin (n κ)`) |
| `Fintype.equivFin`, `Finset.toList`, `Classical.choose` inside an encoding | Mathlib | **X** in any encoding, pre-processing map or target (C13: not a fixed function of the data) |

## F. Polynomials, multilinearity, tensor powers (Mathlib unless stated; r1 §E)

| Name | File:line | Use |
|---|---|---|
| `MvPolynomial.restrictDegree`, `mem_restrictDegree`, `mem_restrictDegree_iff_sup` | `Mathlib/RingTheory/MvPolynomial/Basic.lean:101, 111, 116` | **MR** (multilinear = `restrictDegree 1`) |
| `totalDegree_add`, `totalDegree_mul`, `totalDegree_finset_prod`, `totalDegree_finset_sum`, `totalDegree_C`, `totalDegree_X`, `totalDegree_rename_le` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:373, 403, 441, 445, 356, 368, 494` | **MR** |
| `vars`, `vars_mul`, `vars_add_subset` | `Mathlib/Algebra/MvPolynomial/Variables.lean:65, 114, 100` | **MR** (BAD via `vars`) |
| `eval₂Hom_congr'`, `eval₂_congr` | `Variables.lean:253`; `Mathlib/Algebra/MvPolynomial/Eval.lean:204` | **MR** (good outputs: evaluation agrees off the variables) |
| `eval_eq`, `eval_monomial`, `eval_map`, `eval₂_eq_eval_map`, `eval_rename` | `Eval.lean:237, 245, 417, 339`; `Mathlib/Algebra/MvPolynomial/Rename.lean:188` | **MR** |
| `weightedTotalDegree`, `le_weightedTotalDegree`, `weightedTotalDegree_zero` | `Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:90, 112, 108` | **MR** (`pubDegree`, `privDegree`) |
| `weightedTotalDegree_one`, `weightedTotalDegree_rename_of_injective` | `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:50, 56` | **MR** (`rename_of_injective` also carries the degrees across the C13 renaming) |
| `MvPolynomial.rename`, `eval_rename` | `Mathlib/Algebra/MvPolynomial/Rename.lean:50, 188` | **MR** (structured variables → `Fin (pubLen κ) ⊕ Fin (privLen κ)`, C13) |
| `Finsupp.weight` (+`weight_apply`), `MvPolynomial.support_mul` | `Mathlib/Data/Finsupp/Weight.lean:74, 77`; `Mathlib/Algebra/MvPolynomial/Basic.lean:554` | **MR** for the missing closure lemmas |
| `MvPolynomial.sumAlgEquiv` | `Mathlib/Algebra/MvPolynomial/Equiv.lean:295` | NR |
| `Finset.prod_univ_sum` (∏ of sums = sum over `piFinset` of ∏) | `Mathlib/Algebra/BigOperators/Ring/Finset.lean:150` | **MR** (s̄^{⊗D} expansion; no tensor library) |
| `Matrix.mulVec`, `Matrix.mul_apply` | Mathlib `Data/Matrix` | **MR** (b = A s + e + σ; U V = M) |
| `Matrix.kroneckerMap`, `mul_kronecker_mul`, `TensorProduct` | `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:55, 369` | **X** (not needed; a function on `Fin D → Fin (ℓ+1)` is simpler) |
| `RazborovSmolensky.squarefreeMonomial`, `squarefreePolynomial`, `squarefreeMonomial_eval` | `TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra/RootCube.lean:311, 317, 323` | **MR if** the job writes multilinear polynomials from subset coefficients (then do not redefine ∏_{i∈s} X_i); NR otherwise |
| `ThresholdFunctions.MultilinearPolynomial` (Walsh ±1 basis over ℝ) | `TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean:52` | NR (different basis and ring) |

## G. Counting and analytic bounds (Claim 4.2, Claim 4.1; r1 §F)

| Name | File:line | Use |
|---|---|---|
| `Nat.choose_le_pow_div` (C(n,r) ≤ n^r / r!), `Nat.pow_le_choose` | `Mathlib/Data/Nat/Choose/Bounds.lean:30, 57` | **MR** |
| `Real.pow_div_factorial_le_exp` (x^n / n! ≤ e^x) | `Mathlib/Analysis/Complex/Exponential.lean:250` | **MR**: with the previous, C(n,k) ≤ (e n / k)^k in a few lines, as **one** disclosed public helper |
| TCSlib local `h_binom` (C(n,k) ≤ (e n / k)^k, a `have` inside a proof) | `TCSlib/KikuchiLDC/LDC/BackgroundFacts.lean:252` | NR (not public; cite it in the helper's disclosure) |
| `choose_le_pow` (n.choose (2α) ≤ n^(2α)) | `TCSlib/GraphTheory/KargerMinCut.lean:933` | NR |
| `Nat.choose_le_choose`, `Nat.descFactorial_le_pow`, `Nat.choose_mul_factorial_mul_factorial` | `Mathlib/Data/Nat/Choose/Basic.lean:320, 132`; `Mathlib/Data/Nat/Factorial/Basic.lean:434` | R |
| `Fintype.card_fun` (uniform functions [m] → [B] count) | `Mathlib/Data/Fintype/BigOperators.lean:195` | R |
| `Real.add_one_le_exp`, `Real.one_sub_div_pow_le_exp_neg`, `Real.exp_one_lt_d9`, `Real.exp_one_gt_d9` | `Exponential.lean:635, 646`; `Mathlib/Analysis/Complex/ExponentialBounds.lean:33, 30` | **MR** |
| `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`, `Real.isLittleO_pow_exp_atTop`, `isLittleO_pow_exp_pos_mul_atTop` | `Mathlib/Analysis/SpecialFunctions/Exp.lean:259, 363`; `…/Pow/Asymptotics.lean:304` | **MR** ("poly(κ)·e^{−κ} ≤ 2^{−κ}/4 eventually") |
| `Real.rpow_natCast`, `Nat.floor` / `Nat.log` API | Mathlib `Analysis/SpecialFunctions/Pow/Real.lean:58`, `Data/Nat/Log.lean` | **MR** (C6, C8) |
| `Nat.findGreatest` (+ `Nat.findGreatest_eq_iff`, `Nat.findGreatest_spec`) | Mathlib `Data/Nat/Find.lean` | **MR** for `κOf` (C11), with a reader `κOf (κ ^ E) = κ` |
| Bertrand: `Nat.exists_prime_lt_and_le_two_mul` (alias `Nat.bertrand`) | `Mathlib/NumberTheory/Bertrand.lean:217, 235` | **MR** for `PrimeSchedule.nonempty` only (non-vacuity; no algorithm uses the chosen schedule, S12) |
| `CharP.natCast_injOn_Iio` | `Mathlib/Algebra/CharP/Basic.lean:55` | R (casting 0/1 and small naturals into ℤ_p) |

## H. PRG notions already in the library (unchanged from r1)

| Name | File:line | Use |
|---|---|---|
| `PRG`, `PRG.Secure` (length-regular, index-free) | `Pseudorandom/Generators/Asymptotic/Defs.lean:132, 170` | **X** to import (S2-B owns the file; the link "a PRG is an sPRG" waits for Stage 2); NR for the shape of `BoolPRG.Secure` |
| `prgAdv` | `Pseudorandom/Generators.lean:73` | NR |

## Appendix: Phase B only (not used by this job)

Kept for the Phase B dispatch; line numbers at `0fec2589` = `cbce64d1`. Phase B may also prefer
word-RAM programs (`ram-bridge-assessment.md`) to any TM-level row below.

| Name | File:line | Phase B use |
|---|---|---|
| `DyadicLinearAlgebra.matVecPoly` (+`_encodeMatrix`, `polyTimeComputable_matVecPoly`), `dotPoly` | `Encoding/DyadicLinearAlgebra.lean:342, 395, 445, 175` | **B**: `A s mod p` at a non-wrapping width (r1 §4.8) |
| `DyadicArithmetic.addPoly`, `mulPoly`, `subPoly` (+ poly lemmas) | `Encoding/DyadicArithmetic.lean:61, 146, 229` | **B** |
| `Complexity.BinArith.mod`, `polyTimeComputable_mod`; `add`, `polyTimeComputable_add`; `mul`, `polyTimeComputable_mul` | `TCSlib/Complexity/ClassP/BinaryArith/Div.lean:55, 245`; `AddSub.lean:141, 162`; `Mul.lean:110, 217` | **B** |
| `Encoding.BinaryArith.toLE`, `polyTimeComputable_toLE` | `Encoding/BinaryArith.lean:60, 114` | **B** (endianness) |
| H16 `Complexity.BinArith.forLoop`, `polyTimeComputable_forLoop` | `TCSlib/Complexity/ClassP/BinaryArith/Loops.lean:82, 126` | **B** (registered host H16) |
| `polyTimeComputable_iterateEmit` | `TCSlib/Complexity/Randomized/Repetition.lean:351` | **B** |
| pairing calculus: `PolyTimeComputable.pairEncode`, `polyTimeComputable_pairFstD/SndD`, `polyTimeComputable_layout`, `polyTimeComputable_pairTakePoly/DropPoly` | `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129, 252, 256`; `TCSlib/Complexity/Randomized/Closure.lean:182`; `TCSlib/Complexity/Randomized/Primitives.lean:194, 207` | **B** (proving the targets at TM level, if Phase B does not go through RAM) |
| `NUPPT.wrap`, `runAtL_wrap`, `runAt_wrap`, `wrapCoinsEquiv`; `NUPPT.preComp`, `runAt_preComp` | `Asymptotic/ReductionSupport.lean:148, 186, 200, 169, 318, 351` | **B** (same-parameter hop machines; Phase A's link uses `exists_reparam_pre_post`) |
| `NUPPT.exists_reparam_advice`, `NUPPT.reparam` | `TCSlib/Complexity/Randomized/Closure.lean:325`; `Asymptotic/HardCoreLemmas.lean:449` | NR |
| `expandRedMachine` (PRG hybrid machine) | `Pseudorandom/Generators/Asymptotic/StretchMachine.lean:190` | NR (pattern for a hybrid machine) |
| RAM bridge (proposed names): `WordRAM.polyTimeComputable_of_computes`, `progOut`, `NUPPT.exists_uniform_ofProgram`, `NUPPT.exists_ofProgram` | not on any branch yet (`ram-bridge-assessment.md` §5; Seyoon's bridge branch, names unknown) | **B**: discharge T1–T4 from single uniform programs |
| Sampler bridge: `CoinSampling.CoinSampler`, `bucket`, `UniformSampler`, `bucketRaw`, `Games.ProbComp.Close`, `OutputsSubset` | in-house, stacked on #374 (`briefs/io-components/sampler-bridge/`, ruled 2026-11-18); not at `cbce64d1` | **B** (and **X** for this job even if a later `<BASE>` has it, S2): composes with T3 |
