# Inventory — [PS10] Chapter 2, *Computational Hardness* (§2.1–§2.13, plus the Appendix items Chapter 2 uses)

Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-shelat-2010-ch2.raw.md`
(pages 21–65) and `…-appendix.raw.md`. Read-only survey of the Lean tree; nothing under `TCSlib/` was
touched. Conventions: `n` is the security parameter; "nuPPT" is [PS10, Def 26.8] in the advice
formulation (plan D4); "PPT" is [PS10, Def 23.4/23.5] with the random tape as an input component
(plan D3); `{0,1}^n` is `Fin n → Bool` (plan D5); `Π_n = {p < 2^n | p prime}`; `Z_N^* = (ZMod N)ˣ`;
"negl" = `TCSlib.Cryptography.Negligible`. Paths are relative to the worktree
`/Users/dehmelf/Research/tcslib-pass-shelat`; Mathlib paths are relative to
`.lake/packages/mathlib/Mathlib`.

Scope labels: **core** = mandatory per the plan; **optional** = feasible and useful, or already
formalized (cite only); **deferred** = not needed downstream and/or research-level.

---

## 0. Headline findings for the planners (read first)

**F1. There are no binary-arithmetic machines in the library.** `TCSlib/Complexity` contains no
`FinTM` computing addition, comparison, multiplication, division/mod, gcd, or modular exponentiation on
binary strings (the only counters are `Turing.FinTM.computesFunInTime_incFixed`, `…_lengthBits`,
`…_polyUnary`, `…_polyBits` in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`, which handle
lengths and fixed-width increments). Every "easy to compute / sample / evaluate / invert with
trapdoor" clause of §2.3 and §2.6–§2.12 (f_mult, Euclid, modexp, Miller–Rabin, SamplePrime, factoring/
DL/RSA/Rabin collections) needs them, and so do the *reductions* of Thms 33.5, 36.3, 55.2, 61.8
(they multiply, divide, take gcds). Building them in the `Build/` style is a research-level effort
(the pairing primitives alone are 7.6k lines). **Recommendation (Q1):** a hypothesis bundle
`TCSlib.Cryptography.Candidates.ArithmeticFP` (fields: `PolyTimeComputable` for binary `mul`,
`divMod`, `xgcd`, `modExp`, comparison, and the decoding of binary numerals), taken as an explicit
hypothesis by every candidate theorem (no axiom; `#print axioms` stays clean), with its discharge a
deferred build target. The asymptotic OWF/collection *definitions* remain machine-based; only the
number-theoretic *instances* are conditional.

**F2. Algorithm 64.2 (universal one-way function) is wrong as printed** and the proof of Theorem 63.1
does not go through for it: `f_universal(⟨M, x⟩) = M(x)` lets an inverter return `⟨M', x'⟩` with a
different machine `M'`, which yields no preimage under `M_g`. The standard (Levin/Goldreich) definition
outputs `⟨M, M(x)⟩`; with it the text's union-bound argument is valid. Formalize the corrected
function (Deviation recorded in the docstring; listed in `text_errors`).

**F3. Security parameter vs input length (Q2).** Thm 35.1's `f'` lives on `({0,1}^n)^{m(n)}` and
Thm 42.2's `g` on `{0,1}^{ℓ₁(n)+ℓ₂(n)}`; the text's `f : {0,1}* → {0,1}*` with hardness "at every n"
cannot be met by these functions at lengths outside the image of `ℓ`. Recommended shape: an
asymptotic one-way function is a family `f n : (Fin (ℓ n) → Bool) → List Bool` with an explicit
polynomial input length `ℓ n = C·(n+1)^c` (default `ℓ n = n`), "easy" = some `FinTM Bool` computes
`pairEncode 1^n (ofFn x) ↦ f n x` within `Ct·(n+1)^ct`, "hard" = for every nuPPT receiving
`pairEncode 1^n (f n x)`, negligible in `n`. For `ℓ n = n` this is the text's definition (the honest
evaluator additionally reads `1^n`, harmless). Alternative: `ℓ` strictly increasing and the evaluator
on bare `x` (recover `n` by search; `computesFunInTime_splitSolveWith` is the model primitive).

**F4. Dyadic samplers are never exactly uniform on `Π_n`, `Z_q`, `Z*_{Φ(N)}`, `Z_N^*`, `QR_N` (Q3).**
Keep the hardness experiments on the *ideal* uniform distributions (as the text), and formalize the
"easy to sample" clauses as PPT samplers within statistical distance `2^{-n}` of uniform (strict
PPT with truncated rejection loops; Deviation). One bridging lemma (any success probability moves by
at most the statistical distance; `distAdv_le_statDist` is the model) connects the two. The needed
density facts are elementary: `|Π_n| ≥ 2^n/(2n)` (Chebyshev), `φ(m)/m ≥ 1/(log₂ m + 1)` (new, for
`Z*_{Φ(N)}`), `φ(pq)/pq ≥ 1/4` (for `Z_N^*`), 4-to-1 squaring (for `QR_N`).

**F5. Rabin needs more than the text states (Q4).** Thms 60.5/60.6/61.7/61.8/63.10 need `p ≠ q`
odd; Thm 61.8 (⇐) needs square roots modulo arbitrary primes but the text only proves `p ≡ 3 (mod 4)`;
Thm 63.10's `Gen` must sample primes `≡ 3 (mod 4)`, whose density is not available in Mathlib (no
Dirichlet-type bound). Formalize the Rabin results for Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`),
with the factoring assumption restricted to that index distribution, and take the density of
`3 (mod 4)` primes as an explicit hypothesis of the `Gen`-efficiency clause of Thm 63.10.

**F6. Primality testing (Q6).** The text relies on "primality testing is in polynomial time" (AKS,
unproved here) for SamplePrime and the `Gen` of Thms 51.1/53.2/57.2/61.7/63.10, and on Miller–Rabin
whose composite-case lemma (50.15b) is deferred by the plan. Recommended: a hypothesis
`PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` inside the Q1 bundle;
Miller–Rabin is formalized as a sampler with its prime-case correctness (core) and the composite
bound (deferred). Thms 33.5 and 36.3 are formalized with the one-call / random-planting reductions
that need no primality test (plan decision).

**F7. Uniform position in Thm 35.1 (Q7).** `OneWay.yaoTry` draws `i : Fin q` uniformly; coins of
polynomial length give exact uniformity only for `q` a power of two. Choose `m(n) := 2^{⌈log₂(2n q(n))⌉}`
(any larger `m` is allowed by the theorem), or route through Q3's statistical bridge.

**F8. Concrete-layer additions.** Garg files are frozen; new concrete lemmas go in a new file
`TCSlib/Cryptography/Candidates/Concrete.lean` (reductions and probability lemmas used by the
candidates) and in `TCSlib/Cryptography/Asymptotic/OneWay.lean` itself (small ones). List in §4.

**F9. Closure/Repetition requirements consumed by Chapter 2** are listed in §5 so that the machine
layer (Randomized/Closure.lean, Repetition.lean) can be sized before the skeletons are written.

---

## 1. Inventory table

Columns: ID · kind · title · proposed file (under `TCSlib/`) · difficulty 1–5 · scope · existing Lean
(short; full paths in §2) · note key. `(cite)` = already formalized, nothing to do beyond citing.

| ID | kind | title | proposed file | diff | scope | existing Lean |
|---|---|---|---|---|---|---|
| Def-21.1 | definition | Algorithm = deterministic TM over {0,1} | (cite) `Complexity/TuringMachine/Finite.lean` | 1 | optional | `Turing.FinTM Bool` |
| Def-21.2 | definition | Running time; polynomial time | (cite) `Complexity/ClassNP/PolyTime.lean` | 1 | optional | `FinTM.ComputesFunInTime`, `Complexity.PolyTimeComputable`, `Complexity.P` |
| Def-21.3 | definition | Deterministic computation of f | (cite) | 1 | optional | `FinTM.ComputesFunInTime`, `FinTM.Computes` |
| Rem-22.1 | claim | §2.1.1 background: Halting, time hierarchy, SAT | (cite) | 1 | optional | `Complexity.HALT_not_computable`, `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete` |
| Def-23.4 | definition | PPT (randomized TM with coin input) | `Complexity/Randomized/PPT.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime` |
| Def-23.5 | definition | Running time of a randomized TM (worst case over coins) | `Complexity/Randomized/PPT.lean` | 1 | core | — |
| Def-24.6 | definition | PPT computes f with probability 1 | `Complexity/Randomized/PPT.lean` | 2 | core | — (needs C7) |
| Rem-24.2 | claim | Majority amplification 1/2+1/poly → 1−2^{-n} | `Complexity/Randomized/Repetition.lean` | 4 | deferred | — (Chernoff) |
| Def-24.7 | definition | Efficient private-key encryption | `Cryptography/Asymptotic/Encryption.lean` | 2 | core | — |
| Def-26.8 | definition | Non-uniform PPT (advice form) | `Complexity/Randomized/NonUniform.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly` |
| Rem-26.2 | claim | Machine-sequence ⟺ advice formulation of nuPPT | — | 4 | deferred | `Turing.timed_universal` (for ⇒) |
| Claim-26.3 | infrastructure | nuPPT closure calculus (pre/post, pairing, coins, advice, repetition) | `Complexity/Randomized/{Closure,Repetition}.lean` | 5 | core | `computesFunInTime_comp/cond`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `PolyTimeComputable.*` |
| Def-26.1 | definition | Worst-case one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Rem-27.1 | claim | NP ⊄ BPP ⟺ worst-case OWF exist ("show this!") | — | 5 | deferred | `Complexity.NP` |
| Def-27.2 | definition | Negligible / non-negligible | (cite) `Cryptography/Foundations/Negligible.lean` | 1 | optional | `Negligible`, `not_negligible_iff`, `negligible_two_pow_neg` |
| Def-27.3 | definition | Strong one-way function | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | `invProb` |
| Rem-28.1 | claim | (t,s,ε)-one-wayness (concrete security) | (cite) | 1 | optional | `invProb` (the concrete layer is this) |
| Def-28.4 | definition | Weak one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Def-29.1 | definition | f_mult | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Rem-29.2 | claim | f_mult is not strongly one-way (3/4 attack) | — | 2 | deferred | — |
| Def-29.3 | definition | Π_n and the uniform distribution on it | `Cryptography/NumberTheory/Chebyshev.lean` | 1 | core | `Nat.primesBelow`, `Nat.primeCounting'` |
| Asm-30.1 | assumption | Factoring assumption | `Cryptography/Candidates/Factoring.lean` | 2 | core | `uprob`, `Negligible` |
| Thm-31.3 | theorem | Chebyshev: π(x) > x/(2 log₂ x) | `Cryptography/NumberTheory/Chebyshev.lean` | 4 | core | `Nat.four_pow_lt_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le`, `Nat.primesBelow_card_eq_primeCounting'` |
| Claim-32.4 | claim | p^{ν_p(C(2x,x))} ≤ 2x | (cite) | 1 | optional | `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_log` |
| Claim-33.1 | corollary | Prime density: \|Π_n\| ≥ 2^n/(2n) | `Cryptography/NumberTheory/Chebyshev.lean` | 3 | core | as Thm-31.3 |
| Rem-33.2 | claim | Primality testing in polynomial time (AKS) | hypothesis in `Cryptography/Candidates/Arithmetic.lean` | 5 | deferred | — |
| Thm-33.5 | theorem | Factoring ⟹ f_mult weakly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_and_le_mul`, `uprob_pi_forall`, `not_negligible_iff` + C1 |
| Alg-33.6 | algorithm | A′ (and the one-call A″) | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Claim-34.1 | claim | f_mult(x′,y′) = pq ⟹ x′ ∈ {p,q} | `Cryptography/Candidates/Factoring.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd` |
| Thm-35.1 | theorem | Weak → strong (Yao direct product) | `Cryptography/Asymptotic/OneWay.lean` | 4 | core | `OneWay.yao_amplification`, `prodFun`, `yaoInverter`, `invProb_prodFun_le`, `one_sub_invProb_yaoInverter_le` |
| Thm-35.2 | theorem | g(x,y) = (f x, f y) strong if f strong | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | pattern `OneWay.invProb_pad_le` + C2 |
| Thm-36.3 | theorem | Factoring ⟹ f_mult^{4n³} strongly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_update`, `sum_uprob_eq_card_mul`, `uprob_pi_forall`, `uprob_and_le_mul` + C3, C8 |
| Claim-36.2 | claim | (1−1/(4n²))^{4n³} ≤ e^{−n} | `Cryptography/Candidates/Concrete.lean` | 1 | core | `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul` (pattern `yao_amplification_exp`) |
| Alg-37.4 | algorithm | A′(z′) with planting (random-position variant) | `Cryptography/Candidates/Factoring.lean` | 1 | core | `uprob_update` |
| Alg-38.5 | algorithm | A₀(f, y) and its 2nm²p(n)-fold repetition | (cite) `Cryptography/OneWayFunctions/Amplification.lean` | 1 | optional | `OneWay.yaoTry`, `OneWay.yaoInverter` |
| Claim-38.2 | claim | PS10 parameters instantiate `yao_amplification` | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `OneWay.yao_amplification`, exp bounds |
| Claim-39.1 | claim | Pr[A fails \| x good] ≤ (1−θ)^T ≈ e^{−n} | (cite) | 1 | optional | `OneWay.one_sub_invProb_yaoInverter_le` |
| Claim-39.2 | claim | Many good elements: \|G_n\| ≥ 2^n(1−1/(2q)) | (cite) | 1 | optional | `OneWay.invProb_prodFun_le` |
| Def-41.1 | definition | Collection of one-way functions | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `HardcoreBit.PushesUniform`, `invProb` (pattern) |
| Thm-42.2 | theorem | Collection of OWFs ⟺ strong OWF | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `PolyTimeComputable.pairEncode/.comp`, `uprob_prod`, `PushesUniform.uprob_eq` |
| Fact-42.1 | fact | Modular arithmetic laws | (cite) | 1 | optional | `Nat.add_mod`, `Nat.mul_mod` |
| Alg-43.2 | algorithm | ExtendedEuclid | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.xgcd`, `Nat.gcdA/gcdB`, `Nat.gcd_eq_gcd_ab`, `ZMod.inv` |
| Claim-43.3 | claim | ≤ 2n recursive calls when a < 2^n | `Cryptography/NumberTheory/Euclid.lean` | 3 | core | — |
| Claim-44.4 | claim | gcd(a,b) = gcd(b, a mod b) | (cite) | 1 | optional | `Nat.gcd_rec`, `Nat.gcd_comm` |
| Claim-44.5 | claim | Correctness ax+by = gcd (induction) | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.gcd_eq_gcd_ab` (Mathlib's own xgcd) |
| Rem-43.6 | claim | Euclid runs in poly(log a + log b) (machine) | Q1 hypothesis | 5 | deferred | — |
| Alg-45.5 | algorithm | Modular exponentiation (repeated squaring) | `Cryptography/NumberTheory/ModExp.lean` | 2 | core | `Nat.pow_mod`, `Nat.ModEq.pow` |
| Thm-45.6 | theorem | ≤ 2(⌊log₂ x⌋+1) modular multiplications; O(log x log² N) | `Cryptography/NumberTheory/ModExp.lean` | 2 | optional | `TimeM` (`Cryptography/RSA.lean`) cost model, optional |
| Def-46.7 | definition | Group | (cite) | 1 | optional | `Group`, `CommGroup` |
| Ex-46.1 | example | (Z_N, +) | (cite) | 1 | optional | `ZMod N` |
| Thm-46.8 | theorem | (Z_N^*, ×) is a group; Z_N^* = {x ∈ [1,N−1] \| gcd(x,N)=1} | `Cryptography/NumberTheory/Units.lean` | 1 | optional | `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime`, `ZMod.unitOfCoprime`, `ZMod.mul_inv_eq_gcd` |
| Def-46.9 | definition | Prime | (cite) | 1 | optional | `Nat.Prime` |
| Claim-47.1 | claim | p ∣ ab ⟹ p ∣ a ∨ p ∣ b (exercise) | (cite) | 1 | optional | `Nat.Prime.dvd_mul` |
| Claim-47.2 | claim | Φ(p) = p−1; Φ(pq) = (p−1)(q−1) (p ≠ q) | `Cryptography/NumberTheory/Units.lean` | 1 | core | `Nat.totient_prime`, `Nat.totient_mul`, `Nat.coprime_primes`, `ZMod.card_units_eq_totient` |
| Thm-47.10 | theorem | Euler | (cite) | 1 | optional | `ZMod.pow_totient`, `Nat.ModEq.pow_totient` |
| Cor-48.11 | corollary | Fermat | (cite) | 1 | optional | `ZMod.pow_card_sub_one_eq_one` |
| Cor-48.12 | corollary | a^x ≡ a^{x mod Φ(N)} (mod N), a ∈ Z_N^* | `Cryptography/NumberTheory/Units.lean` | 1 | core | `ZMod.pow_totient`, `Nat.div_add_mod` |
| Rem-48.2 | claim | Given Φ(N), a^x mod N efficient for any x (machine) | Q1 hypothesis | 5 | deferred | Cor-48.12 + Alg-45.5 |
| Ex-48.3 | example | 2^{61241} mod 21 (garbled) | — | 1 | optional | `decide` |
| Def-49.1 | definition | Miller–Rabin liar set L_N (corrected) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | — |
| Alg-49.13 | algorithm | Miller–Rabin test (t rounds) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | `uprob_pi_forall` |
| Thm-49.14 | theorem | MR correct on primes; errs on composites w.p. ≤ 2^{−t} | `Cryptography/NumberTheory/Primality.lean` | 2 | core (prime) / deferred (composite) | `uprob_pi_forall` |
| Lem-50.15a | lemma | N odd prime ⟹ L_N = Z_N^* | `Cryptography/NumberTheory/Primality.lean` | 3 | core | `ZMod.pow_card_sub_one_eq_one`, `mul_self_eq_one_iff`, `sq_eq_sq_iff_eq_or_eq_neg` |
| Lem-50.15b | lemma | N odd composite ⟹ \|L_N\| ≤ (N−1)/2 | `Cryptography/NumberTheory/Primality.lean` | 5 | deferred | `Subgroup.card_subgroup_dvd_card` |
| Rem-49.3 | claim | Infinitely many Carmichael numbers | — | 5 | deferred | (weaker) `Nat.exists_infinite_pseudoprimes` |
| Rem-50.2 | claim | AKS deterministic primality | — | 5 | deferred | — |
| Alg-50.16 | algorithm | SamplePrime(n) (truncated strict-PPT form) | `Cryptography/NumberTheory/Primality.lean` | 3 | core | C4, C8 |
| Lem-51.17 | lemma | SamplePrime: uniform prime, failure ≤ 2^{−n}, poly time | `Cryptography/NumberTheory/Primality.lean` | 3 (+4 machine) | core | C4; Claim-33.1; `exists_loopFindTM` |
| Thm-51.1 | theorem | Factoring collection | `Cryptography/Candidates/Factoring.lean` | 3 | core | Lem-51.17, Claim-34.1, Def-41.1 |
| Def-52.1 | definition | Generator of a group; Gen_G | (cite) | 1 | optional | `Subgroup.zpowers`, `IsCyclic.exists_generator` |
| Rem-52.2 | claim | Prime-order groups; Z_p^* order p−1; safe primes, squares subgroup | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card` |
| Asm-52.2 | assumption | Discrete-log assumption (relative to a group family) | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | — |
| Thm-52.3 | theorem | DL collection | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | Def-41.1, Asm-52.2 |
| Claim-53.1 | claim | Safe-prime generator test g ≠ ±1, g^q ≠ 1 | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `orderOf_dvd_of_pow_eq_one`, `ZMod.card_units` |
| Claim-53.2 | claim | x ↦ g^x : Z_q → G_q is a bijection (DL is a permutation) | `Cryptography/Candidates/DiscreteLog.lean` | 2 | optional | `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq` |
| Asm-53.1 | assumption | RSA assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | `ZMod.unitsEquivCoprime` |
| Thm-53.2 | theorem | RSA collection | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `HardcoreBit.pushesUniform_equiv`, C9 |
| Thm-54.3 | theorem | x ↦ x^e permutes Z_N^* when e ∈ Z*_{Φ(N)} | `Cryptography/NumberTheory/Units.lean` | 2 | core | `ZMod.pow_totient`, `RSA.rsa_crt_pow`, `RSA.rsa_correctness` |
| Def-55.1 | definition | Collection of one-way permutations | `Cryptography/Asymptotic/Collections.lean` | 1 | core | Def-41.1 |
| Thm-55.2 | theorem | RSA assumption ⟹ factoring assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `ZMod.inv`/`Nat.gcdA`, `uprob_fst` |
| Alg-55.3 | algorithm | A′(N, e, y) via factoring | `Cryptography/Candidates/RSA.lean` | 1 | core | — |
| Def-56.1 | definition | Collection of trapdoor permutations | `Cryptography/Asymptotic/Collections.lean` | 2 | core | Def-55.1 |
| Thm-57.2 | theorem | RSA is a TDP collection ("exercise") | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-53.2, Thm-54.3, Alg-43.2 |
| Def-57.0 | definition | QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | `MonoidHom.range`, `powMonoidHom` |
| Lem-57.1 | lemma | QR_p subgroup of size (p−1)/2; two roots each | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `legendreSym.card_sqrts`, `ZMod.euler_criterion`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.card_units` |
| Claim-58.1 | claim | x² = y² in Z_p ⟹ x = ±y | (cite) | 1 | optional | `sq_eq_sq_iff_eq_or_eq_neg` |
| Thm-58.2 | theorem | p = 4k+3: (y^{k+1})² = y for y ∈ QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.pow_card_sub_one_eq_one` |
| Ex-58.3 | exercise | Square roots for p ≡ 1 (mod 4) | — | 4 | deferred | — |
| Thm-58.3 | theorem | Chinese Remainder (k pairwise coprime moduli) | (cite; k = 2 bridge) `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | optional | `ZMod.chineseRemainder`, `Nat.chineseRemainderOfList`, `Nat.chineseRemainder` |
| Claim-59.1 | claim | Explicit CRT inverse y = Σ b_i n_i a_i; two Euclid calls | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | optional | `Nat.chineseRemainder` |
| Ex-59.2 | example | p = 7, q = 11 | — | 1 | optional | `decide` |
| Def-59.3 | definition | QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | — |
| Thm-59.4 | theorem | x ∈ QR_N ⟺ x mod p ∈ QR_p ∧ x mod q ∈ QR_q | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder`, `Units.map`, `RingEquiv.map_pow` |
| Thm-60.5 | theorem | Squaring on Z_N^* is 4-to-1 (p ≠ q odd) | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | Lem-57.1, Thm-59.4 |
| Cor-60.6 | corollary | \|QR_N\| = \|Z_N^*\|/4 | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Finset.card_eq_sum_card_fiberwise` |
| Claim-60.7 | claim | Roots mod N from roots mod p, q via CRT | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder` |
| Ex-60.8 | example | N = 77 example (garbled) | — | 1 | optional | `decide` |
| Thm-61.7 | theorem | Rabin collection is one-way under factoring | `Cryptography/Candidates/Rabin.lean` | 4 | core | C5, C6, Claim-62.1 |
| Thm-61.8 | theorem | Rabin one-way ⟺ factoring (Blum integers) | `Cryptography/Candidates/Rabin.lean` | 4 (⇒) / 3 (⇐, Blum) | core | Thm-58.2, Claim-60.7, C6 |
| Alg-62.9 | algorithm | Factoring adversary A′(N) from a root finder | `Cryptography/Candidates/Rabin.lean` | 1 | core | — |
| Claim-62.1 | claim | x² ≡ z², z ≢ ±x ⟹ gcd(x−z, N) ∈ {p,q} | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Int.gcd`, `ZMod.chineseRemainder` |
| Claim-62.2 | claim | Half the time the root differs from ±x (symmetry lemma) | `Cryptography/Candidates/Concrete.lean` | 3 | core | `uprob_comp_equiv`, `uprob_or_le` |
| Thm-63.10 | theorem | Rabin TDP on Blum integers | `Cryptography/Candidates/Rabin.lean` | 4 | core | Claim-63.1, C5, Thm-58.2, `ZMod.euler_criterion` |
| Claim-63.1 | claim | Blum N: each square has exactly one root in QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `ZMod.exists_sq_eq_neg_one_iff`, Lem-57.1, Thm-59.4 |
| Thm-63.1 | theorem | Universal one-way function (corrected) | `Cryptography/Asymptotic/Universal.lean` | 5 | core | `Turing.timed_universal(_concrete)`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `OneWay.card_log_bits_le` |
| Alg-64.2 | algorithm | f_universal (definition + poly-time computability) | `Cryptography/Asymptotic/Universal.lean` | 4 | core | `Turing.timed_universal_concrete`, `universalBlockBound`, `computesFunInTime_polyBits`, `PolyTimeComputable.pairEncode` |
| Lem-64.3 | lemma | Strong OWF computable in O(n²) (padding) | `Cryptography/Asymptotic/Universal.lean` | 3 | core | `OneWay.pad`, `OneWay.padInverter`, `OneWay.invProb_pad_le`, `FinTM.one_work_tape_binary`, `exists_codeTM` |
| Claim-65.1 | claim | PickG: Pr[code field = ⟨M_g⟩] ≥ 1/n | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_eq_one_div_card`, `OneWay.card_log_bits_le`, `decode_encode_pad` |
| Claim-65.2 | claim | Union bound 1/n³ + (1−1/n) and the contradiction | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_or_le`, `not_negligible_iff` |
| App-A.1 | fact | Union bound | (cite) | 1 | optional | `uprob_or_le`, `uprob_exists_le` |
| App-A.2 | fact | Markov; Chebyshev's inequality | (cite) | 1 | optional | `HardcoreBit.uprob_mul_le_uexp`, `HardcoreBit.uprob_le_abs_le` |
| Thm-188.7 | theorem | Chernoff bound | — | 4 | deferred | `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (measure-theoretic Hoeffding) |
| Lem-189.8 | lemma | Majority vote (garbled statement) | — | 4 | deferred | — |
| App-A.3 | fact | Pairwise-independent sampling inequality | (cite) | 1 | optional | `HardcoreBit.chebyshev_pairwise(_ident)` |
| Thm-189.9 | theorem | Cauchy–Schwarz | (cite) | 1 | optional | `Finset.sum_mul_sq_le_sq_mul_sq` |
| Def-191.10 | definition | DP (= P) | (cite) | 1 | optional | `Complexity.P` |
| Def-191.11 | definition | NP (witness relation, \|y\| ≤ p(\|x\|)) | (cite) | 1 | optional | `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le` |
| Def-192.12 | definition | BPP | `Complexity/Randomized/PPT.lean` | 2 | deferred | — |

---

## 2. Statements, existing Lean, bridges, and text issues (one entry per item)

Full paths of the existing declarations cited below:

* `Turing.FinTM`, `Turing.FinTM.ComputesInTime`, `.ComputesFunInTime`, `.Computes`, `.ComputesInTime.mono`, `.computesInTime_iff` — `TCSlib/Complexity/TuringMachine/Finite.lean`.
* `Complexity.PolyTimeComputable`, `Complexity.PolyBound`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `.output_length_le` — `TCSlib/Complexity/ClassNP/PolyTime.lean`.
* `Complexity.PolyTimeComputable.pairEncode`, `.pairMapSnd`, `.append`, `Complexity.polyTimeComputable_{const,prepend,unary,polyUnary,pairFstD,pairSndD,pairConcat,pairSwap,ite,and,lenLe,lenEq,of_linear}`, `Complexity.pairFstD`, `Complexity.pairSndD`, `Complexity.pairMapSnd` — `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`.
* `Complexity.mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `mem_P_of_test`, `test_of_mem_P`, `inter_mem_P`, `union_mem_P` — `TCSlib/Complexity/ClassNP/PClosure.lean`.
* `Complexity.P`, `Complexity.DTIME`, `Turing.FinTM.DecidesInTime` — `TCSlib/Complexity/ClassP/{P,DTIME}.lean`.
* `Complexity.NP`, `Complexity.P_subset_NP`, `Complexity.mem_NP_iff_exists_length_le` — `TCSlib/Complexity/ClassNP/NP.lean`.
* `Turing.FinTM.DecidesWithAdviceInTime`, `Complexity.DTIMEAdvice`, `Complexity.PAdvicePoly`, `Complexity.P_subset_PAdvicePoly` — `TCSlib/Complexity/CircuitComplexity/Advice.lean`.
* `Turing.pairEncode`, `Turing.pairDecode`, `Turing.pairEncode_injective`, `Turing.length_pairEncode`, `Turing.CodeTM`, `Turing.CodeTM.toFinTM`, `Turing.CodeTM.serialize`, `Turing.MachineCode` (`encode`, `decode`, `decode_encode_pad`), `Turing.MachineCode.decode_encode`, `Turing.EffectiveMachineCode` (`canonizer`, `canonizerTime`, `canonizer_computes`), `Turing.exists_codeTM`, `Turing.length_bits_le_self` — `TCSlib/Complexity/TuringMachine/Encoding.lean`.
* `Turing.exists_effectiveMachineCode` — `TCSlib/Complexity/TuringMachine/MathlibBridge.lean:1099`.
* `Turing.universal`, `Turing.timed_universal`, `Turing.timed_universal_concrete` — `TCSlib/Complexity/TuringMachine/Universal.lean`; `Turing.universalBlockBound` (= `3·|serialize| + 5·(numStates+1) + 20`) — `TCSlib/Complexity/TuringMachine/UniversalBlock.lean:750`.
* `Turing.FinTM.one_work_tape_binary` (`M.ComputesFunInTime f T → ∃ M' c, M'.k = 1 ∧ M'.ComputesFunInTime f (fun n => c*(T n+1)^2)`) — `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:965`.
* `Turing.FinTM.computesFunInTime_{id,const,ifEq,comp}`, `Turing.FinTM.exists_comp_on_image`, `exists_comp_partial`, `exists_cond` — `TCSlib/Complexity/TuringMachine/Composition.lean`.
* `Turing.FinTM.computesFunInTime_cond` — `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:711`.
* `Turing.FinTM.exists_loopTM`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM` — `TCSlib/Complexity/TuringMachine/Build/Loop.lean` (lines 2519, 2633, 5508, 5645, 5691).
* `Turing.FinTM.computesFunInTime_{prepend,lengthBits,polyUnary,polyBits,pairEncodeFixed,pairFst,pairSnd,pairValid,pairConcat,pairDup,pairMapSnd,pairLenCheck,stripLast,splitSolve,incFixed,splitSolveWith,unaryToken,appendBit}` — `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
* `Complexity.HALT_not_computable` — `TCSlib/Complexity/Uncomputability/Halting.lean:194`; `Complexity.P_ssubset_EXP`, `Complexity.P_ne_EXP` — `TCSlib/Complexity/TimeHierarchy/Separation.lean`; `Complexity.SAT_NPComplete`, `Complexity.SAT3_NPComplete` — `TCSlib/Complexity/CookLevin/Hardness.lean`.
* `TCSlib.Cryptography.Negligible`, `Noticeable`, `Negligible.{mono,add,mul,mul_pow,const_mul}`, `negligible_two_pow_neg`, `Noticeable.not_negligible`, `not_negligible_iff`, `not_negligible_sub`, `exists_not_negligible_not_noticeable` — `TCSlib/Cryptography/Foundations/Negligible.lean`.
* `TCSlib.Cryptography.uprob`, `uexp`, `uprob_eq_card_filter`, `uprob_eq_uexp`, `uprob_nonneg`, `uprob_le_one`, `uprob_true`, `uprob_false`, `uprob_not`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `half_le_uprob_good`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` — `TCSlib/Cryptography/Foundations/Probability.lean`.
* `TCSlib.Cryptography.invProb`, `predProb`, `acceptProb`, `distAdv`, `acceptProb_comp_equiv`, `uprob_comp_eq_sum_map`, `distAdv_le_statDist` — `TCSlib/Cryptography/Foundations/Experiments.lean`.
* `TCSlib.Cryptography.OneWay.{uprob_congr,uexp_mono,uexp_add,uexp_const_mul,uexp_const,uexp_indicator,uprob_and_le_mul,sum_uprob_eq_card_mul,uprob_pi_forall,uprob_update,uprob_eq_one_div_card}` — `TCSlib/Cryptography/OneWayFunctions/Basic.lean`.
* `TCSlib.Cryptography.OneWay.{prodFun,yaoTry,yaoInverter,yaoTryProb,yaoBad,yaoInverter_spec,prodFun_update,invProb_prodFun_le,one_sub_invProb_yaoInverter_le,yao_amplification,yao_amplification_exp}` — `TCSlib/Cryptography/OneWayFunctions/Amplification.lean`.
* `TCSlib.Cryptography.OneWay.{pad,padInverter,invProb_pad_le,tableInverter,invProb_tableInverter,card_log_bits_le,exists_inverter_log_output}` — `TCSlib/Cryptography/OneWayFunctions/OutputLength.lean`.
* `TCSlib.Cryptography.OneWay.{patch,patchInverter,invProb_patch_le,invProb_patch_le_of_correction,exists_correction,invProb_update_le}` — `TCSlib/Cryptography/OneWayFunctions/Robustness.lean`.
* `TCSlib.Cryptography.HardcoreBit.{PushesUniform,PushesUniform.uprob_eq,PushesUniform.comp,pushesUniform_equiv,pushesUniform_id,pushesUniform_add_right}` — `TCSlib/Cryptography/HardcoreBit/Basic.lean`; `TCSlib.Cryptography.HardcoreBit.{uprob_mul_le_uexp,uprob_le_abs_le,chebyshev_pairwise,chebyshev_pairwise_ident}` — `TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean`.
* `RSA.{rsa_core,rsa_zmod_of_factor,rsa_zmod_p,rsa_zmod_q,rsa_crt,rsa_crt_pow,PublicKey,SecretKey,encrypt,decrypt,rsa_correctness}`, `TimeM` — `TCSlib/Cryptography/RSA.lean` (legacy; no policy header; `SecretKey` carries `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`).
* Mathlib: `Nat.xgcd`, `Nat.gcdA`, `Nat.gcdB`, `Nat.gcd_eq_gcd_ab`, `Nat.exists_mul_emod_eq_gcd`, `Nat.exists_mul_emod_eq_one_of_coprime` (`Data/Int/GCD.lean`); `Nat.gcd_rec` (Lean core `Init/Data/Nat/Gcd.lean`); `ZMod.inv` (defined through `Nat.gcdA`), `ZMod.mul_inv_eq_gcd`, `ZMod.unitOfCoprime`, `ZMod.unitsEquivCoprime`, `ZMod.chineseRemainder : ZMod (m*n) ≃+* ZMod m × ZMod n` (`Data/ZMod/Basic.lean`); `ZMod.pow_totient`, `Nat.ModEq.pow_totient`, `ZMod.pow_card_sub_one_eq_one`, `ZMod.card_units`, `FiniteField.pow_dichotomy`, `FiniteField.unit_isSquare_iff` (`FieldTheory/Finite/Basic.lean`); `ZMod.card_units_eq_totient`, `Nat.totient_prime`, `Nat.totient_mul`, `Nat.totient_eq_card_coprime` (`Data/Nat/Totient.lean`); `Nat.coprime_primes`, `Nat.Prime.dvd_mul`, `Nat.decidablePrime` (`Data/Nat/Prime/{Basic,Defs}.lean`); `Nat.primeCounting`, `Nat.primeCounting'`, `Nat.primesBelow`, `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting'_add_le` (upper bound only) (`NumberTheory/PrimeCounting.lean`, `NumberTheory/SmoothNumbers.lean`); `Nat.exists_prime_lt_and_le_two_mul`, `Nat.centralBinom_le_of_no_bertrand_prime` (`NumberTheory/Bertrand.lean`); `Nat.four_pow_lt_mul_centralBinom`, `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.centralBinom_eq_two_mul_choose` (`Data/Nat/Choose/Central.lean`); `Nat.factorization_choose_le_log`, `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_one`, `Nat.prod_pow_factorization_choose`, `Nat.prod_pow_factorization_centralBinom` (`Data/Nat/Choose/Factorization.lean`); `primorial_le_4_pow` (`NumberTheory/Primorial.lean`); `ZMod.euler_criterion`, `ZMod.euler_criterion_units`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.exists_sq_eq_neg_one_iff`, `legendreSym.card_sqrts` (`NumberTheory/LegendreSymbol/Basic.lean`); `sq_eq_sq_iff_eq_or_eq_neg`, `Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff` (`Algebra/Ring/Commute.lean`); `IsCyclic.exists_generator`, `isCyclic_of_prime_card`, `orderOf_eq_card_of_forall_mem_zpowers`, `zmodCyclicMulEquiv` (`GroupTheory/SpecificGroups/Cyclic.lean`); `orderOf_dvd_card`, `pow_card_eq_one` (`GroupTheory/OrderOfElement.lean`); `instance : IsCyclic (ZMod p)ˣ` (`RingTheory/ZMod/UnitsCyclic.lean`, `RingTheory/IntegralDomain.lean`); `Nat.chineseRemainder` (`Data/Nat/ModEq.lean`), `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfFinset` (`Data/Nat/ChineseRemainder.lean`); `Nat.ProbablePrime`, `Nat.FermatPsp`, `Nat.exists_infinite_pseudoprimes` (`NumberTheory/FermatPsp.lean`); `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (`Probability/Moments/SubGaussian.lean`); `Finset.sum_mul_sq_le_sq_mul_sq` (`Algebra/Order/BigOperators/Ring/Finset.lean`); `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`. **Absent from this Mathlib revision:** Miller–Rabin / strong pseudoprimes, any lower bound on `π(x)`, `ZMod.prodEquivPi`, `Nat.powMod`, a density bound for primes `≡ 3 (mod 4)`, a lower bound on `φ(m)/m`.

### §2.1 Efficient computation and adversaries

**Def-21.1 (Algorithm).** An algorithm is a deterministic Turing machine with input and output over `{0,1}`. — Existing: `Turing.FinTM Bool` (bundled finite multi-tape TM, append-only output tape). No work; cite. Deviation already recorded in the complexity library (multi-tape, binary alphabet).

**Def-21.2 (Running time, polynomial time).** `A` runs in time `T` if for all `x`, `A(x)` halts within `T(|x|)` steps; polynomial time if `T(n) = n^c` for some `c`. — Existing: `FinTM.ComputesFunInTime f T`, `Complexity.PolyTimeComputable f` (bound `C·(n+1)^c`), `Complexity.P` (`n^c + 1`). The text's literal `n^c` is degenerate at `n = 0` (`Complexity.DTIME_eq_empty_of_exists_zero`); the campaign uses `C·(n+1)^c` everywhere (brief §2). Cite.

**Def-21.3 (Deterministic computation).** `A` computes `f` if for all `x`, `A(x)` outputs `f(x)`. — Existing: `FinTM.ComputesFunInTime`, `FinTM.Computes`. Cite.

**Rem-22.1 (§2.1.1 hard problems).** (i) Halting is uncomputable; (ii) the time hierarchy gives functions computable in exponential but not polynomial time; (iii) SAT is NP-complete, conjectured not in P. — Existing: `Complexity.HALT_not_computable` (relative to an `EffectiveMachineCode`), `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete`. Cite only.

**Def-23.4 (PPT).** A randomized algorithm is a TM with an extra random tape of uniform independent bits. **Formal (D3):** a structure with a `FinTM Bool` `M`, coin-length constants `(Cr, cr)` and time constants `(Ct, ct)` such that for every `x : List Bool` and every `r : Fin (Cr·(|x|+1)^cr) → Bool`, `M` halts on `pairEncode x (ofFn r)` within `Ct·(|x|+1)^ct` steps; `M.run x r` is its completed output; `M(x)` is the sampler `r ↦ M.run x r` (a `(Fin ℓ → Bool) → List Bool`, directly usable by `uprob`). Deviation: coins are an input component (reading a random tape sequentially is a bounded-cost simulation), and the coin length is an explicit polynomial. — Existing pattern: `FinTM.DecidesWithAdviceInTime` (pair input, time in `|x|`). New file `TCSlib/Complexity/Randomized/PPT.lean`. Difficulty 3 (definition + run/sampler API + basic lemmas `run_eq_of_computesInTime`, determinism via `ComputesInTime.output_unique`).

**Def-23.5 (Running time, randomized).** `A` runs in time `T` if for all `x` and *every* random tape, `A(x)` halts within `T(|x|)` steps (worst case over coins). — Folded into Def-23.4's time clause (the clause quantifies over all `r`). Expected polynomial time is not formalized (plan D8).

**Def-24.6 (PPT computes f).** `A` computes `f` if for all `x`, `A(x) = f(x)` with probability 1 over the random tape. **Formal:** `∀ x r, M.run x r = f x`. Lemma (C7): on a finite uniform coin space `uprob (fun r => M.run x r = f x) = 1 ↔ ∀ r, M.run x r = f x`, so the formal clause is the text's. Difficulty 2. Consequence: `PPT.Computes f → PolyTimeComputable (fun x => f x)`-style bridge is *not* automatic (the machine reads coins); provide `PolyTimeComputable_of_PPTComputes` by hard-wiring the all-zero coin string (`computesFunInTime_pairEncodeFixed`-style prepend of coins is on the wrong side — needs a `pairMapSnd`/`append` closure: `x ↦ pairEncode x 0^{ℓ(|x|)}` is `PolyTimeComputable.pairEncode` of `id` and `polyUnary`-then-zeros). Difficulty 2.

**Rem-24.2 (majority amplification).** If a polynomial-time randomized `A` computes `f` with probability `≥ 1/2 + 1/p(n)` on every input, then running `A` `ℓ(n)` times and taking the most frequent output computes `f` with probability `≥ 1 − 2^{−n}` (Chernoff). — Deferred: needs Thm-188.7/Lem-189.8 and Repetition; nothing in Chapters 2–4 core depends on it (Garg's concrete majority arguments use Chebyshev for pairwise independence). Difficulty 4.

**Def-24.7 (Efficient private-key encryption).** `(Gen, Enc, Dec)` are PPTs; `Gen(1^n)` outputs a key `k`; `Enc_k(m)` for `m ∈ {0,1}^n` outputs `c`; `Dec_k(c)` outputs `m ∈ {0,1}^n ∪ {⊥}`; for all `n` and `m ∈ {0,1}^n`, `Pr[k ← Gen(1^n) : Dec_k(Enc_k(m)) = m] = 1` (over the coins of `Gen` and `Enc`). **Formal:** messages `Fin n → Bool`; keys/ciphertexts `List Bool`; `Enc`/`Dec` receive `pairEncode 1^n (pairEncode k m)` (so their polynomial bounds are in `n`; the text says "polynomial in the size of their inputs" — with `|k| ≤ poly(n)` the two readings agree); `Dec` output decoded as an `n`-bit string or `⊥`. Correctness quantifies over all coin strings (Def-24.6 reading). Asymptotic/Encryption.lean (plan). Difficulty 2. Depends on Def-23.4.

**Def-26.8 (nuPPT).** A sequence `{A_i}` of probabilistic machines with `|A_i| < d(i)` and running time `< d(i)` for a polynomial `d`; `A(x)` runs `A_{|x|}(x)`. Equivalently (text): a uniform PPT with a polynomial-length advice string per input length. **Formal (D4):** a PPT `M` plus `α : ℕ → List Bool` with `|α n| ≤ Ca·(n+1)^ca`, run on `pairEncode (pairEncode x (α |x|)) r`, time `Ct·(|x|+1)^ct` for every `r`. Deviation: the machine-sequence formulation is not formalized. — Existing pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly`. New file `TCSlib/Complexity/Randomized/NonUniform.lean`. Difficulty 3. Note the standing convention "any adversarial algorithm is implicitly nuPPT" (p. 26) governs Defs 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and Assumptions 30.1, 52.2, 53.1.

**Rem-26.2 (equivalence of nuPPT formulations).** Deferred (difficulty 4): `⇒` would use `Turing.timed_universal` with the description `A_{|x|}` as advice; `⇐` hard-wires the advice. Not needed downstream under D4.

**Claim-26.3 (closure calculus; implicit throughout).** The class of nuPPT samplers is closed under: (a) post-composition with `PolyTimeComputable` maps (decoding, projections); (b) pre-composition/pairing with `PolyTimeComputable` maps of the input and of computed strings; (c) using fresh coin segments as uniform strings of polynomial length and as uniform elements of `Fin 2^k`; (d) hard-wiring advice; (e) `T(n)` fresh-coin calls of a nuPPT with "first success" (loop) or concatenated outputs; (f) Boolean tests (equality of strings, `f(z) = y`). — Existing building blocks: `Turing.FinTM.computesFunInTime_comp` (budget `c·(T₁ n + T₂ (T₁ n) + 1)`, needs `Monotone T₂`), `computesFunInTime_cond`, `exists_loopFindTM`/`exists_emitLoopTM` (loop with fuel `R |x|` and per-round body contract), `exists_installCallTM`/`exists_emitCallTM` (callable module with clean seams), `PolyTimeComputable.comp/.pairEncode/.append`, `polyTimeComputable_ite/and/lenEq`, `pairFstD/pairSndD`. The plan's `Closure.lean`/`Repetition.lean` are this item; difficulty 5 for (e) (the plan's named risk), 3 for (a)–(d),(f). Every theorem below depends on it.

### §2.2 One-way functions

**Def-26.1 (Worst-case OWF).** `f : {0,1}* → {0,1}*` is worst-case one-way if (1) some PPT computes `f` on all inputs (equivalently `PolyTimeComputable f`, by Def-24.6 and C7), and (2) there is no nuPPT `A` with `∀ x, Pr_r[f(A(f x; r)) = f x] = 1`. **Formal (D5/Q2):** for a family `f n : (Fin (ℓ n) → Bool) → List Bool`: `¬ ∃ A : NUPPT, ∀ n x, ∀ r, decode_n (A.run (pairEncode 1^n (f n x)) r) is some x' with f n x' = f n x`. Note the text gives `A` only `f(x)`; D5 adds `1^n`. Difficulty 2. Nothing downstream uses it except Rem-27.1.

**Rem-27.1.** "Assuming NP ⊄ BPP, worst-case one-way functions exist; in fact the two are equivalent (show this!)." Deferred (difficulty 5): requires Def-192.12 (BPP) and, with nuPPT adversaries (§2.1.3), the correct class is non-uniform (`NP ⊄ BPP/poly`); the text mixes uniform BPP with non-uniform inverters. Recorded as a text issue; nothing downstream.

**Def-27.2 (Negligible).** `ε` is negligible if `∀ c ∃ n₀ ∀ n > n₀, ε(n) ≤ 1/n^c`; non-negligible if `∃ c` with `ε(n_i) > 1/n_i^c` for infinitely many `n_i`. — Existing: `TCSlib.Cryptography.Negligible` (`∀ c ∃ n₀ ∀ n ≥ n₀, |μ n| < 1/n^c`; equivalent on `[0,1]`-valued functions by shifting `c`), `not_negligible_iff` (`≥` form), `negligible_two_pow_neg` (the example `2^{−n}`), `Negligible.add/mul/mul_pow/const_mul`. Optional one-line bridges `negligible_iff_le`, `not_negligible_iff_lt` if a statement needs the text's inequalities verbatim. The example `n^{−log log n}` is optional.

**Def-27.3 (Strong OWF).** (1) easy: as Def-26.1(1); (2) for every nuPPT `A` there is a negligible `ε` with, for all `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ ε(n)`. **Formal:** `StrongOWF f ℓ := PolyTimeComputable-easy ∧ ∀ A : NUPPT, Negligible (fun n => invProb (f n) (A.inverter n))` where `A.inverter n : List Bool → coins → (Fin (ℓ n) → Bool)` decodes `A`'s output as an `ℓ n`-bit string (wrong length ↦ a fixed default that only lowers the probability — D5 Deviation). — Existing: `invProb` (exactly the per-`n` experiment, with `1^n` "implicit in the fixed types"). Difficulty 3 (definition + the two decoding lemmas + the lemma that the coin space of the experiment is the nuPPT's coin type). Asymptotic/OneWay.lean.

**Rem-28.1 ((t,s,ε)-one-wayness).** The concrete layer's `invProb f A ≤ ε` at one `n` for an adversary of a given size/time *is* this notion; no new declaration. Cite.

**Def-28.4 (Weak OWF).** (1) easy; (2) there is a polynomial `q` such that for every nuPPT `A` and all sufficiently large `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ 1 − 1/q(n)`. **Formal:** `∃ C c, 0 < C ∧ ∀ A, ∃ n₀, ∀ n ≥ n₀, invProb (f n) (A.inverter n) ≤ 1 − 1/(C·(n+1)^c)`. Difficulty 2.

### §2.3 Multiplication, primes, factoring

**Def-29.1 (f_mult).** `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`, else `x·y`, on pairs of `n`-bit numbers (input length `2n`, output in binary). **Formal:** `fmult n : (Fin n → Bool) × (Fin n → Bool) → ℕ` (then `Nat.bits`), or on `Fin (2^n) × Fin (2^n)`. Deviation: the text's `ℕ² → ℕ` "picked uniformly from ℕ²" means `n`-bit numbers. Candidates/Factoring.lean. Difficulty 1. The "easy to compute" clause needs binary multiplication (Q1 hypothesis).

**Rem-29.2 (f_mult not strongly one-way).** The adversary `A(z) = (2, z/2)` for even `z` (else `(0,0)`) inverts with probability `≥ 3/4`. **Text issue:** `z/2` has up to `2n − 1` bits, so `(2, z/2)` is a preimage of a *different input length*; with inputs fixed to `n` bits (D5) this attack is invalid, and no typed attack is given. Deferred (difficulty 2 for the untyped reading, which is outside the campaign's model). Nothing depends on it.

**Def-29.3 (Π_n).** `Π_n = {q | q < 2^n ∧ q prime}`; the uniform distribution on it. **Formal:** `Primes n := {p : Fin (2^n) // (p : ℕ).Prime}` (a `Fintype`), `uprob` over it; cardinality `= Nat.primeCounting' (2^n) = #(Nat.primesBelow (2^n))` (`Nat.primesBelow_card_eq_primeCounting'`). Chebyshev.lean. Difficulty 1. Note `Π_n` contains `2` and small primes, and the text's later "`n`-bit primes" is loose; use `Π_n` consistently (Deviation noted at Thm-51.1).

**Asm-30.1 (Factoring).** For every nuPPT `A` there is a negligible `ε` with `Pr[p ← Π_n; q ← Π_n; N ← pq : A(N) ∈ {p, q}] < ε(n)` for all `n`. **Formal:** `FactoringAssumption := ∀ A : NUPPT, Negligible (fun n => uprob (fun (z : Primes n × Primes n × coins) => decodeℕ (A.run (pairEncode 1^n (bits (p·q))) r) ∈ {p, q}))`. Deviations: `A` receives `1^n` (the text passes only `N`, whose length is `≤ 2n`); `<` vs `≤` immaterial; `p = q` and `p = 2` are allowed by the text (probability `≤ 2n/2^n` by Claim-33.1). Difficulty 2.

**Thm-31.3 (Chebyshev).** For real `x > 1`, `π(x) > x/(2 log₂ x)`. Proof: `X = C(2x, x) = ∏_{p < 2x} p^{ν_p(X)} ≥ 2^x` and `p^{ν_p(X)} ≤ 2x`, so `2^x ≤ (2x)^{π(2x)}`, i.e. `π(2x) ≥ x/log₂(2x) = (1/2)·2x/log₂(2x)`; odd arguments via `π(2x) = π(2x−1)` (`2x` composite for `x ≥ 2`) and monotonicity of `t/log t`. — Existing Mathlib: `Nat.four_pow_lt_mul_centralBinom` (`4^n < n·centralBinom n`, `n ≥ 4`), `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le` (`p^{ν_p(C(n,k))} ≤ n`), `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting`. No lower bound on `π` exists in Mathlib. **Formal statement recommendation:** prove the integer core `2^x ≤ (2x)^{π(2x)}` for `x ≥ 1` (hence `x ≤ π(2x)·⌈log₂(2x)⌉`), derive Claim-33.1 from it, and state the real-logarithm form of the theorem as a corollary (`Real.logb`). Difficulty 4 (3 for the integer core). Text issues: `log` means `log₂`; "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`, strict for `x ≥ 2`); the odd-case step uses `t/log t` increasing for `t ≥ 3`.

**Claim-32.4.** `log(2x)/log p > ν_p(X)`, i.e. `p^{ν_p(X)} < 2x`. **Text issue:** strictness fails (`x = 1, p = 2`); the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is `Nat.pow_factorization_choose_le` (with `Nat.factorization_choose_le_log`). Cite.

**Claim-33.1 (prime density).** For `n ≥ 1`, `|Π_n| ≥ 2^n/(2n)`, i.e. a uniform `x < 2^n` is prime with probability `≥ 1/(2n)`; consequently a uniform pair is a prime pair with probability `≥ 1/(4n²)` (independence: `uprob_prod`/`uprob_pi_forall`). From Thm-31.3's integer core at `x = 2^{n−1}`: `2^{n−1} ≤ π(2^n)·n`. Chebyshev.lean. Difficulty 3. **Text issue:** §2.6.6 (p. 50) claims the probability "exceeds `(2^n/n)/2^n = 1/n`", inconsistent with the `1/(2n)` of §2.3.2 and with Thm 31.3.

**Rem-33.2 (primality testing in P).** The text uses "primality testing can be done in polynomial time" (AKS, [aks04]) in Alg-33.6/37.4 and SamplePrime. **Formal:** hypothesis `PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` in the Q1 bundle (`Nat.decidablePrime` gives the mathematical test; its machine is not available). Deferred (difficulty 5 to discharge). Thms 33.5/36.3 are formalized without it.

**Thm-33.5.** Factoring assumption ⟹ `f_mult` is weakly one-way: with `q(2n) := 8n²`, for every nuPPT `A` and all large `n`, `Pr[x, y ← {0,1}^n : f_mult(A(1^{2n}, xy)) = xy] ≤ 1 − 1/(8n²)`. **Reduction (one-call variant `A″`):** `A″(1^n, N) := fst(A(1^{2n}, N))`. **Concrete lemma (C1):** if `S` is the success event of `A` on uniform `(x, y)` and `E` = "both prime" with `Pr[E] ≥ δ := 1/(4n²)`, then `Pr[S | E] ≥ 1 − (1 − Pr[S])/δ`; with `1 − Pr[S] ≤ 1/(8n²)` this gives `Pr[S | E] ≥ 1/2` (the text's `1/(8n²)` is weaker than what the argument yields). The conditional distribution of `(x, y)` given `E` is uniform on `Π_n × Π_n` (the factoring distribution), and on `E` a successful answer is a factor (Claim-34.1). Asymptotic: `A″` is `A` with a `PolyTimeComputable` projection (Claim-26.3(a)); `≥ 1/2` infinitely often contradicts negligibility (`not_negligible_iff`). "Easy to compute" needs Q1 (`mul`). — Existing: `uprob_and_le_mul`, `uprob_mono`, `uprob_fst`, `uprob_prod`, `uprob_pi_forall`, `not_negligible_iff`. Difficulty 3. Text issues: Alg 33.6 line 7 writes `A(1^n, z′)` (should be `1^{2n}`); the formal theorem uses `A″`, as the text itself suggests.

**Alg-33.6 (A′ / A″).** `A′(z)`: sample `x, y ← {0,1}^n`; if both prime set `z′ := z` else `z′ := xy`; `w ← A(1^{2n}, z′)`; return `w` if both prime. `A″`: always `z′ := z`, always output `w` (no primality test). Formalize `A″` only (plan). Difficulty 1.

**Claim-34.1 (unique factorization step).** If `p, q` are primes and `x′, y′ < 2^n` with `f_mult(x′, y′) = pq`, then `x′ ∈ {p, q}` (and `y′` is the other). Proof: `pq ≠ 1` so `x′, y′ ≠ 1` and `x′y′ = pq`; `x′ ≠ 0`; `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd`. Factoring.lean. Difficulty 2.

### §2.4 Hardness amplification

**Thm-35.1 (weak → strong).** For any weak OWF `f` (with polynomial `q`) there is a polynomial `m` (the proof takes `m(n) = 2n·q(n)`) such that `f′(x₁, …, x_{m(n)}) = (f(x₁), …, f(x_{m(n)}))` on `({0,1}^n)^{m(n)}` is strongly one-way (security parameter `n`, input length `n·m(n)`). — **Existing (concrete, complete):** `OneWay.prodFun f q` (= `f′`), `yaoTry` (= Alg 38.5's `A₀`), `yaoInverter f B T` (= the `T`-fold repetition `A`), `yaoBad` (= complement of `G_n`), `invProb_prodFun_le` (Claim-39.2), `one_sub_invProb_yaoInverter_le` (Claim-39.1), `yao_amplification` (parametric in `a, θ, T`: `(1−a)^q + qθ < μ ⟹ 1 − a − (1−θ)^T ≤ invProb f (yaoInverter f B T)`). **Bridge:** (i) Claim-38.2 instantiates PS10's parameters; (ii) `yaoInverter f (A′ n) T` is a nuPPT: `T = 2n m² p(n)` fresh-coin calls of `A′` (Claim-26.3(e)), `m − 1` evaluations of `f` per call by `f`'s machine (loop with emitted chunks, `exists_emitLoopTM`), uniform `i : Fin m` from coins (Q7: take `m` a power of two), the test `f(z_i) = y` (equality machine), decoding of `A′`'s output tuple; (iii) from "`f′` not strong" obtain `c` and infinitely many `n` with `μ_n ≥ 1/n^c` (`not_negligible_iff`), conclude `invProb f (…) > 1 − 1/q(n)` infinitely often, contradicting Def-28.4; (iv) lengths: `A′` receives `1^{n·m(n)}`; the tuple `(Fin m → Fin n → Bool)` is encoded as the `nm`-bit concatenation (`Fin.appendEquiv`-style equivalence, cf. `owpBitsEquiv` in `Pseudorandom/GeneratorFromPermutation.lean`). Difficulty 4. Asymptotic/OneWay.lean. Text issues (proof): "For each `j ∈ [1, n]`" should be `[1, m]`; the displayed chain with the factor `m` is garbled — the concrete `invProb_prodFun_le` is the correct computation.

**Thm-35.2 (simple security reduction).** If `f` is a strong OWF then `g(x, y) = (f(x), f(y))` (input length `2n`) is a strong OWF. **Concrete lemma (C2, new):** `invProb (pairFun f) A′ ≤ invProb f (pairInverter f A′)` with `pairInverter f A′ u (y, r) := (A′ (u, f y) r).1` — proof exactly as `OneWay.invProb_pad_le` (`uprob_comp_equiv (Equiv.prodAssoc)`, `uprob_mono`); the text's test "`f(a) = u`" is unnecessary for the inequality. Asymptotic: the inverter samples `y`, evaluates `f`, calls `A′`, projects (Claim-26.3(a)–(c)); `1/p(2n)` infinitely often ⟹ non-negligible. Difficulty 3 (1 concrete + 2 bridge). Note `g = prodFun f 2` up to the equivalence `Fin 2 → α ≃ α × α`, so Thm-35.1's machinery also applies but is overkill.

**Thm-36.3 (f_mult amplified).** Factoring assumption and `m_n = 4n³` ⟹ `f′((x₁,y₁), …, (x_m, y_m)) = (f_mult(x₁,y₁), …)` on `({0,1}^{2n})^{m_n}` is strongly one-way. **Reduction (random-planting, one-call; the text's exercise):** `A″(1^n, N)`: sample `i ← [m]` and fresh pairs `(x_j, y_j)` for `j ≠ i`; put `z_i := N`, `z_j := x_j y_j`; call `A(1^{n′}, z⃗)`; output the first component of its `i`-th answer. **Concrete lemma (C3, new; mirror of `invProb_prodFun_le`'s proof with bad set = "pair not both prime"):** `Pr[A″ factors] ≥ (invProb (prodFun fmult m) A − (1 − δ)^m)/m` where `δ = Pr[pair both prime] ≥ 1/(4n²)`: by `uprob_update` planting at position `i` equals the uniform experiment conditioned on pair `i` prime; `sum_uprob_eq_card_mul` makes `i` uniform; `uprob_pi_forall` bounds `Pr[no pair prime] = (1 − δ)^m`; Claim-34.1 turns an inverse into a factor. Then Claim-36.2 and `μ ≥ 1/p(n′)` infinitely often give success `≥ 1/(2 m p(n′))` infinitely often. Deviation: no primality test, planting at a uniform position (instead of "the first prime pair"). Difficulty 3. Depends on Claim-36.2, Claim-34.1, Claim-33.1, Claim-26.3, Q1. Text issues: Alg 37.4 "Output `x′_i`" should output a factor and check it; `n′ = 2n·m(n) = 8n⁴`.

**Claim-36.2.** `(1 − 1/(4n²))^{4n³} = ((1 − 1/(4n²))^{4n²})^n ≤ e^{−n}` (and `e^{−n} ≤ 2^{−n}`, negligible by `negligible_two_pow_neg`). Pattern: `yao_amplification_exp` (`Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`). Concrete.lean. Difficulty 1.

**Alg-37.4.** The random-planting `A′` (above). Difficulty 1.

**Alg-38.5 (A₀ and A).** `A₀(f, y)`: pick `i ← [m]`, fresh `x_j`, `y_j = f(x_j)` for `j ≠ i`, `y_i = y`, call `A′`, output `z_i` if `f(z_i) = y` else `⊥`; `A` runs `A₀` `2nm²p(n)` times and returns the first non-`⊥` answer. — Existing: `OneWay.yaoTry` (coins `(i, xs, r)`), `OneWay.yaoInverter f B T` (first success via `List.foldr`), `yaoInverter_spec`. Cite.

**Claim-38.2 (parameter instantiation).** With `m := 2n q(n)` (or the next power of two, Q7), `p(n) := p′(n·m)`, `a := 1/(2q(n))`, `θ := 1/(2m²p(n))`, `T := 2nm²p(n)`: for all large `n`, `(1 − a)^m + mθ ≤ e^{−n} + 1/(2mp(n)) < 1/p(n)` and `1 − a − (1 − θ)^T ≥ 1 − 1/(2q(n)) − e^{−n} > 1 − 1/q(n)`; hence `yao_amplification` (with `[NeZero m]`, `[Inhabited (Fin n → Bool)]`) yields `invProb f (yaoInverter …) > 1 − 1/q(n)`. Pure real arithmetic; Asymptotic/OneWay.lean. Difficulty 2.

**Claim-39.1.** `Pr[A fails | x ∈ G_n] ≤ (1 − 1/(2m²p(n)))^{2m²np(n)} ≈ e^{−n}`. — Existing: the `(1 − θ)^T` term of `OneWay.one_sub_invProb_yaoInverter_le`. Cite.

**Claim-39.2 (many good elements).** `|G_n| ≥ 2^n(1 − 1/(2q(n)))`, else `A′` would invert `f′` with probability `< 1/(2p(n)) + e^{−n} < 1/p(n)`. — Existing: `OneWay.invProb_prodFun_le` (`μ ≤ (1 − Pr[S])^q + qθ Pr[S]`), used contrapositively inside `yao_amplification`. Cite.

### §2.5 Collections

**Def-41.1 (Collection of OWFs).** `F = {f_i : D_i → R_i}_{i ∈ I}` with: (1) a PPT `Gen` with `Gen(1^n) ∈ I`; (2) a PPT that on input `i` returns a uniformly random element of `D_i`; (3) a PPT computing `f_i(x)` from `(i, x)`; (4) for every nuPPT `A` there is a negligible `ε` with `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y] ≤ ε(n)`. **Formal design (Collections.lean):** a structure `OWCollection` with index strings `i : List Bool`, for each `i` a `Fintype` domain `D i` with an injective encoding `encD i : D i → List Bool` and a total decoder (wrong strings ↦ failure), `f i : D i → List Bool`; `Gen : PPT` (sampler of indices, coin length polynomial in `n`); `Sample : PPT` on input `i` with `PushesUniform (fun r => decode (Sample.run i r))` onto `D i` *or* (Q3) within statistical distance `2^{−n}` of uniform; `Eval : PolyTimeComputable (fun z => f (pairFstD z) (decode (pairSndD z)))`; hardness via a new per-`n` experiment `collInvProb F A n := uprob (fun (r₁, x, ρ) => let i := Gen.run 1^n r₁; f i (decode (A.run (pairEncode 1^n (pairEncode i (f i x))) ρ)) = f i x)` where `x` is uniform in `D i` (a dependent product: use `Σ`-type or the sampler's coins with `PushesUniform`). — Existing: `HardcoreBit.PushesUniform` and `.uprob_eq`, `invProb` (pattern). Difficulty 4 (design-heavy; the dependent-domain probability space is the subtle point — simplest is to define the experiment over `(r₁, r₂, ρ)` with `x := Sample i r₂` and require exact `PushesUniform`, matching the text's "uniformly random element"). Text issues: (4) says "p.p.t. `A`" against the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should read `f_i`; `R_i` is never constrained; "uniformly random element of `D_i`" presupposes `D_i` finite.

**Thm-42.2 (collection ⟺ strong OWF).** (⇐) a strong OWF `f` gives the collection with `Gen(1^n) = 1^n` (index = unary parameter), `D_{1^n} = {0,1}^n`, `f_{1^n} = f n`: difficulty 2 (the text's "`I = {0}`, `D_0 = ℕ`" is sloppy: the domain must depend on `n`; Deviation). (⇒, "left as an exercise") given a collection, `g_n(r₁, r₂) := (i, f_i(x))` with `i = Gen(1^n; r₁)`, `x = Sample(i; r₂)` is a strong OWF with input length `ℓ₁(n) + ℓ₂(n)` (Q2). Proof: `g` is `PolyTimeComputable` from `Gen`, `Sample`, `Eval` (`PolyTimeComputable.comp/.pairEncode`); an inverter `A_g` of `g` gives the collection inverter `A_F(1^n, i, y) := Sample(i; (A_g(1^{ℓ(n)}, pairEncode i y)).2)`: if `g(r₁′, r₂′) = (i, y)` then `Gen(r₁′) = i` and `f_i(Sample(i; r₂′)) = y`; the law of `(i, x)` under uniform `(r₁, r₂)` equals the law in Def-41.1(4) by `PushesUniform.uprob_eq` applied conditionally on `i` (`uprob_prod`). Difficulty 4. Depends on Def-41.1, Def-27.3, Claim-26.3.

### §2.6 Computational number theory

**Fact-42.1.** `(a mod N + b mod N) mod N = (a + b) mod N`, `((a mod N)(b mod N)) mod N = ab mod N`. — `Nat.add_mod`, `Nat.mul_mod`. Cite.

**Alg-43.2 (ExtendedEuclid).** `ExtendedEuclid(a, b)` for `a > b > 0`: if `a mod b = 0` return `(0, 1)`; else `(x, y) ← ExtendedEuclid(b, a mod b)`, return `(y, x − y⌊a/b⌋)`. **Formal:** `extEuclid : ℕ → ℕ → ℤ × ℤ` by well-founded recursion on `b`, plus `extEuclidCalls : ℕ → ℕ → ℕ` (recursive-call count). — Existing: Mathlib `Nat.xgcd`/`Nat.gcdA`/`Nat.gcdB`/`Nat.gcd_eq_gcd_ab` (Bézout, the standard extended Euclid), `ZMod.inv` (computable inverse through `Nat.gcdA`; used by `ZMod.mul_inv_eq_gcd`). The text's variant and its call count are new. Euclid.lean. Difficulty 2.

**Claim-43.3.** If `a > b ≥ 0` and `a < 2^n` then `ExtendedEuclid(a, b)` makes at most `2n` recursive calls. Induction on `n`: if `b < 2^n` the next call is in the hypothesis; if `b ≥ 2^n` then `a mod b < 2^{n+1} − b ≤ 2^n`, so two calls later the hypothesis applies. Difficulty 3. Text issues: case 2 writes `b > 2^n` (should be `≥`); the precondition `b ≥ 0` allows `b = 0`, where the recursion as written swaps arguments once more.

**Claim-44.4.** `gcd(a, b) = gcd(b, a mod b)`. — Lean core `Nat.gcd_rec` with `Nat.gcd_comm`. Cite.

**Claim-44.5 (correctness).** `ExtendedEuclid(a, b) = (x, y) ⟹ ax + by = gcd(a, b)` (strong induction on `b`; the text's regrouping). Difficulty 2. (Mathlib's `Nat.gcd_eq_gcd_ab` is the same statement for `Nat.xgcd`.)

**Rem-43.6.** "Polynomial time in `log a + log b`" at the machine level — deferred (Q1); mathematically Claim-43.3 is the step bound.

**Alg-45.5 (ModularExponentiation).** `r := 1; while x > 0: if x odd then r := r·a mod N; x := ⌊x/2⌋; a := a² mod N; return r`. **Formal:** `modExp a x N` by binary recursion on `x` (`Nat.binaryRec` or strong recursion), with `modExp_eq : N > 0 → modExp a x N = a^x % N` (`Nat.pow_mod`, `Nat.pow_succ`, `Nat.mul_mod`). ModExp.lean. Difficulty 2. No `powMod` exists in this Mathlib revision.

**Thm-45.6.** On `(a, x, N)` with `a ∈ [1, N]`, Alg 45.5 computes `a^x mod N` in time `O(log x · log² N)`. **Formal (optional):** the loop executes at most `⌊log₂ x⌋ + 1` iterations, each with at most two modular multiplications of numbers `< N` (so `≤ 2(⌊log₂ x⌋+1)` multiplications); optionally a `TimeM ℕ` version (`TCSlib/Cryptography/RSA.lean` cost monad) charging `log² N` per multiplication. Machine-level bound deferred (Q1). Difficulty 2. Text issues: the restriction `a ∈ [1, N]` is immaterial; the later remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Alg 45.5 does not have.

**Def-46.7 (Group).** Mathlib `Group`/`CommGroup`. Cite. **Ex-46.1** `(Z_N, +)` = `ZMod N` as `AddCommGroup`. Cite.

**Thm-46.8.** `(Z_N^*, ×)` with `Z_N^* = {x ∈ [1, N−1] | gcd(x, N) = 1}` is a group (closure via Def-46.9/Claim-47.1; inverses via Euclid). — Existing: `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime : (ZMod n)ˣ ≃ {x : ZMod n // Nat.Coprime x.val n}`, `ZMod.unitOfCoprime`, `ZMod.inv_coe_unit`, `ZMod.mul_inv_eq_gcd`. Optional one-line bridge to the text's set (`x.val ∈ [1, N−1]` for `N ≥ 2`). Units.lean. Difficulty 1.

**Def-46.9 (Prime).** `Nat.Prime`. Cite. **Claim-47.1** `p ∣ ab ⟹ p ∣ a ∨ p ∣ b`: `Nat.Prime.dvd_mul`. Cite.

**Claim-47.2 (totient values).** `Φ(p) = p − 1` for prime `p`; `Φ(pq) = (p−1)(q−1)` for distinct primes ("show this by counting"); `|Z_N^*| = Φ(N)`. — `Nat.totient_prime`, `Nat.totient_mul` + `Nat.coprime_primes`, `ZMod.card_units_eq_totient`. Units.lean (one lemma `totient_mul_prime_prime`). Difficulty 1. Text issue: the formula needs `p ≠ q` (`Φ(p²) = p(p−1)`).

**Thm-47.10 (Euler).** `∀ a ∈ Z_N^*, a^{Φ(N)} = 1 mod N`. — `ZMod.pow_totient` (units), `Nat.ModEq.pow_totient`. Cite. **Cor-48.11 (Fermat).** `ZMod.pow_card_sub_one_eq_one`. Cite.

**Cor-48.12.** For `a ∈ Z_N^*`, `a^x ≡ a^{x mod Φ(N)} (mod N)`: write `x = Φ(N)·(x / Φ(N)) + x mod Φ(N)` (`Nat.div_add_mod`) and apply Euler. Units.lean. Difficulty 1 (used by RSA decryption exponent arithmetic). **Rem-48.2** (efficiency "for any `x` given `Φ(N)`") is machine-level: deferred (Q1). **Ex-48.3** (paper-and-pencil example, garbled in the pdftotext): optional `decide`.

**Def-49.1 (L_N, corrected).** For odd `N > 2` write `N − 1 = u·2^j` with `u` odd; `L_N := {α ∈ Z_N | α^{N−1} = 1 ∧ ∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} ∈ {1, −1}}` ("no non-trivial square root of 1 among the intermediate powers"). Primality.lean. Difficulty 2. **Text error:** the text writes "`N = u2^j`" and a condition using `i = j` only, which is vacuous (`α^{u2^{j+1}} = (α^{N−1})² = 1` always and then requires `α^{N−1} = 1`, already assumed).

**Alg-49.13 (Miller–Rabin).** Handle `N = 2` (and even `N`); repeat `t` times: `α ← Z_N`, if `α ∉ L_N` output "composite"; output "prime". **Formal:** a sampler `millerRabin N t : (Fin t → Fin N) → Bool`. Difficulty 2. The membership test "`α ∈ L_N` by repeated squaring with internal checks" is Alg-45.5 instrumented (math: trivial; machine: Q1).

**Thm-49.14.** If `N` is prime the test outputs "prime" (probability 1); if `N` is (odd) composite it outputs "composite" with probability at least `1 − 2^{−t}`. Prime case from Lem-50.15a (core, difficulty 2); composite case from Lem-50.15b via `uprob_pi_forall` (`Pr[all t samples in L_N] = (|L_N|/N)^t ≤ 2^{−t}`) — deferred with the lemma. Text issue: "with probability `1 − 2^{−t}`" should be "at least".

**Lem-50.15a.** `N` odd prime ⟹ `L_N = Z_N^*` (`|L_N| = N − 1`): Fermat gives `α^{N−1} = 1` for `α ≠ 0`; in the field `ZMod N`, `β² = 1 → β = ±1` (`mul_self_eq_one_iff`/`sq_eq_sq_iff_eq_or_eq_neg`). Difficulty 3 (the index bookkeeping). **Lem-50.15b.** `N > 2` odd composite ⟹ `|L_N| ≤ (N−1)/2` (text: `<`): the liars lie in a proper subgroup of `Z_N^*` (with the "largest index" construction for Carmichael numbers) and Lagrange (`Subgroup.card_subgroup_dvd_card`). Deferred (plan), difficulty 5. Text issue: "`N > 2` composite" should say odd composite (even `N` is handled by the base case).

**Rem-49.3 / Rem-50.2.** Infinitely many Carmichael numbers; AKS. Out of scope / deferred. (Mathlib has `Nat.exists_infinite_pseudoprimes` for Fermat pseudoprimes to a fixed base — weaker.)

**Alg-50.16 (SamplePrime).** Repeat `x ← {0,1}^n` until `x` is prime. **Formal (strict PPT, truncated):** `T(n) := 2n²` independent uniform `x_t < 2^n`; output the first prime, else `⊥`. Primality.lean. Difficulty 3. Deviation: expected running time is not formalized; the primality test is `Nat.Prime` (exact) at the concrete layer and `PrimalityFP` (Q6) at the machine layer; with Miller–Rabin instead the output is only statistically close to uniform.

**Lem-51.17.** SamplePrime outputs a uniformly random element of `Π_n` in time `poly(n)`. **Formal:** (i) `Pr[⊥] ≤ (1 − 1/(2n))^{2n²} ≤ e^{−n}` (Claim-33.1, `uprob_pi_forall`, exp bound C8); (ii) conditioned on success the output is uniform on `Π_n` (C4: for i.i.d. uniform draws the first draw landing in `E` is uniform on `E`); (iii) the sampler is a PPT given `PrimalityFP` (loop `exists_loopFindTM` with fuel `2n²`). Difficulty 3 (+4 for (iii)). Text issue: "exceeds `1/n`" (should be `1/(2n)`).

**Thm-51.1 (factoring collection).** `I = ℕ`, `D_i = {(p, q) prime, |p| = |q| = i/2}`, `f_i(p, q) = pq`; factoring assumption ⟹ collection of OWFs. **Formal:** `Gen(1^n) = 1^n` (index `2n`), `D_n = Primes n × Primes n`, `Sample` = two SamplePrime calls (Q3: within `2e^{−n}` of uniform), `Eval` = multiplication (Q1), hardness: an inverter returning `(p′, q′)` with `p′q′ = N` gives a factor (Claim-34.1), so `A_fact(1^n, N) := fst(A(1^n, 1^n, N))`. Factoring.lean. Difficulty 3. Text issue: `D_i` uses exactly-`i/2`-bit primes while Asm-30.1 uses `Π_n`; the formalization uses `Π_n` throughout (Deviation).

### §2.8 Discrete logarithm

**Def-52.1 (Generator).** `g ∈ G` is a generator if `{g, g², …} = G`; `Gen_G` is the set of generators. — `Subgroup.zpowers g = ⊤`, `IsCyclic.exists_generator`, `orderOf_eq_card_of_forall_mem_zpowers`. Cite.

**Rem-52.2.** In a group of prime order every non-identity element is a generator; `Z_p^*` has order `p − 1` (not prime); for a safe prime `p = 2q + 1` the subgroup of squares has prime order `q`; sampling safe primes has no known guarantee. — `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card`; the squares subgroup is `MonoidHom.range (powMonoidHom 2)` of index 2 (Lem-57.1). Optional, difficulty 2. Units.lean.

**Asm-52.2 (DL).** "If `G_q` is a group of prime order `q`, then for every nuPPT `A` there is a negligible `ε` with `Pr[q ← Π_n; g ← Gen_{G_q}; x ← Z_q : A(g^x) = x] < ε(n)`." **Formal design:** a structure `DLGroupFamily` with, for each index `(q, desc)`, a finite group `G` of order `q` with injective string encoding of elements, `PolyTimeComputable` multiplication (hence exponentiation by repeated squaring, Alg-45.5 at the group level), and a PPT index sampler `GenDL(1^n)` returning `(q, g)` with `q ∈ Π_n` prime and `g ≠ 1` (a generator since `|G| = q` prime); the assumption: `∀ A, Negligible (fun n => Pr[(q,g) ← GenDL(1^n); x ← Z_q : A(1^n, q, g, g^x) = x])`. Deviations: `A` receives `q, g` (the text passes `g^x` only); the ideal "`q ← Π_n; g ← Gen_{G_q}`" is replaced by the family's own sampler (the text itself notes that sampling `(q, g)` efficiently is not known in general — Bach/Kalai); exact uniformity of `x ← Z_q` via Q3. Difficulty 3. DiscreteLog.lean. Text issues: `G_q` unspecified; `A(g^x)` lacks `q, g`.

**Thm-52.3 (DL collection).** `I = {(q, g) | q ∈ Π_k, g ∈ Gen_{G_q}}`, `D_i = Z_q`, `R_i = G_q`, `f_{q,g}(x) = g^x`; DL assumption ⟹ collection of OWFs. **Formal:** `Gen = GenDL`, `Sample` = uniform `Z_q` (Q3), `Eval` = exponentiation; hardness: the DL experiment *is* the collection's inversion experiment since `g^{x′} = g^x ⟺ x′ = x` in `Z_q` (`pow_eq_pow_iff_modEq`, `orderOf g = q`). Difficulty 3. Text issues: `R_i = G_p` and `f_{p,g}` typos (`q`); mixes `k` and `n`.

**Claim-53.1 (safe-prime generator test).** For `p = 2q + 1` with `p, q` prime, `g ∈ Z_p^*` is a generator iff `g ≠ ±1` and `g^q ≠ 1`: the order of `g` divides `2q`, so it is `1, 2, q` or `2q`. — `orderOf_dvd_of_pow_eq_one`, `orderOf_dvd_card`, `ZMod.card_units`. Optional, difficulty 2.

**Claim-53.2 (DL functions are permutations).** If `g` generates a group `G` of order `q` then `x ↦ g^x : ZMod q → G` is a bijection. — `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq`. Optional (the "DL is a collection of one-way permutations" remark after Thm 52.3), difficulty 2.

### §2.9 RSA

**Asm-53.1 (RSA).** For every nuPPT `A` there is a negligible `ε` with `Pr[p, q ← Π_n; N ← pq; e ← Z*_{Φ(N)}; y ← Z_N^*; x ← A(N, e, y) : x^e ≡ y (mod N)] < ε(n)`. **Formal:** `Φ(N) := (p−1)(q−1)` (valid for `p ≠ q`; the text's distribution allows `p = q`, where `Φ(p²) ≠ (p−1)²` — restrict to `p ≠ q` or define `Φ` as `Nat.totient N`), `e` uniform in `(ZMod (Φ N))ˣ`, `y` uniform in `(ZMod N)ˣ`, `A` receives `pairEncode 1^n (bits N, bits e, bits y)`, output decoded as a number `x` with `x^e % N = y`. RSA.lean. Difficulty 3.

**Thm-53.2 (RSA collection).** `I = {(N, e) | N = pq, p, q ∈ Π_n, e ∈ Z*_{Φ(N)}}`, `D_i = R_i = Z_N^*`, `f_{N,e}(x) = x^e mod N`; RSA assumption ⟹ collection of OWFs. **Formal:** `Gen`: two SamplePrime calls, `N`, `Φ`, then `e` by rejection sampling over `[0, Φ)` with `gcd(e, Φ) = 1` (needs C9 `φ(Φ)/Φ ≥ 1/(log₂ Φ + 1)` for a polynomial truncation, Q3); `Sample`: rejection sampling of `Z_N^*` (density `≥ 1/4` for `N = pq`); `Eval` = modexp (Q1). Hardness: by Thm-54.3 `x ↦ x^e` is a bijection of `Z_N^*`, so `(e, x^e)` with `x` uniform has the law of `(e, y)` with `y` uniform (`HardcoreBit.pushesUniform_equiv`, `PushesUniform.uprob_eq`); an inverter of `f_{N,e}` is an RSA breaker with the same probability. Difficulty 3. Text issue: the proof's "`{x, e ← Z_N^* : (e, x^e mod N)}`" samples `e` from the wrong group (should be `Z*_{Φ(N)}`).

**Thm-54.3 (RSA is a permutation).** For `e ∈ Z*_{Φ(N)}`, `x ↦ x^e mod N` is a permutation of `Z_N^*` with inverse `y ↦ y^d`, `ed ≡ 1 (mod Φ(N))`: `x^{ed} = x^{cΦ(N)+1} = x` by Euler. — Existing: `ZMod.pow_totient` (units; direct), and the legacy `RSA.rsa_crt_pow`/`RSA.rsa_correctness` (all of `ZMod (p*q)` for `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`, via CRT). Units.lean (or RSA.lean). Difficulty 2.

### §2.10–§2.11 Permutations and trapdoors

**Def-55.1 (Collection of OWPs).** A collection of OWFs with every `f_i` a permutation (`D_i = R_i`, `f_i` bijective). Collections.lean. Difficulty 1.

**Thm-55.2 (RSA ⟹ Factoring).** If some nuPPT `A` factors `N = pq` (random `n`-bit primes) with probability `≥ 1/p(n)` (infinitely often), then `A′` (Alg-55.3) inverts `f_{N,e}` with probability `≥ 1/p(n)` (infinitely often); hence the RSA assumption implies the factoring assumption. **Formal:** `FactoringAssumption` is implied by `RSAAssumption`, proved contrapositively: `A′(1^n, N, e, y)`: `p′ ← A(1^n, N)`, `q′ := N / p′`; if `p′q′ ≠ N` abort; `Φ := (p′−1)(q′−1)`; `d := e^{−1} mod Φ` (`ZMod.inv`, computable by `Nat.gcdA`); output `y^d`. Whenever `A` returns a factor, `A′` succeeds (Thm-54.3), and the law of `N` is the factoring law regardless of `(e, y)` (`uprob_fst`-style marginalization), so `Pr[A′ wins] ≥ Pr[A factors]`. Difficulty 3. Machine-level: Q1 (`divMod`, `xgcd`, `modExp`). Text issue: the factoring assumption's `A` outputs one factor while Alg 55.3 expects the pair (compute the other by division); "running time of `A′` is `A` plus `O(log³ n)`" is a cost-model remark.

**Alg-55.3.** The adversary above. Difficulty 1.

**Def-56.1 (Trapdoor permutations).** `F = {f_i : D_i → R_i}` with (1) each `f_i` a permutation; (2) PPT `Gen(1^n) = (i, t)`; (3) PPT uniform sampler of `D_i`; (4) PPT evaluator; (5) for every nuPPT `A` there is negligible `ε` with `Pr[(i, t) ← Gen(1^n); x ← D_i; y ← f_i(x); z ← A(1^n, i, y) : f_i(z) = y] ≤ ε(n)`; (6) PPT `Inv((i, t), y) = f_i^{−1}(y)` for `y ∈ R_i`. Collections.lean. Difficulty 2. Text issue: "`≤ e(k)`" should be `e(n)`.

**Thm-57.2 (RSA is a TDP collection; "the proof is an exercise").** With `Gen(1^n) = ((N, e), d)`, `ed ≡ 1 (mod Φ(N))`, `f^{−1}_{N,d}(y) = y^d mod N`: under the RSA assumption, RSA is a collection of trapdoor permutations. Proof: (1) Thm-54.3; (2)–(4) as Thm-53.2 plus `d` from Alg-43.2; (5) Thm-53.2; (6) `(x^e)^d = x` (Thm-54.3). RSA.lean. Difficulty 3.

### §2.12 Rabin

**Def-57.0 (QR_p).** `QR_p := {x² mod p | x ∈ Z_p^*}`, as the subgroup `MonoidHom.range (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ)`. QuadraticResidues.lean. Difficulty 1.

**Lem-57.1.** For an odd prime `p`, `QR_p` is a subgroup of `Z_p^*` of order `(p−1)/2`; every `a ∈ QR_p` has exactly two square roots `±x` with `x ≠ −x`. Proof: the squaring homomorphism has kernel `{±1}` (`Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff`), of order 2 since `p` is odd, so the image has order `(p−1)/2` (`Subgroup.card_eq_card_quotient_mul_card_subgroup`, `QuotientGroup.quotientKerEquivRange`); alternatively `legendreSym.card_sqrts` (`#{x | x² = a} = legendreSym p a + 1`) with `ZMod.euler_criterion`. Difficulty 3. **Claim-58.1** (`x² = y² → x = ±y` in `Z_p`): `sq_eq_sq_iff_eq_or_eq_neg`. Cite.

**Thm-58.2.** If `p = 4k + 3` is prime and `y ∈ QR_p`, then `(±y^{k+1})² = y`: with `y = a²`, `(y^{k+1})² = a^{4k+4} = a^{p+1} = a²` by Fermat (`ZMod.pow_card_sub_one_eq_one`, `a ≠ 0`). Difficulty 2.

**Ex-58.3 (exercise).** Square roots modulo `p ≡ 1 (mod 4)` (Tonelli–Shanks/Cipolla). Deferred (difficulty 4): not needed for the Blum-integer Rabin results; needed only for Thm-61.8 (⇐) in the text's generality.

**Thm-58.3 (CRT).** For pairwise coprime `p₁, …, p_k`, `N = ∏ p_i`, the map `y ↦ (y mod p_i)_i : Z_N → ∏ Z_{p_i}` is a bijection. — `ZMod.chineseRemainder` (`k = 2`, ring equivalence; all uses in the chapter have `k = 2`), `Nat.chineseRemainder`, `Nat.chineseRemainderOfList`/`…OfFinset` (general `k`, existence and uniqueness). Cite; an optional `k`-fold ring-equiv bridge by induction (difficulty 2). **Claim-59.1** (explicit inverse `y = Σ_i b_i n_i a_i`, `b_i n_i ≡ 1 (mod p_i)`, two Euclid calls): optional, difficulty 2 (math); machine-level deferred. **Ex-59.2** (`p = 7`, `q = 11`): optional `decide`.

**Def-59.3 (QR_N).** `QR_N := {x² mod N | x ∈ Z_N^*}`. Difficulty 1.

**Thm-59.4.** For `N = pq` (distinct primes) and `x ∈ Z_N^*`, `x ∈ QR_N ⟺ (x mod p ∈ QR_p ∧ x mod q ∈ QR_q)`. Proof: transport squares and units along `ZMod.chineseRemainder` (`Units.map`, `RingEquiv.map_pow`). Difficulty 2. Text issues: "`zinQRq`" typo; the two directions of the proof are labelled backwards.

**Thm-60.5.** For `N = pq` with `p ≠ q` odd primes, squaring on `Z_N^*` is 4-to-1: every `y ∈ QR_N` has exactly four square roots in `Z_N^*`. Proof: roots of `y` correspond under CRT to pairs (root mod `p`, root mod `q`), `2 × 2` by Lem-57.1. Difficulty 3. Text omits `p ≠ q` and oddness (fails for `N = p²` or `p = 2`).

**Cor-60.6.** `|QR_N| = |Z_N^*|/4 = Φ(N)/4`. Fiber counting (`Finset.card_eq_sum_card_fiberwise`). Difficulty 2.

**Claim-60.7 (roots from the factors).** If `a² ≡ y (mod p)` and `b² ≡ y (mod q)` then `s := CRT^{−1}(a, b)` satisfies `s² ≡ y (mod N)`; hence with `p, q` known, square roots modulo `N` reduce to square roots modulo `p` and `q`. Difficulty 2 (math; used by Thm-61.8 (⇐) and Thm-63.10(6)); machine-level deferred (Q1). **Ex-60.8** (`N = 77` example): optional `decide`; the pdftotext numbers are garbled (`71` vs `42`, `(1,5)`, `(0,3)`).

**Thm-61.7 (Rabin collection).** `I = {N = pq | p, q ∈ Π_n}`, `D_N = Z_N^*`, `R_N = QR_N`, `f_N(x) = x² mod N`; factoring ⟹ collection of OWFs. **Formal (Q4):** indices restricted to `p ≠ q` odd (or Blum), with the factoring assumption on the same index distribution; `Gen` as in Thm-51.1 with a `p ≠ q` re-sample; `Sample` = rejection sampling of `Z_N^*`; `Eval` = squaring mod `N` (Q1); hardness = Thm-61.8 (⇒). Rabin.lean. Difficulty 4. Text issue: "`Z_n^*`" for `Z_N^*`.

**Thm-61.8 (Rabin one-way ⟺ factoring).** (⇒ direction of the text, i.e. factoring hard ⟹ Rabin one-way, proved contrapositively) if a nuPPT `A` returns a square root of `y = x²` (`x ← Z_N^*`) with probability `≥ 1/p(n)` infinitely often, then `A′` (Alg-62.9) factors `N` with probability `≥ 1/(2p(n))` infinitely often. Concrete content: Claim-62.2 (the root differs from `±x` half the time) + Claim-62.1 (`gcd(x − z, N)` is then a prime factor). Asymptotic: `A′` samples `x`, squares, calls `A`, tests, takes a gcd (Q1). Difficulty 4. (⇐, "only if": Rabin one-way ⟹ factoring hard, contrapositively) if a nuPPT `A` factors with probability `≥ 1/r(n)` i.o., then `A′(N, y)`: factor, take roots mod `p` and mod `q` (Thm-58.2 — **only for `p ≡ q ≡ 3 (mod 4)`**), combine by Claim-60.7; success `≥ 1/r(n)` i.o. Difficulty 3 for Blum integers; the general case needs Ex-58.3 (text gap). Text issues: mixes `n` and `k`; the "1/2p(k)" bound; the heuristic "A outputs one of the four roots with equal probability" is replaced by the symmetry argument of Claim-62.2.

**Alg-62.9.** `A′(N)`: `x ← Z_N^*`; `y := x² mod N`; `z ← A(1^n, N, y)`; if `z² ≢ y` abort; else output `gcd(x − z, N)`. Difficulty 1.

**Claim-62.1.** For `N = pq` (distinct primes) and `x, z ∈ Z_N^*` with `x² ≡ z² (mod N)` and `z ≢ ±x (mod N)`, `gcd(x − z, N) ∈ {p, q}` (`x − z` taken in `ℤ`, or `(x − z) mod N` in `ℕ`): `N ∣ (x−z)(x+z)` but `N ∤ (x−z)`, `N ∤ (x+z)`, so exactly one of `p, q` divides `x − z` (`Nat.Prime.dvd_mul`, CRT). QuadraticResidues.lean. Difficulty 2.

**Claim-62.2 (symmetry lemma, concrete).** Let `Z : QR_N → ρ → Z_N^*` depend on `x` only through `y = x²` (and coins). Then `Pr_{x, r}[Z(x², r)² = x² ∧ Z(x², r) ∉ {x, −x}] ≥ (1/2)·Pr_{x, r}[Z(x², r)² = x²]`. Proof: let `u := CRT^{−1}(1, −1)` and `σ(x) := ux`; `σ` is a bijection of `Z_N^*` with `σ(x)² = x²` and `σ(x) ∉ {±x}` (for `p, q` odd distinct); the events `S ∧ B` and `S ∧ B∘σ` (`B(x) := Z(x², r) ∈ {±x}`) are disjoint subsets of `S` with equal probability (`uprob_comp_equiv`), so `2·Pr[S ∧ B] ≤ Pr[S]`. New concrete lemma in `Candidates/Concrete.lean`. Difficulty 3. Used by Thm-61.7/61.8 and (with `Z` = the QR root) by Thm-63.10.

**Thm-63.10 (Rabin TDP).** `I = {N = pq | p, q ∈ Π_n, p ≡ q ≡ 3 (mod 4)}`, `D_N = R_N = QR_N`, `Gen(1^n) = (N, (p, q))`, `f_N(x) = x² mod N`, `f^{−1}_{p,q}(y)` = the unique root of `y` in `QR_N`; factoring (on Blum integers) ⟹ collection of TDPs. Components: (1) Claim-63.1; (2) `Gen` samples Blum primes — density of primes `≡ 3 (mod 4)` below `2^n` is **not available** (no Dirichlet-type bound in Mathlib): take `BlumPrimeDensity : |{p ∈ Π_n | p ≡ 3 (mod 4)}| ≥ 2^n/(C(n+1)^c)` as an explicit hypothesis of the `Gen` clause (Q4); (3) `Sample`: square a uniform `r ∈ Z_N^*` — 4-to-1 maps push uniform to uniform (C5); (4) squaring (Q1); (5) hardness: Claim-62.2 with `Z := A`'s answer (the QR root): with `r` uniform in `Z_N^*`, `r ∉ {±x}` half the time, and `gcd(r − x, N)` factors `N` (Claim-62.1); (6) `Inv`: roots mod `p`, `q` by Thm-58.2, select the residues by Euler's criterion (`ZMod.euler_criterion`, exponent `(p−1)/2`), combine by Claim-60.7. Rabin.lean. Difficulty 4. Deviation: factoring assumption restricted to Blum moduli; density hypothesis.

**Claim-63.1 ("future homeworks").** For a Blum integer `N = pq` (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`), every `y ∈ QR_N` has exactly one square root in `QR_N`; hence squaring is a permutation of `QR_N`. Proof: `−1 ∉ QR_p` for `p ≡ 3 (mod 4)` (`ZMod.exists_sq_eq_neg_one_iff`), so of the roots `±a` mod `p` exactly one is a residue; likewise mod `q`; Thm-59.4 selects exactly one of the four roots. QuadraticResidues.lean. Difficulty 3.

### §2.13 Universal one-way function

**Thm-63.1 (universal OWF).** If some (strong) one-way function exists, then the polynomial-time computable `f_universal` of Alg-64.2 is one-way. The proof shows weak one-wayness (with `q(n) = n³`) and invokes Thm-35.1. **Formal (corrected, F2):** `f_univ c (y) := let k := ⌊log₂ |y|⌋; M := y.take k; x := y.drop k; pairEncode M (U(pairEncode (pairEncode (bits ((|y|+1)³)) M) x))` where `U` is the machine of `Turing.timed_universal_concrete c` (output `true :: M(x)` on halting within the budget, `[false]` otherwise), for a fixed `c : EffectiveMachineCode` (exists: `Turing.exists_effectiveMachineCode`) satisfying `∃ A B, ∀ k, c.canonizerTime k ≤ A·2^{B·k}` (so that the simulator's code-dependent coefficient `3|M| + canonizerTime |M| + |serialize| + 2|bits numStates| + 2q₀ + 16 + universalBlockBound + 14`, with `|serialize| ≤ canonizerTime |M|` by output-length ≤ time and `numStates ≤ |serialize|`, is `poly(n)` for `|M| = ⌊log₂ n⌋`). Statement: `(∃ g, StrongOWF g) → WeakOWF (f_univ c)` with `q(n) = n³`, and `StrongOWF (prodFun-amplification of f_univ c)` by Thm-35.1. Proof: Lem-64.3 gives a strong `g′` and a `CodeTM` `M_g` computing it within `c₀·(m+1)²` (≤ `(n+1)³` for large `n`); Claim-65.1: with probability `≥ 1/n` the code field of a uniform `y` is `encode M_g` padded with `true`s (`decode_encode_pad`); on that event `f_univ(y) = pairEncode M (true :: g′(x))` with `x` uniform of length `m = n − ⌊log₂ n⌋`, and an inverse `⟨M′, x′⟩` must have `M′ = M` (the code is part of the output; `pairEncode_injective`) and `g′(x′) = g′(x)`; Claim-65.2 turns "`A` inverts with probability `> 1 − 1/n³` infinitely often" into "the inverter `B(1^m, z) := x′` from `A(1^n, pairEncode M_g (true :: z))` inverts `g′` with probability `≥ 1/n²` at `m(n) = n − ⌊log₂ n⌋` infinitely often" — non-negligible in `m` (`m ↦ n` is recovered by advice or search), contradicting strong one-wayness. — Existing: `Turing.timed_universal`, `timed_universal_concrete`, `universalBlockBound`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `pairEncode_injective`, `OneWay.card_log_bits_le`, `uprob_eq_one_div_card`, `not_negligible_iff`. Universal.lean. Difficulty 5. Text issues: output must include `M` (F2); "hardness amplification construction from §2.3" should be §2.4; `|y|³` budget becomes `(|y|+1)³`.

**Alg-64.2 (f_universal).** Interpret `y` as `⟨M, x⟩` with `|M| = log|y|`; run `M` on `x` for `|y|³` steps; output `M(x)` if it halts, else `⊥`. **Formal:** as above (corrected). Poly-time computability: `y ↦ (y.take ⌊log₂|y|⌋, y.drop ⌊log₂|y|⌋)` needs a new primitive "split at `⌊log₂ |y|⌋`" (`computesFunInTime_lengthBits` gives `bits |y|`, whose length is `⌊log₂|y|⌋ + 1`; difficulty 3), `computesFunInTime_polyBits 1 3` gives `bits ((|y|+1)³)`, `PolyTimeComputable.pairEncode` assembles `U`'s input, `computesFunInTime_comp` runs `U` (its bound is quadratic in the budget times the code-dependent coefficient), and `PolyTimeComputable.pairEncode` prepends `M`. Difficulty 4.

**Lem-64.3.** If `g` is a strong OWF then there is a strong OWF `g′` computable in time `O(n²)`: `g′(⟨a, b⟩) = ⟨a, g(b)⟩` with `|a| = n^c − n`, `|b| = n`. **Formal:** `g′ n (a, b) := (a, g k(n) b)` with `|b| = k(n)` and `|a| = n − k(n)` where `k` is chosen so that the coded machine for `g` runs within the quadratic budget on `b` (if `M_g` runs in `C(k+1)^c` multi-tape, `one_work_tape_binary` gives a one-tape binary machine in `c′(C(k+1)^c+1)²`, so take `n := ` that bound plus `k`, i.e. `k(n) ≈ n^{1/(2c)}`), and a `CodeTM` (`exists_codeTM`) computing `g′` within `c₀(n+1)²`: copy `a` (linear), parse the split (lengths known from `n`), run `M_g` on `b`. Hardness: `OneWay.invProb_pad_le` (`pad`, `padInverter`) + nuPPT closure (sample `a`, call `A`, project). Difficulty 3 (+3 for the machine time analysis). Universal.lean. Note the text's `⟨a, b⟩` pairing is immaterial when the split lengths are fixed by `n`; plain concatenation avoids `pairEncode`'s doubling.

**Claim-65.1 (PickG).** For `n` with `⌊log₂ n⌋ ≥ |encode M_g|`, `Pr_{y ← {0,1}^n}[y.take ⌊log₂ n⌋ = encode M_g ++ 1^{⌊log₂ n⌋ − |encode M_g|}] = 2^{−⌊log₂ n⌋} ≥ 1/n` (`uprob_fst`, `uprob_eq_one_div_card`, `card_log_bits_le`), and on this event `decode (y.take …) = M_g` (`decode_encode_pad`). Difficulty 2.

**Claim-65.2 (union bound).** If `Pr[Invert] > 1 − 1/n³` and `Pr[PickG] ≥ 1/n` then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + 1 − 1/n`, so for `n ≥ 2` `Pr[Invert ∧ PickG] ≥ 1/n − 1/n³ ≥ 1/n³` (text) — and in fact `Pr[Invert | PickG] ≥ 1 − 1/n²`; the `g′`-inverter's success at length `m(n)` is at least this, infinitely often, so not negligible (`not_negligible_iff`; the map `n ↦ n − ⌊log₂ n⌋` is unbounded and non-decreasing with steps `≤ 1`, so infinitely many `n` give infinitely many `m`). Difficulty 2.

### Appendix items Chapter 2 relies on

**App-A.1 (union bound).** `uprob_or_le`, `uprob_exists_le`. Cite. **App-A.2 (Markov, Chebyshev).** `HardcoreBit.uprob_mul_le_uexp` (Markov form), `HardcoreBit.uprob_le_abs_le`. Cite. **App-A.3 (pairwise-independent sampling).** `HardcoreBit.chebyshev_pairwise`, `chebyshev_pairwise_ident` (bits; the appendix states it for `|X_i| ≤ 1`). Cite.

**Thm-188.7 (Chernoff).** For independent `X_1, …, X_n` with `E X_i = μ` and `|X_i| ≤ 1`, `Pr[|Σ X_i − μn| ≥ εn] ≤ 2^{−ε²n}` (the text writes `≥ ε`, dimensionally wrong; constants "chosen for simplicity"). Deferred (difficulty 4): Mathlib's Hoeffding `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` is measure-theoretic (sub-Gaussian MGFs) and would need a `uprob`-bridge; only Rem-24.2/Lem-189.8 use it.

**Lem-189.8 (Majority vote).** `Pr[X_i = b] ≥ 1/2 + 1/p(n)`, `ℓ > p(n)²` ⟹ `Pr[majority = b] > 1 − 2^{??}` (garbled; proof unfinished "…"). Deferred (difficulty 4 via Chernoff; Chebyshev alone gives only `1 − O(1/n)` error with `ℓ = n p(n)²`).

**Thm-189.9 (Cauchy–Schwarz).** `Finset.sum_mul_sq_le_sq_mul_sq`. Cite.

**Def-191.10 (DP).** `Complexity.P`. Cite. **Def-191.11 (NP).** Witness relation `R_L ∈ P`, `|y| ≤ p(|x|)` — `Complexity.NP` (exact length `C(|x|+1)^c`, concatenation) with `Complexity.mem_NP_iff_exists_length_le` (bounded-length paired form). Cite. **Def-192.12 (BPP).** `L ∈ BPP` iff some PPT `M` has `Pr[M(x) = 1] ≥ 2/3` for `x ∈ L` and `Pr[M(x) = 0] ≥ 2/3` for `x ∉ L`. Deferred (difficulty 2 once Def-23.4 exists); only Rem-27.1 uses it.

---

## 3. Text errors and issues (consolidated)

Outright errors (also returned as `text_errors`):

1. **Algorithm 64.2 / Theorem 63.1:** `f_universal(⟨M, x⟩) = M(x)` omits the machine description from the output; the proof ("`A` must invert a hard instance of `g`") is invalid because the inverse may be `⟨M′, x′⟩` with `M′ ≠ M_g`. Correct definition: output `⟨M, M(x)⟩`.
2. **§2.6.5, definition of `L_N`:** "`N = u2^j`" should be `N − 1 = u·2^j`; the second condition is stated with `i = j` only and is vacuous; intended: for all `i < j`, `α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. **Claim 32.4** is false as a strict inequality (`x = 1`, `p = 2`); correct: `p^{ν_p(C(2x,x))} ≤ 2x`.
4. **§2.6.6 (p. 50):** "the probability that a uniformly sampled `n`-bit integer is prime exceeds `1/n`" — Theorem 31.3 (and §2.3.2's own corollary) gives `1/(2n)`.
5. **Theorem 60.5, Corollary 60.6, Theorems 61.7, 61.8, 63.10:** require `p ≠ q` odd primes; `Π_n` contains 2 and the sampling allows `p = q`. Likewise `Φ(pq) = (p−1)(q−1)` (p. 47) and `Φ(N)` in Assumption 53.1 need `p ≠ q`.
6. **Theorem 61.8 (⇐):** needs square roots modulo arbitrary primes, but only `p ≡ 3 (mod 4)` is proved (Theorem 58.2; the rest is "left as an exercise").
7. **Theorem 59.4:** "`zinQRq`" typo; the proof's `⇒`/`⇐` labels are swapped.
8. **Theorem 52.3:** `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; **Assumption 52.2:** `A` receives only `g^x` (needs `q, g`); `G_q` is unspecified.
9. **Theorem 53.2 proof:** "`x, e ← Z_N^*`" samples `e` from the wrong group (`Z*_{Φ(N)}`).
10. **Definition 56.1(5):** "`≤ e(k)`" should be `e(n)`.
11. **Definition 41.1(4):** "p.p.t. `A`" contradicts the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should be `f_i`.
12. **Theorem 42.2 proof idea:** "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n` (`{0,1}^n`).
13. **§2.4.3 proof:** "For each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra factor `m` is garbled.
14. **Algorithm 33.6, line 7:** `A(1^n, z′)` should be `A(1^{2n}, z′)`; **Algorithm 37.4:** "Output `x′_i`" should output a verified factor.
15. **Lemma 189.8:** statement garbled ("`1 − 2??`"), proof unfinished; **Theorem 188.7:** threshold `ε` should be `εn`.
16. **§2.3 attack on `f_mult`:** `A(z) = (2, z/2)` returns a preimage of a different input length; with `n`-bit inputs it does not show `f_mult` is not strongly one-way.
17. **Claim 43.3 case 2:** "`b > 2^n`" should be `b ≥ 2^n`.
18. **Example p. 61 (`N = 77`):** numbers garbled (`71`/`42`, `(1,5)`, `(0,3)`).
19. **Theorem 63.1 proof:** "hardness amplification construction from §2.3" should be §2.4.
20. **Theorem 49.14:** "with probability `1 − 2^{−t}`" should be "at least"; **Lemma 50.15:** "`N > 2` composite" should be odd composite.
21. **p. 27:** "NP ⊄ BPP ⟺ worst-case one-way functions exist (show this!)" mixes the uniform class BPP with the non-uniform adversaries of §2.1.3.
22. **Theorem 45.6 / p. 46:** the remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Algorithm 45.5 does not have.
23. **Theorem 31.3 proof:** "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`).
24. **Theorem 61.8 / 55.2:** mix `n` and `k`; **Theorem 61.7:** `Z_n^*` for `Z_N^*`; **Theorem 51.1:** `D_i` uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.

Non-error sloppiness handled by Deviations: adversaries receive `1^n` everywhere (Assumptions 30.1/52.2/53.1 omit it); dyadic samplers approximate the ideal uniform distributions (Q3); expected polynomial time (SamplePrime) replaced by strict PPT with `2^{−n}` failure; polynomial normal form `C(n+1)^c`.

---

## 4. New concrete-layer lemmas (Garg files are frozen; put these in `TCSlib/Cryptography/Candidates/Concrete.lean` unless noted)

* **C1** `uprob_cond_ge`: for `E, S : α → Prop` with `Pr[E] ≥ δ > 0`, the probability of `S` on the uniform subtype `{a // E a}` equals `Pr[S ∧ E]/Pr[E]` and is `≥ 1 − (1 − Pr[S])/δ` (Thm-33.5). Also the identification of `uprob` on `Primes n × Primes n` with the conditional law on `Fin (2^n) × Fin (2^n)`.
* **C2** `invProb_pairFun_le` (Thm-35.2) — in `Asymptotic/OneWay.lean`.
* **C3** `invProb_prodFun_plant_le`: random-position planting with a bad set (Thm-36.3); may be stated generally enough to re-derive `invProb_prodFun_le`.
* **C4** `first_hit_uniform`: for i.i.d. uniform draws `x_1, …, x_T`, the first `x_t ∈ E` is uniform on `E` conditioned on existence, and `Pr[no hit] = (1 − Pr[E])^T` (Lem-51.17; also the rejection samplers of Q3).
* **C5** `pushesUniform_of_card_fiber`: a map all of whose fibers have the same size pushes uniform to uniform (`QR_N` sampling, Thm-63.10(3)); converse-type lemma for 4-to-1 (Cor-60.6).
* **C6** Claim-62.2 (Rabin symmetry lemma).
* **C7** `uprob_eq_one_iff_forall` (Def-24.6).
* **C8** `one_sub_inv_pow_le_exp_neg`: `(1 − 1/a)^{a·n} ≤ e^{−n}` for `a ≥ 1`, and `e^{−n} ≤ 2^{−n}` (Claim-36.2, Lem-51.17, Claim-38.2).
* **C9** `totient_div_self_ge`: `φ(m)/m ≥ 1/(log₂ m + 1)` for `m ≥ 1` (the `i`-th smallest prime factor is `≥ i + 1`, `∏_{k=2}^{K}(1 − 1/k) = 1/K`) — in `NumberTheory/Units.lean`; needed for sampling `Z*_{Φ(N)}` (Thm-53.2) by truncated rejection.
* **C10** statistical-switch lemma: replacing a sampler by one within statistical distance `δ` changes any success probability by `≤ δ` (Q3; `distAdv_le_statDist` is the model) — in `Asymptotic/Collections.lean`.

## 5. Machine-layer requirements consumed by Chapter 2 (for `Randomized/{Closure,Repetition}.lean`)

* R1 post-processing by `PolyTimeComputable` (decode `n`-bit strings, projections `pairFstD/pairSndD`, numeral decoding) — all theorems.
* R2 pre-processing: `x ↦ pairEncode 1^n (h x)` for `PolyTimeComputable h`; planting a given string into a computed tuple at a coin-chosen position (Thms 35.1, 36.3).
* R3 coin splitting: using disjoint segments of the coin string as independent uniform strings / `Fin 2^k` elements (every reduction).
* R4 advice pass-through (every reduction uses the given nuPPT's advice).
* R5 `T(n)` fresh-coin calls returning the first success (`exists_loopFindTM`): Thm-35.1, SamplePrime, rejection samplers.
* R6 `m(n)` evaluations of a `PolyTimeComputable` function with concatenated outputs (`exists_emitLoopTM`): `prodFun` evaluation in Thms 35.1/36.3/63.1 amplification.
* R7 calling the clocked universal machine with a hard-wired code (`computesFunInTime_pairEncodeFixed`, `computesFunInTime_comp`): Thm-63.1.
* R8 equality test of two computed strings and `ite` (`polyTimeComputable_ite`, `lenEq`): Thm-35.1's `f(z_i) = y`, Alg-62.9's `z² = y`.
* R9 (Q1 bundle) binary arithmetic: `mul`, `divMod`, `xgcd`, `modExp`, comparison, numeral/string decoding; (Q6) primality test. Taken as hypotheses in `Candidates/Arithmetic.lean`.

## 6. Proposed file split (changes to the plan's layout)

* Add `TCSlib/Cryptography/Candidates/Arithmetic.lean` (the Q1/Q6 hypothesis bundle, docstring explaining why it is a hypothesis) and `TCSlib/Cryptography/Candidates/Concrete.lean` (C1, C3–C6, C8). Both under the `Candidates.lean` facade.
* `Candidates/Factoring.lean` (Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Alg-37.4, Thm-51.1) is at risk of exceeding 600 lines: split `Candidates/FactoringAmplified.lean` for Thm-36.3 if needed.
* `NumberTheory/Chebyshev.lean` holds Def-29.3, Thm-31.3, Claim-33.1; `NumberTheory/Primality.lean` holds Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a/b (b sorried under a sketch, deferred), Alg-50.16, Lem-51.17.
* `Asymptotic/Universal.lean` holds Thm-63.1, Alg-64.2, Lem-64.3, Claims 65.1–65.2, plus the new log-split primitive if it is not placed in a `Complexity/Randomized` helper (it is a deterministic machine; placing it in `Complexity/TuringMachine/Build/` would touch frozen files — put it in `Asymptotic/Universal.lean` as a private construction or in a new `Complexity/Randomized/Primitives.lean`).
* Definitions 24.7 (Encryption.lean) and 192.12 (PPT.lean, deferred) sit outside the Chapter-2 files as the plan prescribes.

## 7. Build order (dependencies)

PPT.lean → NonUniform.lean → Closure.lean/Repetition.lean → Asymptotic/OneWay.lean (Defs 26.1, 27.3, 28.4; Thms 35.2, 35.1 with Claim-38.2) → Asymptotic/Collections.lean (Defs 41.1, 55.1, 56.1; Thm 42.2) → NumberTheory/{Chebyshev, Euclid, ModExp, Units, Primality, QuadraticResidues}.lean (independent of the machine layer except Lem-51.17(iii)) → Candidates/{Arithmetic, Concrete, Factoring, DiscreteLog, RSA, Rabin}.lean → Asymptotic/Universal.lean (needs OneWay.lean, Thm-35.1, and the universal machine).
