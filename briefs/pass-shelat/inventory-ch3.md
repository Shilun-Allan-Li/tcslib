# Inventory — [PS10] Chapter 3, *Indistinguishability & Pseudo-Randomness* (§3.1–§3.12, plus the appendix facts its proofs cite)

Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-shelat-2010-ch3.raw.md`
(pdftotext; results numbered `<page>.<counter>`). Read-only on Lean; this file is the planners' input.

## 0. How to read this file

* **Ids.** Numbered results keep the book's number (`Def-69.4`, `Lem-71.6`, `Thm-87.3`, `Alg-92.1`,
  `Asm-105.1`). Unnumbered but substantive claims get a synthetic id `<Kind>-<page>.<letter>`
  (e.g. `Claim-73.a` = the "show this!" on p. 73). Proof cases and lemmas inside a proof are
  `<parent>.<n>` (e.g. `Thm-87.3.4`).
* **Quantifier conventions used in every statement below** (fixed by the plan, D3–D7):
  `n` is the security parameter; strings of length `n` are `Fin n → Bool`; an *ensemble* `X` is a
  family `X n : (Fin (s n) → Bool) → (Fin (ℓ n) → Bool)` of samplers from uniform coin strings of
  explicit polynomial length (D6); **PPT** = `FinTM Bool` run on `pairEncode x r`, worst-case time
  over all coin strings, computes a function when the output is the same for every coin string
  (D3); **nuPPT** = PPT + advice string `α n` of explicit polynomial length (D4); "`D` distinguishes
  `X n, Y n` with probability `ε`" means `distAdv (X n) (Y n) D > ε`; "negligible" is
  `TCSlib.Cryptography.Negligible`; "non-negligible" = `¬ Negligible`, equivalently (by
  `not_negligible_iff`) `∃ c, ∀ n₀, ∃ n ≥ n₀, 1/n^c ≤ |μ n|` ("infinitely often").
* **Concrete vs asymptotic.** Every theorem is a concrete reduction (one `n`, exact inequality,
  adversaries are plain functions of input and coins — mostly already proved in the Garg layer,
  namespace `TCSlib.Cryptography`) *plus* an asymptotic wrapper: (i) instantiate the concrete
  reduction at each `n`, (ii) show the reduction is an nuPPT by closure lemmas, (iii) negligible
  arithmetic. The column *existing Lean* names what is proved; *reuse note* says what the bridge
  must add.
* **Scope.** `core` = mandatory (plan's content or needed downstream); `optional` = feasible and
  worthwhile; `deferred` = stated without proof in the text and nothing downstream needs it, or
  out of reach.
* **Difficulty** 1 trivial … 5 research-level fill (for the asymptotic statement including its
  concrete part, unless the item is marked "concrete only").

### External dependencies referred to by label (not chapter-3 items)

| Label | Meaning | Where it will live |
| --- | --- | --- |
| `Machine-PPT` | D3: `PPT` structure, run/sampler semantics `run M n : (Fin (coins n) → Bool) → List Bool`, `ComputesFun` (same output for every coin string), typed decoding of outputs (`List Bool` → `Fin m → Bool`, wrong length = failure/`false`) | `TCSlib/Complexity/Randomized/PPT.lean` |
| `Machine-NUPPT` | D4: nuPPT = PPT + advice `α n` of length `Cα (n+1)^cα`, run on `pairEncode (pairEncode x (α |x|)) r`; Boolean output `decide (out = [true])` | `Randomized/NonUniform.lean` |
| `Machine-Closure` | pre/post-composition with a PPT, pairing of inputs, hard-wiring a per-`n` constant (index `i`, message `m_n`, sign bit) into advice, drawing extra coins, a PPT is an nuPPT | `Randomized/Closure.lean` |
| `Machine-Repetition` | polynomially many calls of an nuPPT with fresh coins and a post-processing (majority, list, XOR) — the load-bearing lemma for GL, DL, multi-message | `Randomized/Repetition.lean` |
| `Machine-Loop` | iterate a PPT-computable function `poly(n)` times (PRG expansion, GGM evaluation, Shamir/Blum–Micali) | `Randomized/Repetition.lean` (or Closure) |
| `Machine-Primitives` | poly-time string primitives not yet in `Build/Primitives.lean`: bitwise XOR of two equal-length strings, inner product mod 2, majority of a bit list, string equality, `Fin.cons`/`append`/truncation on tapes, unary/binary length bookkeeping | `TCSlib/Complexity/Randomized/Primitives.lean` (new) |
| `Ensemble-D6` | `Ensemble` structure (seed length, output length as explicit polynomials, sampler), `Samplable X` (sampler is a PPT) | `Asymptotic/Ensembles.lean` |
| `Oracle-D7` | nuPPT oracle adversaries: an nuPPT that *drives* a `QueryTree` (next query / final bit computed by the machine from `1^n`, coins, and the transcript so far), query bound `q(n)` explicit polynomial | `Asymptotic/PRF.lean` |
| `Def-24.7` | private-key encryption scheme (Gen PPT, Enc PPT, Dec PPT, correctness w.p. 1), ch. 2 inventory | `Asymptotic/Encryption.lean` |
| `Def-27.3`, `Def-41.1`, `Def-55.1`, `Def-56.1` | strong OWF; collection of OWFs; OWP collection; trapdoor permutations (ch. 2) | `Asymptotic/OneWay.lean`, `Asymptotic/Collections.lean` |
| `Asm-52.2`, `Thm-52.3`, `Thm-58.2`, `Thm-45.6` | DL assumption; the DL collection; square roots mod `p ≡ 3 (4)`; repeated squaring (ch. 2) | `Candidates/DiscreteLog.lean`, `NumberTheory/*` |
| `OWP-single` | a *single* one-way permutation `f n : (Fin n → Bool) ≃ (Fin n → Bool)`, PPT-computable, one-way (Def 27.3) — the text's "let `f` be a one-way permutation" in Thm 79.4 / Cor 81.7 / Thm 87.3 / ch. 4 Thm 126.4 | `Asymptotic/OneWay.lean` (ch. 2 inventory should define it; flagged here) |

### Proposed file split for chapter 3 (refines the plan's layout)

| File | Contents | Why it differs from the plan |
| --- | --- | --- |
| `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def 69.3, 69.4, the "distinguishes with probability" notations, Lem 71.5, Lem 71.6, Rem 72.7, Claim 72.a, Ex 72.b, Claim 73.a, Lem 73.8, quantifier bridge | as planned |
| `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean` | Def 74.1, 75.2 (+Rem 75.3), Def 77.1, Claim 67.a, next-bit soundness (Thm-75.4.conv), asymptotic Thm 75.4 | as planned, minus the concrete next-bit reduction |
| `TCSlib/Cryptography/Asymptotic/NextBit.lean` (**new**) | concrete next-bit reduction: hybrids `H^i`, flipped hybrid, mixing identity, Alg 76.5, exact bound `1/2 + ε/ℓ` | the Garg layer has no next-bit material; the frozen `Pseudorandom/` tree (and its facade) must not be edited, so the new concrete reduction lives in the campaign's tree |
| `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def 78.3 (single + collection), Thm 79.4, Claim 79.a, Lem 80.5, Cor 81.7, Shamir remarks, Thm 87.3 (a: padding, b: GL asymptotic, collection version) | as planned |
| `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean` (**new**) | Lem 84.1 and its sub-items (Alg 84.2, NT facts, majority test, range reduction) | Lemma 84.1 alone is 400+ lines of concrete reduction; keep `Candidates/DiscreteLog.lean` for Asm 52.2/Thm 52.3 |
| `TCSlib/Cryptography/Asymptotic/Encryption.lean` | Def 91.1 (on Def 24.7), Alg 92.1, Claim 92.a (OTP), Thm 92.2, Def 93.1, Thm 94.2 | as planned |
| `TCSlib/Cryptography/Asymptotic/PRF.lean` | random functions (Def 95.a, Claim 95.b), Def 96.1, Claim 96.a–c, Def 96.2, Cor 97.a (WLOG length-doubling), GGM evaluation is PPT, Thm 97.3 | as planned |
| `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (**new**) | Alg 99.1, Thm 99.2 (concrete: PRF reduction, collision bound, OTP) | Thm 99.2's concrete proof is new and long; separate from PRF.lean to respect the 600-line guideline |
| `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def 102.1, 102.2, Claims 103.a–b, Def 103.c, Thm 103.d, Def 103.e, Thm 103.f, Alg 104.3, Lem 104.a, Thm 104.4 | as planned |
| `TCSlib/Cryptography/Candidates/ElGamal.lean` (**new**) | Asm 105.1 (relative to a group generator), NT 105.a (safe primes, `G_q`), Claim 106.a (DDH ⇒ DL), Alg 106.2, Claim 107.a, Thm 107.3, Def 107.b (message encoding) | number theory + a concrete assumption belong with the candidates, not in PublicKey.lean |
| (appendix) | Thm 188.7, Lem 189.8, pairwise-independent sampling — all replaced by existing `chebyshev_pairwise` / `uprob_majority_fails_le`; Chernoff optional in `Asymptotic/Chernoff.lean` if ever needed | — |

## 1. Inventory table

Legend: scope C = core, O = optional, D = deferred. "Garg" = concrete layer already proved (namespace
`TCSlib.Cryptography`, source tag `[Gar26]`). Full statements, reuse notes and text issues are in §2.

| Id | Kind | § | Title | Scope | Diff | Proposed file | Existing Lean (concrete) | Depends on |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Claim-67.a | claim (show this) | 3.0 | no generator makes a perfectly random longer string | O | 2 | Asymptotic/Pseudorandom.lean | `statDist`, `distAdv_le_statDist` | — |
| Def-69.3 | definition | 3.1 | ensembles of distributions | C | 2 | Asymptotic/Ensembles.lean | samplers `σ → γ` (Experiments.lean) | Ensemble-D6 |
| Def-69.4 | definition | 3.1 | computational indistinguishability `≈`; "distinguishes with probability ε / μ(·)" | C | 2 | Asymptotic/Ensembles.lean | `distAdv`, `Negligible` | Def-69.3, Machine-NUPPT |
| Lem-71.5 | lemma | 3.1.1 | closure under efficient operations | C | 3 | Asymptotic/Ensembles.lean | `sunglassRed`, `distAdv_sunglassRed`, `pushSampler`, `distAdv_comp` | Def-69.4, Machine-Closure |
| Lem-71.6 | lemma | 3.1.1 | hybrid lemma | C | 1 | Asymptotic/Ensembles.lean | `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `mixDist`, `distAdv_mixDist_eq` | — |
| Rem-72.7 | remark | 3.1.1 | acceptance probability is a pseudometric; hybrid = triangle inequality | O | 1 | Asymptotic/Ensembles.lean | `abs_sub_le` | — |
| Claim-72.a | claim | 3.1.1 | a long chain of pairwise-indistinguishable distributions with distinguishable ends | O | 2 | Asymptotic/Ensembles.lean | `distAdv_le_statDist` | Def-69.4 |
| Ex-72.b | example | 3.1.1 | `{x⊕y}` ≈ `{z⊕y}` for pairwise-indistinguishable samplable `X,Y,Z` | O | 2 | Asymptotic/Ensembles.lean | `distAdv_sunglassRed` | Lem-71.5, Ensemble-D6 |
| Claim-73.a | claim (show this) | 3.1.1 | a predictor is a distinguisher (converse of 73.8; same identity) | C | 2 | Asymptotic/Ensembles.lean | `uprob_bool_prod` (GeneratorFromPermutation.lean) | Def-69.4 |
| Lem-73.8 | lemma | 3.1.1 | prediction lemma | C | 3 | Asymptotic/Ensembles.lean | `uprob_bool_prod`; pattern of `predProb_owpPredictor_false/true`, `exists_owpPredictor` | Def-69.4, Machine-Closure |
| Claim-73.b | implicit | 3.1 | "for infinitely many n with 1/p(n)" ⇔ non-negligible | C | 1 | Asymptotic/Ensembles.lean | `not_negligible_iff`, `Negligible.mono` | — |
| Def-74.1 | definition | 3.2.1 | pseudorandom ensembles | C | 1 | Asymptotic/Pseudorandom.lean | `prgAdv` (= `distAdv G id`) | Def-69.4 |
| Def-75.2 | definition | 3.2.2 | next-bit test | C | 2 | Asymptotic/Pseudorandom.lean | — | Def-69.3, Machine-NUPPT |
| Rem-75.3 | convention | 3.2.2 | predictor receives `1^n` | C | 1 | Asymptotic/Pseudorandom.lean | — | Def-75.2 |
| Thm-75.4 | theorem | 3.2.2 | completeness of the next-bit test (asymptotic) | C | 4 | Asymptotic/Pseudorandom.lean | — | Thm-75.4.c, Lem-71.6, Lem-73.8, Machine-Closure |
| Thm-75.4.c | theorem (concrete) | 3.2.2 | next-bit reduction: `∃ i < ℓ, ∃ flip`, predictor success `≥ 1/2 + ε/ℓ` | C | 4 | Asymptotic/NextBit.lean | `exists_hybrid_gap`, `acceptProb_update`, `uprob_bool_prod`, `prgHybrid` (pattern) | — |
| Thm-75.4.1 | hybrid def | 3.2.2 | hybrids `H^i_n = x_1…x_i u_{i+1}…u_ℓ` with `H^0 = U_ℓ`, `H^ℓ = X_n` | C | 2 | Asymptotic/NextBit.lean | pattern `prgHybrid`, `multicopyHybrid` | — |
| Thm-75.4.2 | claim | 3.2.2 | mixing identity `H^i = ½ H^{i+1} + ½ H̃^{i+1}` | C | 2 | Asymptotic/NextBit.lean | `acceptProb_id_owp` (same trick), `uprob_bool_prod` | Thm-75.4.1 |
| Alg-76.5 | algorithm | 3.2.2 | next-bit predictor `A'(1^n, t_1…t_i)` from a distinguisher | C | 2 | Asymptotic/NextBit.lean | pattern `owpPredictor` | Thm-75.4.2 |
| Thm-75.4.conv | claim (implicit) | 3.2.2 | soundness: pseudorandom ⇒ passes the next-bit test | O | 2 | Asymptotic/Pseudorandom.lean | `distAdv_comp` | Def-75.2, Claim-73.a |
| Def-77.1 | definition | 3.3.1 | pseudorandom generator | C | 2 | Asymptotic/Pseudorandom.lean | `prgAdv` | Def-74.1, Machine-PPT |
| Constr-77.a | construction | 3.3.2 | Shamir's generator `f^n(s)‖…‖f(s)‖s` | O | 1 | Asymptotic/HardCore.lean | — | OWP-single |
| Claim-78.a | claim | 3.3.2 | iterates of a permutation on a uniform seed are uniform | O | 1 | Asymptotic/HardCore.lean | `uprob_comp_equiv`, `acceptProb_comp_equiv` | — |
| Claim-78.b | claim | 3.3.2 | unpredictable *numbers* need not give unpredictable *bits* (a OWP may fix bits) | O | 2 | Asymptotic/HardCore.lean | `predProb_positionBit`, `predProb_fixedBitPredictor` (NoFixedBit.lean) | — |
| Def-78.3 | definition | 3.3.3 | hard-core predicate for a function `f` | C | 2 | Asymptotic/HardCore.lean | `predProb` | Machine-NUPPT, Machine-PPT |
| Def-78.3.coll | definition (unnumbered, needed) | 3.3.3 | hard-core predicate for a collection `{f_i}` | C | 2 | Asymptotic/HardCore.lean | `predProb` (indexed sampler) | Def-41.1, Def-78.3 |
| Claim-78.c | claim (stated, unproved) | 3.3.3 | LSB and `half_N` are hard-core for RSA | D | 5 | — | — | — |
| Thm-79.4 | theorem | 3.3.4 | `G(s) = f(s)‖h(s)` is a PRG for a OWP `f` with hard-core `h` | C | 3 | Asymptotic/HardCore.lean | `owpGen`, `owpPredictor`, `exists_owpPredictor`, `exists_owpPredictorBits`, `prgAdv_comp_equiv` | Def-77.1, Def-78.3, OWP-single, Machine-Closure |
| Claim-79.a | claim (in proof) | 3.3.4 | the first `n` bits of `G(s)` are uniform; next-bit predictors for positions `≤ n` succeed w.p. exactly `1/2` | O | 2 | Asymptotic/HardCore.lean | `uprob_comp_equiv` | Claim-78.a |
| Lem-80.5 | lemma | 3.3.5 | expansion of a one-bit-stretch PRG to `ℓ(n)` bits | C | 3 | Asymptotic/HardCore.lean | `prgExt`, `prgExtBits`, `prgExtRed`, `exists_prgExtRed_ge`, `exists_prgExtBitsRed_ge`, `prgExtAvgRed`, `prgAdv_prgExtAvgRed`, `distAdv_comp` | Def-77.1, Lem-71.5, Lem-71.6, Machine-Loop |
| Cor-81.7 | corollary | 3.3.5 | `G(x) = h(x)‖h(f(x))‖…‖h(f^{ℓ}(x))` is a PRG | C | 2 | Asymptotic/HardCore.lean | `prgExt` closed form `(G ((prgStep G)^[i] s)).1`, `prgExt_succ` | Thm-79.4, Lem-80.5 |
| Constr-82.a | construction (unproved) | 3.3.5 | PRG from a *collection* of OWPs, `G(r_1,r_2)` | D | 3 | Asymptotic/HardCore.lean | `prgExt` (needs a non-uniform-seed generalization) | Def-55.1, Def-78.3.coll |
| Constr-82.b | construction (unproved) | 3.3.6 | Blum–Micali PRG (modular exponentiation, `half_{p-1}`) | D | 3 | Candidates/DiscreteLogHardcore.lean | — | Lem-84.1, Constr-82.a |
| Constr-83.a | construction (unproved) | 3.3.6 | RSA PRG (`LSB`) | D | 5 | — | — | Claim-78.c |
| Constr-83.b | construction (unproved) | 3.3.6 | Blum–Blum–Shub (`LSB`, squaring mod `N`) | D | 5 | — | — | — |
| Claim-83.c | claim (unproved) | 3.3.6 | `log n` bits per iteration remain secure | D | 5 | — | — | — |
| Lem-84.1 | lemma | 3.4.1 | `half_{p-1}` is hard-core for `f_{p,g}(x) = g^x mod p` under DL | C | 5 | Candidates/DiscreteLogHardcore.lean | `uprob_majority_fails_le`, `chebyshev_pairwise`, `half_le_uprob_threshold`, `uprob_exists_le`, Mathlib `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.euler_criterion`, `IsCyclic (ZMod p)ˣ` | Asm-52.2, Thm-52.3, Thm-58.2, Thm-45.6, Machine-Repetition, Lem-84.1.1–.5 |
| Lem-84.1.0 | claim | 3.4.1 | `half_{p-1}` is PPT-computable from `x` | C | 1 | Candidates/DiscreteLogHardcore.lean | — | Machine-PPT |
| Lem-84.1.1 | number theory | 3.4.1 | for a generator `g` of `Z_p^*`: `g^{(p-1)/2} = -1`; `y = g^{2x}` has exactly the roots `g^x, g^{x+(p-1)/2}`; `y` is a square iff its DL is even | C | 2 | Candidates/DiscreteLogHardcore.lean | Mathlib `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.euler_criterion`, `orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient` | — |
| Alg-84.2 | algorithm | 3.4.1 | bit-by-bit DL from a perfect `half` oracle; correctness | C | 3 | Candidates/DiscreteLogHardcore.lean | — | Lem-84.1.1 |
| Alg-85.a | algorithm | 3.4.1 | randomized majority test replacing line 8 (`z_i = y_{k-1} g^{r_i}`, count `lo`) | C | 3 | Candidates/DiscreteLogHardcore.lean | `majority`, `uprob_majority_fails_le`, `pairwiseUniform_eval` | Alg-84.2 |
| Lem-84.1.3 | claim | 3.4.1 | `Pr[noinc | low] ≤ 1/2 − ε/2` (re-randomization error `≤ ε/2`) for instances with DL in `[0, εp/4]` | C | 3 | Candidates/DiscreteLogHardcore.lean | `uprob_or_le`, `pushesUniform_add_right` | Alg-85.a |
| Lem-84.1.4 | claim (gap: "as we will show later") | 3.4.1 | range reduction: solving DL on `[0, εp/4]` solves DL w.p. `≥ ε/4 − negl` | C | 3 | Candidates/DiscreteLogHardcore.lean | `uprob_eq_one_div_card` | Alg-85.a |
| Lem-84.1.5 | claim (missing in text) | 3.4.1 | good-instance argument: success `1/2+ε` averaged over `(p,g,x)` gives `≥ ε/2` fraction of `(p,g)` with per-instance success `≥ 1/2+ε/2`; union bound over the `|p|` rounds | C | 3 | Candidates/DiscreteLogHardcore.lean | `half_le_uprob_threshold`, `uprob_exists_le` | — |
| Thm-87.3 | theorem | 3.4.2 | Goldreich–Levin: `g(x,r) = (f(x), r)` is a OWF (OWP) and `⟨x,r⟩` is hard-core for `g` | C | 4 | Asymptotic/HardCore.lean | see .a/.b | Thm-87.3.a, Thm-87.3.b |
| Thm-87.3.a | claim | 3.4.2 | `g` is one-way (and a permutation if `f` is) | C | 2 | Asymptotic/HardCore.lean | `OneWay.pad`, `OneWay.padInverter`, `OneWay.invProb_pad_le` (OutputLength.lean); `HardcoreBit.glPad` | Def-27.3, Machine-Closure |
| Thm-87.3.b | claim | 3.4.2 | `⟨x,r⟩` is hard-core for `g` (general case, asymptotic) | C | 4 | Asymptotic/HardCore.lean | `HardcoreBit.glBit`, `guessInverter`, `invProb_guessInverter`, `invProb_guessInverter_cubic` | Thm-87.3.c, Thm-87.3.1–.9, Machine-Repetition, Machine-Primitives |
| Thm-87.3.c | definition | 3.4.2 | the setting `g`, `h = ⟨·,·⟩`, inverters keeping `r`, per-`x` success `secProb` | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `ip`, `glPad`, `glBit`, `glInverter`, `secProb`, `predProb_glPad_eq` | — |
| Thm-87.3.1 | proof case | 3.4.3 | oversimplified case: perfect predictor ⇒ perfect inverter (queries `e_i`) | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `perfectRecover`, `perfectInverter`, `invProb_perfectInverter`, `ip_single` | — |
| Thm-87.3.2 | proof case | 3.4.3 | less simplified case `3/4 + ε`: pairs `(r, r ⊕ e_i)`, majority of `m` trials, success `≥ ε/4` | C | 1 | (exists) HardcoreBit/ThreeQuarters.lean | `trialBit`, `majorityRecover`, `majorityInverter`, `trialBit_correct`, `uprob_majorityRecover_ne_le`, `invProb_majorityInverter` | — |
| Thm-87.3.3 | claim | 3.4.3 | good set `S`: `Pr[x ∈ S] ≥ ε/2` (both thresholds `3/4`, `1/2`) | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `half_le_uprob_good`, `half_le_uprob_threshold` | — |
| Fact-88.4 | fact | 3.4.3 | `⟨a, b ⊕ c⟩ = ⟨a,b⟩ ⊕ ⟨a,c⟩` | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `ip_add`, `ip_sum` | — |
| Alg-88.5 | algorithm | 3.4.3 | `B(y)` for the less simplified case | C | 1 | (exists) HardcoreBit/ThreeQuarters.lean | `majorityInverter` | — |
| Alg-89.6 | algorithm | 3.4.3 | `B(y)` for the general case with subroutine `C` producing `(⟨x,r_j⟩, r_j)` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `guessRecover`, `guessInverter`, `idealRecover`, `GuessCoins` | — |
| Thm-87.3.6 | claim | 3.4.3 | with pairwise-independent samples each `x_i` is wrong w.p. `≤ 1/(4mε'^2)`; union bound over `n` bits gives `< 1/2` when `m ≥ 2n/ε'^2` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `uprob_idealRecover_ne_le`, `one_sub_sum_le_uprob_eq` | — |
| Thm-87.3.7 | claim (show this!) | 3.4.3 | subset sums `r_I = ⊕_{j∈I} s_j` over nonempty `I ⊆ [log m]` are pairwise independent and uniform | C | 1 | (exists) HardcoreBit/PairwiseIndependence.lean | `subsetSum`, `pairwiseUniform_subsetSum`, `card_nonempty_finset` | — |
| Thm-87.3.8 | claim | 3.4.3 | all `log m` guesses `b'_j` are right w.p. `1/m`; then every `b_I` is right | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `uprob_guess_eq`, `guessRecover_correct_guess`, `uprob_guessRecover_ge` | — |
| Thm-87.3.9 | claim | 3.4.3 | final bound: `B` inverts w.p. `ε'/(2m) = (ε/2)^3/(4n)` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `invProb_guessInverter` (`ε/(4·2^k)`), `invProb_guessInverter_cubic` (`ε^3/(16n)`) | — |
| Thm-87.3.coll | theorem (needed by 104.4, ch.4) | 3.4.2 | GL for a collection: `g_i(x,r) = (f_i(x), r)`, `⟨x,r⟩` hard-core for the collection | C | 3 | Asymptotic/HardCore.lean | the per-`i` concrete theorems + `half_le_uprob_threshold` over `i` | Thm-87.3.b, Def-41.1, Def-78.3.coll |
| Def-91.1 | definition | 3.5 | single-message secure (private-key) encryption | C | 2 | Asymptotic/Encryption.lean | `distAdv` | Def-24.7, Machine-NUPPT |
| Alg-92.1 | algorithm | 3.6 | PRG-OTP scheme: `k ← U_{n/2}`, `Enc_k(m) = m ⊕ G(k)` | C | 2 | Asymptotic/Encryption.lean | — | Def-77.1, Def-24.7, Machine-Primitives |
| Claim-92.a | claim (OTP perfect secrecy, used) | 3.6 | `m ⊕ U` is uniform; `{m_0 ⊕ U}` and `{m_1 ⊕ U}` are identical | C | 1 | Asymptotic/Encryption.lean | `uprob_comp_equiv`, `pushesUniform_xor`, `acceptProb_comp_equiv` | — |
| Thm-92.2 | theorem | 3.6 | scheme 92.1 is single-message secure | C | 2 | Asymptotic/Encryption.lean | `distAdv_comp`, `prgAdv`, `abs_sub_le_sum_hybrids` | Alg-92.1, Claim-92.a, Lem-71.5, Lem-71.6 |
| Def-93.1 | definition | 3.7 | multi-message secure encryption | C | 2 | Asymptotic/Encryption.lean | `distAdv`, `copies`-style tuple samplers | Def-91.1 |
| Thm-94.2 | theorem | 3.7 | a multi-message secure scheme is not deterministic-and-stateless | C | 2 | Asymptotic/Encryption.lean | — | Def-93.1, Def-24.7 |
| Def-95.a | definition | 3.8.1 | random function `RF_n`, two descriptions (table / lazy machine) | C | 1 | (exists) Pseudorandom/Functions/Defs.lean | `randomFunction` | — |
| Claim-95.b | claim | 3.8.1 | the table and lazy descriptions give identical distributions | C | 1 | (exists) Pseudorandom/Functions/LazySampling.lean | `QueryTree.evalLazy`, `QueryTree.uprob_evalLazy`, `extendStream` | — |
| Def-96.1 | definition | 3.8.2 | oracle indistinguishability | C | 3 | Asymptotic/PRF.lean | `QueryTree`, `OracleAdversary`, `oracleDist`, `OracleAdversary.BoundedBy` | Oracle-D7 |
| Claim-96.a | claim ("easy to verify") | 3.8.2 | closure under efficient (oracle) operations for oracle ensembles | O | 3 | Asymptotic/PRF.lean | `QueryTree.simulate`, `QueryTree.eval_simulate`, `BoundedBy.simulate` (one-query-per-query case) | Def-96.1 |
| Claim-96.b | claim | 3.8.2 | hybrid lemma for oracle ensembles | C | 1 | Asymptotic/PRF.lean | `exists_hybrid_gap` | Def-96.1 |
| Claim-96.c | claim | 3.8.2 | prediction lemma for oracle ensembles | O | 2 | Asymptotic/PRF.lean | `uprob_bool_prod` | Def-96.1, Lem-73.8 |
| Def-96.2 | definition | 3.8.2 | pseudorandom function family | C | 2 | Asymptotic/PRF.lean | `prfAdv`, `prfAdv_eq`, `prfAdv_nonneg` | Def-96.1, Machine-PPT |
| Cor-97.a | claim (in proof) | 3.8.2 | any PRG yields a length-doubling PRG (truncate to `n+1` bits, then Lem 80.5) | C | 2 | Asymptotic/PRF.lean | `distAdv_comp`, `prgExtBits` | Def-77.1, Lem-80.5 |
| Constr-97.b | construction | 3.8.2 | GGM family `f_s(b_1…b_n) = g_{b_n}(⋯g_{b_1}(s)⋯)` | C | 1 | (exists) Pseudorandom/Functions/GGM.lean | `pairSel`, `ggmFrom`, `ggm`, `ggmBits`, `splitHalves` | — |
| Claim-97.c | claim (Def 96.2 clause 1) | 3.8.2 | `f_s(x)` is PPT-computable from `(s, x)` | C | 3 | Asymptotic/PRF.lean | — | Machine-Loop |
| Thm-97.3 | theorem | 3.8.2 | PRG ⇒ PRF (GGM is a PRF) | C | 4 | Asymptotic/PRF.lean | `ggm_prfAdv_le`, `exists_ggm_dist`, `ggmBits_prfAdv_le`, `exists_ggmBits_dist`, `ggmDist`, `ggmBitsDist` | Def-96.2, Cor-97.a, Thm-97.3.1–.3, Oracle-D7, Machine-Closure |
| Thm-97.3.1 | hybrids | 3.8.2 | level hybrids `HF^i` (levels `≤ i` random), `HF^1 = f_s`, `HF^n = RF_n` | C | 1 | (exists) GGM.lean | `hybridOracle`, `hybridProb`, `hybridProb_zero`, `hybridProb_top`, `levelAdv` | — |
| Thm-97.3.2 | sub-hybrids | 3.8.2 | query sub-hybrids `HHF^j`, `p(n)` many; gap `ε/(n p(n))` | C | 1 | (exists) SubHybrids.lean | `subHybridStream`, `subHybridProb`, `tableDist`, `table_hybrid`, `hybridProb_level` | — |
| Thm-97.3.3 | claim | 3.8.2 | `HHF^j` can be emulated in PPT (lazy sampling); closure gives a PRG distinguisher | C | 4 | Asymptotic/PRF.lean | `uprob_evalLazy`, `noteQuery`, `ggmDist` cost docstring | Oracle-D7, Machine-Closure, Machine-Loop |
| Alg-99.1 | algorithm | 3.9 | many-message scheme `Enc_k(m) = (r, m ⊕ f_k(r))` | C | 2 | Asymptotic/MultiMessage.lean | — | Def-96.2, Def-24.7, Machine-Primitives |
| Thm-99.2 | theorem | 3.9 | scheme 99.1 is multi-message secure | C | 4 | Asymptotic/MultiMessage.lean | `prfAdv`, `oracleDist`, `distAdv_le_statDist`, `uprob_exists_le`, `pushesUniform_eval_pair` | Alg-99.1, Thm-99.2.1–.3, Oracle-D7, Machine-Closure |
| Thm-99.2.1 | claim | 3.9 | `H1 ≈ H2` (and `H5 ≈ H6`): the oracle adversary with `q+1` queries built from `D` | C | 3 | Asymptotic/MultiMessage.lean | `QueryTree` (chain of `q+1` queries), `prfAdv` | — |
| Thm-99.2.2 | claim | 3.9 | `H2` vs `H3`: distinguishable only on a collision `r_i = r_j`, probability `≤ C(q+1,2)·2^{-n}` | C | 4 | Asymptotic/MultiMessage.lean | `uprob_exists_le`, `uprob_eq_one_div_card`, `uprob_update_absorb`, `PushesUniform` | — |
| Thm-99.2.3 | claim | 3.9 | `H3 = H4` by OTP perfect secrecy (vector version) | C | 1 | Asymptotic/MultiMessage.lean | `Claim-92.a`, `PushesUniform.prodMap` | Claim-92.a |
| Def-102.1 | definition | 3.10 | public-key encryption scheme (with message sampler clause 4) | C | 2 | Asymptotic/PublicKey.lean | — | Machine-PPT |
| Def-102.2 | definition | 3.10 | secure PKE | C | 2 | Asymptotic/PublicKey.lean | `distAdv` | Def-102.1, Machine-NUPPT |
| Claim-103.a | claim | 3.10 | perfect secrecy is impossible for PKE (unbounded adversary) | O | 2 | Asymptotic/PublicKey.lean | `statDist`, `distAdv_le_statDist` | Def-102.1 |
| Claim-103.b | claim | 3.10 | deterministic PKE is insecure | O | 2 | Asymptotic/PublicKey.lean | — | Def-102.2, Machine-Closure |
| Def-103.c | definition (unnumbered) | 3.10 | multi-message secure PKE | C | 2 | Asymptotic/PublicKey.lean | — | Def-102.2 |
| Thm-103.d | theorem (exercise) | 3.10 | for PKE, single-message security ⇒ multi-message security | C | 3 | Asymptotic/PublicKey.lean | `exists_hybrid_gap`, `multicopyRed` (pattern) | Def-103.c, Lem-71.5, Lem-71.6, Machine-Closure |
| Def-103.e | definition (unnumbered) | 3.10 | single-bit secure PKE | C | 1 | Asymptotic/PublicKey.lean | — | Def-102.1 |
| Thm-103.f | theorem (stated) | 3.10 | single-bit secure PKE ⇒ secure PKE by bitwise encryption | C | 3 | Asymptotic/PublicKey.lean | — | Thm-103.d, Def-103.e |
| Constr-104.a | remark | 3.10.1 | `Enc_i(m) = f_i(m)` (textbook RSA) is deterministic hence insecure | O | 1 | Asymptotic/PublicKey.lean | — | Claim-103.b |
| Alg-104.3 | algorithm | 3.10.1 | 1-bit PKE from a TDP with hard-core bit: `(f_i(r), b_i(r) ⊕ m)` | C | 2 | Asymptotic/PublicKey.lean | `owpGen` (pattern) | Def-56.1, Def-78.3.coll |
| Lem-104.a | lemma (concrete, in proof) | 3.10.1 | a distinguisher of `(pk, f_pk(r), b(r))` vs `(pk, f_pk(r), ¬b(r))` with advantage `ε` yields a predictor of `b` with success exactly `1/2 + ε/2` (indexed `owpPredictor`) | C | 3 | Asymptotic/PublicKey.lean | `owpPredictor`, `predProb_owpPredictor_false/true`, `acceptProb_id_owp`, `uprob_bool_prod` | — |
| Thm-104.4 | theorem | 3.10.1 | TDPs (with hard-core bit) ⇒ scheme 104.3 is a secure single-bit PKE | C | 3 | Asymptotic/PublicKey.lean | Lem-104.a | Alg-104.3, Lem-104.a, Lem-73.8, Thm-87.3.coll, Machine-Closure |
| Asm-105.1 | assumption | 3.11 | DDH in the order-`q` subgroup of `Z_p^*`, `p = 2q+1` safe prime | C | 2 | Candidates/ElGamal.lean | `distAdv` | Ensemble-D6, NT-105.a |
| NT-105.a | number theory | 3.11 | `p = 2q+1` prime: squares form the unique subgroup `G_q` of order `q`, cyclic, every `≠ 1` element generates; `a ↦ a^2` is 2-to-1 onto `G_q` | C | 3 | Candidates/ElGamal.lean | Mathlib `IsCyclic (ZMod p)ˣ`, `Subgroup.card_eq_card_quotient_mul_card_subgroup`, `ZMod.euler_criterion`, `IsCyclic.card_pow_eq_one_le`, `orderOf_eq_prime` | — |
| Claim-106.a | claim | 3.11 | DDH ⇒ DL (a DL solver breaks DDH) | O | 3 | Candidates/ElGamal.lean | — | Asm-105.1, Asm-52.2 |
| Claim-106.b | claim | 3.11 | in `Z_p^*` itself DDH is false: element orders (2, q, 2q) distinguish tuples | O | 3 | Candidates/ElGamal.lean | Mathlib `legendreSym`, `ZMod.euler_criterion` | NT-105.a |
| Alg-106.2 | algorithm | 3.11 | El Gamal `Gen/Enc/Dec` | C | 2 | Candidates/ElGamal.lean | — | NT-105.a, Machine-PPT, Thm-45.6 |
| Claim-107.a | claim (missing in text) | 3.11 | `h = g^2` for uniform `g ∈ Z_p^*` is uniform on `G_q`; it is a generator unless `h = 1` (probability `1/q`); statistical distance to "uniform generator" is `1/q` | C | 2 | Candidates/ElGamal.lean | `pushesUniform_of_surjective`, `statDist` | NT-105.a |
| Thm-107.3 | theorem (exercise) | 3.11 | DDH ⇒ El Gamal (message space `G_q`) is secure | C | 3 | Candidates/ElGamal.lean | `distAdv_comp`, `acceptProb_comp_equiv` (`Equiv.mulLeft`), `abs_sub_le_sum_hybrids` | Alg-106.2, Asm-105.1, Claim-107.a, Lem-71.5, Lem-71.6 |
| Def-107.b | definition (missing in text) | 3.11 | encoding of bit strings into `G_q` (`m ↦ ±m`, the square), so that Def 102.1's `{0,1}^n` message space is met | O | 3 | Candidates/ElGamal.lean | Mathlib `ZMod.exists_sq_eq_neg_one_iff` (`p ≡ 3 (4)`) | NT-105.a |
| Claim-107.c | claim (unproved) | 3.12 | one-way functions are minimal: PRG ⇒ OWF (also PRF/encryption ⇒ OWF) | O | 3 | Asymptotic/Pseudorandom.lean | `distAdv`, `invProb` | Def-77.1, Def-27.3 |
| Claim-107.d | claim (unproved, cited) | 3.12 | no black-box PKE from OWF | D | 5 | — | — | — |
| Thm-188.7 | appendix | A | Chernoff bound `Pr[∑X_i − μn ≥ ε] ≤ 2^{-ε²n}` | O | 3 | Asymptotic/Chernoff.lean (only if needed) | replaced by `chebyshev_pairwise` | — |
| Lem-189.8 | appendix | A | majority vote of `ℓ > p(n)^2` biased samples is right w.h.p. (statement garbled: "`1 − 2??`") | O | 1 | (exists) PairwiseIndependence.lean | `uprob_majority_fails_le` (bound `1/(4δ²ℓ)`) | — |
| Ineq-189.a | appendix | A | pairwise-independent sampling inequality `Pr[|∑X_i/n − μ| ≥ ε] ≤ (1−μ²)/(nε²)` | C | 1 | (exists) PairwiseIndependence.lean | `chebyshev_pairwise`, `chebyshev_pairwise_ident` (bits, bound `1/(4δ²m)`) | — |

## 2. Statements, reuse notes, text issues

### 2.1 §3.0–§3.1 Ensembles and computational indistinguishability

**Claim-67.a** (p. 67, "show this") — *No generator outputs a perfectly random longer string.*
Statement: for every `n < m` and every `G : (Fin n → Bool) → (Fin m → Bool)`, the pushforward of
`U_n` under `G` is not `U_m`; quantitatively `statDist (G_* U_n) U_m ≥ 1 − 2^{n−m} ≥ 1/2`, so an
unbounded distinguisher (membership in the image of `G`) has advantage `≥ 1/2`. Reuse: `statDist`,
`FinDist.map`, `distAdv_le_statDist` (the test "is `t` in the image" is a deterministic
distinguisher; `acceptProb` on `G` is `1`, on `U_m` is `|image|/2^m ≤ 2^{n−m}`). Optional,
difficulty 2. (The text argues via Shannon's theorem from ch. 1; the pigeonhole form is simpler.)

**Def-69.3** — *Ensemble.* A sequence `{X_n}` with `X_n` a distribution over `{0,1}^*`. D6 reading:
`structure Ensemble` with `seedLen outLen : ℕ → ℕ` (explicit `C(n+1)^c` formulas, or at least
`PolyBound`) and `sample n : (Fin (seedLen n) → Bool) → (Fin (outLen n) → Bool)`; the distribution
`X_n` is the pushforward of uniform seeds (dyadic). `Samplable X` := the sampler family is computed
by one PPT on input `1^n` (coins = seed). Deviation: every distribution is dyadic (the text allows
arbitrary distributions over `{0,1}^*`; the text's own ensembles are all of this form, except the
DDH/El Gamal ones that sample primes and `Z_q` — see Asm-105.1).
Reuse: samplers `σ → γ` of `Foundations/Experiments.lean` are the one-`n` slices.

**Def-69.4** — *Computational indistinguishability.* `X ≈ Y` iff for every nuPPT `D` there is a
negligible `ε` with `|Pr[t ← X_n : D(t)=1] − Pr[t ← Y_n : D(t)=1]| < ε(n)` for all `n`. Formal:
`CompIndist X Y := ∀ D : NUPPT, Negligible (fun n => distAdv (X.sample n) (Y.sample n) (D.dist n))`
where `D.dist n : (Fin (outLen n) → Bool) → (Fin (coins n) → Bool) → Bool` runs the machine on
`pairEncode (pairEncode (List.ofFn t) (α n)) (List.ofFn r)` and reads `[true]`. Note: the text's
`∃ ε negligible, ∀ n, gap(n) < ε(n)` is equivalent to `Negligible gap` because `gap ∈ [0,1]`
(`Negligible.mono` one way; take `ε = gap + 2^{-n}` with `Negligible.add` the other way).
Also define the notations: `Distinguishes D X_n Y_n ε := ε < distAdv …` ("with probability `ε`")
and the ensemble version "for all `n`". The text does **not** give `D` the input `1^n` in Def 69.4
(it does in Def 75.2 and 96.1); with `outLen n ≥ 1` polynomial and the advice string of length
depending on `n`, the machine can recover `n` from `|α|` or `|t|` — record as a convention
(adversaries always receive `1^n`, D5), no mathematical difference.
Text issue: strict `<` here, `≤` in Defs 91.1/93.1/102.2 — immaterial.

**Lem-71.5** — *Closure under efficient operations.* If `X ≈ Y` then for every nuPPT `M`,
`{M(X_n)} ≈ {M(Y_n)}`. Here `M(X_n)` is the ensemble with sampler `pushSampler (M.run n) (X.sample n)`
(seed = seed of `X` ++ coins of `M`); its seed length is polynomial, so it is an ensemble in the D6
sense. Concrete: `distAdv_sunglassRed : distAdv X Y (sunglassRed P D) = distAdv (pushSampler P X) (pushSampler P Y) D`
(exact equality, randomized `P`), `distAdv_comp` (deterministic `P`). Bridge: `D' = D ∘ M` is an
nuPPT (Machine-Closure: post-composition, advice concatenation `pairEncode (α_M n) (α_D n)`, coin
splitting `r = r_M ++ r_D` with explicit lengths), then `Negligible.mono` with the equality.
Difficulty 3 (all in the machine closure).

**Lem-71.6** — *Hybrid lemma.* If `D` distinguishes `X^1` and `X^m` with probability `ε` then some
`i ∈ [1, m−1]` has `D` distinguishing `X^i, X^{i+1}` with probability `ε/m`. Concrete:
`exists_hybrid_gap (P : ℕ → ℝ) (ht : 0 < t) : ∃ k < t, |P 0 − P t| / t ≤ |P k − P (k+1)|` with
`P i = acceptProb (X^{i+1}) D` and `t = m − 1` (the proof's own bound is `ε/(m−1) > ε/m`; the
text's `ε/m` is weaker but correct — note the off-by-one in text_issues). Also
`abs_sub_le_sum_hybrids` (telescoping form) and the uniform variant `distAdv_mixDist_eq`
(random index, exact `|P 0 − P t|/t`), which removes the non-uniform choice of `i`. Nothing to
add; difficulty 1. Statement in Lean should be the concrete one (no machines involved).

**Rem-72.7** — `D ↦ Pr[D(·)=1]` induces a pseudometric; the hybrid lemma is the triangle
inequality. Formal: `distAdv X Z D ≤ distAdv X Y D + distAdv Y Z D` (`abs_sub_le`). Optional,
difficulty 1 (one-liner, useful as API).

**Claim-72.a** — "it is easy to construct a long sequence in which adjacent pairs are
indistinguishable but the extremes are distinguishable": e.g. `2^n + 1` single-bit distributions
`B_i = Bernoulli(i/2^n)` (sampler from `n` coins: output `1` iff the seed, read as a number, is
`< i`): `statDist B_i B_{i+1} = 2^{-n}`, hence `distAdv ≤ 2^{-n}` for every `D`
(`distAdv_le_statDist`) — adjacent pairs are even *statistically* indistinguishable, while
`B_0 = 0` and `B_{2^n} = 1` are told apart by the identity with advantage `1`. Optional,
difficulty 2.

**Ex-72.b** — For pairwise `≈` ensembles `X, Y, Z` over `{0,1}^n` with PPT samplers,
`{x ← X_n; y ← Y_n : x ⊕ y} ≈ {y ← Y_n; z ← Z_n : z ⊕ y}`: instance of Lem-71.5 with
`M(t) = t ⊕ y`, `y ← Y_{|t|}` (needs `Samplable Y`), applied to `X ≈ Z`. Concrete:
`distAdv_sunglassRed` with `P t c = t + Y.sample n c`. Optional, difficulty 2.

**Claim-73.a** (p. 73, "show this!") — *Predicting implies distinguishing.* If `A` satisfies
`Pr[b ← {0,1}; t ← X^b_n : A(t) = b] ≥ 1/2 + δ`, then `A` itself (as a distinguisher) has
`|Pr[A(X^1)=1] − Pr[A(X^0)=1]| ≥ 2δ`. Concrete identity (to be proved once, used by 73.8, 75.4,
104.4): for samplers `X⁰, X¹` and `A : γ → ρ → Bool`,
`uprob (fun (b, s, r) => A (X^b s) r = b) = 1/2 + (acceptProb X¹ A − acceptProb X⁰ A)/2`
(`uprob_bool_prod` splits on `b`; `uprob_not` for the `b = 0` half). Both directions of the
prediction lemma are this identity. Core, difficulty 2.

**Lem-73.8** — *Prediction lemma.* If a nuPPT `D` distinguishes `{X⁰_n}, {X¹_n}` with probability
`μ(n)` for infinitely many `n`, there is a nuPPT `A` with
`Pr[b ← {0,1}; t ← X^b_n : A(t) = b] ≥ 1/2 + μ(n)/2` for infinitely many `n`. Proof: `A = D` or
`A = 1 − D` according to the sign of `Pr[D(X¹)=1] − Pr[D(X⁰)=1]` (the sign is a per-`n`
non-uniform choice = one advice bit; the text's "one of these works for infinitely many `n`"
avoids advice by pigeonhole on an infinite set — both routes are available; the advice route gives
the stronger "for every `n`" statement). Concrete: from Claim-73.a's identity,
`∃ flip : Bool, predProb₂ X⁰ X¹ (flipPred D flip) = 1/2 + distAdv X⁰ X¹ D / 2` (the pattern of
`exists_owpPredictor`/`predProb_owpPredictor_true`). Asymptotic: `¬Negligible (distAdv …)` ⇒
`¬Negligible (predAdv …)` for the nuPPT `A` with advice bit `flip n`. Difficulty 3 (advice bit
hard-wiring + output negation: Machine-Closure).
Text issue: the hypothesis quantifies "for infinitely many `n`" — this is the `not_negligible_iff`
form; also the conclusion's `A` depends on `D` only, as it should.

**Claim-73.b** — The ubiquitous "assume for contradiction there is a polynomial `p` such that for
infinitely many `n` the advantage exceeds `1/p(n)`" is exactly `not_negligible_iff`
(`¬Negligible μ ↔ ∃ c, ∀ n₀, ∃ n ≥ n₀, 1/n^c ≤ |μ n|`); with `1/p(n)` for a general polynomial
`p` replaced by `1/n^c` (fine: `p(n) ≤ n^c` eventually). Exists; difficulty 1. Planners: every
asymptotic theorem is stated positively (`Negligible …`) and proved by contraposition through this
lemma.

### 2.2 §3.2 Pseudorandomness and the next-bit test

**Def-74.1** — *Pseudorandom ensemble.* `X` (over `{0,1}^{ℓ(n)}`) is pseudorandom iff
`X ≈ {U_{ℓ(n)}}`. Formal: `Pseudorandom X := CompIndist X (uniformEnsemble X.outLen)`; at one `n`
the advantage is `prgAdv (X.sample n) D = distAdv (X.sample n) id D`. Difficulty 1.

**Def-75.2** — *Next-bit test.* `X` over `{0,1}^{ℓ(n)}` passes the next-bit test iff for every
nuPPT `A` there is a negligible `ε` with, for all `n` and all `i`,
`Pr[t ← X_n : A(1^n, t_1 … t_i) = t_{i+1}] < 1/2 + ε(n)`. Intended index range: `0 ≤ i < ℓ(n)`
(prefix of length `i`, predicted bit `t_{i+1}`, bits 1-indexed); the text writes
`i ∈ [0, …, ℓ(n)]`, which includes a nonexistent bit `t_{ℓ(n)+1}`. Formal (one `n`):
`nextBitProb (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) := uprob fun (s, r) => A (Fin.init-prefix (X s) i) r = X s i`
(0-indexed: prefix of length `i.val`, predict bit `i`). Asymptotic: `∀ A nuPPT, Negligible (fun n => sup_i (nextBitProb … − 1/2))`
— the `∀ i` inside a single negligible `ε` is important (the text's quantifier order is
`∃ ε ∀ n ∀ i`); formalize as `∀ A, ∃ ε, Negligible ε ∧ ∀ n i, nextBitProb … ≤ 1/2 + ε n`, or
equivalently `Negligible (fun n => ⨆ i, …)` over the finite `i`. The machine `A` gets `1^n` and
the prefix (as `pairEncode (1^n) prefix`); `i` is the prefix length. **Rem-75.3** is the
convention that `A` gets `1^n` (so its time is polynomial in `n`, not in the prefix length) — D5.

**Thm-75.4** — *Completeness of the next-bit test.* If `X` passes the next-bit test then `X` is
pseudorandom. Contrapositive proof in the text; the formal route: concrete reduction
`Thm-75.4.c` + `Claim-73.b` + machine closure.

**Thm-75.4.c** (concrete, new) — for every sampler `X : σ → Fin ℓ → Bool` (`0 < ℓ`) and every
distinguisher `D : (Fin ℓ → Bool) → ρ → Bool`, there exist `i : Fin ℓ` and `flip : Bool` such that
`nextBitProb X i (nextBitPred D i flip) ≥ 1/2 + prgAdv X D / ℓ`, where `nextBitPred D i flip`
(= **Alg-76.5**) on a prefix `t_1…t_i` draws `ℓ − i` uniform bits `u_{i+1}…u_ℓ` and coins for
`D`, runs `g ← D(t_1…t_i u_{i+1}…u_ℓ)`, outputs `u_{i+1}` if `g = 1` and `¬u_{i+1}` otherwise
(negated if `flip`). Proof plan (the text's, made exact):
* **Thm-75.4.1** hybrids `H^i : σ × (Fin ℓ → Bool) → Fin ℓ → Bool`, `H^i (s,u) j = if j < i then X s j else u j`;
  `acceptProb (H^0) D = acceptProb id D` (`acceptProb_snd`), `acceptProb (H^ℓ) D = acceptProb X D`
  (`acceptProb_fst`). Hybrid lemma: `∃ i < ℓ, prgAdv X D / ℓ ≤ |P(H^i) − P(H^{i+1})|`.
* flipped hybrid `H̃^{i+1} (s,u) j = if j < i then X s j else if j = i then ¬X s i else u j`.
* **Thm-75.4.2** mixing identity: `P(H^i) = (P(H^{i+1}) + P(H̃^{i+1}))/2` — the bit `u_i` of `H^i`
  equals `X s i` or `¬X s i` each with probability `1/2` independently of everything else
  (`uprob_bool_prod` after the bijection `(b, s, u) ↦ (s, update u i (xor b (X s i)))`, as in
  `acceptProb_id_owp`). Hence `|P(H^{i+1}) − P(H̃^{i+1})| ≥ 2 prgAdv/ℓ`.
* predictor analysis: `nextBitProb X i (nextBitPred D i false) = 1/2 + (P(H^{i+1}) − P(H̃^{i+1}))/2`
  — the completed string is a sample of `H^{i+1}` when `u_{i+1} = t_{i+1}` and of `H̃^{i+1}`
  otherwise (Claim-73.a's identity with `X¹ = H^{i+1}`, `X⁰ = H̃^{i+1}`); `flip = true` gives
  `1/2 − (…)/2`. Choose `flip` by the sign.
Reusable patterns: `prgHybrid`/`acceptProb_prgExtRed_right` (planting a uniform bit via
`acceptProb_update`), `owpPredictor`/`predProb_owpPredictor_false` (predictor from a
distinguisher plus one random bit). Difficulty 4 (new 250-line concrete file).
Asymptotic bridge: `i(n)` and `flip(n)` are advice; `nextBitPred` = draw `ℓ(n) − i` coins,
concatenate, one call of `D`, compare/negate (Machine-Closure + Machine-Primitives). Then
`not_negligible_iff` on `prgAdv` gives `c` with `prgAdv ≥ n^{-c}` i.o., so the predictor has
advantage `≥ n^{-c}/ℓ(n)` i.o., contradicting Def 75.2 (`Negligible.mul_pow`-style arithmetic).

Text issues (Thm 75.4 proof): (a) Alg 76.5 draws "`ℓ(n) − i` bits `← U_{ℓ(n)−1}`" — should be
`U_{ℓ(n)−i}`; (b) `H̃^i_n` is defined with `x̄_i` and a stray `u_{l(m)}`, while the argument uses
`H̃^{i+1}` flipping bit `i+1`; (c) the proof's hybrids are 0-indexed `x_0 x_1 …` while Def 75.2 is
1-indexed `t_1 t_2 …`; (d) the final displayed probability has `A(t) = 1` where `A(t) = b` is meant,
and the prediction-lemma display writes `D` for `A`; (e) the text applies the hybrid lemma with
`ℓ(n)+1` hybrids and claims gap `1/(p(n)ℓ(n))` (fine, `ℓ` gaps).

**Thm-75.4.conv** (implicit converse: pseudorandom ⇒ passes next-bit test) — concrete: for a
next-bit predictor `A` at position `i` with success `1/2 + δ` on `X`, the distinguisher
`D(t) := [A(t_1…t_i) = t_{i+1}]` has `acceptProb X D = 1/2 + δ` and `acceptProb id D = 1/2`
exactly (the uniform bit `t_{i+1}` is independent of the prefix and of `A`'s coins), hence
`prgAdv X D = δ`. Optional, difficulty 2; it is the honest statement behind "a pseudorandom
distribution passes all efficient tests".

### 2.3 §3.3 Pseudorandom generators and hard-core bits

**Def-77.1** — *PRG.* `G : {0,1}^* → {0,1}^*` is a PRG iff (1) `G` is computable by a PPT
(Def 24.6: same output for every coin string, so effectively deterministic polynomial time:
`Complexity.PolyTimeComputable` on `List Bool`), (2) `|G(x)| > |x|`, (3) `{x ← U_n : G(x)}` is
pseudorandom. Formal: `structure PRG` with `stretch : ℕ → ℕ` (explicit polynomial `ℓ`, `n < ℓ n`),
`G : ∀ n, (Fin n → Bool) → (Fin (ℓ n) → Bool)`, `computable : PolyTimeComputable (bridge of G)`,
`secure : ∀ D nuPPT, Negligible (fun n => prgAdv (G n) (D.dist n))`. Deviation: length-regular
(`|G(x)|` depends only on `|x|`), as the concrete layer assumes; the text's `G : {0,1}^* → {0,1}^*`
with `|G(x)| > |x|` admits irregular lengths, which no construction in the book uses.

**Constr-77.a / Claim-78.a / Claim-78.b** (Shamir's generator, p. 77–78). `G(s) = f^n(s)‖…‖f(s)‖s`.
Claim-78.a: if `f` is a permutation of `{0,1}^n` and `x` uniform then `f^k(x)` is uniform
(`uprob_comp_equiv` with `(Equiv.iterate f k)`; also `acceptProb_comp_equiv`). Claim-78.b: the
blocks are unpredictable (inverting `f`) but individual bits may be predictable — a OWP may leave
the first two bits of its input unchanged; the concrete witness is Garg's Claim 2.3
(`predProb_fixedBitPredictor`, `predProb_positionBit` in `HardcoreBit/NoFixedBit.lean`: a fixed
input bit of `f(x_{-y})‖x_y‖y` is predicted with probability `1`). Both optional (difficulty 1–2);
record as remarks in `HardCore.lean`'s module docstring if not formalized.

**Def-78.3** — *Hard-core predicate.* `h : {0,1}^* → {0,1}` is hard-core for `f` iff `h` is
PPT-computable and for every nuPPT `A` there is a negligible `ε` with, for all `n`,
`Pr[x ← {0,1}^n : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)`. Formal:
`HardCore (f : ∀ n, (Fin n → Bool) → (Fin (m n) → Bool)) (h : ∀ n, (Fin n → Bool) → Bool) :=
PolyTimeComputable h ∧ ∀ A nuPPT, Negligible (fun n => predProb (f n) (h n) (A.pred n) − 1/2)`
(`predProb f B A = uprob fun (x, r) => A (f x) r = B x` is the exact one-`n` slice; the
`− 1/2` may be negative, which `Negligible` (absolute values) tolerates, or state
`∃ ε, Negligible ε ∧ ∀ n, predProb … ≤ 1/2 + ε n`). Text issue: the definition mixes `k` and `n`
(`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); intended `k = n`. Note the text says hard-core "for
`f(x)`" with `f` a single function (not a collection), and later uses it for collections:

**Def-78.3.coll** (unnumbered, needed by Lem 84.1, Alg 104.3/Thm 104.4 and ch. 4 Thm 126.4) —
`{h_i}` is hard-core for the collection `{f_i : D_i → R_i}_{i ∈ I}` with index sampler `Gen` iff
`h_i(x)` is PPT-computable from `(i, x)` and for every nuPPT `A` there is a negligible `ε` with
`Pr[i ← Gen(1^n); x ← D_i : A(1^n, i, f_i(x)) = h_i(x)] ≤ 1/2 + ε(n)`. Concretely this is
`predProb` for the sampler `(c, x) ↦ (i(c), x)` on the typed domain `Σ i, D_i` or, in the D5/D6
style, for `f n : (Fin (s n) → Bool) × (Fin n → Bool) → …` with the index drawn from the first
component (`pairEncode i (f_i x)` on tapes). Difficulty 2.

**Claim-78.c** — LSB and `half_N` are hard-core for RSA "under the RSA assumption" (stated as
known, no proof; Alexi–Chor–Goldreich–Schnorr). Deferred (difficulty 5; nothing downstream needs
it; the RSA PRG of §3.3.6 is illustrative).

**Thm-79.4** — Let `f` be a one-way permutation (single function, `f n : (Fin n → Bool) ≃ (Fin n → Bool)`,
PPT-computable, one-way) and `h` hard-core for `f`. Then `G(s) = f(s)‖h(s)` (output length `n+1`)
is a PRG. Concrete (exists, with `β := Unit`): `owpGen f B : α × β → α × β × Bool`,
`exists_owpPredictor : ∃ flip, predProb (owpPair f) B (owpPredictor D flip) = 1/2 + prgAdv (owpGen f B) D`;
with `β = Unit`, `owpPair f ≃ f` and `owpGen f B ≃ (f s, B s)`; the bit-string form needs the
re-encoding `(Fin n → Bool) × Bool ≃ (Fin (n+1) → Bool)` (`Fin.snocEquiv`-style; `owpBitsEquiv`
is the `n+n+1` version) and `prgAdv_comp_equiv`. Deviation (proof route): the text proves 79.4
through Thm 75.4 ("the first `n` bits are uniform so the predictor must be for bit `n+1`",
Claim-79.a); the formal proof uses Garg's direct reduction (one call of `D` on `f(s)‖σ` with a
random bit `σ`, output `σ` or `¬σ`), which gives the exact bound `1/2 + ε` without the `1/ℓ` loss.
Record in the docstring. Text issues: the proof says "`A` predicts the `i`th bit with probability
`1/p(n)`" (meaning advantage) and "contradicts that `b` is hard-core" (`b` should be `h`).
Bridge: the predictor is nuPPT (one extra coin, one call, advice bit `flip`: Machine-Closure);
`not_negligible_iff`. Difficulty 3.
Downstream: ch. 4 Thm 126.4 uses the same `f, h` with `Com(b, r) = (f(r), b ⊕ h(r))` — see Lem-104.a.

**Claim-79.a** (in the proof of 79.4) — for a permutation `f`, `{s ← U_n : f(s)}` is `U_n`, so a
next-bit predictor for any position `i ≤ n` of `G(s) = f(s)‖h(s)` succeeds with probability
exactly `1/2`. Optional, difficulty 2 (not needed on the formal route).

**Lem-80.5** — *Expansion.* Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG and `ℓ` a polynomial;
`G'(s) = b_1 … b_{ℓ(n)}` where `X_0 = s`, `X_{i+1}‖b_{i+1} = G(X_i)`. Then `G'` is a PRG.
Concrete (exists): `prgExtBits G l : (Fin n → Bool) → Fin (l + n) → Bool` (bits *and* final seed),
`exists_prgExtBitsRed_ge : ∃ k < l, prgAdv (prgExtBits G l) D / l ≤ prgAdv G (prgExtBitsRed G l k D)`;
the text's `G'` is the projection of `prgExtBits G l` onto its first `l` bits, and the projection
is a deterministic post-processing (`distAdv_comp`: a distinguisher of the projected output is a
distinguisher of the full output with the same advantage). Also the uniform version
`prgAdv_prgExtAvgRed` (exact `ε/l`, random `k`). Encoding deviations: Garg's `G : S → Bool × S`
puts the bit first and reads `G(s)` as `(bit, next seed)` via `Fin.consEquiv`; the text's
`X_{i+1}‖b_{i+1}` puts the seed first — a fixed re-encoding (`prgAdv_comp_equiv`). The text's
proof (hybrids `H^i = U_{m−i}‖G_i(U_n)`, reduction `M(y)` that knows `i`) is Garg's up to indexing.
Bridge: the reduction at hybrid `k` makes `l − k − 1` calls to `G` (Machine-Loop) and one call to
`D`, draws `l` coins, and has `k` as advice; `G'` itself is PPT-computable by iterating `G` `ℓ(n)`
times (Machine-Loop); `Negligible.mul_pow` for the factor `ℓ(n)`. Difficulty 3.
Text issues: `m(n)` and `ℓ(n)` used interchangeably; hybrids "for `i = 1, …, m(n)`" should start
at `0`; in `M(y)` the input `y` is read as `y_1` = bit, `y_2…y_{n+1}` = seed, contradicting the
construction's `X_{i+1}‖b_{i+1}` order; `G'` drops the final seed while the hybrids keep it
implicitly.

**Cor-81.7** — For a OWP `f` with hard-core bit `h`, `G(x) = h(x)‖h(f(x))‖h(f^{(2)}(x))‖…‖h(f^{ℓ(n)}(x))`
is a PRG. Proof: apply Lem 80.5 to `G'(x) = f(x)‖h(x)` (Thm 79.4). Formal: with
`G₁ s := (h s, f s) : Bool × S`, the closed form of `prgExt` gives output bit `i` equal to
`(G₁ ((prgStep G₁)^[i] s)).1 = h (f^[i] s)` and `prgStep G₁ = f`, so the corollary's formula is
`prgExt G₁ l` projected to bits (with `l = ℓ(n) + 1` bits `i = 0 … ℓ(n)`). Text issue: the formula
lists `ℓ(n)+1` bits (`i = 0 … ℓ(n)`) whereas Lem 80.5 produces `ℓ(n)`; harmless. Expansion needs
`ℓ(n) + 1 > n`. Difficulty 2 (composition + the closed-form identity). PPT-computability of `G`:
Machine-Loop over `f` and `h`.

**Constr-82.a** — PRG from a collection of OWPs `{f_i}` with hard-core bits `{h_i}`:
`G(r_1, r_2) = h_i(f_i(x))‖h_i(f_i^{(2)}(x))‖…` where `r_1` samples `i` and `r_2` samples `x ∈ D_i`
("can be easily adapted"; no proof). Deferred: `prgExt` assumes a *uniform* seed type `S` and
`prgAdv` against uniform `Bool × S`; here the seed `(i, x)` is not uniform on a product type and
the one-bit generator `(i, x) ↦ (h_i(x), (i, f_i(x)))` must keep `i` in its state. The needed
generalization: stretch extension for `G : S → Bool × S` relative to a seed *sampler* `μ : σ → S`
with `G_*μ ≈ (U_1, μ)` ("`μ`-pseudorandom one-bit generator"); the hybrids and the reduction go
through verbatim with `μ` in place of `id` (`acceptProb_update` is unchanged). Then `i` must be
dropped from the output (`distAdv_comp`). Difficulty 3; nothing downstream needs it (ch. 4 uses a
single OWP). The three instantiations **Constr-82.b** (Blum–Micali: Lem 84.1 + Constr-82.a),
**Constr-83.a** (RSA PRG: Claim-78.c), **Constr-83.b** (BBS: hard-core LSB for squaring, not in the
text) and **Claim-83.c** (`log n` bits per iteration, "provably secure", unproved) are deferred.

### 2.4 §3.4 Hard-core bits from any one-way function

**Lem-84.1** — *DL hard-core bit.* Under the DL assumption, `half_{p−1}(x) := [0 ≤ x ≤ (p−1)/2]`
is a hard-core predicate for `f_{p,g}(x) = g^x mod p` of the collection `DL` (index `(p, g)` with
`p` an `n`-bit prime and `g` a generator of `Z_p^*`, domain `Z_{p−1}`; Thm 52.3 writes the index
as `(q, g)` with `D_i = Z_q`, `R_i = G_p` — garbled). Precise intended statement: for every nuPPT
`A` there is a negligible `ε` with
`Pr[(p,g) ← Gen_DL(1^n); x ← Z_{p−1} : A(1^n, p, g, g^x) = half_{p−1}(x)] ≤ 1/2 + ε(n)`,
provided `Pr[(p,g) ← Gen_DL(1^n); x ← Z_{p−1} : B(1^n, p, g, g^x) = x]` is negligible for every
nuPPT `B` (DL in `Z_p^*`). **Text error:** Assumption 52.2 is stated for *prime-order* groups
`G_q`, but the lemma, Alg 84.2 and the proof use `Z_p^*` (even order `p−1`, `g^{(p−1)/2} = −1`,
square roots split the exponent's parity); the lemma needs DL in `Z_p^*` for a uniform generator
`g` (as in Thm 52.3's collection), which is a different assumption from 52.2. Formalize the DL
assumption for the `Z_p^*` collection explicitly (ch. 2 inventory: Thm 52.3's `DL` collection) and
cite 52.2 as the stated form. Also "`x ← Z_p`" in the proof should be `x ← Z_{p−1}`.
Scope core (the task lists it), difficulty 5 — the hardest item of the chapter; the text's proof
is a sketch with four gaps (Lem-84.1.3–.5 and the square-root algorithm). Recommended split:

* **Lem-84.1.0** `half_{p−1}` is PPT-computable (a comparison; trivial, Machine-PPT).
* **Lem-84.1.1** number theory (concrete, Mathlib): for `p` an odd prime and `g` a generator of
  `(ZMod p)ˣ`: `g^{(p−1)/2} = −1` (`ZMod.pow_div_two_eq_neg_one_or_one` plus `orderOf g = p − 1`
  via `orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient`, `Nat.totient_prime`);
  `g^e` is a square iff `e` is even (`ZMod.euler_criterion`); the square roots of `g^{2x}` are
  exactly `g^x` and `g^{x + (p−1)/2} = −g^x`. Difficulty 2.
* **Alg-84.2** bit-by-bit DL with a *perfect* oracle `A(y) = half_{p−1}(DL(y))`: for `k = |p|`
  down to `1`: if `y_k` is a square set `x_k = 0` else `x_k = 1, y_k ← y_k/g`; `y_{k−1} ← √y_k`
  (one of the two roots); if `A(y_{k−1}) = 0` then `y_{k−1} ← −y_{k−1}`; output the bits `x`.
  Correctness: with `y = g^e`, each round halves `e` (after removing the parity bit) and the oracle
  selects the root with the *smaller* exponent `⌊e/2⌋ < (p−1)/2`; after `|p|` rounds the bits are
  the binary expansion of `e`. Text issues: the loop writes `k = |p|` and decrements. (Run-3
  audit P8-3: the root selection "IF `b = 0` THEN `y_{k−1} ← −y_{k−1}`" is *consistent* with
  `half`'s convention — `half = 1` iff the exponent is in the lower half, and the root with
  `A = 1` is kept; the boundary exponent `(p−1)/2` only arises as the second root `−1` of
  `y = 1`, whose canonical root `y^{(p+1)/4} = 1` is kept under either convention, so the strict
  `half_{p−1}(x) := [2x < p−1]` of the formalization is a harmless variant, not a necessity.)
  Difficulty 3 (concrete, deterministic correctness).
  The square root itself is **Thm 58.2** (ch. 2, `p ≡ 3 (mod 4)`; the general case is "an
  exercise" in the text and not in Mathlib as an algorithm). For the *concrete* lemma the root
  may be `Classical.choose`; for the *asymptotic* lemma the inverter must be PPT, so either
  (i) take "modular square roots are PPT-computable" as an explicit hypothesis of the asymptotic
  statement, or (ii) restrict `Gen_DL` to primes `p ≡ 3 (mod 4)` (Thm 58.2 is one modular
  exponentiation, Thm 45.6). Planners must choose; (ii) is recommended (Deviation).
* **Alg-85.a** the randomized majority test replacing line 8: `ℓ` times draw `r_i ← Z_{p−1}`,
  set `z_i = y_{k−1} g^{r_i}`, `b_i ← A(z_i)`, increment `lo` when `(b_i = 0 ∧ r_i < (p−1)/2) ∨ (b_i = 1 ∧ r_i ≥ (p−1)/2)`;
  decide by majority. Concrete analysis: the trials are independent (fresh `r_i`, fresh coins), so
  `uprob_majority_fails_le` (pairwise independence suffices; `pairwiseUniform_eval`) gives failure
  `≤ 1/(4 δ² ℓ)` with `δ = ε/2`, i.e. the text's "Chernoff, `ℓ = (1/ε)²`" becomes an explicit `ℓ`
  with `1/(ε² ℓ) ≤ 1/(4|p|)` so that the union bound over `|p|` rounds leaves failure `≤ 1/4`.
  Difficulty 3.
* **Lem-84.1.3** `Pr[noinc | low(y_{k−1})] ≤ 1/2 − ε/2` for instances whose exponent lies in
  `[0, s]`, `s = εp/4`: conditioned on a fixed instance with exponent `e ≤ s`, the exponent of
  `z_i` is `e + r_i mod (p−1)`, and `half(e + r_i) ≠ half(r_i)` only when `r_i` is within `s` of
  a boundary (`[(p−1)/2 − s, (p−1)/2)` or `[p−1−s, p−1)`), probability `≤ 2s/(p−1) ≤ ε/2`; union
  bound with `A`'s error `1/2 − ε` (per-instance success `≥ 1/2 + ε` — see .5). Needs
  `pushesUniform_add_right` (`r ↦ e + r` is a bijection of `Z_{p−1}`) and `uprob_or_le`.
  Difficulty 3. Text issue: the text's success probability is `1/2 + ε` with "`ε = s(n)`" (should
  be `1/s(n)`), and the arithmetic `1/2 − ε + 2(ε/4)` treats `s` as `εp/4` with two intervals of
  length `s` (total `2s/p = ε/2`) — consistent but sloppy.
* **Lem-84.1.4** range reduction ("as we will show later" — never shown): a solver `B₀` for
  instances with exponent in `[0, s]` yields a solver for all instances: pick `t ← [0, ⌈(p−1)/s⌉)`
  uniformly, run `B₀` on `y · g^{−ts}` and output `x₀ + ts`; the shifted exponent lies in `[0, s]`
  with probability `≥ s/(p−1) − 1/(p−1) ≈ ε/4` (`uprob_eq_one_div_card`-style counting). So the
  DL inverter succeeds with probability `≥ (ε/4)(3/4)` on the good `(p, g)`. Difficulty 3.
* **Lem-84.1.5** (missing in the text) the predictor's success `1/2 + ε` is averaged over
  `(p, g, x)`; the reduction fixes `(p, g)` from its input. Good-set argument over `(p, g)`:
  `half_le_uprob_threshold` gives a set of `(p, g)` of probability `≥ ε/2` on which the success
  over uniform `x` is `≥ 1/2 + ε/2` (rename `ε` accordingly in .3); the final inversion probability
  is `≥ (ε/2) · (ε/8) · (3/4)` up to the constants chosen. Union bound over the `|p|` rounds
  (`uprob_exists_le`). Difficulty 3.
Asymptotic bridge: the inverter makes `|p| · ℓ(n)` calls to `A` with fresh coins
(Machine-Repetition), modular exponentiations (Thm 45.6), square roots (Thm 58.2), majority
(Machine-Primitives), and samples `Z_{p−1}` from coins — exact uniform sampling of `Z_{p−1}` by a
worst-case-time PPT is impossible; sample `|p| + n` bits and reduce mod `p−1` (statistical distance
`≤ 2^{−n}`), recorded as a Deviation (the same device is needed for Asm 105.1 / Alg 106.2). Everything
else is `Negligible` arithmetic. Total difficulty 5; recommend the concrete statement as the core
deliverable and the asymptotic wrapper with (ii) above.

**Thm-87.3** — *Goldreich–Levin.* Let `f` be a OWF (resp. OWP) and `g(x, r) = (f(x), r)` with
`|x| = |r|`. Then `g` is a OWF (resp. OWP) and `h(x, r) = ⟨x, r⟩` is a hard-core predicate for `g`.
**Text error:** the statement says "hard-core predicate for `f`"; it is for `g` (the proof and all
uses are for `g`). Two parts:

* **Thm-87.3.a** `g` one-way: concrete `OneWay.invProb_pad_le : invProb (pad f) A ≤ invProb f (padInverter A)`
  with `pad f (x, y) = (f x, y)` — exactly `g`; `padInverter A v (y, r) = (A (v, y) r).1` draws the
  padding and calls `A` once (Machine-Closure). `g` is a permutation iff `f` is (`Equiv.prodCongr f (Equiv.refl _)`).
  Note `HardcoreBit.glPad f` is the same map on bit strings (`glPad f z = (f z.1, z.2)`); the two
  developments should be glued by `rfl`/`Prod.ext`. Difficulty 2.
* **Thm-87.3.b** `⟨x,r⟩` hard-core for `g`, asymptotic: for every nuPPT `A`, `Negligible (fun n => predProb (glPad (f n)) glBit (A.pred n) − 1/2)`.
  Proof: if not, `not_negligible_iff` gives `c` with `predProb ≥ 1/2 + n^{−c}` for infinitely many
  `n`; set `ε = n^{−c}` and `k(n) = ⌈log₂(2 n^{2c+1} + 1)⌉` (depends only on `n, c`), so that
  `2n ≤ ε² (2^k − 1)`; `invProb_guessInverter` gives `invProb (glPad f) (guessInverter A k) ≥ ε/(4·2^k) ≥ n^{−c}/(16 n^{2c+1} + 8)`
  — inverse polynomial infinitely often, contradicting one-wayness of `g` (87.3.a). Use
  `invProb_guessInverter` (hypothesis `hk` only), **not** `invProb_guessInverter_cubic` (its second
  hypothesis `ε² 2^k ≤ 4n` cannot be guaranteed uniformly when `ε` is unknown to the reduction).
  The inverter `guessInverter A k` makes `n(2^k − 1) = O(n^{2c+2})` calls to `A` with fresh coins,
  draws `k` strings and `k` bits, computes subset XORs, inner products and `n` majorities
  (Machine-Repetition + Machine-Primitives); `k(n)` and `c` are hard-wired (advice or computed from
  `n`). Difficulty 4.
Concrete sub-items all exist (`HardcoreBit/*`): the setting **Thm-87.3.c** (`ip`, `glPad`, `glBit`,
`glInverter`, `secProb`, `predProb_glPad_eq`); the **oversimplified case** Thm-87.3.1
(`invProb_perfectInverter`: `predProb = 1 ⇒ invProb = 1`, queries `e_i`, `ip_single`); the
**less simplified case** Thm-87.3.2 (`invProb_majorityInverter`: `3/4 + ε ≤ predProb`, `n ≤ 2ε²T`
⇒ `ε/4 ≤ invProb`; the text's `m = poly(1/ε)` with Chernoff is `T` with Chebyshev); the good set
Thm-87.3.3 (`half_le_uprob_good`, for both thresholds; the text's displayed inequality chain
`< ε/2 + (1 − ε/2)(3/4 + ε/2) < 3/4 + ε` is this lemma); **Fact-88.4** (`ip_add`, `ip_sum`);
**Alg-88.5** (`majorityInverter`), **Alg-89.6** (`guessInverter` with the "subroutine `C`"
implemented by guessing `b'_1 … b'_{log m}` and forming subset sums); Thm-87.3.6
(`uprob_idealRecover_ne_le`: each bit wrong w.p. `≤ 1/(ε²(2^k − 1))`, then `one_sub_sum_le_uprob_eq`
for the union bound; the text's "`n/(mε'^2) < 1/2` when `m ≥ 2n/ε'^2`" is the hypothesis `hk`);
Thm-87.3.7 (the "show this!": `pairwiseUniform_subsetSum` — note the text takes
`r_1, …, r_{m−1}` as sums over subsets of `log m` strings, i.e. `2^{log m} − 1` *nonempty*
subsets, which matches the formalization exactly; Garg's text included `L = ∅`); Thm-87.3.8
(`uprob_guess_eq`: all `log m` guesses right w.p. `1/m`; `guessRecover_correct_guess`);
Thm-87.3.9 (final bound). **Constants:** in the text's own notation the predictor has success
`1/2 + ε`, the good set uses `ε' = ε/2`, `m = 2n/ε'^2`, and the final bound is
`ε'/(2m) = ε'^3/(4n) = (ε/2)^3/(4n) = ε^3/(32n)`; the concrete layer proves `ε^3/(16n)`
(`invProb_guessInverter_cubic`), which is *stronger*. The plan's seeded note ("`ε^3/(4n)` becomes
`ε^3/(16n)`") compares `ε'` with `ε`; correct it to: PS10 `ε^3/(32n)` ≤ Garg `ε^3/(16n)`.

**Thm-87.3.coll** (unnumbered; required so that "if trapdoor permutations exist" in Thm 104.4 and
"OWP with a hard-core predicate" in ch. 4 Thm 126.4 are meaningful): for a collection `{f_i}`
(OWF/OWP/TDP) with index sampler `Gen`, `g_i(x, r) = (f_i(x), r)` is a collection of the same kind
and `h(x, r) = ⟨x, r⟩` is hard-core for it (Def-78.3.coll). Proof: the concrete GL theorem is per
fixed `f_i`; average over `i`: if the predictor succeeds w.p. `≥ 1/2 + ε` over `(i, x, r)`, then
`half_le_uprob_threshold` gives a set of `i` of probability `≥ ε/2` on which it succeeds w.p.
`≥ 1/2 + ε/2`, and `invProb_guessInverter` applies to each such `f_i` (the inverter receives `i`
as part of its input `(i, f_i(x), r)`); inversion probability `≥ (ε/2) · (ε/2)/(4·2^k)`. Difficulty 3.

### 2.5 §3.5–§3.7 Secure private-key encryption

**Def-91.1** — *Single-message security.* An efficient private-key scheme `(Gen, Enc, Dec)`
(Def 24.7: `Gen(1^n)` PPT, `Enc_k(m)` PPT for `m ∈ {0,1}^n`, `Dec_k(c)` PPT with output in
`{0,1}^n ∪ {⊥}`, `Pr[Dec_k(Enc_k(m)) = m] = 1`) is single-message secure iff for every nuPPT `D`
there is a negligible `ε` with, for all `n` and all `m_0, m_1 ∈ {0,1}^n`,
`distAdv {k ← Gen(1^n) : Enc_k(m_0)} {k ← Gen(1^n) : Enc_k(m_1)} D ≤ ε(n)`. Formal: the scheme is
a structure with `keyLen, ctLen : ℕ → ℕ` (explicit polynomials), `gen n : coins → key`,
`enc n : key → msg → coins → ct`, `dec n : key → ct → Option msg`, PPT fields and correctness;
`SingleMessageSecure S := ∀ D nuPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (encDist S n m₀) (encDist S n m₁) (D.dist n) ≤ ε n`
with `encDist S n m : (keyCoins × encCoins) → ct`. The quantifier order (`ε` before `m_0, m_1`) is
the text's; equivalently `Negligible (fun n => ⨆ m₀ m₁, distAdv …)` over the finite message space.
Deviation: message length is a fixed polynomial of `n` (the text's `n`; Alg 92.1 uses `2n`-bit
messages below). Downstream: ch. 4 Thm 112.2 (zero-knowledge encryption ⇔ security) needs exactly
this definition plus a PPT message sampler.

**Alg-92.1** — `Gen(1^n): k ← U_{n/2}`; `Enc_k(m) = m ⊕ G(k)`; `Dec_k(c) = c ⊕ G(k)` with `G`
length-doubling. Text issue: `n/2` needs `n` even. Formal (Deviation): key length `n`, message and
ciphertext length `2n`, `G : {0,1}^n → {0,1}^{2n}` (or any `ℓ(n)`-bit message with a PRG of
stretch `ℓ`). Enc/Dec are PPT: one evaluation of `G` and a bitwise XOR (Machine-Primitives: XOR of
two equal-length strings given as `pairEncode`). Correctness: `(m ⊕ G k) ⊕ G k = m` (`add_add_cancel`
in the Boolean ring). Difficulty 2.

**Claim-92.a** — *OTP perfect secrecy (used in Thm 92.2 and 99.2).* For every `m : Fin ℓ → Bool`,
the map `u ↦ m + u` is a bijection, so `{u ← U_ℓ : m ⊕ u}` is `U_ℓ`; hence
`acceptProb (fun u => m₀ + u) D = acceptProb (fun u => m₁ + u) D` for every `D`.
Exists as `pushesUniform_xor`/`uprob_comp_equiv (Equiv.addLeft m)`; one-liner. Vector version
(Thm-99.2.3): `(u_j) ↦ (m_j + u_j)` is a bijection of `Fin q → Fin ℓ → Bool`.

**Thm-92.2** — Scheme 92.1 is single-message secure. Concrete: for all `D`, `m_0, m_1`,
`distAdv (Enc(m₀)) (Enc(m₁)) D ≤ prgAdv G (fun z r => D (m₀ + z) r) + prgAdv G (fun z r => D (m₁ + z) r)`.
Proof: hybrids `H¹ = m₀ ⊕ G(U_n)`, `H² = m₀ ⊕ U_{2n}`, `H³ = m₁ ⊕ U_{2n}`, `H⁴ = m₁ ⊕ G(U_n)`;
`|P(H¹) − P(H²)| = prgAdv G (D ∘ (m₀ ⊕ ·))` by `distAdv_comp`; `P(H²) = P(H³)` by Claim-92.a;
`|P(H³) − P(H⁴)|` likewise; triangle inequality (`abs_sub_le_sum_hybrids` with `t = 3` or two
`abs_sub_le`). Bridge: `D ∘ (m_i ⊕ ·)` is nuPPT with `m_i^n` hard-wired as advice (the text's
footnote: "`M_i` is non-uniform as it has the message hard-coded") — Machine-Closure; the message
family `n ↦ (m₀^n, m₁^n)` extracted from the negation of the definition (choice of a witness pair
per `n`: `Classical.choose`, fine). Difficulty 2. Text issues: hybrid labels "`H²_n` (OTP with
`m_1`)" should read `m_0`; "distinguishes two consecutive hybrids with probability `1/4p(n)`" is
`1/(3p(n))` (three gaps).

**Def-93.1** — *Multi-message security.* For every nuPPT `D` and every polynomial `q` there is a
negligible `ε` with, for all `n` and all `m_0, …, m_{q(n)}, m'_0, …, m'_{q(n)} ∈ {0,1}^n`,
`distAdv {k ← Gen : (Enc_k(m_0), …, Enc_k(m_{q(n)}))} {k ← Gen : (Enc_k(m'_0), …)} D ≤ ε(n)`;
the `q(n) + 1` encryptions use one key and independent encryption coins. Formal: sampler
`multiEncDist S n q (m : Fin (q+1) → msg) : keyCoins × (Fin (q+1) → encCoins) → Fin (q+1) → ct`.
Note the count is `q(n) + 1` messages (indices `0 … q(n)`). Difficulty 2.

**Thm-94.2** — A multi-message secure scheme cannot be deterministic and stateless. Precise: if
`Enc` is deterministic (`enc n k m c` does not depend on `c`) and stateless (the model is
stateless anyway), the scheme is correct, `n ≥ 1` and `q(n) ≥ 1`, then the PPT distinguisher
`D((c_0, c_1, …)) = [c_0 = c_1]` has advantage exactly `1` between the encryptions of
`(m_0, m_0, …)` and `(m_0, m_1, …)` with `m_0 ≠ m_1`: in the first `c_0 = c_1`; in the second
`c_0 ≠ c_1` because `Dec_k` is a function and recovers `m_0 ≠ m_1` (correctness with probability
`1`, `forall_of_uprob_eq_one`). Hence Def 93.1 fails (a negligible `ε` is eventually `< 1`).
Difficulty 2 (string equality: Machine-Primitives/`polyTimeComputable_lenEq`-style test).
Text issue: the proof needs correctness to get `c'_0 ≠ c'_1` (not stated) and `m_0 ≠ m_1`.

The discussion after Thm 94.2 (`r ‖ m ⊕ f(r)`, "no PRG produces exponentially many bits",
birthday collisions for `|r| = O(log n)`) is motivation, not claims to formalize.

### 2.6 §3.8–§3.9 Pseudorandom functions and multi-message encryption

**Def-95.a / Claim-95.b** — `RF_n` is the uniform distribution on functions `{0,1}^n → {0,1}^n`
(`randomFunction I O = id` on the seed type `I → O`, `Fintype.card_fun` gives `2^{n 2^n}`). The
"computational description" (answer a new query with a fresh uniform value, repeat recorded
answers) gives the same distribution: `QueryTree.uprob_evalLazy` (lazy sampling with `q` fresh
values equals the uniform table, for trees making `≤ q` queries). Both exist; difficulty 1.

**Def-96.1** — *Oracle indistinguishability.* For ensembles `{O_n}, {O'_n}` of distributions over
functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, `{O_n} ≈ {O'_n}` iff for every nuPPT oracle machine `D`
there is a negligible `ε` with `|Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]| < ε(n)`
for all `n`. Typo: the text writes `{O'_n} ≈ {O'_n}`. D7 reading: an oracle ensemble is a family
of samplers `O n : seeds → (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)` (for `RF_n` the seed *is* the table
— exponentially long, fine at the concrete level; for a keyed family the seed is the key); an
nuPPT oracle adversary is an nuPPT `M` that, on `(1^n, α_n, coins, transcript)`, outputs the next
query or a final bit, with an explicit polynomial query bound `q(n)`; it determines a
`OracleAdversary ρ I O` (a `QueryTree` per coin string) with `BoundedBy (q n)`, and the advantage
is `distAdv (O n) (O' n) (oracleDist A)`. Deviation (D7): no machine-level oracle tape; the
`Turing.OracleTM` of `TuringMachine/Oracle.lean` is a *decision*-oracle model (yes/no answers),
not usable for string-valued oracles without new infrastructure. Difficulty 3 (the unfolding of
the driver machine into a `QueryTree` with the bound is the only real work).
**Claim-96.a** (closure under efficient oracle operations): if `{O_n} ≈ {O'_n}` and `M` is an nuPPT
oracle machine computing a function with oracle access, then `{M^{O_n}} ≈ {M^{O'_n}}` as oracle
ensembles. Concrete: a "query-tree-valued simulation" `QueryTree.bind`: each query `x` of the
outer tree is answered by running an inner tree (`M` on `x`) against the oracle; `eval` and the
query bound multiply. Only the one-query-per-query case exists (`QueryTree.simulate`,
`eval_simulate`, `BoundedBy.simulate`). Optional, difficulty 3.
**Claim-96.b** (hybrid lemma for oracles) is `exists_hybrid_gap` on `acceptProb (O^i) (oracleDist A)`;
exists. **Claim-96.c** (prediction lemma for oracles) is Claim-73.a's identity with the oracle
distinguisher; optional, difficulty 2.

**Def-96.2** — *PRF.* A family `{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` is pseudorandom iff (1)
`f_s(x)` is computable by a PPT given `(s, x)` and (2) `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle
ensembles. Formal: `F n : (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`,
`PolyTimeComputable (bridge of (s, x) ↦ F n s x)`, and `∀ A nuPPT-oracle with bound q, Negligible (fun n => prfAdv (F n) (A n))`
where `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)` (exists, `Defs.lean`).
Difficulty 2. Remark (p. 96, "critical that `s` is not revealed") is not a claim in the model.

**Cor-97.a** (first sentence of the proof of Thm 97.3: "any PRG `g` is sufficient to construct a
PRG `g'` with polynomial expansion … WLOG `g` is length-doubling") — from a PRG `G : n → ℓ(n) > n`
bits: truncation `G₁ = G` restricted to its first `n + 1` bits is a PRG (post-processing by a
projection: `distAdv_comp`), and Lem 80.5 applied to `G₁` with `ℓ' = n` gives output `2n` bits
(`prgExtBits G₁ n : Fin (n + n) → Bool`). Needed so that Thm 97.3 can be stated literally ("if a
PRG exists then PRFs exist"). Difficulty 2 (plus Machine-Loop for computability).

**Constr-97.b** — GGM: `f_s(b_1 … b_n) = g_{b_n}(⋯ g_{b_1}(s) ⋯)` with `g(x) = g_0(x)‖g_1(x)`.
Exists: `ggmBits G : (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool` (`ggm (splitHalves ∘ G)`),
`ggmFrom`, `pairSel`. **Claim-97.c** (clause (1) of Def 96.2 for GGM): `(s, x) ↦ f_s(x)` is
PPT-computable: `n` evaluations of `G` with a selected half — Machine-Loop over the bits of `x`
(`exists_loopTM`-based) plus `splitHalves` on tapes (prefix/suffix extraction). Difficulty 3.

**Thm-97.3** — If a PRG exists then a PRF exists; precisely: if `G : {0,1}^n → {0,1}^{2n}` is a
PRG then `ggmBits G` is a PRF. Concrete (exists): `ggmBits_prfAdv_le : A.BoundedBy q → prfAdv (ggmBits G) A ≤ ∑_{i<n} ∑_{j<q} distAdv G id (ggmBitsDist G A q i j)`
and `exists_ggmBits_dist : 0 < n → 0 < q → ∃ i j, prfAdv (ggmBits G) A / (n q) ≤ distAdv G id (ggmBitsDist G A q i j)`.
Hybrids: **Thm-97.3.1** level hybrids `HF^i` (`hybridOracle G i`: levels `≤ i` random, below
pseudorandom; `hybridProb_zero`: `H_0 = f_s`, `hybridProb_top`: `H_n = RF_n`; the text's indexing
`HF^1 = f_s`, `HF^n = RF_n` has `n − 1` gaps and bound `ε/n`; the formal one has `n` gaps);
**Thm-97.3.2** query sub-hybrids `HHF^j` (`subHybridProb`, `tableDist`, `table_hybrid`,
`hybridProb_level`; Deviation documented in `SubHybrids.lean`: sub-hybrids indexed by *distinct*
prefixes in order of first appearance, the challenge answers every query with that prefix);
**Thm-97.3.3** "queries to `HHF^j` can be emulated in PPT (lazy sampling)": the distinguisher
`ggmBitsDist G A q i j` (cost documented in its docstring: one run of `A`, `≤ n` evaluations of
`G` per query, `q` fresh seeds and `q` fresh pairs as coins, a list of `≤ q` prefixes) must be
exhibited as an nuPPT oracle-free distinguisher: Oracle-D7 (driving `A`'s query tree inside the
reduction), Machine-Loop (`G` iterations), Machine-Closure (advice `i, j`), lazy-sampling list
maintenance (`noteQuery`) — difficulty 4. Then `Negligible.mul_pow` for the factor `n q(n)`.
Bridge total difficulty 4.

**Alg-99.1** — `Gen(1^n): k ← U_n`; `Enc_k(m): r ← U_n, output (r, m ⊕ f_k(r))`; `Dec_k(r, c) = c ⊕ f_k(r)`
for a PRF `{f_k}` and `m ∈ {0,1}^n`. Ciphertext length `2n`; Enc PPT (Claim-97.c + XOR). Difficulty 2.

**Thm-99.2** — Scheme 99.1 is multi-message secure. Concrete statement (new): for every `D` and
message vectors `m, m' : Fin (q+1) → Fin n → Bool`,
`distAdv (multiEnc m) (multiEnc m') D ≤ prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) · 2^{−n}`
where **Thm-99.2.1** `A_m D : OracleAdversary` draws `r_0 … r_q`, queries the oracle at each `r_j`
(a chain of `q + 1` `query` nodes, `BoundedBy (q+1)`), and runs `D` on `((r_j, m_j ⊕ F(r_j)))_j`
— `H¹ → H²` is `prfAdv F (A_m D)` by definition of `oracleDist` (and `acceptProb` unfolding);
**Thm-99.2.2** `|P(H²) − P(H³)| ≤ C(q+1,2) 2^{−n}`: `H²` uses a uniform table `R` at the points
`r_j`, `H³` uses fresh uniform pads `p_j`; on the event `Inj := ∀ i ≠ j, r_i ≠ r_j` the tuple
`(R(r_j))_j` is uniform (evaluation of a uniform table at distinct points pushes uniform to
uniform: a generalization of `pushesUniform_eval_pair` to injective index tuples, provable via
`Equiv.funSplitAt`/`uprob_update_absorb` by induction, or by `uprob_pi_forall` counting), so the two
hybrids agree conditioned on `Inj`; `Pr[¬Inj] ≤ ∑_{i<j} Pr[r_i = r_j] = C(q+1,2) 2^{−n}`
(`uprob_exists_le`, `uprob_eq_one_div_card`); a coupling lemma "two experiments that agree on an
event `E` have advantage `≤ Pr[¬E]`" (new, generic, difficulty 2; `distAdv_le_statDist` is an
alternative route via `FinDist`); **Thm-99.2.3** `P(H³) = P(H⁴)` by the vector OTP (Claim-92.a);
`H⁴ → H⁵ → H⁶` symmetric. Difficulty 4 (new 300–400-line concrete file). Bridge: `A_m D` is an
nuPPT oracle adversary with `q(n) + 1` queries and the messages as advice (Oracle-D7,
Machine-Closure); `Negligible` arithmetic with `C(q(n)+1, 2) 2^{−n}` (`negligible_two_pow_neg`,
`Negligible.mul_pow`). Text issue: the collision bound is written `C(q(n), 2) 2^{−n}` for
`q(n) + 1` values; should be `C(q(n)+1, 2)`.

### 2.7 §3.10–§3.12 Public-key encryption, DDH, El Gamal, closing remarks

**Def-102.1** — *PKE scheme.* `(Gen, Enc, Dec)` with (1) `(pk, sk) ← Gen(1^n)` PPT; (2)
`c ← Enc_pk(m)` PPT for `m ∈ {0,1}^n`; (3) `Dec_sk(c)` deterministic with output in `{0,1}^n ∪ {⊥}`;
(4) a polynomial-time `M` with `M(1^n, i)` = the `i`-th `n`-bit message in some order (if it
exists); (5) `Pr[(pk,sk) ← Gen(1^n) : Dec_sk(Enc_pk(m)) = m] = 1` for all `n`, `m`. Formal: structure
with explicit polynomial lengths for `pk, sk, ct`, PPT fields, `dec` a plain function (PolyTime),
correctness, and a `PolyTimeComputable` message enumerator (clause (4) is odd — for `{0,1}^n`
messages the `i`-th message is the binary expansion of `i`; keep it as a field so that ch. 4
Thm 112.2's analogue for PKE can use it, or drop it with a Deviation note; the plan's seeded issue
list already flags Thm 112.2's sampler). Difficulty 2.

**Def-102.2** — *Secure PKE.* For every nuPPT `D` there is a negligible `ε` with, for all `n` and
`m_0, m_1 ∈ {0,1}^n`, `distAdv {(pk,sk) ← Gen : (pk, Enc_pk(m_0))} {… (pk, Enc_pk(m_1))} D ≤ ε(n)`
(the public key is part of the distinguisher's input). Difficulty 2.

**Claim-103.a** — perfect secrecy is impossible for PKE: for a correct scheme and `m_0 ≠ m_1`, the
supports of `Enc_pk(m_0)` and `Enc_pk(m_1)` are disjoint for each `(pk, sk)` (a common ciphertext
would decrypt to both), so `statDist ((pk, Enc_pk(m_0))) ((pk, Enc_pk(m_1))) = 1` and the
(unbounded) test "is `c` in the support of `Enc_pk(m_0)`" has advantage `1`. Optional, difficulty 2.
**Claim-103.b** — deterministic PKE is insecure: if `Enc_pk(m)` ignores its coins, the nuPPT
`D(pk, c) = [c = Enc_pk(m_0)]` has advantage `1` (needs `Enc` PPT so that `D` is efficient, and
correctness for `Enc_pk(m_0) ≠ Enc_pk(m_1)`). Optional, difficulty 2. **Constr-104.a**
(`Enc_i(m) = f_i(m)`, "the RSA cryptosystem", p. 104) is an instance.

**Def-103.c** (unnumbered) — multi-message PKE security: as Def 93.1 with `(pk, Enc_pk(m_0), …, Enc_pk(m_{q(n)}))`,
fresh coins per encryption, one key pair. **Thm-103.d** (exercise, p. 103) — for PKE,
single-message security implies multi-message security. Concrete: for every `D`, `q`, `m, m'`:
`distAdv (multiEnc m) (multiEnc m') D ≤ ∑_{j ≤ q} distAdv (singleEnc m_j) (singleEnc m'_j) (D_j)`
where `D_j(pk, c)` encrypts `m'_0 … m'_{j−1}` and `m_{j+1} … m_q` itself under `pk` (fresh coins),
places `c` at position `j` and runs `D` — the key point being that encryption needs only `pk`
(impossible for private-key schemes). This is `exists_multicopyRed_ge`'s hybrid with a shared
`pk` and position-dependent samplers; reuse the proof pattern (`multicopyHybrid`, planting via
`acceptProb_update`), not the lemma itself (it assumes identical copies and no shared parameter).
Bridge: `D_j` is nuPPT (runs `Enc` `q` times: Machine-Repetition; advice `j`, messages). Difficulty 3.
Downstream: ch. 4 Def 126.3/Thm 126.4 "multi-value hiding follows by a simple hybrid argument
(show this!)" is the same lemma with `Com(v, r)` in place of `Enc_pk`; design the concrete lemma
generically (a family of samplers `X_j(pk; m)` with `pk` sampled once) so both uses share it.

**Def-103.e** (unnumbered) — single-bit secure PKE: Def 102.2 with message space `{0,1}`
(`m_0 = 0`, `m_1 = 1` only). **Thm-103.f** (stated, p. 103) — encrypting an `n`-bit message bit by
bit under a single-bit secure PKE gives a secure PKE for `{0,1}^n` (and the resulting scheme meets
Def 102.1 with `Dec` returning `⊥` if any bit decrypts to `⊥`). Proof: Thm-103.d for the
single-bit scheme with `q = n − 1` gives `distAdv ≤ ∑_{i<n} (single-bit advantage of D_i) ≤ n · ε(n)`;
`Negligible.mul_pow`. Difficulty 3 (mostly bookkeeping of the bitwise scheme as a PKE).

**Alg-104.3** — 1-bit PKE from a TDP collection with hard-core bits: `Gen(1^n): (f_i, f_i^{−1}) ← Gen_T(1^n)`,
`pk = (f_i, b_i)` (the index `i`), `sk = f_i^{−1}` (the trapdoor `t`); `Enc_pk(m): r ← {0,1}^n, (f_i(r), b_i(r) ⊕ m)`;
`Dec_sk(c_1, c_2) = b_i(f_i^{−1}(c_1)) ⊕ c_2`. Correctness is `f_i^{−1}(f_i(r)) = r`. Domain
Deviation: the text samples `r ← {0,1}^n` while Def 56.1 has domains `D_i` with a sampler; take
`D_i = {0,1}^n` or sample `r ← D_i` with the collection's sampler (the proof is the same). The
hard-core bits `b_i` come from Thm-87.3.coll applied to the TDP (`g_i(x, r) = (f_i(x), r)`, which
is again a TDP). Difficulty 2.

**Lem-104.a** (the concrete content of the proof of Thm 104.4; also the hiding proof of ch. 4
Thm 126.4) — for a family of permutations `f_i` with bits `b_i` and an index sampler, and any
distinguisher `D` of `X⁰ = (i, f_i(r), b_i(r))` versus `X¹ = (i, f_i(r), ¬b_i(r))` (these are the
encryptions of `0` and `1`), the predictor `A'(i, y)`: draw `c ← {0,1}`, `m ← D(i, (y, c))`, output
`c ⊕ m` (negated if `flip`), satisfies, for one `flip`,
`predProb (fun (i, r) => (i, f_i r)) (fun (i, r) => b_i r) (A' flip) = 1/2 + distAdv X⁰ X¹ D / 2`.
This is `predProb_owpPredictor_false/true`, `acceptProb_id_owp`, `exists_owpPredictor` with an
index carried along (`owpGen f B` has a fixed `f : α ≃ α`; the indexed version replaces `α` by
`Σ i, D_i` or threads `i` through `β`). The text's proof first applies the prediction lemma to the
ciphertext distinguisher and then converts the predictor `A` of `m` into a predictor of `b`: the
composite is exactly `owpPredictor`. Difficulty 3.

**Thm-104.4** — If trapdoor permutations exist then scheme 104.3 is a secure single-bit PKE.
Precise: for a TDP collection with a hard-core bit family (Thm-87.3.coll supplies one), scheme
104.3 satisfies Def-103.e. Proof: Lem-104.a + `not_negligible_iff`; bridge: `A'` is nuPPT (one
coin, one call, advice bit). Text issues: the hypothesis omits the hard-core bit (needs 87.3 for
collections); "By the prediction lemma, there exist a machine `A` such that
`Pr[… D(pk, Enc_pk(m)) = m]`" writes `D` for `A`. Difficulty 3.

**Asm-105.1** — *DDH.* `{p ← Π̃_n; y ← Gen_q; a, b ← Z_q : (p, y, y^a, y^b, y^{ab})} ≈ {…; a, b, z ← Z_q : (p, y, y^a, y^b, y^z)}`,
where `Π̃_n = {p ∈ Π_n : p = 2q + 1, q ∈ Π_{n−1}}` (safe primes), `Gen_q` = generators of the
order-`q` subgroup `G_q ⊆ Z_p^*` (every element `≠ 1` of `G_q`). Formalization issues: (i) no
PPT is known to sample safe primes (the text says so in §2.8), and exact uniform sampling of
`Z_q` by a worst-case-time PPT is impossible — so the assumption should be stated **relative to a
group-instance generator** `GenG : PPT` outputting `(p, q, y)` with `p = 2q + 1` prime and `y` a
generator of `G_q`, and with exponents sampled as `(|q| + n)`-bit numbers reduced mod `q`
(statistical distance `≤ 2^{−n}` from uniform), as Deviations; alternatively state the assumption
with the uniform (non-efficient) samplers at the concrete level and only require efficiency of the
reduction (which is all Thm 107.3 uses) — but then Alg 106.2's `Gen` is not PPT, violating
Def 102.1(1). Recommended: `GenG` abstraction (standard), `DDH GenG := CompIndist (ddhReal GenG) (ddhRandom GenG)`.
(ii) The tuple is encoded as a bit string (`pairEncode` chain) — D6. Difficulty 2 given NT-105.a.

**NT-105.a** — for `p = 2q + 1` with `p, q` prime (`q` odd): `Z_p^* ≅ (ZMod p)ˣ` is cyclic of order
`2q` (Mathlib instance `IsCyclic Rˣ` for finite integral domains, `ZMod.card_units_eq_totient`,
`Nat.totient_prime`); the squares form a subgroup of order `q` (image of `x ↦ x^2`, kernel `{±1}`,
`Subgroup.card_eq_card_quotient_mul_card_subgroup`), which is the unique subgroup of order `q`
(`IsCyclic.card_pow_eq_one_le`); it is cyclic of prime order so every element `≠ 1` generates
(`orderOf_eq_prime`/`orderOf_dvd_card`); `x ∈ G_q ↔ x^q = 1 ↔ IsSquare x` (`ZMod.euler_criterion`).
Difficulty 3 (Mathlib glue; nothing exists in TCSlib; `SchnorrProtocol.lean` works in an abstract
group `G` with `ZMod q` exponents and may be a model for the El Gamal file).

**Claim-106.a** — DDH ⇒ DL (p. 106): if DL in `G_q` is solvable w.p. `δ` (non-negligible), the
distinguisher that computes `a` from `y^a` and tests `(y^b)^a = z` has advantage `≥ δ(1 − 1/q)`
(on a DDH tuple it accepts whenever the DL succeeds; on a random tuple it accepts only if the DL
succeeds *and* `z = y^{ab}`, probability `δ/q`). Optional, difficulty 3 (needs the DL assumption in
`G_q`, Asm 52.2's actual form).
**Claim-106.b** — in a non-prime-order group such as `Z_p^*` the DDH assumption is false (element
orders `2, q, 2q`, i.e. the Legendre symbol, distinguish `y^{ab}` from `y^z`). Optional, difficulty 3
(Mathlib `legendreSym`, `quadraticChar`); the Garg plan deferred the same attack.

**Alg-106.2** — El Gamal: `Gen(1^n)`: safe prime `p = 2q + 1` of length `n`; random `g ∈ Z_p`,
`h = g^2 mod p`; `a ← Z_q`; `pk = (p, h, h^a)`, `sk = (p, h, a)`. `Enc_pk(m)`: `b ← Z_q`,
`(h^b, h^{ab} · m)`. `Dec_sk(c_1, c_2) = c_2 / c_1^a`. Correctness: `h^{ab} m / (h^b)^a = m` for
`m ∈ Z_p^*` (`c_1 ≠ 0`). Text issues: `g` "random in `Z_p`" may be `0` or `±1`, giving `h ∈ {0, 1}`
(then `pk` is degenerate; probability `3/p`); `Gen` should draw `g ∈ Z_p^* ∖ {±1}` or resample;
`q` is omitted from `pk` (recoverable as `(p−1)/2`). **Message space (text error, see Thm 107.3):**
`m` must lie in `G_q`. Formal: `Gen = GenG` plus `a`; `pk = (p, q, h, h^a)`. Modular exponentiation
is Thm 45.6; sampling as in Asm-105.1. Difficulty 2.

**Claim-107.a** (missing in the text) — for uniform `g ∈ Z_p^*`, `h = g^2` is uniform on `G_q`
(`x ↦ x^2` is a surjective homomorphism `Z_p^* → G_q` with fibres of size `2`:
`pushesUniform_of_surjective`); `h` is a generator of `G_q` unless `h = 1` (probability `1/q`), so
the distribution of `h` is within statistical distance `1/q ≤ 2^{−(n−2)}` of the uniform generator
`y ← Gen_q` used in Asm 105.1 (`statDist`, `distAdv_le_statDist`); this term is negligible and
must be added to the bound in Thm 107.3. Difficulty 2.

**Thm-107.3** — If DDH holds then El Gamal is secure. Precise (with message space `G_q`): for every
nuPPT `D` there is a negligible `ε` with, for all `n` and `m_0, m_1 ∈ G_q`,
`distAdv {(pk, Enc_pk(m_0))} {(pk, Enc_pk(m_1))} D ≤ ε(n)`. Concrete: with `T_real = (p, h, h^a, h^b, h^{ab})`
and `T_rand = (p, h, h^a, h^b, h^z)`,
`distAdv (Enc(m₀)) (Enc(m₁)) D ≤ ddhAdv (D ∘ mult m₀) + ddhAdv (D ∘ mult m₁) + 2/q`
where `mult m (p, h, A, B, Z) = ((p, h, A), (B, Z · m))` (`distAdv_comp`), the middle hybrids
`(pk, h^b, h^z m_0)` and `(pk, h^b, h^z m_1)` coincide because `z ↦ h^z m` is a bijection of `G_q`
for `m ∈ G_q` (`Equiv.mulLeft`, `acceptProb_comp_equiv`), and `2/q` accounts for Claim-107.a
(generator vs square sampling). **Text error:** with `m ∈ Z_p^*` arbitrary (as the scheme is
written), `h^z · m` ranges over the coset `m G_q`, so encryptions of a quadratic residue and a
non-residue are distinguishable by the Legendre symbol of `c_2` (Claim-106.b); the "exercise" is
false as stated and true for `m ∈ G_q` (or with **Def-107.b**: encode `m ∈ [1, q]` as `m` if
`IsSquare m` else `p − m` — exactly one is a square since `−1` is a non-residue for `p ≡ 3 (4)`,
`ZMod.exists_sq_eq_neg_one_iff`, and `p = 2q + 1` with `q` odd is `≡ 3 (4)`; decoding compares
with `q`; this meets Def 102.1's bit-string message space up to length bookkeeping — optional,
difficulty 3). Bridge: `D ∘ mult m_i` is nuPPT with `m_i` as advice and one modular
multiplication (Thm 45.6-level arithmetic; Machine-Closure). Difficulty 3.

**Claim-107.c** (§3.12, "one-way functions are a minimal assumption, because the existence of any
of these primitives implies the existence of one-way functions") — the PRG case is formalizable:
a PRG `G` with stretch `ℓ(n) ≥ n + 1` is a OWF: an inverter `B` with `invProb G B = δ` gives the
distinguisher `D(t) = [G(B(t)) = t]`, accepting `G(U_n)` w.p. `δ` and `U_ℓ` w.p. `≤ 2^{n−ℓ} ≤ 1/2`
(only image points can be accepted), so `prgAdv ≥ δ − 1/2` — this needs `δ > 1/2`; the standard
proof first amplifies or uses `ℓ ≥ 2n` (then `2^{−n}`) — for a general PRG compose with Lem 80.5
first. Optional, difficulty 3. The PRF/encryption ⇒ OWF cases and **Claim-107.d** (Impagliazzo–Rudich,
no black-box PKE from OWF) are deferred (the latter is not formalizable in this framework).

### 2.8 Appendix facts cited by chapter-3 proofs

**Thm-188.7** (Chernoff, `Pr[|∑X_i − μn| ≥ ε] ≤ 2^{−ε²n}`), **Lem-189.8** (majority vote; the
statement is garbled, "`> 1 − 2??`", proof unfinished "we have that …") and the unnumbered
**pairwise-independent sampling inequality** (`Pr[|∑X_i/n − μ| ≥ ε] ≤ (1 − μ²)/(nε²)`, "a corollary of
Chebyshev") are used in Lem 84.1 (majority test), Thm 87.3 (both cases) and the remark after
Def 24.6. The concrete layer replaces all of them by Chebyshev for pairwise independent bits:
`chebyshev_pairwise`, `chebyshev_pairwise_ident` (`Pr[|∑X_i − pm| ≥ δm] ≤ 1/(4δ²m)`) and
`uprob_majority_fails_le` (majority of `m` pairwise independent trials each right w.p. `≥ 1/2 + δ`
fails w.p. `≤ 1/(4δ²m)`), which give polynomially many trials instead of `O(ε^{−2} log)` — enough
for every asymptotic statement. Chernoff (not in Mathlib in this form; Mathlib has
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` for measures) is optional, difficulty 3, and only
worth doing if an exponentially small failure probability is ever needed (ch. 4's GI simulator
truncation uses `(1/2)^n`, not Chernoff).

## 3. Errors and gaps in the source text (chapter 3)

Outright errors (`text_errors`):

1. **Theorem 87.3** states that `⟨x, r⟩` is a hard-core predicate "for `f`"; it is for
   `g(x, r) = (f(x), r)` (the proof and every use are for `g`).
2. **Lemma 84.1 vs Assumption 52.2**: the DL assumption is stated for prime-order groups `G_q`,
   while Lemma 84.1, Algorithm 84.2 and the proof use the full group `Z_p^*` of even order
   (`g^{(p−1)/2} = −1`, parity of the exponent via quadratic residuosity). The lemma needs DL in
   `Z_p^*` for a uniform generator (Theorem 52.3's collection, itself garbled: index `(q, g)`,
   domain `Z_q`, range `G_p`). Also `x ← Z_p` should be `x ← Z_{p−1}`, and "`ε = s(n)`" should be
   `ε = 1/s(n)`.
3. **Theorem 107.3 / Algorithm 106.2**: El Gamal is written for arbitrary `m ∈ Z_p` while DDH is
   over the order-`q` subgroup `G_q`; for messages in different cosets of `G_q` (a residue and a
   non-residue) the ciphertext's second component reveals the coset (Legendre symbol), so the
   scheme is not secure as stated. Correct with message space `G_q` (or an encoding into `G_q`).
   Also `Gen` draws `g ∈ Z_p` (may be `0, ±1`, giving a degenerate `h`).
4. **Definition 75.2** quantifies `i ∈ [0, …, ℓ(n)]` and predicts `t_{i+1}`, which does not exist
   for `i = ℓ(n)`; intended `0 ≤ i < ℓ(n)`.
5. **Definition 78.3** mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); intended `k = n`.
6. **Definition 96.1** has the typo `{O'_n} ≈ {O'_n}`.
7. **Theorem 104.4** omits the hard-core bit from its hypothesis ("if trapdoor permutations
   exist") — it needs Theorem 87.3 for collections; its proof writes `D` where `A` (the
   predictor from the prediction lemma) is meant.
8. **Algorithm 76.5** draws "`ℓ(n) − i` random bits `← U_{ℓ(n)−1}`" (should be `U_{ℓ(n)−i}`); the
   proof of Theorem 75.4 defines `H̃^i` with `x̄_i` and a stray `u_{l(m)}` but uses `H̃^{i+1}`,
   mixes 0- and 1-indexed bits, and its last display has `A(t) = 1` for `A(t) = b`.
9. **Lemma 80.5's proof**: `m(n)` and `ℓ(n)` are used interchangeably; the hybrids "for
   `i = 1, …, m(n)`" must start at `0`; the reduction `M(y)` reads `y` as bit-then-seed while the
   construction writes `X_{i+1}‖b_{i+1}` (seed-then-bit).
10. **Theorem 99.2's proof**: the collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`
    (`q(n) + 1` values `r_0 … r_{q(n)}`).
11. **Algorithm 84.2 / p. 86**: the analysis bounds `Pr[noinc | low(y_{k−1})]` by `1/2 − ε/2`,
    but with the increment rule as printed (`lo` counts disagreements `b_i ≠ half(r_i)`) this is
    the complementary event; the majority test itself and line 11's root selection ("IF `b = 0`
    THEN `y_{k−1} ← −y_{k−1}`": keep the root iff `A` answers `1` = lower half) are consistent
    with `half`'s convention. (Run-3 audit P8-3 corrects the run-1 reading, which called line 11
    inverted and a strict `half` necessary; the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant — the boundary exponent `(p−1)/2` only arises as the
    second root `−1` of `y = 1`, whose canonical root is `1`.)
12. **Theorem 92.2's proof**: hybrid `H²_n` is labelled "OTP with `m_1`" but is `m_0 ⊕ r`; with
    four hybrids the gap is `1/(3p(n))`, not `1/(4p(n))` (harmless).

Gaps the formalization must fill (not errors): the range reduction "as we will show later" in
Lemma 84.1 (never shown); the good-instance averaging over `(p, g)` in Lemma 84.1; the square-root
algorithm for `p ≡ 1 (mod 4)` ("exercise", not in Mathlib); the PKE single ⇒ multi message
theorem and the bitwise single-bit ⇒ full-message theorem (p. 103, "exercise"/"follows directly");
Theorem 107.3 ("exercise") including the generator-vs-square sampling term `1/q`; Lemma 189.8's
garbled statement; Corollary 81.7's extra bit; Lemma 71.6's `ε/m` where the proof gives `ε/(m−1)`.

## 4. Guidance for the planners

### 4.1 What the machine layer must provide for chapter 3 (ordered by how many items need it)

1. `Machine-NUPPT` + `Machine-Closure` (post-composition with a PPT, hard-wired per-`n` constants
   as advice, extra coins, pairing of inputs): every asymptotic item.
2. `Machine-Primitives`: XOR of two equal-length strings (Alg 92.1, 99.1, 104.3, GL), string
   equality (Thm 94.2, Claim 103.b), inner product mod 2 and majority (GL inverter, DL majority
   test), prefix/suffix/`cons`/`append` on tapes (next-bit predictor, `prgExtBits`, `splitHalves`).
3. `Machine-Loop`: iterate a PPT map `poly(n)` times (Lem 80.5's `G'`, Cor 81.7's `G`, GGM
   evaluation, the reductions of Lem 80.5 and Thm 97.3).
4. `Machine-Repetition`: polynomially many calls with fresh coins + aggregation (GL inverter
   `n(2^k − 1)` calls, DL inverter `|p| ℓ(n)` calls, PKE single ⇒ multi reduction `q(n)` encryptions,
   Thm 99.2's oracle adversary).
5. `Oracle-D7`: nuPPT-driven query trees with an explicit query bound; a reduction that *hosts* an
   oracle adversary and answers its queries itself (GGM distinguisher, Thm 99.2) — this is where
   the design panel's decision matters most for chapter 3.
6. Number-theoretic PPT algorithms from chapter 2: modular exponentiation (Thm 45.6), square
   roots mod `p ≡ 3 (4)` (Thm 58.2), a group-instance generator for safe primes (abstracted), and
   near-uniform sampling of `Z_q` from coins (statistical error `2^{−n}`, Deviation).

### 4.2 Risk ranking (chapter 3)

| Item | Risk | Mitigation |
| --- | --- | --- |
| Lem-84.1 (DL hard-core bit) | highest: four proof gaps, square-root algorithm, `Z_p^*` vs prime-order mismatch, `~500` lines | concrete statement with `p ≡ 3 (4)` and `Classical.choose` roots as core; asymptotic wrapper with the sqrt restriction; keep in its own file; accept a sorry under a full sketch if the fill stalls |
| Thm-99.2 (multi-message) | high: new concrete proof with a coupling/collision argument | prove a generic "agree on an event `E` ⇒ advantage `≤ Pr[¬E]`" lemma and "uniform table at distinct points is uniform" first |
| Thm-97.3 bridge (GGM distinguisher as nuPPT) | high: depends on Oracle-D7 and Loop | state the asymptotic theorem with the concrete `exists_ggmBits_dist` and a single admitted closure lemma "`ggmBitsDist` is nuPPT" if needed |
| Thm-75.4.c (next-bit reduction) | medium: new 250-line concrete file but all tools exist | copy the structure of `Generators.lean` (`prgHybrid`, `acceptProb_prgExtRed_right`) |
| Thm-87.3.b bridge (GL inverter as nuPPT) | medium: `n 2^k` calls, subset XOR table | Machine-Repetition with a `Fin n × NESubset k` index; `k(n) = ⌈log₂(2n^{2c+1}+1)⌉` |
| Thm-107.3 / Asm-105.1 | medium: number theory glue + sampling deviations | `GenG` abstraction; message space `G_q` |

### 4.3 Items of chapter 3 that chapter 4 consumes

Def 91.1 and Def 24.7 (Thm 112.2: security ⇔ zero-knowledge, needs a PPT message sampler);
Def 102.1/102.2 (ZK for PKE, remark only); Lem 71.6 (every ch. 4 hybrid proof); Lem 71.5
(Thm 128.8's closure step); Thm 79.4's `f, h` and Lem-104.a (Thm 126.4: `Com(b, r) = (f(r), b ⊕ h(r))`,
"hiding follows using identically the same proof as Theorem 104.4"); Thm-103.d's generic
shared-parameter hybrid (Def 126.3's multi-value hiding, "show this!"); Thm-87.3 for a single OWP
(so that "OWP with a hard-core predicate" in Thm 126.4 is available from "OWP exists").

### 4.4 Statement-shape recommendations

* Keep every concrete lemma free of machines (exact inequalities on `distAdv`/`predProb`/`invProb`
  for arbitrary function adversaries), in the style of the Garg layer; put *all* machine content in
  the asymptotic wrappers, each of which has the fixed three-step shape (instantiate, closure,
  negligible arithmetic).
* Prefer the *advice* route for per-`n` choices (`i`, `flip`, `m_n`, `k(n)`); the averaged
  uniform reductions (`mixDist`, `prgExtAvgRed`, `multicopyAvgRed`, `distAdv_multicopyAvgRed`)
  are available when a uniform reduction is wanted, but the text's proofs are non-uniform.
* State security definitions positively with `Negligible` and prove theorems by contraposition
  through `not_negligible_iff`; never quantify over abstract polynomials (use `n^c`, `Negligible.mul_pow`).
* Lengths: every ensemble/scheme carries explicit `C (n+1)^c` length formulas (plan convention);
  the PRG stretch `ℓ` must satisfy `n < ℓ n`; GGM and Alg 99.1 use `2n`; Alg 92.1 uses key `n`,
  message `2n` (Deviation from `n/2`).

### 4.5 Alignment with the parallel run-1 documents (checked 2026-10-27 22:00)

* `inventory-ch2.md` uses the ids `Def-24.7`, `Def-27.3`, `Def-41.1`, `Asm-52.2`, `Thm-52.3`,
  `Def-55.1`, `Def-56.1`, `Thm-58.2`, `Thm-45.6`, `Rem-52.2` (safe primes / squares subgroup),
  `Thm-188.7`, `Lem-189.8` — the labels used above refer to those items. Its `Asm-52.2` is
  already "relative to a group family" (`DLGroupFamily`, sampler `GenDL`), which is the shape
  Lem-84.1 needs **except** that Lem-84.1 works in `Z_p^*` (even order); the DL hard-core file
  must instantiate the family with `G = (ZMod p)ˣ`, `|G| = p − 1` (not prime) — coordinate with
  the ch. 2 owner (the family structure should not force prime order). The `OWP-single` label is
  ch. 2's `FunFamily` (design doc §3.1) with a bijectivity field.
* `design-faithful-tapes.md` names the machine layer `Poly` (`C (n+1)^c`), `PPT` (`runWith`,
  `sampleAt`, `sample`, `Computes`, `Coins`), `NUPPT` (advice form; `NUPPTSeq` verbatim form with
  an equivalence theorem), `ones n = 1^n`, `decodeBits n : List Bool → Option (Fin n → Bool)`,
  `FunFamily`, `StrongOneWay`/`WeakOneWay` over `NUPPT` with `Negligible (invSucc F A)`. The
  chapter-3 definitions should follow the same pattern: `CompIndist X Y := ∀ A : NUPPT, Negligible (distAdvAt X Y A)`,
  with `distAdvAt` built from `A.sampleAt`, `decodeBits`, and `distAdv`.
