/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Pseudorandom
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-bit test and its completeness

The *next-bit test* of [PS10, §3.2.2]: an ensemble `{X_n}` over `{0,1}^{ℓ(n)}` passes it if
no non-uniform PPT `A`, given `1^n` and a prefix `t_1 ⋯ t_i` of a sample `t ← X_n`, predicts
the next bit `t_{i+1}` with probability noticeably above `1/2` [PS10, Definition 75.2,
Remark 75.3]. The theorem of the section is its *completeness* [PS10, Theorem 75.4]: an
ensemble that passes the next-bit test is pseudorandom.

The file has two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`).

* **Concrete** (one `ℓ`, samplers `X : σ → Fin ℓ → Bool`, adversaries as functions of the
  input and of uniform coins): the next-bit experiment `nextBitProb`, the hybrids
  `nextBitHybrid X i` (`H^i_n`: the first `i` bits from `X`, the rest uniform) and
  `nextBitHybridFlip X i` (`H̃^{i+1}_n` of the text: bit `i` negated), the next-bit predictor
  `nextBitPred D i flip` of [PS10, Algorithm 76.5], and the exact next-bit reduction
  `exists_nextBitPred`: a distinguisher of `X` from uniform with advantage `ε` yields a
  position `i < ℓ` and a sign `flip` at which the predictor succeeds with probability at
  least `1/2 + ε/ℓ`. The ingredients are the hybrid lemma `hybrid_lemma`
  [PS10, Lemma 71.6], the mixing identity `acceptProb_nextBitHybrid_mix`
  (`H^i = ½ H^{i+1} + ½ H̃^{i+1}`), and the predictor analysis
  `nextBitProb_nextBitPred_false/true` (the identity of [PS10, Lemma 73.8] specialised to the
  two hybrids).
* **Asymptotic**: `Ensemble.NextBitUnpredictable` [PS10, Definition 75.2] and the
  completeness theorem `Ensemble.NextBitUnpredictable.pseudorandom` [PS10, Theorem 75.4],
  proved by instantiating the concrete reduction at each `n`, hard-wiring the sign into the
  advice of the predictor machine (the position is read off the length of the prefix), and
  finishing with the contradiction idiom `not_negligible_iff_exists_polyExpr`.

The implicit converse ("a pseudorandom ensemble passes the next-bit test", the soundness of
the test the text takes for granted) is `nextBitDist` / `prgAdv_nextBitDist` concretely and
`Ensemble.Pseudorandom.nextBitUnpredictable` asymptotically.

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5).

**Deviation:** `nextBitPred` draws `ℓ(n)` uniform bits and ignores the first `i` (the text's
`U_{ℓ(n)−1}` is a typo for `U_{ℓ(n)−i}`; a coin polynomial independent of `i` keeps one
coin type per `n` in the machine layer, D3).

**Repair (run-3 audit P2-2):** `NextBitUnpredictable.pseudorandom` is stated in its frozen
shape (DESIGN.md §2.12); the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` is now the field
`Ensemble.nonempty` (with an empty seed type the experiment has probability `0`, the ensemble
passes the next-bit test vacuously, and the always-accepting distinguisher has advantage `1`).

## Main definitions

* `TCSlib.Cryptography.nextBitProb` — the next-bit experiment at one parameter.
* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable` — passing the next-bit test
  [PS10, Definition 75.2, Remark 75.3].
* `TCSlib.Cryptography.prefixOf`, `TCSlib.Cryptography.completePrefix` — prefix of length
  `i` and its completion by uniform bits.
* `TCSlib.Cryptography.nextBitHybrid`, `TCSlib.Cryptography.nextBitHybridFlip` — the hybrids
  `H^i_n` and `H̃^{i+1}_n` of the proof of [PS10, Theorem 75.4].
* `TCSlib.Cryptography.nextBitPred` — the next-bit predictor [PS10, Algorithm 76.5].
* `TCSlib.Cryptography.nextBitDist` — the distinguisher built from a next-bit predictor
  (soundness direction).

## Main results

* `TCSlib.Cryptography.exists_nextBitPred` — the concrete next-bit reduction
  (`1/2 + prgAdv X D / ℓ ≤` predictor success for some `i < ℓ` and some sign).
* `TCSlib.Cryptography.acceptProb_nextBitHybrid_zero`,
  `TCSlib.Cryptography.acceptProb_nextBitHybrid_self`,
  `TCSlib.Cryptography.acceptProb_nextBitHybrid_mix` — the hybrid identities
  `H^0 = U_ℓ`, `H^ℓ = X_n`, `H^i = ½ H^{i+1} + ½ H̃^{i+1}`.
* `TCSlib.Cryptography.nextBitProb_nextBitPred_false`,
  `TCSlib.Cryptography.nextBitProb_nextBitPred_true` — the predictor analysis.
* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom` — completeness of the
  next-bit test [PS10, Theorem 75.4].
* `TCSlib.Cryptography.nextBitProb_id`, `TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable`
  — the uniform ensemble passes the next-bit test with probability exactly `1/2`
  (non-vacuity).
* `TCSlib.Cryptography.prgAdv_nextBitDist`,
  `TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable` — soundness of the test.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.2: Definition 75.2, Remark 75.3, Theorem 75.4, Algorithm 76.5; §3.1.1: Lemmas 71.6,
  73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5; the predictor-from-distinguisher pattern of
  Theorem 3.2 and the hybrid pattern of Theorem 3.1).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The next-bit experiment and the next-bit test [PS10, Definition 75.2] -/

/-- **The next-bit experiment** at one parameter: the probability, over a uniform seed `s` of
the sampler `X : σ → {0,1}^ℓ` and uniform coins `r`, that the predictor `A`, given the prefix
of length `i` of `t = X s`, outputs bit `i` of `t` — the quantity
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}]` of [PS10, Definition 75.2] with `0`-indexed bits
(prefix of length `i`, predicted bit `i`). -/
noncomputable def nextBitProb {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i

/-- **Passing the next-bit test** [PS10, Definition 75.2]: for every non-uniform PPT `A` there
is a negligible `ε` such that for all `n` and all positions `i < ℓ(n)`,
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}] ≤ 1/2 + ε(n)`. The predictor is the machine `A`
activated at parameter `n` on `⟨1^n, t_1 ⋯ t_i⟩` (`A.predictor n i`), which is the convention
of [PS10, Remark 75.3]: `A` receives `1^n` so that its size and running time may be polynomial
in `n` rather than in the possibly short prefix. The quantifier order `∀ A ∃ ε ∀ n ∀ i` is the
text's (one negligible function for all positions).

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5). -/
def Ensemble.NextBitUnpredictable {ℓ : PolyExpr} (X : Ensemble ℓ) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1 / 2 + ε n

/-- The next-bit success probability is nonnegative. -/
theorem nextBitProb_nonneg {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    0 ≤ nextBitProb X i A :=
  uprob_nonneg _

/-- The next-bit success probability is at most one. -/
theorem nextBitProb_le_one {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb X i A ≤ 1 :=
  uprob_le_one _

/-- **The text's strict form of Definition 75.2** — "there exists a negligible `ε` with
success `< 1/2 + ε(n)` for all `n` and `i`" — is equivalent to the frozen `≤` form
[PS10, Definition 75.2]: one direction is `le_of_lt`, the other replaces `ε(n)` by
`ε(n) + 2^{-n}`. -/
theorem Ensemble.nextBitUnpredictable_iff_lt {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.NextBitUnpredictable ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) < 1 / 2 + ε n := by
  constructor
  · intro h A
    obtain ⟨ε, hε, hle⟩ := h A
    refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n i => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith [hle n i]
  · intro h A
    obtain ⟨ε, hε, hlt⟩ := h A
    exact ⟨ε, hε, fun n i => (hlt n i).le⟩

/-! ### Prefixes and their completion -/

/-- The prefix of length `i` of an `ℓ`-bit string (`t_1 ⋯ t_i` of [PS10, Definition 75.2],
`0`-indexed). -/
def prefixOf {ℓ : ℕ} (i : Fin ℓ) (x : Fin ℓ → Bool) : Fin i → Bool :=
  fun j => x (Fin.castLE i.isLt.le j)

/-- Completion of a prefix `t` of length `i` by the bits `u_i ⋯ u_{ℓ-1}` of a string `u`:
the string `t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ` fed to the distinguisher in [PS10, Algorithm 76.5]. -/
def completePrefix {ℓ : ℕ} (i : Fin ℓ) (t : Fin i → Bool) (u : Fin ℓ → Bool) : Fin ℓ → Bool :=
  fun j => if h : (j : ℕ) < i then t ⟨j, h⟩ else u j

/-- The next-bit experiment, written with `prefixOf` (definitional unfolding). -/
theorem nextBitProb_eq {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb X i A = uprob fun z : σ × ρ => A (prefixOf i (X z.1)) z.2 = X z.1 i :=
  rfl

/-- Completing the prefix of `x` by `u` gives `x` on the first `i` positions and `u` after. -/
theorem completePrefix_prefixOf {ℓ : ℕ} (i : Fin ℓ) (x u : Fin ℓ → Bool) :
    completePrefix i (prefixOf i x) u = fun j : Fin ℓ => if (j : ℕ) < i then x j else u j := by
  funext j
  unfold completePrefix prefixOf
  by_cases h : (j : ℕ) < i
  · simp only [h, dite_true, if_true]
    congr 1
  · simp [h]

/-! ### The hybrids of the proof of Theorem 75.4 -/

/-- The hybrid `H^i_n = {x ← X_n; u ← U_ℓ : x_1 ⋯ x_i u_{i+1} ⋯ u_ℓ}` of the proof of
[PS10, Theorem 75.4]: the first `i` bits from the sample, the remaining bits uniform. All
hybrids share the seed space `σ × {0,1}^ℓ` (the unused coordinates are ignored), so that
`H^0 = U_ℓ` and `H^ℓ = X_n` hold as identities of acceptance probabilities. -/
def nextBitHybrid {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : ℕ) :
    σ × (Fin ℓ → Bool) → Fin ℓ → Bool :=
  fun z j => if (j : ℕ) < i then X z.1 j else z.2 j

/-- The flipped hybrid `H̃^{i+1}_n = {x ← X_n; u ← U_ℓ : x_1 ⋯ x_i x̄_{i+1} u_{i+2} ⋯ u_ℓ}`
of the proof of [PS10, Theorem 75.4] (`0`-indexed: bit `i` is the negation of `x_i`). The
text's display of `H̃^i_n` carries a stray `u_{ℓ(m)}` and mixes the indexings; this is the
distribution its argument uses. -/
def nextBitHybridFlip {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : ℕ) :
    σ × (Fin ℓ → Bool) → Fin ℓ → Bool :=
  fun z j => if (j : ℕ) < i then X z.1 j else if (j : ℕ) = i then !X z.1 j else z.2 j

/-- **`H^0_n = U_ℓ`**: the zeroth hybrid is uniform (the sample is ignored). -/
theorem acceptProb_nextBitHybrid_zero {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X 0) D = acceptProb (id : (Fin ℓ → Bool) → _) D := by
  have h : nextBitHybrid X 0 = fun z : σ × (Fin ℓ → Bool) => z.2 := by
    funext z j
    simp [nextBitHybrid]
  rw [h]
  exact acceptProb_snd (fun u : Fin ℓ → Bool => u) D

/-- **`H^ℓ_n = X_n`**: the last hybrid is the sample itself (the uniform bits are ignored). -/
theorem acceptProb_nextBitHybrid_self {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X ℓ) D = acceptProb X D := by
  have h : nextBitHybrid X ℓ = fun z : σ × (Fin ℓ → Bool) => X z.1 := by
    funext z j
    simp [nextBitHybrid, j.isLt]
  rw [h]
  exact acceptProb_fst X D

/-- **Bit `i` of a uniform string is a uniform bit, independent of everything else**: for
every event `p` on `(σ × {0,1}^ℓ) × ρ` and every bit `g s` depending on the first seed,
`Pr[p] = ½ Pr[p ∘ (plant g s at bit i)] + ½ Pr[p ∘ (plant ḡ s at bit i)]`. This is the
"`H^i` is sampled by drawing from `H^{i+1}` or from `H̃^{i+1}` with probability `1/2`" step of
the proof of [PS10, Theorem 75.4], in a form shared by the mixing identity and the predictor
analysis. (The planting map `(b, (s, u), r) ↦ ((s, update u i (b ⊕ g s)), r)` is 2-to-1, not a
bijection — run-3 audit P2-3 — so the proof adjoins an ignored uniform bit instead.)

**Proof sketch.** Adjoin an ignored uniform bit `b` (`uprob_fst` after `Equiv.prodComm`),
then apply the involution `ψ (b, (s, u), r) := (u_i ⊕ g s, (s, update u i (b ⊕ g s)), r)` of
`Bool × ((σ × {0,1}^ℓ) × ρ)` (`uprob_comp_equiv`; `ψ ∘ ψ = id` by `Function.update_idem`,
`Function.update_self`, `Function.update_eq_self`) and split on `b` with `uprob_bool_prod`:
the `b = false` section plants `g s`, the `b = true` section plants `!g s`. -/
private theorem uprob_split_bit {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ} (i : Fin ℓ)
    (g : σ → Bool) (p : (σ × (Fin ℓ → Bool)) × ρ → Prop) :
    uprob p = (uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
        p ((z.1.1, Function.update z.1.2 i (g z.1.1)), z.2)) +
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
        p ((z.1.1, Function.update z.1.2 i (!g z.1.1)), z.2))) / 2 := by
  have h1 : uprob (fun w : Bool × ((σ × (Fin ℓ → Bool)) × ρ) => p w.2) = uprob p := by
    rw [← uprob_comp_equiv (Equiv.prodComm ((σ × (Fin ℓ → Bool)) × ρ) Bool)
      (fun w : Bool × ((σ × (Fin ℓ → Bool)) × ρ) => p w.2)]
    exact uprob_fst p
  let ψ : Bool × ((σ × (Fin ℓ → Bool)) × ρ) ≃ Bool × ((σ × (Fin ℓ → Bool)) × ρ) :=
    { toFun := fun w => (xor (w.2.1.2 i) (g w.2.1.1),
        ((w.2.1.1, Function.update w.2.1.2 i (xor w.1 (g w.2.1.1))), w.2.2))
      invFun := fun w => (xor (w.2.1.2 i) (g w.2.1.1),
        ((w.2.1.1, Function.update w.2.1.2 i (xor w.1 (g w.2.1.1))), w.2.2))
      left_inv := fun w => by
        obtain ⟨b, ⟨s, u⟩, r⟩ := w
        simp [Function.update_idem]
      right_inv := fun w => by
        obtain ⟨b, ⟨s, u⟩, r⟩ := w
        simp [Function.update_idem] }
  rw [← h1, ← uprob_comp_equiv ψ, uprob_bool_prod]
  simp only [ψ, Equiv.coe_fn_mk, Bool.false_xor, Bool.true_xor]

/-- Planting `x_i` at position `i` of the uniform part of `H^i` gives `H^{i+1}`:
`nextBitHybrid X i (s, update u i (X s i)) = nextBitHybrid X (i+1) (s, u)` (case split on
`j < i`, `j = i`, `j > i`). -/
private theorem nextBitHybrid_update_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ)
    (s : σ) (u : Fin ℓ → Bool) :
    nextBitHybrid X i (s, Function.update u i (X s i)) = nextBitHybrid X (i + 1) (s, u) := by
  funext j
  simp only [nextBitHybrid]
  rcases lt_trichotomy (j : ℕ) i with hj | hj | hj
  · simp [hj, Nat.lt_succ_of_lt hj]
  · have hji : j = i := Fin.ext hj
    subst hji
    simp
  · have hne : j ≠ i := fun h => by rw [h] at hj; exact lt_irrefl _ hj
    simp [not_lt.mpr hj.le, Function.update_of_ne hne, show ¬ ((j : ℕ) < (i : ℕ) + 1) by omega]

/-- Planting `x̄_i` at position `i` of the uniform part of `H^i` gives the flipped hybrid
`H̃^{i+1}`: `nextBitHybrid X i (s, update u i (!X s i)) = nextBitHybridFlip X i (s, u)`. -/
private theorem nextBitHybrid_update_not_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool)
    (i : Fin ℓ) (s : σ) (u : Fin ℓ → Bool) :
    nextBitHybrid X i (s, Function.update u i (!X s i)) = nextBitHybridFlip X i (s, u) := by
  funext j
  simp only [nextBitHybrid, nextBitHybridFlip]
  rcases lt_trichotomy (j : ℕ) i with hj | hj | hj
  · simp [hj]
  · have hji : j = i := Fin.ext hj
    subst hji
    simp
  · have hne : j ≠ i := fun h => by rw [h] at hj; exact lt_irrefl _ hj
    simp [not_lt.mpr hj.le, Function.update_of_ne hne, hj.ne']

/-- Completing the prefix of the sample `X s` by `v` is the hybrid `H^i` at the seed `(s, v)`:
the string `completePrefix i (prefixOf i (X s)) v` fed to `D` by the predictor is
`nextBitHybrid X i (s, v)` (`completePrefix_prefixOf`). -/
private theorem completePrefix_prefixOf_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool)
    (i : Fin ℓ) (s : σ) (v : Fin ℓ → Bool) :
    completePrefix i (prefixOf i (X s)) v = nextBitHybrid X i (s, v) := by
  rw [completePrefix_prefixOf]
  rfl

/-- **The mixing identity** `H^i_n = ½ H^{i+1}_n + ½ H̃^{i+1}_n` of the proof of
[PS10, Theorem 75.4]: the acceptance probability of `D` on the hybrid `H^i` is the average
of its acceptance probabilities on `H^{i+1}` and on the flipped hybrid `H̃^{i+1}`, because
bit `i` of `H^i` is a uniform bit, which equals `x_i` or `x̄_i` each with probability `1/2`
independently of everything else.

**Proof sketch.** `uprob_split_bit` at position `i` with the bit `x_i = X s i`: the
acceptance event on `H^i` is the average of the same event with `x_i` planted at bit `i` of
`u` and with `x̄_i` planted there. Planting `x_i` turns `H^i` into `H^{i+1}`
(`nextBitHybrid_update_eq`) and planting `x̄_i` turns it into `H̃^{i+1}`
(`nextBitHybrid_update_not_eq`); read off the two halves (`OneWay.uprob_congr`). (The
run-2 sketch transported the event along a 2-to-1 "bijection"; see `uprob_split_bit`.) -/
theorem acceptProb_nextBitHybrid_mix {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X i) D =
      (acceptProb (nextBitHybrid X (i + 1)) D + acceptProb (nextBitHybridFlip X i) D) / 2 := by
  unfold acceptProb
  rw [uprob_split_bit i (fun s => X s i) (fun z => D (nextBitHybrid X i z.1) z.2 = true)]
  have hA : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      D (nextBitHybrid X i (z.1.1, Function.update z.1.2 i (X z.1.1 i))) z.2 = true) =
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ => D (nextBitHybrid X (i + 1) z.1) z.2 = true) := by
    apply OneWay.uprob_congr
    intro z
    rw [nextBitHybrid_update_eq]
  have hB : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      D (nextBitHybrid X i (z.1.1, Function.update z.1.2 i (!X z.1.1 i))) z.2 = true) =
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ => D (nextBitHybridFlip X i z.1) z.2 = true) := by
    apply OneWay.uprob_congr
    intro z
    rw [nextBitHybrid_update_not_eq]
  rw [hA, hB]

/-! ### The next-bit predictor [PS10, Algorithm 76.5] -/

/-- **The next-bit predictor** `A'(1^n, t_1 ⋯ t_i)` of [PS10, Algorithm 76.5], built from a
distinguisher `D`: draw uniform bits `u` and coins `c` for `D`, run
`g ← D(t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ; c)`, output `u_{i+1}` if `g = 1` and `ū_{i+1}` otherwise;
with `flip = true` the output is negated (the text applies the prediction lemma, which
chooses between a machine and its negation; here the sign is the parameter `flip`,
non-uniform advice in the asymptotic layer, as for `owpPredictor`). It makes one call to
`D`. Coins: `ℓ` uniform bits (of which the first `i` are unused) and `D`'s coins.

**Deviation:** `nextBitPred` draws `ℓ(n)` uniform bits and ignores the first `i` (the text's
`U_{ℓ(n)−1}` is a typo for `U_{ℓ(n)−i}`; a coin polynomial independent of `i` keeps one
coin type per `n` in the machine layer, D3). -/
def nextBitPred {ρ : Type*} {ℓ : ℕ} (D : (Fin ℓ → Bool) → ρ → Bool) (i : Fin ℓ) (flip : Bool) :
    (Fin i → Bool) → (Fin ℓ → Bool) × ρ → Bool :=
  fun t c => xor (if D (completePrefix i t c.1) c.2 then c.1 i else !c.1 i) flip

/-- **Predictor analysis, positive sign**: `nextBitPred D i false` predicts bit `i` of `X`
from the prefix of length `i` with probability exactly
`1/2 + (Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]) / 2` — the last display of the proof of
[PS10, Theorem 75.4] (which writes `A(t) = 1` for `A(t) = b`), i.e. the identity of
[PS10, Lemma 73.8] (`predict_eq`) with `X¹ := H^{i+1}` and `X⁰ := H̃^{i+1}`.

**Proof sketch.** Split on whether the drawn bit `u_i` equals `x_i` (each case has
probability `1/2`, independently of `s`, the other bits of `u`, and `c`: the bijection
`(b, (s, u), c) ↦ (s, (update u i (xor b (X s i)), c))` followed by `uprob_bool_prod`, as in
`predProb_owpPredictor_false`). If `u_i = x_i`, the completed string
`completePrefix i (prefixOf i (X s)) u` is `nextBitHybrid X (i+1) (s, u)`
(`completePrefix_prefixOf`) and the predictor is right iff `D` accepts; if `u_i = x̄_i`, the
completed string is `nextBitHybridFlip X i (s, u)` and the predictor is right iff `D`
rejects (`uprob_not`, which needs the nonemptiness hypotheses). Average the two. -/
theorem nextBitProb_nextBitPred_false {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    [Nonempty ρ] {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    nextBitProb X i (nextBitPred D i false) =
      1 / 2 + (acceptProb (nextBitHybrid X (i + 1)) D -
        acceptProb (nextBitHybridFlip X i) D) / 2 := by
  rw [nextBitProb_eq, ← uprob_comp_equiv (Equiv.prodAssoc σ (Fin ℓ → Bool) ρ)
    (fun z : σ × ((Fin ℓ → Bool) × ρ) => nextBitPred D i false (prefixOf i (X z.1)) z.2 = X z.1 i)]
  simp only [Equiv.prodAssoc_apply]
  rw [uprob_split_bit i (fun s => X s i) (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
    nextBitPred D i false (prefixOf i (X z.1.1)) (z.1.2, z.2) = X z.1.1 i)]
  dsimp only
  have hA : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      nextBitPred D i false (prefixOf i (X z.1.1)) (Function.update z.1.2 i (X z.1.1 i), z.2) =
        X z.1.1 i) = acceptProb (nextBitHybrid X (i + 1)) D := by
    unfold acceptProb
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, completePrefix_prefixOf_eq, nextBitHybrid_update_eq,
      Function.update_self, Bool.xor_false]
    cases D (nextBitHybrid X (i + 1) z.1) z.2 <;> cases X z.1.1 i <;> simp
  have hB : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      nextBitPred D i false (prefixOf i (X z.1.1)) (Function.update z.1.2 i (!X z.1.1 i), z.2) =
        X z.1.1 i) = 1 - acceptProb (nextBitHybridFlip X i) D := by
    unfold acceptProb
    rw [← uprob_not]
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, completePrefix_prefixOf_eq, nextBitHybrid_update_not_eq,
      Function.update_self, Bool.xor_false]
    cases D (nextBitHybridFlip X i z.1) z.2 <;> cases X z.1.1 i <;> simp
  rw [hA, hB]
  ring

/-- **Predictor analysis, negative sign**: `nextBitPred D i true` predicts bit `i` with
probability exactly `1/2 − (Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]) / 2`, the case the
text's appeal to the prediction lemma covers by choosing the negated machine.

**Proof sketch.** The output of `nextBitPred D i true` is the negation of that of
`nextBitPred D i false` (`Bool.xor_true`), so its success probability is one minus that of
`nextBitProb_nextBitPred_false` (`uprob_not`; nonemptiness is needed for the complement). -/
theorem nextBitProb_nextBitPred_true {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    [Nonempty ρ] {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    nextBitProb X i (nextBitPred D i true) =
      1 / 2 - (acceptProb (nextBitHybrid X (i + 1)) D -
        acceptProb (nextBitHybridFlip X i) D) / 2 := by
  have h : nextBitProb X i (nextBitPred D i true) =
      1 - nextBitProb X i (nextBitPred D i false) := by
    unfold nextBitProb
    rw [← uprob_not]
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, Bool.xor_true, Bool.xor_false]
    cases (if D (completePrefix i (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2.1) z.2.2 then z.2.1 i
      else !z.2.1 i) <;> cases X z.1 i <;> simp
  rw [h, nextBitProb_nextBitPred_false]
  ring

/-- **The next-bit reduction, concrete form** (the content of the proof of
[PS10, Theorem 75.4] at one parameter): for every sampler `X` into `{0,1}^ℓ` with `ℓ > 0` and
every distinguisher `D` with PRG advantage `ε = prgAdv X D` against `X`, there are a position
`i < ℓ` and a sign `flip` such that the next-bit predictor `nextBitPred D i flip`
[PS10, Algorithm 76.5] predicts bit `i` of `X` from the prefix of length `i` with probability
at least `1/2 + ε/ℓ`. (The text obtains `1/2 + 1/(p(n)ℓ(n))` from `ε = 1/p(n)`.)

**Proof sketch.** `prgAdv X D = |Pr[D(H^ℓ) = 1] − Pr[D(H^0) = 1]|` by
`acceptProb_nextBitHybrid_self` and `acceptProb_nextBitHybrid_zero`; the hybrid lemma
`hybrid_lemma` (`exists_hybrid_gap`) over `i ↦ acceptProb (nextBitHybrid X i) D` gives
`i < ℓ` with `ε/ℓ ≤ |Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1]|`. By the mixing identity
`acceptProb_nextBitHybrid_mix`, `Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1] =
(Pr[D(H̃^{i+1}) = 1] − Pr[D(H^{i+1}) = 1]) / 2`, so
`δ := Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]` has `|δ| ≥ 2ε/ℓ`. If `0 ≤ δ` take
`flip := false` and `nextBitProb_nextBitPred_false` gives success `1/2 + δ/2 ≥ 1/2 + ε/ℓ`;
otherwise `flip := true` and `nextBitProb_nextBitPred_true` gives `1/2 − δ/2 ≥ 1/2 + ε/ℓ`
(`le_total`, `abs_of_nonneg`/`abs_of_neg`, `div_le_iff₀`). -/
theorem exists_nextBitPred {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ] [Nonempty ρ]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    ∃ (i : Fin ℓ) (flip : Bool),
      1 / 2 + prgAdv X D / ℓ ≤ nextBitProb X i (nextBitPred D i flip) := by
  have hadv : prgAdv X D =
      |acceptProb (nextBitHybrid X 0) D - acceptProb (nextBitHybrid X ℓ) D| := by
    unfold prgAdv distAdv
    rw [acceptProb_nextBitHybrid_zero, acceptProb_nextBitHybrid_self, abs_sub_comm]
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun j => acceptProb (nextBitHybrid X j) D) hℓ
  have hmix := acceptProb_nextBitHybrid_mix X ⟨k, hk⟩ D
  have hδ : prgAdv X D / ℓ ≤ |acceptProb (nextBitHybrid X (k + 1)) D -
      acceptProb (nextBitHybridFlip X k) D| / 2 := by
    rw [hadv]
    refine hgap.trans (le_of_eq ?_)
    rw [hmix, abs_sub_comm, ← abs_two, ← abs_div]
    congr 1
    ring
  rcases le_total 0 (acceptProb (nextBitHybrid X (k + 1)) D -
      acceptProb (nextBitHybridFlip X k) D) with h | h
  · refine ⟨⟨k, hk⟩, false, ?_⟩
    rw [nextBitProb_nextBitPred_false]
    rw [abs_of_nonneg h] at hδ
    dsimp only
    linarith
  · refine ⟨⟨k, hk⟩, true, ?_⟩
    rw [nextBitProb_nextBitPred_true]
    rw [abs_of_nonpos h] at hδ
    dsimp only
    linarith

/-! ### String forms of prefixes and completions -/

/-- The string form of `completePrefix`: the completed string `t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ` is the
list `ofFn t ++ (ofFn u).drop i` — the word `w` the predictor machine of
[PS10, Algorithm 76.5] hands to `D` (elementwise, `List.ext_getElem`). -/
private theorem ofFn_completePrefix {ℓ : ℕ} (i : Fin ℓ) (t : Fin i → Bool) (u : Fin ℓ → Bool) :
    List.ofFn (completePrefix i t u) = List.ofFn t ++ (List.ofFn u).drop i := by
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_append, List.length_drop]; omega)
    fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_drop,
    completePrefix]
  by_cases hj : j < (i : ℕ)
  · simp [hj]
  · simp only [hj, dite_false]
    congr 1
    ext
    simp
    omega

/-- The string form of `prefixOf`: the prefix of length `i` of `t` is `(ofFn t).take i`
(elementwise, `List.ext_getElem`). -/
private theorem ofFn_prefixOf {ℓ : ℕ} (i : Fin ℓ) (t : Fin ℓ → Bool) :
    List.ofFn (prefixOf i t) = (List.ofFn t).take i := by
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_take, prefixOf]
  rfl

/-- Bit `i` of `u` is the head of the suffix `(ofFn u).drop i` — the readout
`StateLoop.headBit_poly` of the machines below (`List.head?_drop`, `List.getElem?_ofFn`). -/
private theorem headD_drop_ofFn {ℓ : ℕ} (i : Fin ℓ) (u : Fin ℓ → Bool) :
    ((List.ofFn u).drop i).headD false = u i := by
  rw [List.headD_eq_head?, List.head?_drop, List.getElem?_ofFn]
  simp [i.isLt]

/-- A distinguisher whose coin string is reindexed by a bijection has the same acceptance
probability (`uprob_comp_equiv` on the coin factor of the sample space). -/
private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (e : ρ ≃ ρ') (D : γ → ρ' → Bool) (D' : γ → ρ → Bool)
    (h : ∀ x r, D x (e r) = D' x r) : acceptProb X D = acceptProb X D' := by
  unfold acceptProb
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl σ) e)]
  apply OneWay.uprob_congr
  intro z
  simp [h]

/-! ### Completeness of the next-bit test [PS10, Theorem 75.4] -/

/-- **The next-bit predictor as a machine** [PS10, Algorithm 76.5]: for a distinguisher
machine `D`, positions `i n < ℓ(n)` and signs `flip n`, a non-uniform PPT `A` with coins
`ℓ + D.coins` and advice `⟨D.advice n, [flip n]⟩` such that, at parameter `n` and position
`i n`, `A` on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete
predictor `nextBitPred (D.distinguisher n (ℓ n)) (i n) (flip n) t (u, c)`: it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `u_{|t|}` or its negation according to the verdict,
negated once more if `flip n`. The position is read off the prefix length `|t| = i n`, so
only the sign is hard-wired.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨D.advice n, [flip n]⟩⟩, r⟩`
cuts `r` into `u := r.take (ℓ n)` and `c := r.drop (ℓ n)` (`polyTimeComputable_pairTakePoly`/
`pairDropPoly ℓ` on `⟨1^n, r⟩`), forms `w := y ++ u.drop |y|` (`pairDropPoly var` on `⟨y, u⟩`,
`PolyTimeComputable.append`), runs `D.output` on `layout 1^n w (D.advice n) c`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), tests the verdict against
`[true]` (`polyTimeComputable_pairEq`), reads `u_{|y|}` as the head of `u.drop |y|` and the sign
as the head of the advice's second component (`StateLoop.headBit_poly`), and combines them
(`polyTimeComputable_ite`, `StateLoop.not_poly`, `StateLoop.xor_poly`). `A := ofPolyTime` of
it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3` (`length_pairEncode`); the coin
split is `Fin.appendEquiv` composed with `finCongr`, and the identity is `runAtL_ofPolyTime`,
the projection identities of the layout, `List.take_left'`/`List.drop_left'`,
`ofFn_completePrefix` and `headD_drop_ofFn`. -/
private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (i : ∀ n, Fin (ℓ.eval n))
    (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (t : Fin (i n) → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n (i n) t (e n (u, c)) =
          nextBitPred (D.distinguisher n (ℓ.eval n)) (i n) (flip n) t (u, c) := by
  -- the coin cut `⟨1^n, r⟩ ↦ u = r.take (ℓ n)`, `c = r.drop (ℓ n)`
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hu : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly ℓ).comp hcut using 1
    funext z
    simp
  have hc : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairDropPoly ℓ).comp hcut using 1
    funext z
    simp
  -- the suffix `u.drop |y|` and the completed word `w = y ++ u.drop |y|`
  have hud : PolyTimeComputable fun z =>
      ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop (NUPPT.inArg z).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp
      (NUPPT.polyTimeComputable_inArg.pairEncode hu) using 1
    funext z
    simp
  have hw := NUPPT.polyTimeComputable_inArg.append hud
  -- the call to `D` and its verdict
  have hg := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hw
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice) hc)
  have hgb : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hg.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  -- the bit `u_{|y|}` and the sign
  have hui := StateLoop.headBit_poly.comp hud
  have hflip : PolyTimeComputable fun z => [(pairSndD (NUPPT.inAdvice z)).headD false] :=
    StateLoop.headBit_poly.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
  have hsel : PolyTimeComputable fun z => [if decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true]) then
        (((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false
      else !(((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false] := by
    convert polyTimeComputable_ite hgb hui (StateLoop.not_poly hui) using 1
    funext z
    split_ifs <;> rfl
  have hF := StateLoop.xor_poly hsel hflip
  -- the advice `⟨D.advice n, [flip n]⟩`
  have hadv : ∀ n, (pairEncode (D.advice n) [flip n]).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) (.const 1)).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, List.length_singleton]
    have := D.advice_length n
    omega
  let A := NUPPT.ofPolyTime hF (.add ℓ D.coins) _ (fun n => pairEncode (D.advice n) [flip n]) hadv
  have hlen : ∀ n, A.coinLen n = ℓ.eval n + D.coinLen n := fun n => rfl
  let e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n := fun n =>
    (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (hlen n).symm) (Equiv.refl Bool))
  refine ⟨A, e, fun n t u c => ?_⟩
  have hofn : List.ofFn (e n (u, c)) = List.ofFn u ++ List.ofFn c := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (hlen n).symm (Fin.append u c)).symm
  simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_eq, hofn, nextBitPred]
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.runAtL, List.take_left', List.drop_left', ofFn_completePrefix]
  split_ifs <;> cases u (i n) <;> cases flip n <;> rfl

/-- **Completeness of the next-bit test** [PS10, Theorem 75.4]: if the ensemble `{X_n}` over
`{0,1}^{ℓ(n)}` (with `ℓ(n) > 0`) passes the next-bit test, then it is pseudorandom.

**Repair (run-3 audit P2-2):** the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` was dropped
(it is the field `Ensemble.nonempty`; with an empty seed type the experiment has probability
`0`, the ensemble passes the next-bit test vacuously, and the always-accepting distinguisher
has advantage `1`); the frozen shape of DESIGN.md §2.12 is restored.

**Proof sketch.** By contradiction, as in the text. Fix a distinguisher `D` with
`¬ Negligible (fun n => prgAdv (X_n) (D.distinguisher n (ℓ n)))`
(`Ensemble.pseudorandom_iff_prgAdv`); by `not_negligible_iff_exists_polyExpr` there is a
positive syntactic polynomial `p` with `1/p(n) ≤ prgAdv` for infinitely many `n`. At every
`n`, `exists_nextBitPred (hℓ n)` (with the instance `X.nonempty n`) gives a position
`i_n < ℓ(n)` and a sign `flip_n` with
`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`
(`choose`). The predictor machine `A` is `exists_nextBitPredMachine D i flip` (advice
`⟨D.advice n, [flip_n]⟩`, coins `ℓ + D.coins`; on `⟨1^n, t⟩` with coins `u ++ c` it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `xor (if g then u_{|t|} else !u_{|t|}) flip_n`, the
position being read off the prefix length). Its functional identity
`A.predictor n i_n t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n t (u, c)`
along the coin split `e : (Fin (ℓ n) → Bool) × D.Coins n ≃ A.Coins n` (`Fin.appendEquiv`)
gives `nextBitProb (X_n) i_n (A.predictor n i_n) = nextBitProb (X_n) i_n (nextBitPred …)`
(`uprob_comp_equiv`). Now `h A` gives a negligible `ε` with `nextBitProb … ≤ 1/2 + ε n` for
all `n, i`; hence `1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n` for infinitely many `n`, i.e.
`¬ Negligible ε` by `not_negligible_iff_exists_polyExpr` with the polynomial `mul p ℓ`
(positive by `hℓ` and `0 < p`), a contradiction. -/
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hℓ : ∀ n, 0 < ℓ.eval n) (h : X.NextBitUnpredictable) :
    X.Pseudorandom := by
  rw [Ensemble.pseudorandom_iff_prgAdv]
  intro D
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  have hex : ∀ n, ∃ (i : Fin (ℓ.eval n)) (flip : Bool),
      1 / 2 + prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n) ≤
        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) :=
    fun n => exists_nextBitPred (hℓ n) (X.X n) (D.distinguisher n (ℓ.eval n))
  choose i flip hif using hex
  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine D i flip
  obtain ⟨ε, hε, hbound⟩ := h A
  have hprob : ∀ n, nextBitProb (X.X n) (i n) (A.predictor n (i n)) =
      nextBitProb (X.X n) (i n) (nextBitPred (D.distinguisher n (ℓ.eval n)) (i n) (flip n)) := by
    intro n
    unfold nextBitProb
    rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (X.σ n)) (e n))]
    apply OneWay.uprob_congr
    rintro ⟨s, u, c⟩
    simp [hA]
  refine (not_negligible_iff_exists_polyExpr.mpr ⟨.mul p ℓ, fun n => ?_, fun n₀ => ?_⟩) hε
  · simp only [PolyExpr.eval_mul]
    exact Nat.mul_pos (hp n) (hℓ n)
  · obtain ⟨n, hn, hpn⟩ := hinf n₀
    refine ⟨n, hn, ?_⟩
    have h1 := hif n
    have h2 := hbound n (i n)
    rw [hprob n] at h2
    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓ n
    have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    have h0 : 0 ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    rw [abs_of_nonneg h0] at hpn
    calc (1 : ℝ) / ((PolyExpr.mul p ℓ).eval n : ℝ)
        = (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
          rw [PolyExpr.eval_mul, Nat.cast_mul, div_div]
      _ ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n : ℝ) := by gcongr
      _ ≤ ε n := by linarith
      _ ≤ |ε n| := le_abs_self _

/-! ### Soundness of the next-bit test (the implicit converse) -/

/-- **A uniform string has an unpredictable next bit**: for every predictor `A` and every
position `i`, `nextBitProb id i A = 1/2` exactly, the bit `t_i` of a uniform `t` being
independent of the prefix and of `A`'s coins [PS10, §3.2.2, the intuition behind the test].

**Proof sketch.** Negating bit `i` of `t` (`Function.update t i (!t i)`) is an involution of
the sample space that fixes the prefix and exchanges the success event with its complement,
so `Pr[success] = Pr[failure] = 1 − Pr[success]` (`uprob_comp_equiv`, `uprob_not`). -/
theorem nextBitProb_id {ρ : Type*} [Fintype ρ] [Nonempty ρ] {ℓ : ℕ} (i : Fin ℓ)
    (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb (id : (Fin ℓ → Bool) → Fin ℓ → Bool) i A = 1 / 2 := by
  let e : (Fin ℓ → Bool) × ρ ≃ (Fin ℓ → Bool) × ρ :=
    { toFun := fun z => (Function.update z.1 i (!z.1 i), z.2)
      invFun := fun z => (Function.update z.1 i (!z.1 i), z.2)
      left_inv := fun z => by
        ext j
        · simp [Function.update_apply]
          split_ifs with hj
          · subst hj; rfl
          · rfl
        · rfl
      right_inv := fun z => by
        ext j
        · simp [Function.update_apply]
          split_ifs with hj
          · subst hj; rfl
          · rfl
        · rfl }
  have hprefix : ∀ (t : Fin ℓ → Bool) (j : Fin i),
      Function.update t i (!t i) (Fin.castLE i.isLt.le j) = t (Fin.castLE i.isLt.le j) := by
    intro t j
    rw [Function.update_of_ne]
    intro hj
    have := congrArg Fin.val hj
    simp at this
    omega
  have hflip : uprob (fun z : (Fin ℓ → Bool) × ρ =>
      A (fun j => id z.1 (Fin.castLE i.isLt.le j)) z.2 = id z.1 i) =
      uprob (fun z : (Fin ℓ → Bool) × ρ =>
        ¬ (A (fun j => id z.1 (Fin.castLE i.isLt.le j)) z.2 = id z.1 i)) := by
    rw [← uprob_comp_equiv e]
    apply OneWay.uprob_congr
    intro z
    simp only [e, Equiv.coe_fn_mk, id, hprefix, Function.update_self]
    cases A (fun j => z.1 (Fin.castLE i.isLt.le j)) z.2 <;> cases z.1 i <;> simp
  unfold nextBitProb
  rw [uprob_not] at hflip
  linarith

/-- **The uniform ensemble passes the next-bit test** (non-vacuity of
[PS10, Definition 75.2]): every predictor succeeds with probability exactly `1/2`, so
`ε := 0` works. -/
theorem Ensemble.uniform_nextBitUnpredictable (ℓ : PolyExpr) :
    (Ensemble.uniform ℓ).NextBitUnpredictable := by
  intro A
  refine ⟨fun _ => 0, negligible_zero, fun n i => ?_⟩
  rw [show (Ensemble.uniform ℓ).X n = id from rfl, nextBitProb_id]
  simp

/-- The distinguisher built from a next-bit predictor `A` at position `i`: accept the string
`t` iff `A(t_1 ⋯ t_i) = t_{i+1}` — the "statistical test" a next-bit predictor induces
[PS10, p. 74, "a pseudorandom distribution needs to pass all efficiently computable
statistical tests"]. -/
def nextBitDist {ρ : Type*} {ℓ : ℕ} (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    (Fin ℓ → Bool) → ρ → Bool :=
  fun t c => decide (A (prefixOf i t) c = t i)

/-- `nextBitDist i A` accepts a sample of `X` exactly when `A` predicts its next bit. -/
theorem acceptProb_nextBitDist {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    acceptProb X (nextBitDist i A) = nextBitProb X i A := by
  unfold acceptProb nextBitProb nextBitDist prefixOf
  apply OneWay.uprob_congr
  intro z
  simp

/-- **Soundness of the next-bit test, concrete form**: the distinguisher induced by a next-bit
predictor `A` at position `i` has PRG advantage exactly `|Pr[A predicts bit i of X] − 1/2|`
(it accepts a uniform string with probability exactly `1/2` by `nextBitProb_id`). Hence a
pseudorandom sampler has no predictor with noticeable next-bit advantage. -/
theorem prgAdv_nextBitDist {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    prgAdv X (nextBitDist i A) = |nextBitProb X i A - 1 / 2| := by
  unfold prgAdv distAdv
  rw [acceptProb_nextBitDist, acceptProb_nextBitDist, nextBitProb_id]

/-- **The next-bit statistical test as a machine**: for a predictor machine `A` and positions
`k n ≤ ℓ(n)`, a non-uniform PPT `Dm` with `A`'s coins and advice `⟨A.advice n, 1^{k n}⟩` which
on `⟨1^n, y⟩` runs `A(1^n, y.take (k n); r)`, reads bit `k n` of `y` and accepts iff the
verdict equals the bit — the untyped form of `nextBitDist (k n) (A.predictor n (k n))`.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨A.advice n, 1^{k n}⟩⟩, r⟩` cuts
`y` at the unary length of the advice's second component (`polyTimeComputable_pairTakePoly`/
`pairDropPoly var` on `⟨1^{k n}, y⟩`), runs `A.output` on `layout 1^n (y.take (k n)) (A.advice n) r`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), reads the bit as the head of
`y.drop (k n)` (`StateLoop.headBit_poly`) and compares twice with `polyTimeComputable_pairEq`
(verdict against `[true]`, then against the bit). `Dm := ofPolyTime` of it with `A.coins` and
advice bound `2·A.adv + 2 + ℓ` (`length_pairEncode`, `hk`); the identity is
`runAtL_ofPolyTime` plus the projection identities of the layout. -/
private theorem exists_nextBitDistMachine {ℓ : PolyExpr} (A : NUPPT) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ ℓ.eval n) :
    ∃ Dm : NUPPT, Dm.coins = A.coins ∧ ∀ n (y r : List Bool),
      Dm.runAtL n y r = [decide ([decide (A.runAtL n (y.take (k n)) r = [true])] =
        [(y.drop (k n)).headD false])] := by
  have hkk := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
  have hpair := hkk.pairEncode NUPPT.polyTimeComputable_inArg
  have hy₁ : PolyTimeComputable fun z =>
      (NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp hpair using 1
    funext z
    simp
  have hb : PolyTimeComputable fun z =>
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false] := by
    convert StateLoop.headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp hpair)
      using 1
    funext z
    simp
  have ha := A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hy₁
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice)
    NUPPT.polyTimeComputable_inCoins)
  have hx : PolyTimeComputable fun z => [decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (ha.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  have hG : PolyTimeComputable fun z => [decide ([decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] =
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false])] := by
    convert polyTimeComputable_pairEq.comp (hx.pairEncode hb) using 1
    funext z
    simp
  have hadv : ∀ n, (pairEncode (A.advice n) (List.replicate (k n) true)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) ℓ).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have := A.advice_length n
    have := hk n
    omega
  refine ⟨NUPPT.ofPolyTime hG A.coins _
    (fun n => pairEncode (A.advice n) (List.replicate (k n) true)) hadv, rfl, fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.runAtL]

/-- **Soundness of the next-bit test, asymptotic form** (the converse of
[PS10, Theorem 75.4], implicit in the text's "a pseudorandom distribution needs to pass all
efficiently computable statistical tests", p. 74): a pseudorandom ensemble passes the
next-bit test.

**Proof sketch.** Fix a predictor machine `A` and let
`ε n := max_{i < ℓ n} (nextBitProb (X_n) i (A.predictor n i) − 1/2)` (`0` if `ℓ n = 0`),
attained at some `i_n` (`Finset.exists_max_image`); then `nextBitProb ≤ 1/2 + ε n` for all
`n, i`, and it suffices to show `Negligible ε`. Otherwise `not_negligible_iff_exists_polyExpr`
gives a positive `p` with `1/p(n) ≤ |ε n|` infinitely often. The distinguisher machine `D` is
`exists_nextBitDistMachine A k` with `k n := i_n` (`0` if `ε n` is not attained): advice
`⟨A.advice n, 1^{k n}⟩`, coins `A.coins`; on `⟨1^n, t⟩` it runs `A` on `⟨1^n, t.take (k n)⟩`,
reads bit `k n` of `t` and outputs `[decide (verdict = [bit])]`. At every `n` with `ε n ≠ 0`
(every `n` of the infinite set), `ε n` is attained at `i_n = k n`, and the functional identity
`D.distinguisher n (ℓ n) t (e r) = nextBitDist i_n (A.predictor n i_n) t r` (`ofFn_prefixOf`,
`headD_drop_ofFn`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
`prgAdv_nextBitDist` and `acceptProb_coins_equiv`,
`prgAdv (X_n) (D.distinguisher n (ℓ n)) = |nextBitProb (X_n) i_n (A.predictor n i_n) − 1/2| =
|ε n| ≥ 1/p(n)` — the advantage being an absolute value, no choice between the predictor and
its negation is needed — contradicting `hX D` through `not_negligible_iff_exists_polyExpr`. -/
theorem Ensemble.Pseudorandom.nextBitUnpredictable {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hX : X.Pseudorandom) : X.NextBitUnpredictable := by
  classical
  intro A
  have hmax : ∀ n, ∃ v : ℝ,
      (∀ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 ≤ v) ∧
      (v = 0 ∨ ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = v) := by
    intro n
    rcases isEmpty_or_nonempty (Fin (ℓ.eval n)) with hemp | hne
    · exact ⟨0, fun j => (hemp.false j).elim, Or.inl rfl⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (ℓ.eval n)))
        (fun j => nextBitProb (X.X n) j (A.predictor n j) - 1 / 2) Finset.univ_nonempty
      exact ⟨_, fun j => hj₀ j (Finset.mem_univ j), Or.inr ⟨j₀, rfl⟩⟩
  choose ε hεle hεeq using hmax
  refine ⟨ε, ?_, fun n j => by linarith [hεle n j]⟩
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  let k : ℕ → ℕ := fun n =>
    if h : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n then
      (h.choose : ℕ) else 0
  have hk : ∀ n, k n ≤ ℓ.eval n := by
    intro n
    simp only [k]
    split_ifs with h
    · exact h.choose.isLt.le
    · exact Nat.zero_le _
  obtain ⟨Dm, hc, hDm⟩ := exists_nextBitDistMachine A k hk
  have hlen : ∀ n, A.coinLen n = Dm.coinLen n := fun n => by simp only [NUPPT.coinLen, hc]
  let e : ∀ n, A.Coins n ≃ Dm.Coins n := fun n =>
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have hofn : ∀ n (r : A.Coins n), List.ofFn (e n r) = List.ofFn r := fun n r =>
    (List.ofFn_congr (hlen n) r).symm
  refine (not_negligible_iff_exists_polyExpr.mpr ⟨p, hp, fun n₀ => ?_⟩)
    ((Ensemble.pseudorandom_iff_prgAdv X).mp hX Dm)
  obtain ⟨n, hn, hpn⟩ := hinf n₀
  refine ⟨n, hn, ?_⟩
  have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
  have hε0 : ε n ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hpn
    have := one_div_pos.mpr hppos
    linarith
  have hex : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n :=
    (hεeq n).resolve_left hε0
  obtain ⟨j₀, hkn, hspec⟩ : ∃ j₀ : Fin (ℓ.eval n), k n = j₀ ∧
      nextBitProb (X.X n) j₀ (A.predictor n j₀) - 1 / 2 = ε n :=
    ⟨hex.choose, by simp only [k, dif_pos hex], hex.choose_spec⟩
  have hid : ∀ (t : Fin (ℓ.eval n) → Bool) (r : A.Coins n),
      Dm.distinguisher n (ℓ.eval n) t (e n r) = nextBitDist j₀ (A.predictor n j₀) t r := by
    intro t r
    simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hDm, hkn, nextBitDist, NUPPT.predictor,
      headD_drop_ofFn, ofFn_prefixOf]
    simp
  have hadv : prgAdv (X.X n) (Dm.distinguisher n (ℓ.eval n)) = |ε n| := by
    rw [← hspec, ← prgAdv_nextBitDist (X.X n) j₀ (A.predictor n j₀)]
    unfold prgAdv distAdv
    rw [acceptProb_coins_equiv (X.X n) (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid,
      acceptProb_coins_equiv id (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid]
  rw [hadv, abs_of_nonneg (abs_nonneg _)]
  exact hpn

end TCSlib.Cryptography
