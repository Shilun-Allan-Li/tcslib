/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite next-bit reductions

At one output length `ℓ`, a predictor receives a prefix of a sample and guesses the next bit.
The hybrids replace the rest of the sample by independent uniform bits. A distinguishing
advantage `ε` yields a position and a sign at which the predictor succeeds with probability
at least `1/2 + ε/ℓ` [PS10, Theorem 75.4]. Conversely, testing a predictor's answer against the
sampled bit gives a distinguisher with advantage equal to the predictor's absolute bias.

## Main definitions

* `TCSlib.Cryptography.nextBitProb` measures prediction success at one position.
* `TCSlib.Cryptography.prefixOf` and `TCSlib.Cryptography.completePrefix` implement prefix
  extraction and completion. Their `List.ofFn` equations connect them to string algorithms.
* `TCSlib.Cryptography.nextBitHybrid` and `TCSlib.Cryptography.nextBitHybridFlip` supply
  the intermediate samplers in the hybrid argument.
* `TCSlib.Cryptography.nextBitPred` and `TCSlib.Cryptography.nextBitDist` give the two
  reductions on finite samplers and adversaries.

## Main results

* `TCSlib.Cryptography.exists_nextBitPred` gives the quantitative hybrid bound.
* `TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero` handles the empty string.
* `TCSlib.Cryptography.nextBitProb_id` gives success probability `1/2` on uniform strings.
* `TCSlib.Cryptography.prgAdv_nextBitDist` gives the converse advantage identity.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.2: Definition 75.2, Theorem 75.4, Algorithm 76.5; §3.1.1: Lemmas 71.6 and 73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5 and Theorems 3.1–3.2).
-/

namespace TCSlib.Cryptography

open Finset

/-! ### The next-bit experiment and the next-bit test [PS10, Definition 75.2] -/

/-- **The next-bit experiment** at one parameter: the probability, over a uniform seed `s` of
the sampler `X : σ → {0,1}^ℓ` and uniform coins `r`, that the predictor `A`, given the prefix
of length `i` of `t = X s`, outputs bit `i` of `t` — the quantity
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}]` of [PS10, Definition 75.2] with `0`-indexed bits
(prefix of length `i`, predicted bit `i`). -/
noncomputable def nextBitProb {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i

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
bijection — a run-3 repair, labelled P2-3 here and noted at gate 03c, finding 5 — so the
proof adjoins an ignored uniform bit instead.)

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
  simp only [acceptProb_def]
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

/-- The predictor runs `D` on the completed prefix, selects bit `i` or its negation according
to the verdict, and flips that result when `flip` is true [PS10, Algorithm 76.5]. -/
theorem nextBitPred_eq {ρ : Type*} {ℓ : ℕ} (D : (Fin ℓ → Bool) → ρ → Bool)
    (i : Fin ℓ) (flip : Bool) (t : Fin i → Bool) (c : (Fin ℓ → Bool) × ρ) :
    nextBitPred D i flip t c =
      xor (if D (completePrefix i t c.1) c.2 then c.1 i else !c.1 i) flip :=
  rfl

/-- **Predictor analysis, positive sign**: `nextBitPred D i false` predicts bit `i` of `X`
from the prefix of length `i` with probability exactly
`1/2 + (Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]) / 2` — the last display of the proof of
[PS10, Theorem 75.4] (which writes `A(t) = 1` for `A(t) = b`), i.e. the identity of
[PS10, Lemma 73.8] (`predict_eq`) with `X¹ := H^{i+1}` and `X⁰ := H̃^{i+1}`.

**Proof sketch.** Reassociate the sample space to `(σ × {0,1}^ℓ) × ρ` (`Equiv.prodAssoc`) and
apply `uprob_split_bit` at position `i` with the bit `x_i = X s i` (an adjoined uniform bit and
the involution `ψ`): the success probability is the average of the success event with `x_i`
planted at bit `i` of `u` and with `x̄_i` planted there. With `x_i` planted, the completed
string `completePrefix i (prefixOf i (X s)) u` is `nextBitHybrid X (i+1) (s, u)`
(`completePrefix_prefixOf_eq`, `nextBitHybrid_update_eq`) and the predictor, which outputs
`u_i = x_i` on acceptance, is right iff `D` accepts; with `x̄_i` planted the completed string is
`nextBitHybridFlip X i (s, u)` (`nextBitHybrid_update_not_eq`) and the predictor is right iff
`D` rejects (`uprob_not`, which needs the nonemptiness hypotheses). Average the two:
`(Pr[D(H^{i+1}) = 1] + 1 − Pr[D(H̃^{i+1}) = 1]) / 2`. (The run-2 sketch transported the event
along the 2-to-1 map `(b, (s, u), c) ↦ (s, (update u i (b ⊕ x_i), c))`; see `uprob_split_bit`.) -/
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
    simp only [acceptProb_def]
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, completePrefix_prefixOf_eq, nextBitHybrid_update_eq,
      Function.update_self, Bool.xor_false]
    cases D (nextBitHybrid X (i + 1) z.1) z.2 <;> cases X z.1.1 i <;> simp
  have hB : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      nextBitPred D i false (prefixOf i (X z.1.1)) (Function.update z.1.2 i (!X z.1.1 i), z.2) =
        X z.1.1 i) = 1 - acceptProb (nextBitHybridFlip X i) D := by
    simp only [acceptProb_def]
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

/-- The PRG advantage is the gap between the extreme hybrids: `prgAdv X D =
|Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`, by `H^0 = U_ℓ` (`acceptProb_nextBitHybrid_zero`) and
`H^ℓ = X` (`acceptProb_nextBitHybrid_self`). -/
private theorem prgAdv_eq_abs_nextBitHybrid {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    prgAdv X D = |acceptProb (nextBitHybrid X 0) D - acceptProb (nextBitHybrid X ℓ) D| := by
  simp only [prgAdv_eq, distAdv_def]
  rw [acceptProb_nextBitHybrid_zero, acceptProb_nextBitHybrid_self, abs_sub_comm]

/-- **No advantage on the empty string**: if `ℓ = 0`, then every distinguisher `D` has PRG
advantage `0` against every sampler `X` into `{0,1}^ℓ` (both `X` and the uniform `U_0` are the
point mass on the empty string). This is the case `ℓ(n) = 0` of [PS10, Theorem 75.4], which
needs no position.

**Proof sketch.** With `ℓ = 0` the two extreme hybrids `H^0` and `H^ℓ` coincide, so the gap
`prgAdv_eq_abs_nextBitHybrid` is `|a − a| = 0`. -/
theorem prgAdv_eq_zero_of_length_eq_zero {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (hℓ : ℓ = 0) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    prgAdv X D = 0 := by
  subst hℓ
  rw [prgAdv_eq_abs_nextBitHybrid, sub_self, abs_zero]

/-- **The next-bit reduction, concrete form** (the content of the proof of
[PS10, Theorem 75.4] at one parameter): for every sampler `X` into `{0,1}^ℓ` with `ℓ > 0` and
every distinguisher `D` with PRG advantage `ε = prgAdv X D` against `X`, there are a position
`i < ℓ` and a sign `flip` such that the next-bit predictor `nextBitPred D i flip`
[PS10, Algorithm 76.5] predicts bit `i` of `X` from the prefix of length `i` with probability
at least `1/2 + ε/ℓ`. (The text obtains `1/2 + 1/(p(n)ℓ(n))` from `ε = 1/p(n)`.)

**Proof sketch.** `prgAdv X D = |Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`
(`prgAdv_eq_abs_nextBitHybrid`); the hybrid lemma
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
  have hadv := prgAdv_eq_abs_nextBitHybrid X D
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
theorem ofFn_completePrefix {ℓ : ℕ} (i : Fin ℓ) (t : Fin i → Bool) (u : Fin ℓ → Bool) :
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
theorem ofFn_prefixOf {ℓ : ℕ} (i : Fin ℓ) (t : Fin ℓ → Bool) :
    List.ofFn (prefixOf i t) = (List.ofFn t).take i := by
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_take, prefixOf]
  rfl

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
    simp only [e, Equiv.coe_fn_mk, id_eq, hprefix, Function.update_self]
    cases A (fun j => z.1 (Fin.castLE i.isLt.le j)) z.2 <;> cases z.1 i <;> simp
  unfold nextBitProb
  rw [uprob_not] at hflip
  linarith

/-- The distinguisher built from a next-bit predictor `A` at position `i`: accept the string
`t` iff `A(t_1 ⋯ t_i) = t_{i+1}` — the "statistical test" a next-bit predictor induces
[PS10, p. 74, "a pseudorandom distribution needs to pass all efficiently computable
statistical tests"]. -/
def nextBitDist {ρ : Type*} {ℓ : ℕ} (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    (Fin ℓ → Bool) → ρ → Bool :=
  fun t c => decide (A (prefixOf i t) c = t i)

/-- The distinguisher accepts `t` exactly when the prediction from its prefix equals bit `i`. -/
theorem nextBitDist_eq {ρ : Type*} {ℓ : ℕ} (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool)
    (t : Fin ℓ → Bool) (c : ρ) :
    nextBitDist i A t c = decide (A (prefixOf i t) c = t i) :=
  rfl

/-- `nextBitDist i A` accepts a sample of `X` exactly when `A` predicts its next bit. -/
theorem acceptProb_nextBitDist {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    acceptProb X (nextBitDist i A) = nextBitProb X i A := by
  unfold nextBitProb nextBitDist prefixOf
  simp only [acceptProb_def]
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
  simp only [prgAdv_eq, distAdv_def]
  rw [acceptProb_nextBitDist, acceptProb_nextBitDist, nextBitProb_id]

end TCSlib.Cryptography
