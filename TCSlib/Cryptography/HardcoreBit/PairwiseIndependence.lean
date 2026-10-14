/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pairwise independence and Chebyshev's inequality

Pairwise independent random variables under the uniform distribution on a finite sample
space [Gar26, Definition 2.4], Chebyshev's inequality for pairwise independent bits
[Gar26, Theorem 2.4], and the source of pairwise independence used in the
Goldreich–Levin proof: the subset sums `S_L = ⊕_{j ∈ L} s_j` of uniform strings
`s_1, …, s_k` over the nonempty subsets `L`.

## Main definitions

* `PairwiseIndep X`: the random variables `X i` are pairwise independent.
* `PairwiseUniform Z`: each `Z i`, and each pair `(Z i, Z j)` with `i ≠ j`, is uniform.
* `ind b`: the real indicator `1` or `0` of a bit.
* `majority v`: the majority bit of a tuple of bits (ties go to `false`).
* `subsetSum L s`: the sum `∑_{j ∈ L} s_j`, the XOR `⊕_{j ∈ L} s_j` for bit strings.

## Main results

* `PairwiseUniform.pairwiseIndep`: functions of a pairwise uniform family are pairwise
  independent.
* `pairwiseUniform_eval`, `PairwiseUniform.prod`: the coordinates of a uniform tuple
  are pairwise uniform, and pairing two pairwise uniform families keeps the property.
* `uexp_sq_sum_sub_eq`: the variance of a sum of pairwise independent bits is the sum
  of the variances `p_i (1 - p_i)`.
* `chebyshev_pairwise`, `chebyshev_pairwise_ident`: [Gar26, Theorem 2.4].
* `uprob_majority_fails_le`: a majority vote over pairwise independent trials, each
  correct with probability at least `1/2 + δ`, fails with probability at most
  `1 / (4 δ² m)`.
* `pairwiseUniform_subsetSum`: the subset sums over nonempty subsets are pairwise
  uniform. [Gar26, §2.5.1, real case], with the deviation that `L = ∅` is excluded.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1, Definition 2.4 and Theorem 2.4.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {Ω Ω' ι β γ δ : Type*} [Fintype Ω] [Fintype Ω'] [Fintype γ] [Fintype δ]

/-! ### Pairwise independence and pairwise uniformity -/

/-- The random variables `X i` on the uniform sample space `Ω` are pairwise independent:
for every two distinct indices `i ≠ j` and values `v, w`,
`Pr[X i = v ∧ X j = w] = Pr[X i = v] · Pr[X j = w]`. [Gar26, Definition 2.4]. -/
def PairwiseIndep (X : ι → Ω → β) : Prop :=
  ∀ i j, i ≠ j → ∀ v w : β, uprob (fun ω => X i ω = v ∧ X j ω = w) =
    uprob (fun ω => X i ω = v) * uprob (fun ω => X j ω = w)

/-- The family `Z i : Ω → γ` is pairwise uniform: each `Z i` is uniform on `γ` and each
pair `(Z i, Z j)` with `i ≠ j` is uniform on `γ × γ`. This is the form in which pairwise
independence arises in [Gar26, §2.5.1]. -/
structure PairwiseUniform (Z : ι → Ω → γ) : Prop where
  /-- Each member is uniform. -/
  marginal : ∀ i, PushesUniform (Z i)
  /-- Each pair of distinct members is uniform on the product. -/
  pair : ∀ i j, i ≠ j → PushesUniform (fun ω => (Z i ω, Z j ω))

/-- Arbitrary functions `H i` of a pairwise uniform family are pairwise independent.

**Proof sketch.** The joint event is an event about the uniform pair `(Z i, Z j)`, where
it is a product event, so its probability factors; each factor is an event about the
uniform `Z i`. -/
theorem PairwiseUniform.pairwiseIndep {Z : ι → Ω → γ} (hZ : PairwiseUniform Z)
    (H : ι → γ → β) : PairwiseIndep (fun i ω => H i (Z i ω)) := by
  intro i j hij v w
  have h1 := (hZ.pair i j hij).uprob_eq (fun z => H i z.1 = v ∧ H j z.2 = w)
  have h2 := (hZ.marginal i).uprob_eq (fun c => H i c = v)
  have h3 := (hZ.marginal j).uprob_eq (fun c => H j c = w)
  simp only at h1 h2 h3 ⊢
  rw [h1, h2, h3, uprob_prod_and (fun a => H i a = v) (fun b => H j b = w)]

/-- Precomposing a pairwise uniform family with a map pushing uniform to uniform keeps it
pairwise uniform. -/
theorem PairwiseUniform.comp_right {Z : ι → Ω → γ} (hZ : PairwiseUniform Z) {π : Ω' → Ω}
    (hπ : PushesUniform π) : PairwiseUniform (fun i ω => Z i (π ω)) :=
  ⟨fun i => hπ.comp (hZ.marginal i), fun i j hij => hπ.comp (hZ.pair i j hij)⟩

/-- Pairing two pairwise uniform families on independent sample spaces gives a pairwise
uniform family on the product.

**Proof sketch.** Up to reordering the four components, the pair of pairs is the product
of the two uniform pairs, and products of uniform maps are uniform. -/
theorem PairwiseUniform.prod {Z : ι → Ω → γ} {W : ι → Ω' → δ} (hZ : PairwiseUniform Z)
    (hW : PairwiseUniform W) : PairwiseUniform (fun i (ω : Ω × Ω') => (Z i ω.1, W i ω.2)) :=
  ⟨fun i => (hZ.marginal i).prodMap (hW.marginal i), fun i j hij =>
    ((hZ.pair i j hij).prodMap (hW.pair i j hij)).comp
      (pushesUniform_equiv (Equiv.prodProdProdComm γ γ δ δ))⟩

/-- The coordinates of a uniform tuple `ω : ι → γ` are pairwise uniform. -/
theorem pairwiseUniform_eval [Fintype ι] [DecidableEq ι] :
    PairwiseUniform (fun i (ω : ι → γ) => ω i) :=
  ⟨fun i => pushesUniform_eval i, fun _ _ hij => pushesUniform_eval_pair hij⟩

/-! ### Chebyshev's inequality -/

/-- The real indicator of a bit: `1` for `true`, `0` for `false`. -/
def ind (b : Bool) : ℝ := if b = true then 1 else 0

/-- The average of the indicator of a random bit is the probability that it is `true`. -/
theorem uexp_ind (X : Ω → Bool) : uexp (fun ω => ind (X ω)) = uprob (fun ω => X ω = true) := by
  classical
  rw [uprob_eq_uexp_ite]
  rfl

/-- The average of a product of two indicators is the probability that both bits are
`true`. -/
theorem uexp_ind_mul_ind (X Y : Ω → Bool) :
    uexp (fun ω => ind (X ω) * ind (Y ω)) = uprob (fun ω => X ω = true ∧ Y ω = true) := by
  classical
  rw [uprob_eq_uexp_ite]
  congr 1
  funext ω
  cases X ω <;> cases Y ω <;> simp [ind]

/-- The sum of the indicators of a tuple of bits is the number of `true` entries. -/
theorem sum_ind [Fintype ι] (v : ι → Bool) : ∑ i, ind (v i) = (#{i | v i = true} : ℝ) := by
  simp only [ind, sum_boole]

/-- The covariance of two bits: `E[(X - p)(Y - q)] = Pr[X ∧ Y] - p q`, where `p, q` are the
probabilities that `X`, `Y` are `true`. -/
theorem uexp_cov [Nonempty Ω] (X Y : Ω → Bool) :
    uexp (fun ω => (ind (X ω) - uprob (fun ω => X ω = true)) *
        (ind (Y ω) - uprob (fun ω => Y ω = true))) =
      uprob (fun ω => X ω = true ∧ Y ω = true) -
        uprob (fun ω => X ω = true) * uprob (fun ω => Y ω = true) := by
  set p := uprob (fun ω => X ω = true)
  set q := uprob (fun ω => Y ω = true)
  have h : (fun ω => (ind (X ω) - p) * (ind (Y ω) - q)) =
      fun ω => ind (X ω) * ind (Y ω) - p * ind (Y ω) - q * ind (X ω) + p * q := by
    funext ω; ring
  rw [h, uexp_add, uexp_sub, uexp_sub, uexp_const_mul, uexp_const_mul, uexp_const,
    uexp_ind_mul_ind, uexp_ind, uexp_ind]
  ring

/-- The variance of a sum of pairwise independent bits is the sum of their variances:
`E[(∑ᵢ (Xᵢ - pᵢ))²] = ∑ᵢ pᵢ (1 - pᵢ)`. [Gar26, proof of Theorem 2.4], the computation
`Var(Y) = m p (1 - p)`, here without assuming identical distribution.

**Proof sketch.** Expand the square into the double sum of covariances. Off the diagonal
they vanish by pairwise independence; on the diagonal `Pr[Xᵢ ∧ Xᵢ] = pᵢ` gives
`pᵢ - pᵢ²`. -/
theorem uexp_sq_sum_sub_eq [Nonempty Ω] [Fintype ι] {X : ι → Ω → Bool}
    (hX : PairwiseIndep X) :
    uexp (fun ω => (∑ i, (ind (X i ω) - uprob (fun ω => X i ω = true))) ^ 2) =
      ∑ i, uprob (fun ω => X i ω = true) * (1 - uprob (fun ω => X i ω = true)) := by
  classical
  have hsq : (fun ω => (∑ i, (ind (X i ω) - uprob (fun ω => X i ω = true))) ^ 2) =
      fun ω => ∑ i, ∑ j, (ind (X i ω) - uprob (fun ω => X i ω = true)) *
        (ind (X j ω) - uprob (fun ω => X j ω = true)) := by
    funext ω; rw [sq, sum_mul_sum]
  rw [hsq, uexp_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [uexp_sum, sum_eq_single i]
  · rw [uexp_cov]
    simp only [and_self]
    ring
  · intro j _ hji
    rw [uexp_cov, hX i j (Ne.symm hji), sub_self]
  · intro h; exact absurd (mem_univ i) h

/-- Markov's inequality for a square: `Pr[|Z| ≥ c] ≤ E[Z²] / c²` for `c > 0`. -/
theorem uprob_le_abs_le [Nonempty Ω] (Z : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    uprob (fun ω => c ≤ |Z ω|) ≤ uexp (fun ω => Z ω ^ 2) / c ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  refine uprob_mul_le_uexp (fun ω => sq_nonneg _) fun ω h => ?_
  rw [← sq_abs (Z ω)]
  exact pow_le_pow_left₀ hc.le h 2

/-- Chebyshev's inequality for pairwise independent bits, not necessarily identically
distributed: with `m ≥ 1` bits and `δ > 0`,
`Pr[|∑ᵢ Xᵢ - ∑ᵢ pᵢ| ≥ δ m] ≤ 1 / (4 δ² m)`. [Gar26, Theorem 2.4], generalized from a
common `p` to individual `pᵢ` (the source's statement is `chebyshev_pairwise_ident`).

**Proof sketch.** Markov's inequality for the square of the deviation gives at most
`Var / (δ m)²`, and `Var = ∑ pᵢ (1 - pᵢ) ≤ m / 4`. -/
theorem chebyshev_pairwise [Nonempty Ω] [Fintype ι] {X : ι → Ω → Bool}
    (hX : PairwiseIndep X) {δ : ℝ} (hδ : 0 < δ) (hm : 0 < Fintype.card ι) :
    uprob (fun ω => δ * Fintype.card ι ≤
        |∑ i, ind (X i ω) - ∑ i, uprob (fun ω => X i ω = true)|) ≤
      1 / (4 * δ ^ 2 * Fintype.card ι) := by
  have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  have h := uprob_le_abs_le
    (fun ω => ∑ i, (ind (X i ω) - uprob (fun ω => X i ω = true))) (mul_pos hδ hm')
  simp only [sum_sub_distrib] at h
  have hv := uexp_sq_sum_sub_eq hX
  simp only [sum_sub_distrib] at hv
  refine h.trans ?_
  rw [hv, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : ∑ i, uprob (fun ω => X i ω = true) * (1 - uprob (fun ω => X i ω = true)) ≤
      Fintype.card ι / 4 := by
    have : ∀ i, uprob (fun ω => X i ω = true) * (1 - uprob (fun ω => X i ω = true)) ≤ 1 / 4 :=
      fun i => by nlinarith [sq_nonneg (uprob (fun ω => X i ω = true) - 1 / 2)]
    calc _ ≤ ∑ _i : ι, (1 / 4 : ℝ) := sum_le_sum fun i _ => this i
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  nlinarith [mul_pos hδ hm']

/-- Chebyshev's inequality for pairwise independent identically distributed bits, each
`true` with probability `p`: `Pr[|∑ᵢ Xᵢ - p m| ≥ δ m] ≤ 1 / (4 δ² m)`.
[Gar26, Theorem 2.4]. -/
theorem chebyshev_pairwise_ident [Nonempty Ω] [Fintype ι] {X : ι → Ω → Bool}
    (hX : PairwiseIndep X) {p : ℝ} (hp : ∀ i, uprob (fun ω => X i ω = true) = p) {δ : ℝ}
    (hδ : 0 < δ) (hm : 0 < Fintype.card ι) :
    uprob (fun ω => δ * Fintype.card ι ≤ |∑ i, ind (X i ω) - p * Fintype.card ι|) ≤
      1 / (4 * δ ^ 2 * Fintype.card ι) := by
  have h := chebyshev_pairwise hX hδ hm
  simp only [hp, sum_const, card_univ, nsmul_eq_mul] at h
  simpa only [mul_comm p] using h

/-! ### Majority votes -/

/-- The majority of a tuple of bits: `true` when strictly more than half of the entries
are `true`, `false` otherwise (ties go to `false`). -/
def majority {κ : Type*} [Fintype κ] (v : κ → Bool) : Bool :=
  decide (Fintype.card κ < 2 * #{i | v i = true})

/-- If the majority of `v` is not `b`, then at most half of the entries of `v` equal `b`. -/
theorem two_mul_card_le_of_majority_ne {κ : Type*} [Fintype κ] (v : κ → Bool) (b : Bool)
    (h : majority v ≠ b) : 2 * #{i | v i = b} ≤ Fintype.card κ := by
  classical
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := univ) (fun i => v i = true)
  have hneg : (univ.filter fun i => ¬ v i = true) = univ.filter fun i => v i = false := by
    ext i; simp
  rw [hneg, card_univ] at hsplit
  cases b
  · simp only [majority, ne_eq, decide_eq_false_iff_not, not_not] at h
    omega
  · simp only [majority, ne_eq, decide_eq_true_eq, not_lt] at h
    omega

/-- A majority vote fails rarely: if trials `X i` are pairwise independent and each is
correct (`true`) with probability at least `1/2 + δ`, `δ > 0`, then at most half of the
`m ≥ 1` trials are correct with probability at most `1 / (4 δ² m)`. [Gar26, §2.5.1], the
bound on `Pr[x'_i ≠ x_i]` in the simple and real cases.

**Proof sketch.** If at most `m / 2` trials are correct, the number of correct trials is
at least `δ m` below its mean `∑ pᵢ ≥ (1/2 + δ) m`; apply Chebyshev. -/
theorem uprob_majority_fails_le [Nonempty Ω] [Fintype ι] {X : ι → Ω → Bool}
    (hX : PairwiseIndep X) {δ : ℝ} (hδ : 0 < δ) (hm : 0 < Fintype.card ι)
    (hp : ∀ i, 1 / 2 + δ ≤ uprob (fun ω => X i ω = true)) :
    uprob (fun ω => 2 * #{i | X i ω = true} ≤ Fintype.card ι) ≤
      1 / (4 * δ ^ 2 * Fintype.card ι) := by
  refine (uprob_mono fun ω hω => ?_).trans (chebyshev_pairwise hX hδ hm)
  have hc : (2 * #{i | X i ω = true} : ℝ) ≤ Fintype.card ι := by exact_mod_cast hω
  have hs : ∑ i, (1 / 2 + δ) ≤ ∑ i, uprob (fun ω => X i ω = true) :=
    sum_le_sum fun i _ => hp i
  rw [sum_const, card_univ, nsmul_eq_mul] at hs
  rw [sum_ind, abs_sub_comm]
  refine le_trans ?_ (le_abs_self _)
  nlinarith

/-! ### Subset sums of uniform strings -/

section SubsetSum

variable {κ G : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup G] [Fintype G]

/-- The subset sum `S_L(s) = ∑_{j ∈ L} s_j` of a tuple `s` of group elements; for bit
strings, where addition is XOR, this is `⊕_{j ∈ L} s_j`. [Gar26, §2.5.1, Figure 2.5]. -/
def subsetSum (L : Finset κ) (s : κ → G) : G := ∑ j ∈ L, s j

/-- The subset sum as an additive homomorphism of the tuple. -/
def subsetSumHom (L : Finset κ) : (κ → G) →+ G where
  toFun := subsetSum L
  map_zero' := by simp [subsetSum]
  map_add' s t := by simp [subsetSum, sum_add_distrib]

omit [Fintype κ] [Fintype G] in
/-- For distinct subsets `L ≠ L'` with `L` nonempty, every `u` is `S_L(s)` for some `s`
with `S_{L'}(s) = 0`.

**Proof sketch.** If some `a ∈ L` lies outside `L'`, put `u` at `a`. Otherwise
`L ⊊ L'`; take `a ∈ L` and `b ∈ L' \ L`, and put `u` at `a` and `-u` at `b`. -/
theorem exists_subsetSum_eq_zero {L L' : Finset κ} (hL : L.Nonempty) (hne : L ≠ L') (u : G) :
    ∃ s : κ → G, subsetSum L s = u ∧ subsetSum L' s = 0 := by
  by_cases h : ∃ a ∈ L, a ∉ L'
  · obtain ⟨a, ha, ha'⟩ := h
    exact ⟨Pi.single a u, by simp [subsetSum, ha], by simp [subsetSum, ha']⟩
  · push_neg at h
    obtain ⟨b, hb', hb⟩ : ∃ b ∈ L', b ∉ L := by
      by_contra h'
      push_neg at h'
      exact hne (Finset.Subset.antisymm h h')
    obtain ⟨a, ha⟩ := hL
    refine ⟨Pi.single a u - Pi.single b u, ?_, ?_⟩
    · simp [subsetSum, sum_sub_distrib, ha, hb]
    · simp [subsetSum, sum_sub_distrib, h a ha, hb']

/-- The subset sums `S_L` of a uniform tuple, over the nonempty subsets `L`, are pairwise
uniform: each `S_L` is uniform, and `(S_L, S_{L'})` is uniform for `L ≠ L'`.
[Gar26, §2.5.1, real case], where pairwise independence of the `Y_i^L` rests on this.
Deviation: the source ranges over all `L ⊆ [log T]`, but `S_∅ = 0` is constant, so it is
neither uniform nor a useful trial; only nonempty subsets are used.

**Proof sketch.** Both maps are additive homomorphisms; they are surjective by
`exists_subsetSum_eq_zero` (combine a solution for `(u, 0)` with one for `(0, v)`), and
surjective homomorphisms push uniform to uniform. -/
theorem pairwiseUniform_subsetSum :
    PairwiseUniform (fun (L : {L : Finset κ // L.Nonempty}) (s : κ → G) => subsetSum L.1 s) := by
  refine ⟨fun L => ?_, fun L L' hne => ?_⟩
  · refine pushesUniform_of_surjective (subsetSumHom (G := G) L.1) fun u => ?_
    obtain ⟨a, ha⟩ := L.2
    exact ⟨Pi.single a u, by simp [subsetSumHom, subsetSum, ha]⟩
  · have hne' : L.1 ≠ L'.1 := fun h => hne (Subtype.ext h)
    refine pushesUniform_of_surjective ((subsetSumHom (G := G) L.1).prod (subsetSumHom (G := G) L'.1))
      fun ⟨u, v⟩ => ?_
    obtain ⟨s, hs, hs'⟩ := exists_subsetSum_eq_zero L.2 hne' u
    obtain ⟨t, ht', ht⟩ := exists_subsetSum_eq_zero L'.2 hne'.symm v
    refine ⟨s + t, ?_⟩
    simp only [AddMonoidHom.prod_apply, map_add, Prod.mk_add_mk, subsetSumHom,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, hs, hs', ht, ht', add_zero, zero_add]

/-- There are `2^k - 1` nonempty subsets of a `k`-element set. -/
theorem card_nonempty_finset :
    Fintype.card {L : Finset κ // L.Nonempty} = 2 ^ Fintype.card κ - 1 := by
  classical
  rw [Fintype.card_subtype]
  have : (univ.filter fun L : Finset κ => L.Nonempty) = univ.erase ∅ := by
    ext L; simp [Finset.nonempty_iff_ne_empty]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset]

end SubsetSum

end TCSlib.Cryptography.HardcoreBit
