/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.StatisticalDistance
import TCSlib.InformationTheory.UniversalHashing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The leftover hash lemma

Hashing a source of min-entropy `k` with a universal family extracts almost-uniform randomness:
the pair `(seed, hash of the source)` is statistically close to uniform, with error
`½ √(|β| · 2^(-k))`. The seed is published alongside the output, so the family is a *strong*
extractor; this is the standard tool for privacy amplification, key derivation from imperfect
sources, and randomness extraction generally.

The proof is the classical collision-probability argument in three steps: universality bounds the
collision probability of `(seed, hash)`, the `ℓ¹`–`ℓ²` bound turns that into a statistical
distance bound, and min-entropy bounds the source's own collision probability.

## Main definitions

* `TCSlib.InformationTheory.hashPair`: the distribution of `(seed, f seed x)` for a uniform seed
  and `x` drawn from the source.

## Main results

* `collision_hashPair_le`: universality bounds the collision probability of `(seed, hash)` by
  `(1/|S|)(collision X + 1/|β|)`.
* `leftover_hash`: **the leftover hash lemma**.

## References

* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999 (Lemma 4.8, the leftover hash lemma).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, Thm 6.18.
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {S α β : Type*} [Fintype S] [Fintype α] [Fintype β]
  [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S] [Nonempty β]

/-- The distribution of the pair `(seed, f seed x)` where the seed is uniform and `x` is drawn
from the source `X`, independently. Closeness of this pair to uniform — rather than of the hash
value alone — is what makes a universal family a *strong* extractor. [Vad12, Thm 6.18] -/
noncomputable def hashPair (f : S → α → β) (X : FinDist α) : FinDist (S × β) :=
  FinDist.map (fun p => (p.1, f p.1 p.2)) (FinDist.prod (uniform S) X)

omit [DecidableEq α] [Nonempty β] in
theorem hashPair_apply (f : S → α → β) (X : FinDist α) (s : S) (y : β) :
    hashPair f X (s, y)
      = (Fintype.card S : ℝ)⁻¹ * ∑ x ∈ univ.filter (fun x => f s x = y), X x := by
  simp only [hashPair, map_apply, Finset.sum_filter, Fintype.sum_prod_type, FinDist.prod_apply,
    Prod.mk.injEq]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem s (mem_univ s)]
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : f s x = y <;> simp [h]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [hb]

/-- **Universality bounds the collision probability of the hashed pair.**

**Proof sketch.** Expanding, the collision probability of `(seed, hash)` is
`|S|⁻² ∑_seed ∑_y (weight of the fibre over y)²`. By `sum_sq_fiber` the inner double sum counts
colliding pairs `(x, x')`, and summing over seeds replaces each pair by the number of seeds under
which it collides. Diagonal pairs contribute `|S| · collision X`; off-diagonal pairs contribute at
most `|S|/|β|` times `(∑ X)² = 1`, by universality. -/
theorem collision_hashPair_le {f : S → α → β} (hf : IsUniversal f) (X : FinDist α) :
    collision (hashPair f X)
      ≤ (Fintype.card S : ℝ)⁻¹ * (collision X + (Fintype.card β : ℝ)⁻¹) := by
  set N : ℝ := (Fintype.card S : ℝ) with hN_def
  set M : ℝ := (Fintype.card β : ℝ) with hM_def
  have hN : (0 : ℝ) < N := by rw [hN_def]; exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < M := by rw [hM_def]; exact_mod_cast Fintype.card_pos
  set c : α → α → ℝ := fun x x' => ((univ.filter (fun s => f s x = f s x')).card : ℝ) with hc_def
  -- Step 1: expand the collision probability over seeds and fibres.
  have hexpand : collision (hashPair f X)
      = N⁻¹ ^ 2 * ∑ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2 := by
    simp only [collision, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hashPair_apply, mul_pow]
  -- Step 2: rewrite the fibre sums as sums over colliding pairs, then count seeds.
  have hpairs : ∀ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2
      = ∑ x, ∑ x', if f s x = f s x' then X x * X x' else 0 := fun s => sum_sq_fiber _ _
  have hswap : ∑ s : S, ∑ x, ∑ x', (if f s x = f s x' then X x * X x' else 0)
      = ∑ x, ∑ x', c x x' * (X x * X x') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Step 3: split the diagonal off and apply universality to the rest.
  have hdiag : ∀ x : α, c x x = N := by
    intro x
    simp [hc_def, hN_def]
  have hoff : ∀ x x' : α, x ≠ x' → c x x' ≤ N / M := fun x x' h => hf x x' h
  have hkey : ∑ x, ∑ x', c x x' * (X x * X x') ≤ N * collision X + N / M := by
    have hsplit : ∀ x : α, ∑ x', c x x' * (X x * X x')
        = c x x * (X x * X x) + ∑ x' ∈ univ.erase x, c x x' * (X x * X x') :=
      fun x => (Finset.add_sum_erase _ _ (mem_univ x)).symm
    have hstep : ∀ x : α, ∑ x', c x x' * (X x * X x')
        ≤ N * (X x * X x) + (N / M) * ∑ x', X x * X x' := by
      intro x
      rw [hsplit x, hdiag x]
      refine add_le_add_left ?_ _
      rw [Finset.mul_sum]
      have h1 : ∑ x' ∈ univ.erase x, c x x' * (X x * X x')
          ≤ ∑ x' ∈ univ.erase x, (N / M) * (X x * X x') :=
        Finset.sum_le_sum fun x' hx' => mul_le_mul_of_nonneg_right
          (hoff x x' (Ne.symm (mem_erase.1 hx').1)) (mul_nonneg (X.nonneg x) (X.nonneg x'))
      refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
      intro x' _ _
      exact mul_nonneg (le_of_lt (div_pos hN hM)) (mul_nonneg (X.nonneg x) (X.nonneg x'))
    calc ∑ x, ∑ x', c x x' * (X x * X x')
        ≤ ∑ x, (N * (X x * X x) + (N / M) * ∑ x', X x * X x') :=
          Finset.sum_le_sum fun x _ => hstep x
      _ = N * collision X + (N / M) * ((∑ x, X x) * (∑ x', X x')) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_mul_sum]
          simp only [collision, sq]
      _ = N * collision X + N / M := by rw [X.sum_prob]; ring
  -- Combine.
  rw [hexpand]
  have hfinal : ∑ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2
      ≤ N * collision X + N / M := by
    rw [Finset.sum_congr rfl fun s _ => hpairs s, hswap]
    exact hkey
  have hsq : (0 : ℝ) ≤ N⁻¹ ^ 2 := sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hfinal hsq) (le_of_eq ?_)
  field_simp

/-- **The leftover hash lemma.** If `f` is a universal hash family into `β` and the source `X` has
min-entropy at least `k`, then `(seed, f seed X)` is within statistical distance
`½ √(|β| · 2^(-k))` of uniform. [HILL99, Lemma 4.8], [Vad12, Thm 6.18]

**Proof sketch.** By the `ℓ¹`–`ℓ²` bound it suffices to bound
`|S × β| · collision (seed, hash) - 1`. Universality gives
`collision ≤ |S|⁻¹ (collision X + |β|⁻¹)`, so that quantity is at most `|β| · collision X`, and
min-entropy `k` bounds `collision X` by `2^(-k)`. -/
theorem leftover_hash {f : S → α → β} {k : ℝ} (hf : IsUniversal f) {X : FinDist α}
    (hX : HasMinEntropy X k) :
    statDist (hashPair f X) (uniform (S × β))
      ≤ (1 / 2) * Real.sqrt (Fintype.card β * (2 : ℝ) ^ (-k)) := by
  refine (statDist_uniform_le_sqrt (hashPair f X)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hc := collision_hashPair_le hf X
  have hCP := collision_le_of_hasMinEntropy hX
  have hstep : (Fintype.card (S × β) : ℝ) * collision (hashPair f X)
      ≤ (Fintype.card β : ℝ) * collision X + 1 := by
    rw [Fintype.card_prod]
    push_cast
    calc (Fintype.card S : ℝ) * (Fintype.card β : ℝ) * collision (hashPair f X)
        ≤ (Fintype.card S : ℝ) * (Fintype.card β : ℝ) *
            ((Fintype.card S : ℝ)⁻¹ * (collision X + (Fintype.card β : ℝ)⁻¹)) := by
          exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (Fintype.card β : ℝ) * collision X + 1 := by field_simp
  have hCPnn : (0 : ℝ) ≤ Fintype.card β := le_of_lt hM
  nlinarith [mul_le_mul_of_nonneg_left hCP hCPnn]

/-- The leftover hash lemma for the affine family over a finite field: if `X` has min-entropy at
least `k` on `F`, then `((a, b), a · X + b)` for a uniform seed `(a, b)` is within
`½ √(|F| · 2^(-k))` of uniform. A concrete witness that the hypotheses of `leftover_hash` are
satisfiable. [Vad12, Thm 6.18] -/
theorem leftover_hash_affine (F : Type*) [Field F] [Fintype F] [DecidableEq F] {k : ℝ}
    {X : FinDist F} (hX : HasMinEntropy X k) :
    statDist (hashPair (fun s : F × F => fun x : F => s.1 * x + s.2) X) (uniform ((F × F) × F))
      ≤ (1 / 2) * Real.sqrt (Fintype.card F * (2 : ℝ) ^ (-k)) :=
  leftover_hash (isUniversal_affine F) hX

end TCSlib.InformationTheory
