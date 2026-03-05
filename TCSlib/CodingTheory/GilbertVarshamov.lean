import TCSlib.CodingTheory.LinearCodes

set_option linter.unusedSectionVars false

/-!
# Gilbert–Varshamov Bound

This file proves the **Gilbert–Varshamov (GV) existence bound**: for any block-length `n`,
dimension `k`, and distance `d` over a `q`-ary alphabet `α`, if

  k ≤ n − ⌈log_q Vol(n, d−1)⌉ − 1,

then there exists an `n × k` generator matrix `G` such that the linear code `G·αᵏ` has
minimum distance at least `d`.

The proof proceeds via a probabilistic argument:

1. `prob_leq_ball_size` : for any nonzero message `x`, the probability that a random
   generator matrix `G` sends `x` to a low-weight codeword is at most `Vol(n,d−1)/|α|ⁿ`.

2. `existence_bound` : by a union bound over all nonzero messages, the number of "bad"
   generator matrices (those sending some nonzero `x` to a codeword of weight < `d`) is
   at most `(|α|ᵏ − 1) · |α|^(nk−n) · Vol(n, d−1)`.

3. `gv_bound` : if `k` is small enough (satisfying the GV condition), the number of bad
   matrices is strictly less than the total `|α|^(nk)`, so at least one good matrix exists.

## Main Results

* `prob_leq_ball_size` : probabilistic bound on low-weight outputs.
* `existence_bound` : union-bound count of bad generator matrices.
* `gv_bound` : existence of a good generator matrix satisfying the GV condition.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory
namespace Codeword

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k : ℕ}

/-- **Probabilistic bound**: for any nonzero message `x ∈ αᵏ`, the fraction of `n×k` matrices
    `G` for which `G·x` has Hamming weight less than `d` is at most `Vol(n,d−1)/|α|ⁿ`. -/
theorem prob_leq_ball_size (x : Codeword k α) (d : ℕ) (h_k : k ≥ 1) (h_x : x ≠ 0) (h_d : d > 0) :
((Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) / (Fintype.card α : ℝ)^(n*k) ≤
((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n := by {

  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}
  let S' := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) ∈ hamming_ball (d-1) zero}

  have h_card_eq : S.card = S'.card := by
    let f : (G : Matrix (Fin n) (Fin k) α) → G ∈ S → (Matrix (Fin n) (Fin k) α) := fun G _ ↦ G
    apply Finset.card_bij f

    have h_map : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), f G hG ∈ S' := by
      simp[f, S]
      unfold weight
      intro G h_dist_le_d
      have h_dist_leq_dminus1 : hamming_distance (Matrix.mulVec G x) zero ≤ d - 1 := by
        have h₁ : (hamming_distance (Matrix.mulVec G x) zero) + 1 ≤ d := by exact Nat.succ_le_of_lt h_dist_le_d
        have h₂ : (hamming_distance (Matrix.mulVec G x) zero) + 1 - 1 ≤ d - 1 := by exact Nat.sub_le_sub_right h₁ 1
        rw[Nat.add_sub_cancel] at h₂
        exact h₂
      rw [mem_toFinset]
      simp[h_dist_leq_dminus1]

    exact h_map

    have h_inj : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), ∀ (G' : Matrix (Fin n) (Fin k) α) (hG' : G' ∈ S), f G hG = f G' hG' → G = G' := by
      intro G G' hG hG' h_fG_eq
      simp[h_fG_eq, f, S]

    exact h_inj

    have h_surj : ∀ G' ∈ S', ∃ G, ∃ (hG : G ∈ S), f G hG = G' := by
      intro G' h_G'inS'
      use G'
      simp[f, S]
      simp[Set.mem_setOf] at h_G'inS'
      rw[mem_toFinset] at h_G'inS'
      simp[Set.mem_setOf] at h_G'inS'
      unfold weight
      apply Nat.lt_of_le_pred
      simp[h_d]
      exact h_G'inS'
    exact h_surj

  simp[S, S'] at h_card_eq
  simp
  rw[h_card_eq]

  let matrix_uniformity := uniformity_lemma n k x h_x h_k

  unfold matrix_dist uniform_vector_dist at matrix_uniformity
  simp at matrix_uniformity

  have h_unif (v: Codeword n α) : (toFinset {G | Matrix.mulVec G x = v}).card / Fintype.card α ^ (n * k) = 1 / ((Fintype.card α : ℝ))^n := by
    apply congr_fun at matrix_uniformity
    specialize matrix_uniformity v
    have h_filter_eq : ↑(filter (fun x_1 => Matrix.mulVec x_1 x = v) Finset.univ) = (toFinset {G | Matrix.mulVec G x = v}) := by
      ext y
      constructor
      · intro h_filter
        rw[Finset.mem_filter] at h_filter
        simp_rw[Set.mem_toFinset, Set.mem_setOf, h_filter]
      · intro h_finset
        rw[Set.mem_toFinset, Set.mem_setOf] at h_finset
        rw[Finset.mem_filter]
        simp[h_finset]

    rw[←h_filter_eq]
    have h_inv : ((Fintype.card α : ℝ) ^ n)⁻¹ = 1 / (Fintype.card α : ℕ) ^ n := by simp
    rw_mod_cast[←h_inv]
    exact matrix_uniformity

  have h_sum : ((toFinset {G : (Matrix (Fin n) (Fin k) α) | Matrix.mulVec G x ∈ hamming_ball (d - 1) zero}).card : ℝ) / (Fintype.card α : ℝ) ^ (n * k) = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => 1 / (Fintype.card α : ℝ)^n := by
    simp[Finset.sum_const]
    have h_ball_eq_sum : (toFinset {G | Matrix.mulVec G x ∈ hamming_ball (d-1) zero}) = (Set.toFinset (⋃ (v : Fin n → α) (h_v : weight v ≤ d-1), {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) = v})) := by
      simp
      ext y
      constructor
      · intro h_ball
        simp
        simp at h_ball
        unfold weight
        simp[h_ball]
      · intro h_union
        apply Set.mem_toFinset.mp at h_union
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h_union
        obtain ⟨hwt, hG⟩ := Set.mem_iUnion.mp hv
        have h_yxv : Matrix.mulVec y x = v := hG
        have h_yx_hd : hamming_distance (Matrix.mulVec y x) 0 ≤ d - 1 := by rw[h_yxv]; exact hwt
        have h_yx_set : Matrix.mulVec y x ∈ toFinset {c' | hamming_distance c' 0 ≤ d - 1} := Set.mem_toFinset.mpr h_yx_hd
        exact (mem_filter_univ y).mpr h_yx_hd

    unfold hamming_ball at h_ball_eq_sum
    simp at h_ball_eq_sum
    rw[h_ball_eq_sum]

    have h_card_eq_sum : (toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v})).card = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => (toFinset {G | Matrix.mulVec G x = v}).card := by
      let hamming_set : Finset (Codeword n α) := toFinset {v | hamming_distance v zero ≤ d - 1}
      let f : Codeword n α → Finset (Matrix (Fin n) (Fin k) α) := fun v => toFinset {G | Matrix.mulVec G x = v}
      let G_union : Finset (Matrix (Fin n) (Fin k) α) := hamming_set.biUnion f

      have h_G_union : G_union = toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v}) := by
        ext G
        simp[Finset.mem_biUnion, Set.mem_toFinset, Set.mem_setOf_eq]
        constructor
        · intro h_a
          simp[G_union] at h_a
          let ⟨a, h_adist, h_Ga⟩ := h_a
          rw[Set.mem_toFinset, Set.mem_setOf] at h_Ga
          rw[←h_Ga] at h_adist
          unfold weight
          simp[hamming_set] at h_adist
          exact h_adist
        · intro h_weight
          let a := Matrix.mulVec G x
          simp[G_union]
          use a
          apply And.intro
          · simp[hamming_set]; exact h_weight
          · rw[Set.mem_toFinset, Set.mem_setOf]

      have h_disjoint : ∀ x ∈ hamming_set, ∀ y ∈ hamming_set, x ≠ y → Disjoint (f x) (f y) := by
        intro a h_a b h_b h_ab
        simp[f]
        rw[Finset.disjoint_iff_ne]
        intro G h_Ga H h_Ha
        simp at h_Ga h_Ha
        rw [←h_Ga, ←h_Ha] at h_ab
        by_contra h_GHeq
        have h_mul_eq : Matrix.mulVec G x = Matrix.mulVec H x := by simp[h_GHeq]
        contradiction

      rw[←h_G_union]
      apply Finset.card_biUnion h_disjoint

    rw[h_card_eq_sum]
    field_simp[matrix_uniformity]
    have h_preimage_card : ∀ (v : Codeword n α), ((toFinset {G | Matrix.mulVec G x = v}).card : ℝ) = ↑(Fintype.card α) ^ (n * k - n) := by
      intro v₀
      specialize h_unif v₀
      field_simp at h_unif
      have h_card_exp : ↑(toFinset {G | Matrix.mulVec G x = v₀}).card  = ((Fintype.card α : ℝ) ^ (n * k)) / ((Fintype.card α : ℝ) ^ n) := by field_simp; exact h_unif
      rw[h_card_exp]
      field_simp[h_card_exp]
      norm_cast
      simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k := by
        rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k'
      have : n + (n * k - n) = n * k := by linarith[h_pow_eq]
      rw[this]

    simp at h_preimage_card
    simp
    simp_rw[h_preimage_card, Finset.sum_const, nsmul_eq_mul]

    have h_exp : (Fintype.card α : ℝ)^(n * k - n) * (Fintype.card α : ℝ)^n = (Fintype.card α : ℝ)^(n * k) := by
      simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k := by
        rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k'
      rw[h_pow_eq]

    rw[←h_exp]
    simp[mul_assoc]
    linarith


  have h_ball_size : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = ((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n := by
    have h_sum_mult : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}).card * (1 / (Fintype.card α : ℝ)^n) := by simp[Finset.sum_const]
    rw[h_sum_mult]
    field_simp
    simp
  simp at h_sum
  simp at h_ball_size
  rw[h_sum, h_ball_size]
}

/-- **Union bound**: the number of `n×k` generator matrices `G` for which some nonzero message
    `x` is sent to a codeword of weight less than `d` is at most
    `(|α|ᵏ − 1) · |α|^(nk−n) · Vol(n, d−1)`. -/
theorem existence_bound (d: ℕ) (h_k : k ≥ 1) (h_d : d > 0) :
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}).card ≤
((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * ((hamming_ball (d-1) (zero : Codeword n α)).card) := by {

  let nonzero : Finset (Codeword k α) := Finset.univ.filter (· ≠ 0)
  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}

  have h_union_eq : S = nonzero.biUnion (fun x => Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}) := by
    ext G
    simp [S, nonzero, Set.mem_toFinset, Set.mem_setOf]

  have h_union_bound : S.card ≤ Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card) := by
    rw [h_union_eq]
    exact Finset.card_biUnion_le

  have h_each_x : ∀ x ∈ nonzero, (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card ≤ (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
    intro x hx
    have h_x_ne : x ≠ 0 := by simp [nonzero] at hx; exact hx
    have h_prob : ((Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) / (Fintype.card α : ℝ)^(n*k) ≤
        ((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n :=
      prob_leq_ball_size x d h_k h_x_ne h_d
    have hq_nk_pos : (0 : ℝ) < (Fintype.card α : ℝ)^(n*k) := by positivity
    have hq_n_pos : (0 : ℝ) < (Fintype.card α : ℝ)^n := by positivity
    have h_nk_ge_n : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    rw [div_le_div_iff₀ hq_nk_pos hq_n_pos] at h_prob
    have h_qnk_split : (Fintype.card α : ℝ)^(n*k) = (Fintype.card α : ℝ)^n * (Fintype.card α : ℝ)^(n*k - n) := by
      rw [← pow_add, Nat.add_sub_cancel' h_nk_ge_n]
    rw [h_qnk_split, ← mul_assoc] at h_prob
    have h_real : (↑(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) ≤
        ↑((Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      have h_rearrange : (↑(hamming_ball (d - 1) (zero : Codeword n α)).card : ℝ) *
          (Fintype.card α : ℝ) ^ n * (Fintype.card α : ℝ) ^ (n * k - n) =
          (Fintype.card α : ℝ) ^ (n * k - n) * ↑(hamming_ball (d - 1) (zero : Codeword n α)).card *
          (Fintype.card α : ℝ) ^ n := by ring
      rw [h_rearrange] at h_prob
      exact le_of_mul_le_mul_right h_prob hq_n_pos
    exact_mod_cast h_real

  have h_sum_leq : Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card) ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
    calc Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card)
        ≤ Finset.sum nonzero (fun _ => (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) :=
          Finset.sum_le_sum h_each_x
      _ = nonzero.card * ((Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
          have h_nonzero_card : nonzero.card = (Fintype.card α)^k - 1 := by
            have h_nonzero_eq : nonzero = Finset.univ \ {(0 : Codeword k α)} := by
              ext x; simp [nonzero]
            rw [h_nonzero_eq, Finset.card_sdiff_of_subset (by simp)]
            simp [Fintype.card_fun, Fintype.card_fin]
          rw [h_nonzero_card]
          ring

  trans Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card)
  · exact h_union_bound
  · exact h_sum_leq
}

/-- **Gilbert–Varshamov bound**: if `k ≤ n − ⌈log_q Vol(n, d−1)⌉ − 1`, then there exists
    an `n×k` generator matrix `G` such that every nonzero message is mapped to a codeword
    of Hamming weight at least `d`. -/
theorem gv_bound (n k q d : ℕ) (h_q : q = (Fintype.card α)) (h_k : k ≤ n - ((Nat.clog q) (hamming_ball (d-1) (zero : Codeword n α)).card) - 1):
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∀ (x : Codeword k α), x ≠ 0 → weight (Matrix.mulVec G x) ≥ d}).card ≥ 1 := by {
  set bc := (hamming_ball (d-1) (zero : Codeword n α)).card with h_bc_def
  let bad_G := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}
  have h_good_eq : Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∀ (x : Codeword k α), x ≠ 0 → weight (Matrix.mulVec G x) ≥ d} =
      Finset.univ \ bad_G := by
    ext G
    simp only [bad_G, Finset.mem_sdiff, Finset.mem_univ, true_and,
               Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · intro h ⟨x, hxne, hlt⟩; exact absurd (h x hxne) (Nat.not_le.mpr hlt)
    · intro h x hxne; exact Nat.le_of_not_lt (fun hlt => h ⟨x, hxne, hlt⟩)
  have h_all_card : Fintype.card (Matrix (Fin n) (Fin k) α) = (Fintype.card α)^(n*k) := by
    simp only [Matrix, Fintype.card_fun, Fintype.card_fin]; ring
  have hq_gt1 : 1 < (Fintype.card α) := Fintype.one_lt_card
  have hq_gt1' : 1 < q := h_q ▸ hq_gt1
  have hq_pos : 0 < (Fintype.card α) := by omega
  have h_ball_le_pow_of_clog_le : ∀ c : ℕ, Nat.clog q bc ≤ c → bc ≤ (Fintype.card α)^c := by
    intro c hc
    rw [h_bc_def, ← h_q] at *
    exact (Nat.clog_le_iff_le_pow hq_gt1').mp hc
  rw [h_good_eq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h_all_card]
  suffices h : bad_G.card < (Fintype.card α)^(n*k) by omega
  by_cases hk0 : k = 0
  · have h_bad_empty : bad_G = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      simp only [bad_G, Set.mem_toFinset, Set.mem_setOf_eq, not_exists, not_and]
      intro G x hxne
      have : x = 0 := by ext i; exact Fin.elim0 (hk0 ▸ i)
      exact absurd this hxne
    simp [h_bad_empty, hk0]
  · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk0
    have h_clog_le : Nat.clog q bc + k + 1 ≤ n := by omega
    have h_ball_le_pow : bc ≤ (Fintype.card α)^(n - k - 1) :=
      h_ball_le_pow_of_clog_le _ (by omega)
    by_cases hd0 : d = 0
    · have h_bad_empty : bad_G = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        simp only [bad_G, Set.mem_toFinset, Set.mem_setOf_eq, not_exists, not_and]
        intro G x _; simp [hd0]
      simp [h_bad_empty]; positivity
    · have hd_pos : d > 0 := Nat.pos_of_ne_zero hd0
      have h_exist : bad_G.card ≤
          ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * bc :=
        existence_bound d hk_pos hd_pos
      have hn_pos : 1 ≤ n := by omega
      have hnk_ge_n : n ≤ n * k := Nat.le_mul_of_pos_right n hk_pos
      have hnk_ge_k : k ≤ n * k := Nat.le_mul_of_pos_left k hn_pos
      have h_exp_combine : n*k - n + (n - k - 1) = n*k - k - 1 := by omega
      have h_exp_merge : k + (n*k - k - 1) = n*k - 1 := by omega
      have h_combine : ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) *
          (Fintype.card α)^(n - k - 1) = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - k - 1) := by
        rw [mul_assoc, ← pow_add, h_exp_combine]
      calc bad_G.card
          ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * bc := h_exist
        _ ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (Fintype.card α)^(n - k - 1) :=
            Nat.mul_le_mul_left _ h_ball_le_pow
        _ = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - k - 1) := h_combine
        _ < (Fintype.card α)^k * (Fintype.card α)^(n*k - k - 1) :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.sub_lt (Nat.pow_pos hq_pos) Nat.one_pos)
              (Nat.pow_pos hq_pos)
        _ = (Fintype.card α)^(n*k - 1) := by rw [← pow_add, h_exp_merge]
        _ ≤ (Fintype.card α)^(n*k) := Nat.pow_le_pow_right hq_pos (by omega)
}

end Codeword
end CodingTheory
