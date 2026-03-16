import TCSlib.CodingTheory.Basic

set_option linter.unusedSectionVars false

/-!
# Linear Codes and the Uniformity Lemma

This file develops the theory of linear codes and a key probabilistic tool used in the
Gilbert–Varshamov existence argument.

## Main Definitions

* `uniform_vector_dist n α` : the uniform distribution on length-`n` vectors over `α`.
* `matrix_dist n k x` : the distribution on length-`n` output vectors induced by a uniformly
  random generator matrix `G` applied to a fixed nonzero message `x ∈ αᵏ`.
* `get_matrix_row` : utility to extract row `i` of a matrix as a `1×k` matrix.

## Main Results

* `Linear_Code_dist_eq_min_weight` : for a linear code, minimum distance equals minimum
  nonzero weight.
* `finite_matrix_dist` : the set `{G | G·x = v}` is finite.
* `uniformity_lemma` : for any nonzero `x ∈ αᵏ`, the output `G·x` is uniformly distributed
  over `αⁿ` when `G` is a uniformly random `n×k` matrix over `α`.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory
namespace Codeword

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k m : ℕ}

/-- For a linear code, minimum distance equals minimum nonzero Hamming weight. -/
lemma Linear_Code_dist_eq_min_weight {m d} (C : Code n α) (h_linear : Linear_Code' C m)
    (h : distance C d) :
    (∀ c ∈ C, c ≠ 0 → weight c ≥ d) ∧ (∃ c ∈ C, weight c = d) := by {
  rcases h_linear with ⟨G, hG⟩
  constructor
  · intros c hc c_nzero
    simp [weight]

    apply h.2 c hc 0
    rcases hG with ⟨hG_image, _⟩
    specialize hG_image 0
    simp at hG_image
    exact hG_image
    exact c_nzero
  · rcases h.1 with ⟨c₁, ⟨hc₁, c₂, ⟨hc₂, ⟨_, hc₁₂dist_eq_d⟩⟩⟩⟩
    use c₁ - c₂
    rcases hG with ⟨hG_image, hG_preimage⟩
    apply hG_preimage at hc₁
    apply hG_preimage at hc₂
    rcases hc₁ with ⟨c₁', hc₁'⟩
    rcases hc₂ with ⟨c₂', hc₂'⟩
    constructor
    · rw[hc₁', hc₂']
      rw[sub_eq_add_neg, ← Matrix.mulVec_neg, ← Matrix.mulVec_add, ← sub_eq_add_neg]
      exact hG_image (c₁' - c₂')
    · rw[← hc₁₂dist_eq_d]
      simp [hamming_distance, weight]
      exact (hammingDist_eq_hammingNorm c₁ c₂).symm
}

/-- The uniform distribution on length-`n` vectors: each vector has probability `1/|α|^n`. -/
noncomputable def uniform_vector_dist (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] :
    (Codeword n α) → ℝ :=
  fun _ => 1 / ((Fintype.card α) ^ n)

/-- The set of matrices `G` such that `G·x = v` is finite. -/
theorem finite_matrix_dist (n k : ℕ) (v : Codeword n α) (x : Codeword k α) :
    Set.Finite { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } := by {
  have dist_subset :
    { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } ⊆
    (Set.univ : Set (Matrix (Fin n) (Fin k) α)) := by
      intro G _
      trivial

  have matrices_fintype : Finite ↑{G | Matrix.mulVec G x = v} := by
    exact Finite.Set.subset (Set.univ : Set (Matrix (Fin n) (Fin k) α)) dist_subset

  exact (Set.finite_coe_iff.mp matrices_fintype)
}

/-- The distribution on `αⁿ` induced by applying a uniformly random `n×k` matrix to `x`:
    `matrix_dist n k x v = |{G | G·x = v}| / |α|^(n·k)`. -/
noncomputable def matrix_dist (n k : ℕ) (x : Codeword k α) : (Codeword n α) → ℝ :=
  fun v => (Set.Finite.toFinset (finite_matrix_dist n k v x)).card / ((Fintype.card α) ^ (n * k))

/-- Utility: extract row `i` of matrix `M` as a `1×k` matrix. -/
def get_matrix_row (n k : ℕ) (M : Matrix (Fin n) (Fin k) α) (i : Fin n) :
    Matrix (Fin 1) (Fin k) α :=
  Matrix.of (fun _ j => (M i) j)

/-- **Uniformity Lemma**: for any nonzero `x ∈ αᵏ`, applying a uniformly random `n×k` matrix
    over `α` to `x` yields the uniform distribution over `αⁿ`. -/
theorem uniformity_lemma (n k : ℕ) (x : Codeword k α) (h_x : x ≠ zero) (h_k : k ≥ 1) :
    matrix_dist n k x = uniform_vector_dist n α := by {

  unfold matrix_dist uniform_vector_dist
  funext v
  simp
  field_simp

  have h : (filter (fun G => Matrix.mulVec G x = v) Finset.univ).card = (Fintype.card α)^(n * (k-1)) := by
    -- Says that the amount of matrices G such that Gx = v is equal to the amount of matrices G such that
    -- for each row G_i, G_ix = v_i
    have h2 : (fun G => Matrix.mulVec G x = v) = (fun G => ∀ i, Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i) := by
      funext G
      apply propext
      apply Iff.intro
      · intro h_G i
        funext x'
        unfold get_matrix_row Matrix.mulVec dotProduct
        simp
        unfold Matrix.mulVec dotProduct at h_G
        simp at h_G
        exact congrFun h_G i
      · intro h_g
        unfold Matrix.mulVec dotProduct
        simp
        unfold get_matrix_row Matrix.mulVec dotProduct at h_g
        simp at h_g
        funext x₀
        have h_g' : (fun x_1 : Fin 1 => Finset.sum Finset.univ fun x_2 => G x₀ x_2 * x x_2) = fun x => v x₀ := by exact h_g x₀
        exact congrFun h_g' 1
    -- Says that the number of matrices G such that for each row G_i, G_ix = v_i is equal to the product
    -- over i of the number of row vectors g such that gx = v_i
    have h3 : (filter (fun G => ∀ (i : Fin n), Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i) Finset.univ).card
    = Finset.prod Finset.univ (fun (i : Fin n) => (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun _ => v i) Finset.univ).card) := by
      have h3₀ : (fun G => ∀ (i : Fin n), Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i)
      = (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) := by
        unfold get_matrix_row Matrix.mulVec dotProduct
        simp
        funext G₀
        simp
        apply Iff.intro
        · intro h_fun i₀
          specialize h_fun i₀
          have h_f : ∀x₀, (fun x_1 : Fin 1=> Finset.sum Finset.univ fun x_2 => G₀ i₀ x_2 * x x_2) x₀ = v i₀ := by exact congr_fun h_fun
          let x₀ : Fin 1 := 1
          specialize h_f x₀
          exact h_f
        · intro h_all i₀
          funext x₀
          specialize h_all i₀
          exact h_all

      have h3₁ : Finset.prod Finset.univ (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun x => v i) Finset.univ).card)
      = ((Finset.univ : Finset (Fin n)).pi (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => (Matrix.mulVec g x = fun x => v i)) Finset.univ))).card := by simp

      let S : Finset ((a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) :=
      ((Finset.univ : Finset (Fin n)).pi (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => (Matrix.mulVec g x = fun _ => v i)) Finset.univ)))

      have h3₂ : S.card = (filter (fun G : Matrix (Fin n) (Fin k) α => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ).card := by
        let f : (s : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) → s ∈ S → (Matrix (Fin n) (Fin k) α) := fun s _ ↦ Matrix.of (fun i j => (s i (Finset.mem_univ i)) 1 j)

        apply Finset.card_bij f

        have h_map_to_generator : ∀ (a : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) (ha : a ∈ S),
        f a ha ∈ filter (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ:= by
          intro a ha
          simp
          intro i

          have h_av : Matrix.mulVec (a i (Finset.mem_univ i)) x = fun _ => v i := by
            apply Finset.mem_pi.mp at ha
            specialize ha i
            specialize ha (Finset.mem_univ i)
            apply Finset.mem_filter.mp at ha
            simp[ha]

          unfold Matrix.mulVec dotProduct at h_av
          simp at h_av
          have : i ∈ Finset.univ := by simp
          have h_av₂ : ∀x₀, (fun x_1 => Finset.sum Finset.univ fun x_2 => a i (this : i ∈ Finset.univ) x_1 x_2 * x x_2) x₀ = v i := by apply congr_fun h_av
          let x₀ : Fin 1 := 1
          specialize h_av₂ x₀
          exact h_av₂

        exact h_map_to_generator

        have h_f_injective : ∀ (a : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) (ha : a ∈ S), ∀ (b : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) (hb : b ∈ S), f a ha = f b hb → a = b := by
          intro a b ha hb
          intro h_fab_eq
          funext y h_y
          apply congr_fun at h_fab_eq
          specialize h_fab_eq y
          simp[f] at h_fab_eq
          apply congr_fun at h_fab_eq
          funext 1 x_k
          specialize h_fab_eq x_k
          simp at h_fab_eq
          simp[h_fab_eq]

        exact h_f_injective

        have h_f_surjective : ∀ b ∈ filter (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ, ∃ a, ∃ (ha : a ∈ S), f a ha = b := by
          simp
          intro b h_eq
          let a₀ : ((a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) := fun a h_a => Matrix.of (fun i j => b a j)
          use a₀
          simp[f]
          constructor
          · simp[S]
            unfold Matrix.mulVec dotProduct
            intro a
            funext x_1
            simp[a₀]
            exact h_eq a
          · funext i j
            simp[a₀]

        exact h_f_surjective

      simp[S] at h3₂
      simp_rw[h3₀, h3₁]
      rw[← h3₂]
      simp

    -- Says that the number of row vectors g such that gx = v_i is equal to |α|^(k-1)
    have h4 : ∀i, (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun _ => v i) Finset.univ).card = (Fintype.card α)^(k-1) := by
      intro i

      unfold Matrix.mulVec dotProduct
      simp

      have h4₀ : (filter (fun g : Matrix (Fin 1) (Fin k) α => (fun x_1 => Finset.sum Finset.univ fun x_2 => g x_1 x_2 * x x_2) = fun x => v i) Finset.univ) =
      Set.toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum (Finset.univ : Finset (Fin k)) fun a => (g 0 a) * (x a)) = v i} := by
        ext x
        simp
        constructor
        · intro h_filter
          apply congr_fun at h_filter
          specialize h_filter 1
          exact h_filter
        · intro h_univ
          funext 1
          exact h_univ

      let c := v i
      let S := (toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum Finset.univ fun a => g 0 a * x a) = c})

      have h4₁ : S.card = (Fintype.card α)^(k-1) := by
        have h_nonzero_element : ∃ (j : Fin k), x j ≠ 0 := by
          by_contra h_zero
          push_neg at h_zero
          have h_x_eq_zero : x = zero := by ext l; exact h_zero l
          exact h_x h_x_eq_zero

        rcases h_nonzero_element with ⟨j, h_j⟩

        have h_rearrange : S = (toFinset {g : Matrix (Fin 1) (Fin k) α | (g 0 j) = (c - Finset.sum (Finset.univ.erase j) fun a => (g 0 a)*(x a)) / (x j)}) := by
          ext y
          simp
          constructor
          · intro h_sum
            simp[S] at h_sum
            rw[h_sum]
            simp
            field_simp[h_sum]
          · intro h_formula
            field_simp at h_formula
            rw[eq_sub_iff_add_eq] at h_formula
            simp[S]
            simp_all

        simp_rw[h_rearrange]
        let S₂ := (toFinset {g : Matrix (Fin 1) (Fin k) α | g 0 j = (v i - Finset.sum (erase Finset.univ j) fun a => g 0 a * x a) / x j})

        have h_g_bijection : S₂.card = (Finset.univ : Finset (Codeword (k-1) α)).card := by
          have h_k1 (l : Fin (k-1)) : ↑l < k := by
            have h_l2 : ↑l < k - 1 := l.2
            omega
          have h_k2 (l : Fin (k-1)) : ↑l + 1 < k := by
            have h_l2 : ↑l < k - 1 := l.2
            omega

          let f : (g : Matrix (Fin 1) (Fin k) α) → g ∈ S₂ → (Codeword (k-1) α) := fun g h_g => (fun (l : Fin (k-1)) => if h_llt : l.val < j then (g 0 ⟨l.val, by exact h_k1 l⟩) else (g 0 ⟨l.val + 1, by exact h_k2 l⟩))
          apply Finset.card_bij f

          simp_all

          have h_f_inj : ∀ (a : Matrix (Fin 1) (Fin k) α) (ha : a ∈ S₂), ∀ (b : Matrix (Fin 1) (Fin k) α) (hb : b ∈ S₂), f a ha = f b hb → a = b := by
            simp[S₂]
            intro a h_a b h_b h_l

            let φa := (fun (l : Fin (k-1)) => if (l : ℕ) < (j : ℕ) then a 0 { val := ↑l, isLt := h_k1 l } else a 0 { val := ↑l + 1, isLt := h_k2 l })
            let φb := (fun (l : Fin (k-1)) => if (l : ℕ) < (j : ℕ) then b 0 { val := ↑l, isLt := h_k1 l } else b 0 { val := ↑l + 1, isLt := h_k2 l })
            have hφ : φa = φb := by simp[φa, φb]; exact h_l

            ext i₁ iκ
            have h_i1 : i₁ = 0 := by fin_cases i₁; simp
            rw[h_i1]
            have h_cases : iκ.val < j.val ∨ iκ.val = j.val ∨ iκ.val > j.val := by
              exact Nat.lt_trichotomy iκ.val j.val

            have h_eq_if_lt (i₀ : Fin k) (h_lt : ↑i₀ < ↑j) : a 0 i₀ = b 0 i₀ := by
              have h_i₀val : i₀ < k-1 := by
                have h_j_le : ↑j ≤ k-1 := Nat.le_pred_of_lt j.2
                exact lt_of_lt_of_le h_lt h_j_le
              have h_φeq : φa ⟨↑i₀, by exact h_i₀val⟩ = φb ⟨↑i₀, by exact h_i₀val⟩ := by exact congrFun hφ ⟨↑i₀, by exact h_i₀val⟩
              have h_φa : φa ⟨↑i₀, by exact h_i₀val⟩ = a 0 ↑i₀ := by
                simp[φa]
                intro h_jleq
                have h_notjleq : ¬(j ≤ i₀) := Nat.not_le_of_gt h_lt
                contradiction
              have h_φb : φb ⟨↑i₀, by exact h_i₀val⟩ = b 0 ↑i₀ := by
                simp[φb]
                intro h_jleq
                have h_notjleq : ¬(j ≤ i₀) := Nat.not_le_of_gt h_lt
                contradiction
              rw[h_φa, h_φb] at h_φeq
              exact h_φeq

            have h_eq_if_gt (i₀ : Fin k) (h_gt : (i₀ : ℕ) > (j : ℕ)) : a 0 i₀ = b 0 i₀ := by
              have h_i₀val : i₀ - 1 < k - 1 := by
                have h_i₀_lt_k : ↑i₀ < k := i₀.2
                have h_i₀_gt_j : ↑i₀ > ↑j := h_gt
                omega

              have h_φeq : φa ⟨↑i₀ - 1, by exact h_i₀val⟩ = φb ⟨↑i₀ - 1, by exact h_i₀val⟩ := by exact congrFun hφ ⟨↑i₀ - 1, by exact h_i₀val⟩
              have h_φa : φa ⟨↑i₀ - 1, by exact h_i₀val⟩ = a 0 ↑i₀ := by
                simp[φa]
                rw[if_neg]
                have h_i₀_pos : (i₀ : ℕ) > 0 := by exact Nat.lt_of_le_of_lt (Nat.zero_le j) h_gt
                have h_i₀_ge_one : 1 ≤ (i₀ : ℕ) := by
                  rw [Nat.one_le_iff_ne_zero]
                  intro h_zero
                  exact Nat.ne_of_gt h_i₀_pos h_zero
                have h_simplify : (i₀ : ℕ) - 1 + 1 = ↑i₀ := by exact Nat.sub_add_cancel h_i₀_ge_one
                simp_rw[h_simplify]
                omega
              have h_φb : φb ⟨↑i₀ - 1, by exact h_i₀val⟩ = b 0 ↑i₀ := by
                simp[φb]
                rw[if_neg]
                have h_i₀_pos : (i₀ : ℕ) > 0 := by exact Nat.lt_of_le_of_lt (Nat.zero_le j) h_gt
                have h_i₀_ge_one : 1 ≤ (i₀ : ℕ) := by
                  rw [Nat.one_le_iff_ne_zero]
                  intro h_zero
                  exact Nat.ne_of_gt h_i₀_pos h_zero
                have h_simplify : (i₀ : ℕ) - 1 + 1 = ↑i₀ := by exact Nat.sub_add_cancel h_i₀_ge_one
                simp_rw[h_simplify]
                omega
              rw[h_φa, h_φb] at h_φeq
              exact h_φeq


            rcases h_cases with (h_lt | h_eq | h_gt)
            · exact h_eq_if_lt iκ h_lt
            · have h_fineq : iκ = j := by exact Fin.eq_of_val_eq h_eq
              rw[h_fineq, h_a, h_b]
              field_simp

              have h_a_sum_split : (Finset.sum (Finset.univ : Finset (Fin k)) fun a_1 => a 0 a_1 * x a_1) =
              (Finset.sum (Finset.filter (fun i => i < j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) + (Finset.sum (Finset.filter (fun i => i > j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) + a 0 j * x j := by
                simp_rw[←Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k)) (fun i => i = j) (fun a_1 => a 0 a_1 * x a_1)]

                have h_eq_j : Finset.filter (fun i => i = j) (Finset.univ : Finset (Fin k)) = {j} := by ext i; simp

                have h_neq_split : Finset.filter (fun i => i ≠ j) (Finset.univ : Finset (Fin k)) = Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k)) ∪ Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k)) := by ext i; simp

                have h_disjoint : Disjoint (Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k))) (Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k))) := by
                  apply Finset.disjoint_filter.mpr
                  intro i h1 h2
                  exact lt_asymm h2

                rw[h_eq_j, Finset.sum_singleton, h_neq_split, Finset.sum_union h_disjoint]
                ring

              have h_b_sum_split : (Finset.sum Finset.univ fun a_1 => b 0 a_1 * x a_1) =
              (Finset.sum (Finset.filter (fun i => i < j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) + (Finset.sum (Finset.filter (fun i => i > j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) + b 0 j * x j := by
                simp_rw[←Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k)) (fun i => i = j) (fun a_1 => b 0 a_1 * x a_1)]

                have h_eq_j : Finset.filter (fun i => i = j) (Finset.univ : Finset (Fin k)) = {j} := by ext i; simp

                have h_neq_split : Finset.filter (fun i => i ≠ j) (Finset.univ : Finset (Fin k)) = Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k)) ∪ Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k)) := by ext i; simp

                have h_disjoint : Disjoint (Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k))) (Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k))) := by
                  apply Finset.disjoint_filter.mpr
                  intro i h1 h2
                  exact lt_asymm h2

                rw[h_eq_j, Finset.sum_singleton, h_neq_split, Finset.sum_union h_disjoint]
                ring

              rw[h_a_sum_split, h_b_sum_split]

              have h_lt_sum_eq : (Finset.sum (filter (fun i => i < j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) = (Finset.sum (filter (fun i => i < j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp at hi
                have h_eq : a 0 i = b 0 i := by exact h_eq_if_lt i hi
                rw[h_eq]

              have h_gt_sum_eq : (Finset.sum (filter (fun i => i > j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) = (Finset.sum (filter (fun i => i > j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp at hi
                have h_eq : a 0 i = b 0 i := by exact h_eq_if_gt i hi
                rw[h_eq]

              simp_rw[h_lt_sum_eq, h_gt_sum_eq]
              ring

            · exact h_eq_if_gt iκ h_gt

          exact h_f_inj

          have h_f_surj : ∀ b ∈ Finset.univ, ∃ a, ∃ (ha : a ∈ S₂), f a ha = b := by
            intro b h_b

            have h_l1 (l : Fin k) (h_lj : ↑l < j) : ↑l < k - 1 := by
              have h_jk : ↑j < k := j.is_lt
              exact Nat.lt_of_lt_of_le h_lj (Nat.le_pred_of_lt h_jk)

            have h_l2 (l : Fin k) (h_lj : ¬(↑l < j)) (h_lj' : ¬(↑l = j)) : ↑l - 1 < k - 1 := by
              have h_lk : l < k := l.is_lt

              have h_cases : k < 1 ∨ k = 1 ∨ k > 1 := by exact Nat.lt_trichotomy k 1

              rcases h_cases with (h_klt | h_keq | h_kgt)
              · omega
              · have h_l0 : l = ⟨0, by exact Nat.lt_of_succ_le h_k⟩ := by
                  apply Fin.ext
                  have h_l_lt_1 : l.val < 1 := by
                    simp
                    subst h_keq
                    interval_cases (l : ℕ)
                    rfl
                  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_l_lt_1)
                have h_j0 : j = ⟨0, by exact Nat.lt_of_succ_le h_k⟩ := by
                  apply Fin.ext
                  have h_j_lt_1 : j.val < 1 := by subst h_keq; exact j.isLt
                  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_j_lt_1)
                push_neg at h_lj'
                rw[h_l0, h_j0] at h_lj'
                contradiction
              · have h_l_geq_1 : 1 ≤ (l : ℕ) := by
                  have h_j_geq_0 : (j : Nat) ≥ 0 := Nat.zero_le _
                  have h_l_gt_j : (j : ℕ) < (l : ℕ) := by
                    contrapose! h_lj'
                    have h_j_leq_l : (j : ℕ) ≤ (l : ℕ) := Nat.le_of_not_lt h_lj
                    exact Fin.ext (Nat.le_antisymm h_lj' h_j_leq_l)
                  have h_l_gt_0 : (0 : Nat) < (l : Nat) := Nat.lt_of_le_of_lt h_j_geq_0 h_l_gt_j
                  exact Nat.succ_le_of_lt h_l_gt_0
                omega


            let p₀ : (Matrix (Fin 1) (Fin k) α) := fun _ l => if h_lj : l < j then b ⟨l.val, by exact h_l1 l h_lj⟩ else (if h_lj' : l = j then 0 else b ⟨l.val - 1, by exact h_l2 l h_lj h_lj'⟩)
            let p : (Matrix (Fin 1) (Fin k) α) := fun _ l => if l ≠ j then (p₀ 0 l) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)
            use p

            have h_p : p ∈ S₂ := by
              let inS₂ (g : Matrix (Fin 1) (Fin k) α) : Prop := g 0 j = (v i - Finset.sum (erase Finset.univ j) fun c => g 0 c * x c) / x j
              have hS₂_mem : S₂ = toFinset {g | inS₂ g} := by simp[S₂, inS₂]
              rw[hS₂_mem, ←Finset.mem_coe]
              have h_finseteq : ↑(toFinset {g | inS₂ g}) = {g | inS₂ g} := by simp
              rw[h_finseteq, Set.mem_setOf_eq]
              simp only [inS₂, p]
              simp only [ne_eq, not_true, ↓reduceIte]
              congr 1
              congr 1
              apply Finset.sum_congr rfl
              intro c hc
              have hcj : c ≠ j := Finset.ne_of_mem_erase hc
              simp [hcj]

            use h_p
            funext l
            change (fun g h_g => (fun (l : Fin (k-1)) => if h_llt : l.val < j then (g 0 ⟨l.val, by exact h_k1 l⟩) else (g 0 ⟨l.val + 1, by exact h_k2 l⟩))) p h_p l = b l
            change (if h_llt : (l : ℕ) < (j : ℕ) then p 0 ⟨l.val, by exact h_k1 l⟩ else p 0 ⟨l.val + 1, by exact h_k2 l⟩) = b l

            split_ifs with h_if
            · let l_cast : (Fin k) := { val := ↑l, isLt := h_k1 l }
              change (fun _ l => if l ≠ j then (p₀ 0 l) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)) 0 l_cast = b l
              change (if l_cast ≠ j then (p₀ 0 l_cast) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)) = b l
              have h_l_neq_j : l_cast ≠ j := by
                have h_l_cast_lt : (l_cast : ℕ) < (j : ℕ) := by simp[l_cast, h_if]
                have h_l_cast_ne : (l_cast : ℕ) ≠ (j : ℕ) := by exact ne_of_lt h_l_cast_lt
                rw [Fin.val_ne_iff] at h_l_cast_ne
                exact h_l_cast_ne
              rw [if_pos h_l_neq_j]
              simp[p₀, l_cast]
              intro h_j_leq
              have h_jl_nat : (j : ℕ) ≤ (l : ℕ) := by
                rw[Fin.le_iff_val_le_val] at h_j_leq
                have h_l_val : (l : ℕ) = (({ val := ↑l, isLt := h_k1 l } : (Fin k)) : ℕ) := by simp
                rw[h_l_val]
                exact h_j_leq
              omega
            · simp[p, p₀]
              split_ifs with h_if₂ h_if₃
              · simp[Fin.ext_iff] at h_if₂
                omega
              · push_neg at h_if
                have h_lj : (↑l + 1 : ℕ) < (↑j : ℕ) :=h_if₃
                omega
              · rfl


          exact h_f_surj

        rw[h_g_bijection]

        have h_codeword_card : (Finset.univ : Finset (Codeword (k-1) α)).card = (Fintype.card α)^(k-1) := by
          rw[Finset.card_univ]
          unfold Codeword
          rw[Fintype.card_fun]
          simp

        rw[h_codeword_card]



      rw[h4₀, h4₁]

    simp_rw[h2, h3, h4]
    simp[←pow_mul, mul_comm]



  norm_cast
  rw[h, ←pow_add]
  congr
  calc
    n * (k - 1) + n = n * (k - 1) + n * 1 := by rw [Nat.mul_one]
    _               = n * ((k - 1) + 1)   := by rw [←Nat.mul_add]
    _               = n * k               := by rw[Nat.sub_add_cancel h_k]
}

end Codeword
end CodingTheory
