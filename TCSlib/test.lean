import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Vector.Basic


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
-- variable (F : GaloisField 2 n)
local notation "q" => Fintype.card F


variable {n : ℕ} {α w : Vector F n}


variable (k e: ℕ)


def apply_polynomial_to_vector {n : ℕ} (p : Polynomial F) (v : Vector F n) : Vector F n :=
  v.map (fun x => p.eval x)

def vector_add {n : ℕ} (u v : Vector F n) : Vector F n :=
  (Vector.zipWith fun x y => x + y) u v

def vector_sub{n : ℕ} (u v : Vector F n) : Vector F n :=
  (Vector.zipWith fun x y => x - y) u v

def weight (v : Vector F n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => v.get i ≠ 0).card

def weight₂ (f : Polynomial F) : ℕ :=
  weight (apply_polynomial_to_vector f α)


def hamming_dist (v1 v2 : Vector F n) : ℕ :=
  weight (vector_sub v1 v2)


-- noncomputable def hamming_dist_poly (f g : Polynomial F) : ℕ :=
--   weight (apply_polynomial_to_vector (f - g) α)


theorem existence {h_n_ge_k : n ≥ k} {h_q_ge_n : q ≥ n} {h_k_ge_one : 1 ≤ k} (h_exist_f : ∃f : Polynomial F, f.degree ≤ ↑(k-1) ∧ hamming_dist (apply_polynomial_to_vector f α) w ≤ e)
: ∃ E Q : Polynomial F, (Polynomial.Monic E) ∧ (Q.degree ≤ ↑(e+k-1)) ∧ (∀ i : Fin n, w.get i * E.eval (α.get i) = Q.eval (α.get i)) :=

-- let f be a polynomial of degree less than k such that the hamming distance between f(α) and w is less than or equal to e
  Exists.elim h_exist_f (fun f (hf : f.degree ≤ ↑(k-1) ∧ hamming_dist (apply_polynomial_to_vector f α) w ≤ e) =>
-- S is the set of indices where apply_polynomial_to_vector f α does not match w
  let S : Finset (Fin n) := (Finset.univ.filter fun i : Fin n => (apply_polynomial_to_vector f α).get i ≠ w.get i)
  let E : Polynomial F := S.prod (fun i => Polynomial.X - Polynomial.C (α.get i)) * Polynomial.X^(e - hamming_dist (apply_polynomial_to_vector f α) w)
  let Q : Polynomial F := E * f

  have card_S_eq_hamming_dist : S.card = hamming_dist (apply_polynomial_to_vector f α) w := by
    simp [hamming_dist, weight, apply_polynomial_to_vector, vector_sub, sub_ne_zero]
    sorry

-- show that E is monic
  have h_E_monic : Polynomial.Monic E := by
    /- simp_rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_pow, Polynomial.leadingCoeff_prod, Polynomial.leadingCoeff_X_sub_C]
    rw [Finset.prod_eq_one, one_mul]
    simp -/
    sorry

-- show that Q has degree less than e+k
  have h_Q_degree : Q.degree ≤ ↑(e+k-1) := by
    /- simp_rw [Polynomial.degree_mul, Polynomial.degree_prod, Polynomial.degree_X_sub_C, Polynomial.degree_X_pow]
    simp [card_S_eq_hamming_dist]
    rw [← Nat.cast_add, ←Nat.add_sub_assoc]

    have h_inequality : ↑(hamming_dist (apply_polynomial_to_vector f α) w + e - hamming_dist (apply_polynomial_to_vector f α) w) +
      Polynomial.degree f ≤ ↑(e + k - 1) :=
      calc
      _ = ↑(hamming_dist (apply_polynomial_to_vector f α) w - hamming_dist (apply_polynomial_to_vector f α) w + e) + Polynomial.degree f := by simp
      _ = ↑e + Polynomial.degree f := by simp
      _ ≤ ↑e + ↑(k -1) := by rel[hf.1]
      _ = ↑(e + k - 1) := by rw [←Nat.cast_add, Nat.add_sub_assoc]; exact h_k_ge_one

    exact h_inequality
    exact hf.2-/
    sorry

  have h_Q_eval : ∀ i : Fin n, w.get i * E.eval (α.get i) = Q.eval (α.get i) := by
    intro i
    by_cases h_equal : w.get i = (apply_polynomial_to_vector f α).get i
    have h_pos : w.get i * E.eval (α.get i) = Q.eval (α.get i) := calc
      _ = (apply_polynomial_to_vector f α).get i * Polynomial.eval (Vector.get α i) E := by simp [h_equal]
      _ = Polynomial.eval (Vector.get α i) f * Polynomial.eval (Vector.get α i) E := by sorry -- simp [apply_polynomial_to_vector]
      _ = Polynomial.eval (Vector.get α i) (f * E) := by simp [Polynomial.eval_mul]
      _ = Polynomial.eval (Vector.get α i) Q := by simp; sorry --ring

    exact h_pos
    have h_E_eq_0 : E.eval (α.get i) = 0 := by
      sorry
      /- simp [apply_polynomial_to_vector, h_equal, vector_sub]
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
      have h_apply : (apply_polynomial_to_vector f α).get i = Polynomial.eval (Vector.get α i) f := by
        simp [apply_polynomial_to_vector, Polynomial.eval_mul]
      have h_i_1 : i ∈ Finset.filter (fun i => ¬Polynomial.eval (Vector.get α i) f = Vector.get w i) Finset.univ := by
        simp
        rw [←h_apply]
        intro h_6
        have h_7 : w.get i = (apply_polynomial_to_vector f α).get i := by simp[h_6]
        exact h_equal h_7

      have h_i_2 : Polynomial.eval (Vector.get α i) (Polynomial.X - Polynomial.C (Vector.get α i)) = 0 := by
        simp
      left
      use i-/
    -- unfold_let Q
    rw [h_E_eq_0]
    rw [Polynomial.eval_mul, h_E_eq_0, zero_mul, mul_zero]
  ⟨E, Q, ⟨h_E_monic, h_Q_degree, h_Q_eval⟩⟩
)
