import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.MvPolynomial.Degrees
import TCSlib.BooleanAnalysis.Circuit

/-
Theorem 1 from paper: For sufficiently large n, any depth-d circuit
that computes parity on n-bits must have at least 1/50 * 2^{0.5 * n^{1/2d}} gates.

-/
theorem parity_notin_ac0 (d : ℕ) (hd : d > 0) :
  ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (C : Circuit n),
    C.depth ≤ d →
    (∀ x : Vector Bool n, C.eval x = parity x) →
    (C.size : ℝ) ≥ (1 / 50 : ℝ) * 2^((0.5 : ℝ) * (n : ℝ)^(1 / (2 * (d : ℝ)))) :=
by
  sorry

-- We need to associate a poly with each circuit.

-- type conversion helper
def boolToZMod3 : Bool → ZMod 3
  | false => 0
  | true  => 1

-- evaluates polynomial on bool vector
noncomputable def evalPolyOnBool {n : ℕ} (P : MvPolynomial (Fin n) (ZMod 3)) (v : Vector Bool n) : ZMod 3 :=
  MvPolynomial.eval (fun i => boolToZMod3 (v.get i)) P

-- output needs to be in {0, 1}
def IsProper {n : ℕ} (P : MvPolynomial (Fin n) (ZMod 3)) : Prop :=
  -- note functions instead of vectors as input
  ∀ x : Fin n → Bool,
    let v := Vector.ofFn x
    evalPolyOnBool P v = 0 ∨ evalPolyOnBool P v = 1

-- counts difference in inputs between circuit and polynomial
noncomputable def numDiffCircuit {n : ℕ} (C : Circuit n) (P : MvPolynomial (Fin n) (ZMod 3)) : ℕ :=
  (Finset.univ.filter (fun (x : Fin n → Bool) =>
    let v := Vector.ofFn x
    boolToZMod3 (C.eval v) ≠ evalPolyOnBool P v)).card

-- counts difference in inputs betwen parity and polynomial
noncomputable def numDiffParity {n : ℕ} (P : MvPolynomial (Fin n) (ZMod 3)) : ℕ :=
  (Finset.univ.filter (fun (x : Fin n → Bool) =>
    let v := Vector.ofFn x
    boolToZMod3 (parity v) ≠ evalPolyOnBool P v)).card


/-
Lemma 2: for every integer t > 0, there exists a (proper) polynomial
of total degree (2t)^d that differs with C on at most size(C) * 2^(n-t) inputs.
-/
theorem lemma_2 (n t : ℕ) (ht : t > 0) (C : Circuit n) :
  ∃ P : MvPolynomial (Fin n) (ZMod 3),
    IsProper P ∧
    P.totalDegree ≤ (2 * t)^(C.depth) ∧
    (numDiffCircuit C P : ℝ) ≤ (C.size : ℝ) * 2^((n : ℝ) - (t : ℝ)) :=
by
  sorry

/-
Lemma 3: let p ∈ F_3[x_1, …, x_n] be a proper polynomial of degree at most √n:
then for sufficiently large n the polynomial p differs from the parity function
on at least 2^n/50 inputs
-/
theorem lemma_3 :
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (P : MvPolynomial (Fin n) (ZMod 3)),
    IsProper P →
    (P.totalDegree : ℝ) ≤ Real.sqrt (n : ℝ) →
    (numDiffParity P : ℝ) ≥ (2^n : ℝ) / 50 :=
by
  sorry
