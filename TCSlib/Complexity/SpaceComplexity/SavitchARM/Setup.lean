/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The setup and the outer search of the Savitch register machine

The non-recursive parts of `Complexity.LogProg.SavitchARM.A`. The setup (`setup_run`)
measures the input, computes the radius `s = (|x| + 2) ^ E`, the width
`w = (|x| + 2) ^ (2E)` and the code bound `K = 2 ^ w` by counting loops, leaving every other
register clear. The outer search (`outerU_run`, `outerV_run`) runs through the candidate
initial codes `U < K` and accepting codes `V < K` and evaluates the midpoint recursion at the
root level `w` for each candidate pair (`Complexity.LogProg.SavitchARM.call_spec`).

Infrastructure for [AB09, §4.2.1, proof of Theorem 4.14]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.SavitchARM.outerSt` — the register files of the outer search.

## Main results

* `Complexity.LogProg.SavitchARM.setup_run` — the setup.
* `Complexity.LogProg.SavitchARM.outerU_run` — the outer search answers whether an initial
  and an accepting code are joined by midpoint reachability at level `w`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-! ## The setup -/

/-- Close a bound on a named register file, reducing its projections first. -/
scoped macro "sbd" : tactic =>
  `(tactic| ((try simp only [St.Bd, St.zero]) <;> (try dsimp only) <;>
    (try simp only [one_mul, zero_add, if_true, ↓reduceIte]) <;> omega))

/-- **Loading the constant `E`**: from `ld j` with `X = j`, the machine counts `X` up to `E`,
then sets `P := P + 1` and reaches `pw`.

**Proof sketch.** Induction on `E - j`. -/
theorem ld_run : ∀ (k j : ℕ) (hj : j < E + 1) (st : St), j + k = E → st.X = j → st.Bd B →
    E ≤ B → st.P + 1 ≤ B →
    AReach (A E) orc x (GuardLe (A E) x B) (some (.ld ⟨j, hj⟩), st.toV, none)
      (some .pw, St.toV { st with X := E, P := st.P + 1 }, none) := by
  intro k
  induction k with
  | zero =>
    intro j hj st hk hX hbd hE hP
    refine step_of hbd ?_
    regs [astep, A, dif_neg (show ¬ j < E by omega)]
    refine reach_of_eq (AReach.refl _) ?_
    congr 3
    ext <;> simp; omega
  | succ k ih =>
    intro j hj st hk hX hbd hE hP
    refine step_of hbd ?_
    regs [astep, A, dif_pos (show j < E by omega)]
    have hbd1 : St.Bd B { st with X := st.X + 1 } := by simp only [St.Bd] at hbd ⊢; omega
    refine reach_of_eq (ih (j + 1) (by omega) _ (by omega) (by simp [hX]) hbd1 hE hP) ?_
    rfl

/-- **The power loop**: from `pw` with `X = j` and `C = T = Z = 0`, the machine multiplies
`P` by `a ^ j`, clears `X`, and reaches `cp sP`.

**Proof sketch.** Induction on `j`: each round decrements `X` and multiplies `P` by `a`
(`mul_run`). -/
theorem pw_run : ∀ (j : ℕ) (st : St), st.X = j → st.C = 0 → st.T = 0 → st.Z = 0 → st.Bd B →
    1 ≤ st.a → st.P * st.a ^ j ≤ B →
    AReach (A E) orc x (GuardLe (A E) x B) (some .pw, st.toV, none)
      (some (.cp .sP 0), St.toV { st with X := 0, P := st.P * st.a ^ j }, none) := by
  intro j
  induction j with
  | zero =>
    intro st hX hC hT hZ hbd ha hb
    refine step_of hbd ?_
    regs [astep, A, hX, if_true]
    refine reach_of_eq (AReach.refl _) ?_
    congr 3
    ext <;> simp [hX]
  | succ j ih =>
    intro st hX hC hT hZ hbd ha hb
    have h1 : st.P ≤ st.P * st.a ^ (j + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have h2 : st.P * st.a ≤ st.P * st.a ^ (j + 1) := by
      apply Nat.mul_le_mul_left
      calc st.a = st.a ^ 1 := (pow_one _).symm
        _ ≤ st.a ^ (j + 1) := Nat.pow_le_pow_right ha (by omega)
    refine step_of hbd ?_
    regs [astep, A, hX, Nat.add_one_ne_zero, if_false]
    refine step_of hbd ?_
    regs [astep, A, hX, Nat.add_sub_cancel]
    have hbd1 : St.Bd B { st with X := j } := by simp only [St.Bd] at hbd ⊢; omega
    refine (mul_run false { st with X := j } hC hT hZ hbd1 (by simp; omega)).trans ?_
    simp only [mvExit, Bool.false_eq_true, if_false]
    have hbd2 : St.Bd B { st with X := j, P := st.P * st.a } := by
      simp only [St.Bd] at hbd ⊢; omega
    refine reach_of_eq (ih _ rfl hC hT hZ hbd2 ha (by
      show st.P * st.a * st.a ^ j ≤ B
      rw [mul_assoc, ← pow_succ']; exact hb)) ?_
    congr 3
    ext <;> simp [pow_succ']
    ring

/-- **The register file after the setup**: radius `s`, width `w`, code bound `2 ^ w`, every
other register clear. -/
def setSt (s w : ℕ) : St := { St.zero with s := s, w := w, K := 2 ^ w }

/-- **The setup** [AB09, §4.2.1: the radius and the vertex-code width are computed first]:
from `scan` with all registers clear, the machine reaches `OU` with radius
`s = (|x| + 2) ^ E`, width `w = (|x| + 2) ^ (2E)` and code bound `2 ^ w`, everything else
clear, through register values at most `B ≥ 2 ^ w`.

**Proof sketch.** Count `n = |x|` (`Complexity.LogProg.inputLength_loop`, asking decider `0`),
move it into `a` and add two, load `X = E` and `P = 1` (`ld_run`), take `P := a ^ E`
(`pw_run`), copy it into `s`, square `P` (`mul_run`), move it into `w`, clear `a`, and shift
`K = 1` left by `w` (`sh_run`). -/
theorem setup_run (hE : 1 ≤ E)
    (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length))
    (hB : 2 ^ ((x.length + 2) ^ (2 * E)) ≤ B) :
    AReach (A E) orc x (GuardLe (A E) x B) (some .scan, St.zero.toV, none)
      (some .OU, (setSt ((x.length + 2) ^ E) ((x.length + 2) ^ (2 * E))).toV, none) := by
  have hw1 : (x.length + 2) ^ (2 * E) < 2 ^ ((x.length + 2) ^ (2 * E)) := Nat.lt_two_pow_self
  have haE : x.length + 2 ≤ (x.length + 2) ^ E := by
    calc x.length + 2 = (x.length + 2) ^ 1 := (pow_one _).symm
      _ ≤ (x.length + 2) ^ E := Nat.pow_le_pow_right (by omega) hE
  have hEw : (x.length + 2) ^ E ≤ (x.length + 2) ^ (2 * E) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsq : (x.length + 2) ^ E * (x.length + 2) ^ E = (x.length + 2) ^ (2 * E) := by
    rw [← pow_add]; ring_nf
  have hEa : E < (x.length + 2) ^ E :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by omega) _)
  -- count `n = |x|`
  have h1 := inputLength_loop (A E) orc x rn 0 .scan .incN (.mv .aN 0) rfl rfl hq B
    (by omega) St.zero.toV (fun r => by fin_cases r <;> simp [St.toV, St.zero])
    (by simp [St.zero])
  refine (h1.mono fun _ h => h).trans ?_
  regs [St.zero]
  refine (mv_run .aN _ (by sbd) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by sbd) ?_
  regs [astep, A]
  refine step_of (by sbd) ?_
  regs [astep, A]
  refine cont (st' := { St.zero with a := x.length + 2 }) (by ext <;> simp [St.zero]) ?_
  -- load `X = E`, `P = 1`
  refine (ld_run E 0 (by omega) _ (by omega) rfl (by sbd) (by omega) (by sbd)).trans ?_
  -- `P := a ^ E`
  refine (pw_run E _ rfl rfl rfl rfl (by sbd) (by sbd) (by sbd)).trans ?_
  -- `s := P`, `P := P · P`, `w := P`
  refine (cp_run .sP _ (by sbd) rfl (by regs [cpDst, cpSrc]; sbd)).trans ?_
  regs [cpDst, cpSrc, cpExit, zero_add, one_mul]
  refine (mul_run true _ rfl rfl rfl (by sbd) (by sbd)).trans ?_
  simp only [mvExit, if_true]
  refine (mv_run .wP _ (by sbd) (by regs [mvDst, mvSrc]; sbd)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by sbd) ?_
  regs [astep, A]
  refine step_of (by sbd) ?_
  regs [astep, A, zero_add]
  -- `K := 2 ^ w`
  refine (cp_run .kW _ (by sbd) rfl (by regs [cpDst, cpSrc]; sbd)).trans ?_
  regs [cpDst, cpSrc, cpExit, zero_add]
  refine reach_of_eq (sh_run .kK _ (by sbd) rfl
    (by regs [shReg]; simp only [St.zero, zero_add, one_mul, hsq]; omega)) ?_
  regs [shReg, shExit]
  congr 3
  ext <;> simp [setSt, St.zero, hsq]

end SavitchARM

end Complexity.LogProg
