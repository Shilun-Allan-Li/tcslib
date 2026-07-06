/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.Subprotocol
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Balanced Simulation of Deterministic Protocols

## Main results

- `Deterministic.Protocol.exists_balanced_simulation`: Any deterministic protocol can be simulated by another satisfying `3^c ≤ 2^c * (numLeaves)^2`

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

private lemma numLeaves_pos (p : Protocol X Y α) : 0 < p.numLeaves := by
  cases p with
  | output a =>
    simp [numLeaves, shape]
  | alice f P =>
    have h : 0 < (P false).numLeaves := numLeaves_pos (P false)
    have hsum : 0 < (P false).numLeaves + (P true).numLeaves := Nat.add_pos_left h _
    simpa [numLeaves, shape] using hsum
  | bob f P =>
    have h : 0 < (P false).numLeaves := numLeaves_pos (P false)
    have hsum : 0 < (P false).numLeaves + (P true).numLeaves := Nat.add_pos_left h _
    simpa [numLeaves, shape] using hsum

private lemma complexity_eq_zero_of_numLeaves_eq_one
    (p : Protocol X Y α) (hleaf : p.numLeaves = 1) :
    p.complexity = 0 := by
  cases p with
  | output a =>
      rfl
  | alice f P =>
      exfalso
      have hs : (P false).shape.numLeaves + (P true).shape.numLeaves = 1 := by
        simpa [numLeaves, shape] using hleaf
      have hp0 : 0 < (P false).shape.numLeaves := by
        simpa [numLeaves] using numLeaves_pos (P false)
      have hp1 : 0 < (P true).shape.numLeaves := by
        simpa [numLeaves] using numLeaves_pos (P true)
      omega
  | bob f P =>
      exfalso
      have hs : (P false).shape.numLeaves + (P true).shape.numLeaves = 1 := by
        simpa [numLeaves, shape] using hleaf
      have hp0 : 0 < (P false).shape.numLeaves := by
        simpa [numLeaves] using numLeaves_pos (P false)
      have hp1 : 0 < (P true).shape.numLeaves := by
        simpa [numLeaves] using numLeaves_pos (P true)
      omega

private lemma max_sq_le_of_balanced
    (m n : ℕ)
    (hm : 3 * m ≤ 2 * n)
    (hout : 3 * (n - m) ≤ 2 * n) :
    9 * max (m ^ 2) ((n - m) ^ 2) ≤ 4 * n ^ 2 := by
  have hmSq : 9 * m ^ 2 ≤ 4 * n ^ 2 := by
    have hpow : (3 * m) * (3 * m) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul hm hm
    nlinarith [sq_nonneg m, sq_nonneg n]
  have houtSq : 9 * (n - m) ^ 2 ≤ 4 * n ^ 2 := by
    have hpow : (3 * (n - m)) * (3 * (n - m)) ≤ (2 * n) * (2 * n) :=
      Nat.mul_le_mul hout hout
    nlinarith [sq_nonneg (n - m), sq_nonneg n]
  by_cases hcase : m ^ 2 ≤ (n - m) ^ 2
  · rw [max_eq_right hcase]
    exact houtSq
  · rw [max_eq_left (le_of_not_ge hcase)]
    exact hmSq

/-- Every deterministic protocol can be simulated by another protocol with the same behavior and
complexity obeying
`3^c ≤ 2^c * (#leaves)^2`. -/
theorem exists_balanced_simulation (p : Protocol X Y α) :
    ∃ q : Protocol X Y α, q.run = p.run ∧
      3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2 := by
  let target : ℕ → Prop := fun n =>
    ∀ p : Protocol X Y α, p.numLeaves = n →
      ∃ q : Protocol X Y α, q.run = p.run ∧
        3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2
  have htarget : ∀ n, target n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih p hpn
    by_cases hn1 : n = 1
    · refine ⟨p, rfl, ?_⟩
      have hleaf1 : p.numLeaves = 1 := by simpa [hn1] using hpn
      have hcomp0 : p.complexity = 0 :=
        complexity_eq_zero_of_numLeaves_eq_one p hleaf1
      subst hn1
      simp [hcomp0, hpn]
    · have hgt1 : 1 < n := by
        have hnpos : 0 < n := by
          have hp : 0 < p.numLeaves := numLeaves_pos p
          simpa [hpn] using hp
        omega
      have hgt1p : 1 < p.numLeaves := by simpa [hpn] using hgt1
      obtain ⟨s, hsp, hbal_lo, hbal_hi⟩ := balanced_subprotocol p hgt1p
      let m := s.numLeaves
      have hm_lt_p : m < p.numLeaves := by
        dsimp [m]
        omega
      have hm_lt_n : m < n := by
        simpa [hpn, m] using hm_lt_p
      have hm_pos : 0 < m := by
        dsimp [m]
        exact numLeaves_pos s
      have hm_le_n : m ≤ n := hm_lt_n.le
      have hout_lt_n : n - m < n := by
        omega
      obtain ⟨qIn, hRunIn, hBoundIn⟩ := ih m hm_lt_n s rfl
      let pOut := prune hsp hm_lt_p
      have hpOut_leaves : pOut.numLeaves = n - m := by
        dsimp [pOut, m]
        simpa [hpn] using prune_numLeaves_of_lt hsp hm_lt_p
      obtain ⟨qOut, hRunOut, hBoundOut⟩ := ih (n - m) hout_lt_n pOut hpOut_leaves
      let q := testSubprotocol hsp qIn qOut
      refine ⟨q, ?_, ?_⟩
      · ext x y
        by_cases hxy : reaches hsp x y
        · calc
            q.run x y = qIn.run x y := by
              simpa [q] using testSubprotocol_run_inside hsp hxy
            _ = s.run x y := by
              simp [hRunIn]
            _ = p.run x y := by
              symm
              exact subprotocol_run_eq_of_reaches hsp hxy
        · calc
            q.run x y = qOut.run x y := by
              simpa [q] using testSubprotocol_run_outside hsp hxy
            _ = pOut.run x y := by
              simp [hRunOut]
            _ = p.run x y := by
              dsimp [pOut]
              exact prune_run_outside_of_lt hsp hm_lt_p hxy
      · have hInBound' : 3 ^ qIn.complexity ≤ 2 ^ qIn.complexity * m ^ 2 := by
          simpa [m] using hBoundIn
        have hOutBound' : 3 ^ qOut.complexity ≤ 2 ^ qOut.complexity * (n - m) ^ 2 := by
          simpa [hpOut_leaves] using hBoundOut
        have hmaxBound :
            3 ^ max qIn.complexity qOut.complexity ≤
              2 ^ max qIn.complexity qOut.complexity * max (m ^ 2) ((n - m) ^ 2) := by
          by_cases hcmp : qIn.complexity ≤ qOut.complexity
          · have hmax : max qIn.complexity qOut.complexity = qOut.complexity := max_eq_right hcmp
            rw [hmax]
            calc
              3 ^ qOut.complexity ≤ 2 ^ qOut.complexity * (n - m) ^ 2 := hOutBound'
              _ ≤ 2 ^ qOut.complexity * max (m ^ 2) ((n - m) ^ 2) :=
                    Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
          · have hcmp' : qOut.complexity ≤ qIn.complexity := le_of_not_ge hcmp
            have hmax : max qIn.complexity qOut.complexity = qIn.complexity := max_eq_left hcmp'
            rw [hmax]
            calc
              3 ^ qIn.complexity ≤ 2 ^ qIn.complexity * m ^ 2 := hInBound'
              _ ≤ 2 ^ qIn.complexity * max (m ^ 2) ((n - m) ^ 2) :=
                    Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
        have hm2 : 3 * m ≤ 2 * n := by
          omega
        have hout2 : 3 * (n - m) ≤ 2 * n := by
          omega
        have hmaxSq : 9 * max (m ^ 2) ((n - m) ^ 2) ≤ 4 * n ^ 2 := by
          exact max_sq_le_of_balanced m n hm2 hout2
        have hqComp : q.complexity = 2 + max qIn.complexity qOut.complexity := by
          dsimp [q]
          exact testSubprotocol_complexity hsp qIn qOut
        rw [hqComp]
        have hstep1 :
            3 ^ (2 + max qIn.complexity qOut.complexity) =
              9 * 3 ^ max qIn.complexity qOut.complexity := by
          simp [pow_add]
        have hstep2 :
            2 ^ (2 + max qIn.complexity qOut.complexity) =
              4 * 2 ^ max qIn.complexity qOut.complexity := by
          simp [pow_add]
        rw [hstep1, hstep2]
        calc
          9 * 3 ^ max qIn.complexity qOut.complexity
              ≤ 9 * (2 ^ max qIn.complexity qOut.complexity * max (m ^ 2) ((n - m) ^ 2)) :=
                Nat.mul_le_mul_left _ hmaxBound
          _ = 2 ^ max qIn.complexity qOut.complexity * (9 * max (m ^ 2) ((n - m) ^ 2)) := by
                ring
          _ ≤ 2 ^ max qIn.complexity qOut.complexity * (4 * n ^ 2) :=
                Nat.mul_le_mul_left _ hmaxSq
          _ = (4 * 2 ^ max qIn.complexity qOut.complexity) * n ^ 2 := by
                ring
          _ = (4 * 2 ^ max qIn.complexity qOut.complexity) * p.numLeaves ^ 2 := by
                simp [hpn]
  exact htarget p.numLeaves p rfl

end Deterministic.Protocol

end CommunicationComplexity
