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

A deterministic protocol with `ℓ` leaves can be simulated by a protocol of communication
complexity `O(log ℓ)`: repeatedly cut out a balanced subprotocol (one with between a third
and two thirds of the leaves), spend two bits announcing whether the input reaches it, and
recurse on the two remaining halves. This is [RY20, Thm 1.3].

## Main definitions

None.

## Main results

- `Deterministic.Protocol.exists_balanced_simulation`: every deterministic protocol `p`
  with `ℓ` leaves is simulated by a protocol `q` with the same input–output behaviour and
  complexity `c` satisfying `3^c ≤ 2^c · ℓ²`, i.e. `c ≤ 2 log_{3/2} ℓ`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*,
  Cambridge University Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- Every protocol has at least one leaf. -/
private lemma numLeaves_pos (p : Protocol X Y α) : 0 < p.numLeaves :=
  -- `numLeaves p` is the leaf count of the shape tree, and every `Tree` has a leaf.
  Tree.numLeaves_pos p.shape

/-- A protocol with exactly one leaf has communication complexity `0`.

**Proof sketch.** Case on the root. An output node has complexity `0` by definition. An
Alice or Bob node has two children, its leaf count is the sum of the children's leaf counts,
and each child has at least one leaf (`numLeaves_pos`), so the count is at least `2`,
contradicting the hypothesis. -/
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

/-- If `m` and `n - m` are both at most two thirds of `n`, then the larger of the squares
`m²` and `(n - m)²` is at most `(4/9) n²`, written as `9 · max(m², (n - m)²) ≤ 4 n²`. -/
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

/-- Gluing step of the balanced simulation: if `qIn` behaves like the subprotocol `s` and
`qOut` behaves like `p` with `s` pruned away, then `testSubprotocol hsp qIn qOut` behaves
like `p`. -/
private lemma simulation_step
    {s p qIn qOut : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves)
    (hRunIn : qIn.run = s.run) (hRunOut : qOut.run = (prune hsp hlt).run) :
    (testSubprotocol hsp qIn qOut).run = p.run := by
  ext x y
  by_cases hxy : reaches hsp x y
  · -- inside the subprotocol: `q` runs `qIn`, i.e. `s`, i.e. `p`
    calc
      (testSubprotocol hsp qIn qOut).run x y = qIn.run x y :=
          testSubprotocol_run_inside hsp hxy
      _ = s.run x y := by rw [hRunIn]
      _ = p.run x y := (subprotocol_run_eq_of_reaches hsp hxy).symm
  · -- outside the subprotocol: `q` runs `qOut`, i.e. the pruned protocol, i.e. `p`
    calc
      (testSubprotocol hsp qIn qOut).run x y = qOut.run x y :=
          testSubprotocol_run_outside hsp hxy
      _ = (prune hsp hlt).run x y := by rw [hRunOut]
      _ = p.run x y := prune_run_outside_of_lt hsp hlt hxy

/-- Arithmetic step of the balanced simulation: the two inductive bounds for the inside
(`m` leaves) and outside (`n - m` leaves) parts, together with the balance conditions
`3m ≤ 2n` and `3(n - m) ≤ 2n`, give the bound for complexity `2 + max cIn cOut`.

**Proof sketch.** Step 1: by cases on which of `cIn`, `cOut` is larger, the corresponding
inductive bound gives `3^max ≤ 2^max · max(m², (n − m)²)` after enlarging the square to the
maximum. Step 2: the balance conditions give `9 · max(m², (n − m)²) ≤ 4n²`
(`max_sq_le_of_balanced`). Step 3: chain
`3^(2 + max) = 9 · 3^max ≤ 9 · 2^max · max(m², (n − m)²) ≤ 2^max · 4n² = 2^(2 + max) · n²`. -/
private lemma simulation_step_bound
    {cIn cOut m n : ℕ}
    (hIn : 3 ^ cIn ≤ 2 ^ cIn * m ^ 2)
    (hOut : 3 ^ cOut ≤ 2 ^ cOut * (n - m) ^ 2)
    (hm : 3 * m ≤ 2 * n) (hout : 3 * (n - m) ≤ 2 * n) :
    3 ^ (2 + max cIn cOut) ≤ 2 ^ (2 + max cIn cOut) * n ^ 2 := by
  -- the larger of the two complexities is bounded by the larger of the two squares
  have hmaxBound :
      3 ^ max cIn cOut ≤ 2 ^ max cIn cOut * max (m ^ 2) ((n - m) ^ 2) := by
    rcases le_total cIn cOut with hcmp | hcmp
    · rw [max_eq_right hcmp]
      exact hOut.trans (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
    · rw [max_eq_left hcmp]
      exact hIn.trans (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
  -- the balance conditions give `9 * max(m², (n-m)²) ≤ 4 n²`
  have hmaxSq : 9 * max (m ^ 2) ((n - m) ^ 2) ≤ 4 * n ^ 2 :=
    max_sq_le_of_balanced m n hm hout
  calc
    3 ^ (2 + max cIn cOut) = 9 * 3 ^ max cIn cOut := by simp [pow_add]
    _ ≤ 9 * (2 ^ max cIn cOut * max (m ^ 2) ((n - m) ^ 2)) :=
        Nat.mul_le_mul_left _ hmaxBound
    _ = 2 ^ max cIn cOut * (9 * max (m ^ 2) ((n - m) ^ 2)) := by ring
    _ ≤ 2 ^ max cIn cOut * (4 * n ^ 2) := Nat.mul_le_mul_left _ hmaxSq
    _ = 2 ^ (2 + max cIn cOut) * n ^ 2 := by rw [pow_add]; ring

/-- Every deterministic protocol `p` with `ℓ` leaves is simulated by a protocol `q` computing
the same function on every input and whose communication complexity `c` satisfies
`3^c ≤ 2^c · ℓ²`. [RY20, Thm 1.3]. Deviation: RY20 state the bound as
`c ≤ 2 log_{3/2} ℓ`; it is stated here multiplicatively as `3^c ≤ 2^c · ℓ²`, which is
equivalent (divide by `2^c`) and avoids real logarithms.

**Proof sketch.** Strong induction on the number of leaves.

1. Reduce to the statement "for all `n`, every protocol with exactly `n` leaves has such a
   simulation", proved by strong induction on `n`.
2. Base case `n = 1`: `p` is a single output node, so its complexity is `0`
   (`complexity_eq_zero_of_numLeaves_eq_one`) and `p` itself is the simulation.
3. Otherwise `p` has more than one leaf, so `balanced_subprotocol` yields a subprotocol `s`
   with `m` leaves, `n/3 ≤ m < 2n/3`; in particular `m < n`.
4. Apply the induction hypothesis twice: to `s` (giving `qIn`), and to `p` with `s` pruned
   away (giving `qOut`); the pruned protocol has exactly `n - m` leaves.
5. Glue: `q := testSubprotocol s qIn qOut` first spends two bits deciding whether the input
   reaches `s`, then runs `qIn` or `qOut`. It agrees with `p` on every input
   (`simulation_step`: inside, `qIn` runs like `s` which runs like `p`; outside, `qOut` runs
   like the pruned protocol which runs like `p`).
6. Arithmetic: `q` has complexity `2 + max(cIn, cOut)`. The inductive bounds for `cIn`
   (against `m²`) and `cOut` (against `(n - m)²`) together with the balance conditions
   `3m ≤ 2n` and `3(n - m) ≤ 2n` give `9 · max(m², (n - m)²) ≤ 4n²`, hence
   `3^{2 + max} ≤ 2^{2 + max} · n²` (`simulation_step_bound`). -/
theorem exists_balanced_simulation (p : Protocol X Y α) :
    ∃ q : Protocol X Y α, q.run = p.run ∧
      3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2 := by
  -- Step 1: strong induction on the number of leaves `n`.
  suffices htarget : ∀ n, ∀ p : Protocol X Y α, p.numLeaves = n →
      ∃ q : Protocol X Y α, q.run = p.run ∧
        3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2 from
    htarget p.numLeaves p rfl
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih p hpn
  by_cases hn1 : n = 1
  · -- Step 2: base case `n = 1`: `p` itself works, its complexity is `0`.
    subst hn1
    have hcomp0 : p.complexity = 0 := complexity_eq_zero_of_numLeaves_eq_one p hpn
    exact ⟨p, rfl, by simp [hcomp0, hpn]⟩
  · -- Step 3: pick a balanced subprotocol `s` with `m = s.numLeaves < n`.
    have hgt1p : 1 < p.numLeaves := by
      have hpos := numLeaves_pos p
      omega
    obtain ⟨s, hsp, hbal_lo, hbal_hi⟩ := balanced_subprotocol p hgt1p
    have hm_lt_p : s.numLeaves < p.numLeaves := by omega
    -- Step 4: induction hypothesis on `s` (inside) and on the pruned protocol (outside).
    obtain ⟨qIn, hRunIn, hBoundIn⟩ := ih s.numLeaves (by omega) s rfl
    have hpOut_leaves : (prune hsp hm_lt_p).numLeaves = n - s.numLeaves := by
      rw [prune_numLeaves_of_lt hsp hm_lt_p, hpn]
    obtain ⟨qOut, hRunOut, hBoundOut⟩ :=
      ih (n - s.numLeaves) (by omega) (prune hsp hm_lt_p) hpOut_leaves
    -- Step 5: glue with `testSubprotocol`; it runs like `p` by `simulation_step`.
    refine ⟨testSubprotocol hsp qIn qOut, simulation_step hsp hm_lt_p hRunIn hRunOut, ?_⟩
    -- Step 6: complexity is `2 + max`, and the arithmetic is `simulation_step_bound`.
    rw [testSubprotocol_complexity, hpn]
    rw [hpOut_leaves] at hBoundOut
    exact simulation_step_bound hBoundIn hBoundOut (by omega) (by omega)

end Deterministic.Protocol

end CommunicationComplexity
