/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Fintype.Powerset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact Deterministic Communication Complexity of Set Disjointness

The set-disjointness function `Disj_n` on subsets of `[n]` [RY20, Ch. 1, eq. (1.2)] and its
exact deterministic communication complexity `D(Disj_n) = n + 1` for `n ≥ 1`. The upper
bound is the trivial protocol in which Alice sends her set; the lower bound
[RY20, Thm 1.25] is the fooling-set argument with the `2 ^ n` pairs `(X, Xᶜ)`
[RY20, Ch. 1, §Using Fooling Sets], carried out here directly as a rectangle count.

## Main definitions

- `Functions.Disjointness.disjointness`: the set-disjointness function on subsets of `[n]`.
- `Functions.Disjointness.foolingSet`: the fooling set of pairs `(X, Xᶜ)`.

## Main results

- `Functions.Disjointness.foolingSet_isFoolingSet`, `Functions.Disjointness.foolingSet_card`:
  the pairs `(X, Xᶜ)` form a fooling set for disjointness of size `2 ^ n`.
- `Functions.Disjointness.communicationComplexity_eq`: for `n ≥ 1`, the deterministic
  communication complexity of set disjointness on subsets of `[n]` is exactly `n + 1`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Functions.Disjointness

open Rectangle
open scoped symmDiff

/-- The set-disjointness function on subsets of `[n]`: `disjointness n X Y` is `true` if and
only if `X ∩ Y = ∅` [RY20, Ch. 1, eq. (1.2)]. -/
noncomputable def disjointness (n : ℕ) (X Y : Set (Fin n)) : Bool :=
  by
    classical
    exact decide (Disjoint X Y)

/-- Disjointness is symmetric in Alice's and Bob's inputs. -/
theorem disjointness_comm (n : ℕ) (X Y : Set (Fin n)) :
    disjointness n X Y = disjointness n Y X := by
  simp [disjointness, disjoint_comm]

/-- The fooling set for disjointness: the set of all pairs `(X, Xᶜ)` of a subset of `[n]`
and its complement [RY20, Ch. 1, §Using Fooling Sets]. -/
def foolingSet (n : ℕ) : Set (Set (Fin n) × Set (Fin n)) :=
  {p | p.2 = p.1ᶜ}

/-- The pairs `(X, Xᶜ)` form a fooling set for disjointness: no monochromatic rectangle
contains two distinct pairs `(X, Xᶜ)` and `(X', X'ᶜ)` [RY20, Ch. 1, §Using Fooling Sets].

**Proof sketch.** Let `R` be a monochromatic rectangle containing `(X, Xᶜ)` and
`(X', X'ᶜ)`; we show `X = X'`. Step 1: if `X = X'` the two pairs coincide. Step 2:
otherwise the cross-membership property of rectangles puts both mixed pairs `(X, X'ᶜ)` and
`(X', Xᶜ)` into `R`, and since `X ≠ X'` the symmetric difference `X ∆ X'` contains some
element `i`. Step 3: if `i ∈ X \ X'`, then `i ∈ X ∩ X'ᶜ`, so the mixed pair `(X, X'ᶜ)` is
intersecting while the diagonal pair `(X, Xᶜ)` is disjoint; monochromaticity of `R` gives
`Disj(X, Xᶜ) = Disj(X, X'ᶜ)`, a contradiction. Step 4: if `i ∈ X' \ X` the same argument
applies with the roles of `X` and `X'` exchanged. -/
theorem foolingSet_isFoolingSet (n : ℕ) :
    IsFoolingSet (foolingSet n) (disjointness n) := by
  intro R hR hmono p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp only [foolingSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with ⟨rfl, hpR⟩
  rcases hq with ⟨rfl, hqR⟩
  by_cases hXX' : X = X'
  · -- Step 1: equal sets give the same pair.
    subst hXX'
    rfl
  · -- Step 2: the mixed pairs lie in `R`, and some `i` separates `X` from `X'`.
    have hcross := (IsRectangle_iff R).mp hR X X' Xᶜ X'ᶜ hpR hqR
    obtain ⟨i, hi⟩ : (X ∆ X').Nonempty := Set.symmDiff_nonempty.mpr hXX'
    rw [Set.mem_symmDiff] at hi
    rcases hi with hi | hi
    · -- Step 3: `i ∈ X \ X'`, so `(X, X'ᶜ)` intersects while `(X, Xᶜ)` is disjoint.
      have hval := hmono X X Xᶜ X'ᶜ hpR hcross.2
      have htrue : disjointness n X Xᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
      have hne : disjointness n X X'ᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
    · -- Step 4: `i ∈ X' \ X`, the mirror image with `X` and `X'` exchanged.
      have hval := hmono X' X' X'ᶜ Xᶜ hqR hcross.1
      have htrue : disjointness n X' X'ᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X' X'ᶜ)
      have hne : disjointness n X' Xᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim

/-- The fooling set of pairs `(X, Xᶜ)` has exactly `2 ^ n` elements, one for each subset
`X ⊆ [n]` [RY20, Ch. 1, §Using Fooling Sets]. -/
theorem foolingSet_card (n : ℕ) :
    Set.ncard (foolingSet n) = 2 ^ n := by
  let f : Set (Fin n) → Set (Fin n) × Set (Fin n) := fun X => (X, Xᶜ)
  have hf : Function.Injective f := by
    intro X X' h
    exact congrArg Prod.fst h
  calc Set.ncard (foolingSet n)
      = Set.ncard (Set.range f) := by
          congr
          ext p
          rcases p with ⟨X, Y⟩
          simp [f, foolingSet, eq_comm]
    _ = 2 ^ n := by
          simpa [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin] using
            Set.ncard_range_of_injective hf

/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
private theorem clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl

/-- The deterministic communication complexity of disjointness on subsets of `[n]` is at
most `n + 1`: Alice sends her set as `n` bits, and Bob sends one bit for the answer
[RY20, Ch. 1, §Disjointness: 'Alice sending X gives an (n+1)-bit protocol']. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (disjointness n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (disjointness n)
      ≤ Nat.clog 2 (Nat.card (Set (Fin n))) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (disjointness n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin,
          Fintype.card_bool, Nat.one_lt_ofNat, Nat.clog_pow]
        rw [clog_two_two]
        norm_num

/-- For `n ≥ 1`, disjointness on subsets of `[n]` has deterministic communication
complexity at least `n + 1` [RY20, Thm 1.25]. Deviation: the bound is exact together with
`communicationComplexity_le`; [Rou16, Cor 4.8] only gives `≥ n`. The hypothesis `n ≥ 1`
is needed for an intersecting pair to exist.

**Proof sketch.** By the rectangle lower bound
(`Deterministic.le_communicationComplexity_of_forall_lt_ncard`) it suffices to show that
every monochromatic rectangle partition of the input space has more than `2 ^ n` parts.
Step 1: for each subset `X` choose a part `rect X` containing the fooling-set pair
`(X, Xᶜ)`. Step 2: `rect` is injective, because a part containing both `(X, Xᶜ)` and
`(X', X'ᶜ)` is a monochromatic rectangle, so the fooling-set property
(`foolingSet_isFoolingSet`) forces `X = X'`. Step 3: hence the range of `rect` has exactly
`2 ^ n` elements. Step 4: the part `R0` containing the intersecting pair `({0}, {0})`
(which exists since `n ≥ 1`) is `false`-monochromatic, whereas every `rect X` contains the
disjoint pair `(X, Xᶜ)` and is `true`-monochromatic; so `R0` is not in the range of
`rect`. Step 5: adjoining `R0` to the range of `rect` gives a subset of the partition with
`2 ^ n + 1` parts. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (disjointness n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  -- Step 1: each pair (X, Xᶜ) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun X : Set (Fin n) =>
    monoPartition_point_mem hPart (X, Xᶜ)
  -- Step 2: rect is injective by the fooling-set property
  have hrect_inj : Function.Injective rect := by
    intro X X' hXX
    have hsub :=
      foolingSet_isFoolingSet n (rect X) (hPart.1 _ (hrect_mem X)) (hPart.2.1 _ (hrect_mem X))
    have hp : (X, Xᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hrect_in X]
    have hq : (X', X'ᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hXX ▸ hrect_in X']
    exact congrArg Prod.fst (hsub hp hq)
  -- Step 3: the image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_set, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  -- Step 4: the rectangle R0 containing the intersecting pair ({0}, {0}) is "false"-mono,
  -- so it is not in the image of rect
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Set (Fin n) := {i0}
  let y0 : Set (Fin n) := {i0}
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨X, rfl⟩
    have hval := monoPartition_values_eq hPart (hrect_mem X) (hrect_in X) hR0_in
    have htrue : disjointness n X Xᶜ = true := by
      simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
    have hne : disjointness n x0 y0 ≠ true := by
      unfold disjointness
      simp only [ne_eq, decide_eq_true_eq]
      intro hdisj
      rw [Set.disjoint_left] at hdisj
      have hnot : i0 ∉ y0 := hdisj (by simp [x0])
      exact hnot (by simp [y0])
    rw [htrue] at hval
    exact (hne hval.symm).elim
  -- Step 5: insert R0 into range rect ⊆ Part, giving 2^n < |Part|
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨X, hX⟩ => hX ▸ hrect_mem X)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]
        omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- For `n ≥ 1`, the deterministic communication complexity of disjointness on subsets of
`[n]` is exactly `n + 1` [RY20, Thm 1.25]. Deviation: [RY20] states the lower bound
`≥ n + 1`; combined with the trivial upper bound this gives the exact value
([Rou16, Cor 4.8] only gives `≥ n`). -/
theorem communicationComplexity_eq (n : ℕ) (hn : 1 ≤ n) :
    Deterministic.communicationComplexity (disjointness n) = n + 1 := by
  apply le_antisymm (communicationComplexity_le n)
  exact le_communicationComplexity n hn

end Functions.Disjointness

end CommunicationComplexity
