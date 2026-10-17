/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardVerifier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The verifier on an assignment

On the input `⟨x, σ⟩` with `σ` the first `3w(w + 1)` values of an assignment `τ` of the
prefix variables, the verifier `Complexity.TQBFHard.predB` of `TQBFHardVerifier` is the flat
form of the `ψ` matrix of `TQBFHardSemantics` over the block tests of `TQBFHardMachine`:
the initial-code test on the block at `w`, the accepting-code test on the block at `2w`, and
"some record's pair is not selected by its parent, or the innermost pair is one step"
(`predB_iff`). The proof reads every block of the word `σ` as the corresponding block of
`τ` (`ofFn_drop_take`).

Infrastructure for `Complexity.TQBF_PSPACEHard`; not itself a book result.

## Main definitions

* none (theorems about the verifier `Complexity.TQBFHard.predB` of `TQBFHardVerifier`).

## Main results

* `Complexity.TQBFHard.predB_iff` — the verifier on an assignment.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity

namespace TQBFHard

open Turing Codec

/-- An indicator is `true` exactly on members. -/
theorem indicator_eq_true_iff {L : Language Bool} {z : List Bool} :
    MultiTapeTM.indicator L z = true ↔ z ∈ L := by
  unfold MultiTapeTM.indicator
  split_ifs with h <;> simp [h]

/-- A slice of the word of the first `M` values of `τ` is a block of `τ`. -/
theorem ofFn_drop_take (τ : ℕ → Bool) {M i k : ℕ} (h : i + k ≤ M) :
    ((List.ofFn fun j : Fin M => τ j).drop i).take k = readBlock τ i k := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn, length_readBlock]
    omega
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, readBlock]

variable (N : FinNDTM Bool) (d c A a : ℕ)

/-- **The verifier on an assignment**: for an input `x` of length `n`, block width
`w = A (n + 1)^a` at least the code-word length `L`, radius `s = 2d (n + 1)^c`, and the word
`σ` of the first `3w(w + 1)` values of `τ`, the verifier accepts `⟨x, σ⟩` iff the block at `w`
is initial, the block at `2w` is accepting, and some record `j < w` has its successor's pair
not selected, or the pair of record `w` is one step.

**Proof sketch.** Each block the verifier cuts out of `σ` is the block of `τ` at the same
offset (`ofFn_drop_take`; the code-word prefix is the block's first `L` letters,
`List.take_take`), the window of record `j` holds the records `j` and `j + 1`, and the
indicators are memberships (`indicator_eq_true_iff`). -/
theorem predB_iff (x : List Bool) (τ : ℕ → Bool)
    (hL : vlen N d c x.length ≤ vwid A a x.length) :
    predB N d c A a (pairEncode x (List.ofFn fun j : Fin (3 * vwid A a x.length *
        vwid A a x.length + 3 * vwid A a x.length) => τ j)) = true ↔
      blockInit N x (vrad d c x.length) (vlen N d c x.length)
          (readBlock τ (vwid A a x.length) (vwid A a x.length)) ∧
        blockAcc N x (vrad d c x.length) (vlen N d c x.length)
          (readBlock τ (2 * vwid A a x.length) (vwid A a x.length)) ∧
        ((∃ i < vwid A a x.length, ¬ Sel (uRec τ (vwid A a x.length) i)
            (vRec τ (vwid A a x.length) i) (zRec τ (vwid A a x.length) (i + 1))
            (uRec τ (vwid A a x.length) (i + 1)) (vRec τ (vwid A a x.length) (i + 1))) ∨
          blockStep N x (vrad d c x.length) (vlen N d c x.length)
            (uRec τ (vwid A a x.length) (vwid A a x.length))
            (vRec τ (vwid A a x.length) (vwid A a x.length))) := by
  set w := vwid A a x.length with hw
  set L := vlen N d c x.length with hLdef
  set s := vrad d c x.length with hs
  set M := 3 * w * w + 3 * w with hM
  set σ := List.ofFn fun j : Fin M => τ j with hσ
  set y := pairEncode x σ with hy
  have hX : pairFstD y = x := by simp [hy]
  have hS : pairSndD y = σ := by simp [hy]
  -- blocks and code prefixes of `σ`
  have hblk : ∀ off, off + w ≤ M → blkAt A a y off = readBlock τ off w := by
    intro off hoff
    simp only [blkAt, hX, hS, ← hw]
    exact ofFn_drop_take τ hoff
  have hcp : ∀ off, off + w ≤ M → cpAt N d c y off = (readBlock τ off w).take L := by
    intro off hoff
    simp only [cpAt, hX, hS, ← hLdef]
    rw [← ofFn_drop_take τ hoff, List.take_take, Nat.min_eq_left hL]
  have hinit : initB N d c A a y = true ↔ blockInit N x s L (readBlock τ w w) := by
    simp only [initB, hX, ← hw, ← hs]
    rw [hcp w (by omega), indicator_eq_true_iff]
    rfl
  have hacc : accB N d c A a y = true ↔ blockAcc N x s L (readBlock τ (2 * w) w) := by
    simp only [accB, hX, ← hw, ← hs]
    rw [hcp (2 * w) (by omega), indicator_eq_true_iff]
    rfl
  have hbase : baseB N d c A a y = true ↔ blockStep N x s L (uRec τ w w) (vRec τ w w) := by
    simp only [baseB, hX, ← hw, ← hs]
    rw [hblk _ (by omega), hblk _ (by omega), hcp _ (by omega), hcp _ (by omega),
      Bool.or_eq_true, decide_eq_true_iff, indicator_eq_true_iff]
    rfl
  -- the windows
  have hwin : ∀ j < w, ∀ k ≤ 5, winBlk (lvlQ A a y j) k = readBlock τ (3 * w * j + k * w) w := by
    intro j hj k hk
    simp only [winBlk, lvlQ, hX, hS, ← hw, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, List.drop_drop]
    apply ofFn_drop_take τ
    have : (j + 2) * w ≤ (w + 1) * w := Nat.mul_le_mul_right _ (by omega)
    have : k * w ≤ 5 * w := Nat.mul_le_mul_right _ hk
    nlinarith
  have hsel : ∀ j < w, selT (lvlQ A a y j) = true ↔ Sel (uRec τ w j) (vRec τ w j)
      (zRec τ w (j + 1)) (uRec τ w (j + 1)) (vRec τ w (j + 1)) := by
    intro j hj
    simp only [selT, hwin j hj 1 (by omega), hwin j hj 2 (by omega), hwin j hj 3 (by omega),
      hwin j hj 4 (by omega), hwin j hj 5 (by omega), Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_iff, Sel, uRec, vRec, zRec]
    have e3 : 3 * w * j + 3 * w = 3 * w * (j + 1) := by ring
    have e4 : 3 * w * j + 4 * w = 3 * w * (j + 1) + w := by ring
    have e5 : 3 * w * j + 5 * w = 3 * w * (j + 1) + 2 * w := by ring
    rw [Nat.one_mul, e3, e4, e5]
  have hor : orB A a y = true ↔ ∃ i < w, ¬ Sel (uRec τ w i) (vRec τ w i) (zRec τ w (i + 1))
      (uRec τ w (i + 1)) (vRec τ w (i + 1)) := by
    simp only [orB, hX, ← hw, List.any_eq_true, List.mem_range, Bool.not_eq_true']
    constructor
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, fun hs' => by rw [← hsel j hj, h] at hs'; exact Bool.false_ne_true hs'⟩
    · rintro ⟨j, hj, h⟩
      refine ⟨j, hj, ?_⟩
      cases hb : selT (lvlQ A a y j)
      · rfl
      · exact absurd ((hsel j hj).mp hb) h
  simp only [predB, Bool.and_eq_true, Bool.or_eq_true]
  rw [hinit, hacc, hbase, hor, and_assoc]
  exact and_congr_right fun _ => and_congr_right fun _ => or_comm

end TQBFHard

end Complexity
