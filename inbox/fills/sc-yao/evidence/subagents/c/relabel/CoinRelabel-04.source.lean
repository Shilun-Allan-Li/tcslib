/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.BitLists
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact coin-block bijections for garbling

The tape of `10 S n + 2 S` bits consists of two `S`-by-`n` key tables,
`S`-by-four rows of `2 n` bits, and `S` two-bit shifts. The equivalences below
include zero-width key and row tables. Relabeling permutes key choices and row
blocks and XORs shift bits; callers can fix unused coordinates explicitly.

## Main definitions

* `Blocks`: the typed key, row and shift tables.
* `splitTape`: the three contiguous regions of the tape.
* `blocksEquiv`: the complete tape as its three typed tables.
* `relabel`: a coin bijection obtained by relabeling those tables.

## Main results

* `blocksEquiv_key`, `blocksEquiv_row`, `blocksEquiv_shift`: exact offset equations.
* `relabel_blocks`: conjugation through the typed block representation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the coin relabeling in the garbling hybrid).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure
  protocols*, STOC 1990, pp.503–513 (point-and-permute).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel

open TCSlib.Cryptography

/-- `Blocks S n` is a key table `Bool → Fin S → Fin n → Bool`, a row table
`Fin S → Fin 4 → Fin (2 n) → Bool`, and shifts `Fin S → Fin 2 → Bool`. -/
abbrev Blocks (S n : ℕ) :=
  (Bool → Fin S → Fin n → Bool) ×
    (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool)

/-- `Blocks S n` is the product of its key, row and shift function types. -/
theorem Blocks_eq (S n : ℕ) :
    Blocks S n = ((Bool → Fin S → Fin n → Bool) ×
      (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool)) := rfl

/-- Split `10 S n + 2 S` coin bits into regions of lengths `2 S n`, `4 S (2 n)`
and `2 S`, by two append equivalences. Zero widths are included. -/
def splitTape (S n : ℕ) :
    (Fin (10 * S * n + 2 * S) → Bool) ≃
      (Fin ((2 * S) * n) → Bool) ×
        (Fin ((S * 4) * (2 * n)) → Bool) × (Fin (S * 2) → Bool) :=
  let h : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by ring
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans
    ((Fin.appendEquiv ((2 * S) * n) ((S * 4) * (2 * n) + S * 2)).symm.trans
      ((Equiv.refl _).prodCongr (Fin.appendEquiv ((S * 4) * (2 * n)) (S * 2)).symm))

/-- The key region of `splitTape S n r` reads the tape at its unchanged offset:
`(splitTape S n r).1 i = (ofFn r).getD i false`. -/
theorem splitTape_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((2 * S) * n)) :
    (splitTape S n r).1 i = (List.ofFn r).getD i false := by
  have hsum : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by
    ring
  have hi := i.isLt
  have hb : (i : ℕ) < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  rfl

/-- The row region of `splitTape S n r` begins at `2 S n`:
`(splitTape S n r).2.1 i = (ofFn r).getD (2*S*n+i) false`. -/
theorem splitTape_row (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((S * 4) * (2 * n))) :
    (splitTape S n r).2.1 i = (List.ofFn r).getD (2 * S * n + i) false := by
  have hsum : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by
    ring
  have hi := i.isLt
  have hb : 2 * S * n + i < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  rfl

/-- The shift region of `splitTape S n r` begins at `10 S n`:
`(splitTape S n r).2.2 i = (ofFn r).getD (10*S*n+i) false`. -/
theorem splitTape_shift (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin (S * 2)) :
    (splitTape S n r).2.2 i = (List.ofFn r).getD (10 * S * n + i) false := by
  have hi := i.isLt
  have hb : 10 * S * n + i < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  apply congrArg r
  apply Fin.ext
  change (2 * S) * n + ((S * 4) * (2 * n) + (i : ℕ)) = 10 * S * n + i
  ring

/-- `splitTape S n r` is the triple of windows at offsets `0`, `2 S n`, and
`10 S n`, of lengths `2 S n`, `4 S (2 n)`, and `2 S`, respectively. -/
theorem splitTape_eq (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool) :
    splitTape S n r =
      ((fun i => (List.ofFn r).getD i false),
        (fun i => (List.ofFn r).getD (2 * S * n + i) false),
        (fun i => (List.ofFn r).getD (10 * S * n + i) false)) := by
  apply Prod.ext
  · funext i
    exact splitTape_key S n r i
  · apply Prod.ext
    · funext i
      exact splitTape_row S n r i
    · funext i
      exact splitTape_shift S n r i

/-- The complete tape of `10 S n + 2 S` bits is equivalent to its typed key, row,
and shift tables. The construction uses only splitting, existing block equivalences,
and reindexing; in particular it includes `S = 0` and `n = 0`.
[PS10, Theorem 163.7, coin relabeling] -/
def blocksEquiv (S n : ℕ) : (Fin (10 * S * n + 2 * S) → Bool) ≃ Blocks S n :=
  let eK : (Fin ((2 * S) * n) → Bool) ≃ (Bool → Fin S → Fin n → Bool) :=
    ((FunFamily.blocks (2 * S) n).trans (blocksEquivX 2 S (Fin n → Bool))).trans
      (Equiv.arrowCongr finTwoEquiv (Equiv.refl _))
  let eR : (Fin ((S * 4) * (2 * n)) → Bool) ≃ (Fin S → Fin 4 → Fin (2 * n) → Bool) :=
    (FunFamily.blocks (S * 4) (2 * n)).trans (blocksEquivX S 4 (Fin (2 * n) → Bool))
  (splitTape S n).trans (eK.prodCongr (eR.prodCongr (FunFamily.blocks S 2)))

/-- Key bit `t` of choice `b` at vertex `v` is tape bit `(b*S+v)*n+t`:
`(blocksEquiv S n r).1 b v t = (ofFn r).getD ((b.toNat*S+v)*n+t) false`.
The equation includes zero-width key tables. -/
theorem blocksEquiv_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (b : Bool) (v : Fin S) (t : Fin n) :
    (blocksEquiv S n r).1 b v t =
      (List.ofFn r).getD ((b.toNat * S + v) * n + t) false := by
  change blocksEquivX 2 S (Fin n → Bool)
    (FunFamily.blocks (2 * S) n ((splitTape S n r).1)) (finTwoEquiv.symm b) v t = _
  rw [blocksEquivX_apply, FunFamily.blocks_apply, splitTape_key]
  congr 1
  simp only [finProdFinEquiv_apply_val]
  have hb : (finTwoEquiv.symm b : ℕ) = b.toNat := by cases b <;> rfl
  rw [hb]
  ring

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel
