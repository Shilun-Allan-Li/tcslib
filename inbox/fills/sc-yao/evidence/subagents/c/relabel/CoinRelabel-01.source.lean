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
    Blocks S n = (Bool → Fin S → Fin n → Bool) ×
      (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool) := rfl

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

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel
