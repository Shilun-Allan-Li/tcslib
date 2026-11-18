/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Reach
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-width words on tapes: arithmetic rows

A word of `W` bits (`BitVec W`) is held on a work tape as its `W` bits, least significant first,
delimited by blanks at the head's offsets `-1` and `W`. This file states the rows that compute
on such words: addition, subtraction and multiplication modulo `2^W`, the arithmetic shift right,
sign extension, writing the word of an integer constant, and the sign and zero tests. They are the
arithmetic of a word RAM run on a Turing machine (`WordRAM.exists_simulation`).

Every row is a five-tape machine over `Bool`: tapes `0` and `1` hold the operands, tape `2` the
destination, and tapes `3` and `4` are blank scratch tapes, left blank. A row writes only the
destination's word interval, leaves every head where it was, and is stated with
`Turing.ReachesWithin`. A consumer places the five tapes among its own with `Turing.embedEmitTM`
and composes the rows with `Turing.Contract.ofReaches`. The words have one width throughout, so
the length of an operand delimits every scan and `W = 0` (empty words) needs no special case.

No row of the catalog reads two tapes with a carry, so addition, subtraction and the tests are
new rows here (the one-tape `Turing.scanTM` covers only single-word transducers).

## Main definitions

* `Turing.bvBits`: the bits of a word, least significant first.
* `Turing.WordAt`: a word delimited at a head.
* `Turing.wordWrite`: the tapes after writing a word at a head.

## Main results

* `Turing.exists_wordAddTM`, `Turing.exists_wordSubTM`, `Turing.exists_wordMulTM`: addition,
  subtraction and multiplication modulo `2^W`, in `O(W)`, `O(W)` and `O(W²)` steps.
* `Turing.exists_wordHalfTM`: the arithmetic shift right by one place.
* `Turing.exists_wordSignExtendTM`: sign extension from `W` to `W + a` bits.
* `Turing.exists_wordIntTM`: the word of an integer constant, as wide as a guide word plus `a`.
* `Turing.exists_wordSignTM`, `Turing.exists_wordNonzeroTM`: the tests `u < 0` and `u ≠ 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: multitape machines; Exercise 1.9: a RAM simulated by a
  Turing machine, whose arithmetic these rows provide.)
-/

namespace Turing

/-! ## Words on tapes -/

/-- **The bits of a word**, least significant first: `bvBits v = [v₀, v₁, …, v_{W-1}]`. -/
def bvBits {W : ℕ} (v : BitVec W) : List Bool := List.ofFn fun i : Fin W => v.getLsbD i

/-- The bits of a word, as an equation. -/
theorem bvBits_def {W : ℕ} (v : BitVec W) :
    bvBits v = List.ofFn fun i : Fin W => v.getLsbD i := rfl

/-- A word of `W` bits has `W` bits. -/
theorem bvBits_length {W : ℕ} (v : BitVec W) : (bvBits v).length = W := by
  simp [bvBits]

/-- Distinct words have distinct bits.

**Proof sketch.** Equal bit lists give `getLsbD` equal at every `i < W` (`List.ofFn_inj`), and
`BitVec.eq_of_getLsbD_eq` concludes. -/
theorem bvBits_injective {W : ℕ} : Function.Injective (bvBits (W := W)) := by
  sorry

/-- **A word delimited at a head**: tape `r` holds `w` from its head, with blanks at the head's
offsets `-1` and `|w|`. The cells beyond are arbitrary. -/
def WordAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (w : List Bool) :
    Prop :=
  ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p

/-- `WordAt`, as an equivalence with its definition. -/
theorem wordAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) :
    WordAt d r w ↔ ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p :=
  Iff.rfl

/-- **The tapes after writing a word at a head**: on tape `r`, the cells from its head on hold `w`
over `|w|` cells; every other cell, of every tape, is unchanged. -/
def wordWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (q - d.workTapePos j)
    else d.workTapes j q

/-- `wordWrite`, as an equation. -/
theorem wordWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) (j : Fin K) (q : ℤ) :
    wordWrite d r w j q =
      if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (q - d.workTapePos j)
      else d.workTapes j q :=
  rfl

/-- **The common precondition of the word rows**: tapes `3` and `4` are blank everywhere. -/
def ScratchBlank {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) : Prop :=
  ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none

/-- `ScratchBlank`, as an equivalence with its definition. -/
theorem scratchBlank_iff {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) :
    ScratchBlank d ↔ ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none :=
  Iff.rfl

/-! ## Arithmetic modulo `2^W` -/

/-- **Addition modulo `2^W`.** From the entry, with `u` on tape `0`, `v` on tape `1`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u + v` on tape `2` and stops at its
exit within `C·(W + 1)` steps, every head within `C·(W + 1)` cells and back where it started.
[AB09, Exercise 1.9]

**Proof sketch.** One lockstep sweep over the three words from their heads, carrying the carry bit
in the state and writing `uᵢ xor vᵢ xor carry`, ending at the blank after the words; then one
sweep back to the heads. The carry out of the top bit is dropped, which is reduction modulo `2^W`
(`BitVec.add` is `BitVec.ofNat` of the sum; the low `W` bits of a sum are the ripple-carry bits).
-/
theorem exists_wordAddTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u + v)) } := by
  sorry

/-- **Subtraction modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u - v`.
[AB09, Exercise 1.9]

**Proof sketch.** The lockstep sweep with a borrow bit in place of the carry, writing
`uᵢ xor vᵢ xor borrow` (equivalently, `u + ¬v + 1`: start the carry at `1` and complement `v`'s
bits as they are read); then the sweep back. -/
theorem exists_wordSubTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u - v)) } := by
  sorry

/-- **Multiplication modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u * v`, within
`C·(W + 1)²` steps and radius `C·(W + 1)`. [AB09, Exercise 1.9]

**Proof sketch.** Shift and add. Copy `u` to scratch tape `3` and clear the destination to `0`.
For each bit of `v`, from the least significant: if it is `1`, add tape `3` into the destination
(the lockstep adder with the destination as an operand, using scratch tape `4` for the sum and
copying it back); then shift tape `3` up by one place in place, dropping its top bit. The
iteration walks `v`'s head one cell per round and stops at its delimiter, so it needs no counter.
Each round is `O(W)` and there are `W` rounds. Finally clear the scratch tapes and return the
heads. The invariant after `r` rounds: the destination holds `u * (v mod 2^r)` and tape `3` holds
`u <<< r`, both modulo `2^W`. -/
theorem exists_wordMulTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1) ^ 2) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u * v)) } := by
  sorry

/-- **The arithmetic shift right by one place.** From the entry, with `u` on tape `0`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u.sshiftRight 1` (that is,
`⌊u / 2⌋` read signed) on tape `2`, within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1`
untouched. [AB09, Exercise 1.9]

**Proof sketch.** Bit `i` of the result is bit `i + 1` of `u`, and the top bit is `u`'s top bit.
Start `u`'s head one cell to the right and sweep both heads together, writing the bit read and
remembering it in the state; at `u`'s right delimiter write the remembered bit once more. For
`W = 0` both words are empty and nothing is written. Then return the heads. -/
theorem exists_wordHalfTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u.sshiftRight 1)) } := by
  sorry

/-- **Sign extension by `a` places.** From the entry, with `u` on tape `0`, a word of `W + a`
cells on tape `2` and blank scratch tapes, the row writes `u.signExtend (W + a)` on tape `2`,
within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1` untouched. The constant `C` depends on
`a`. [AB09, Exercise 1.9]

**Proof sketch.** Copy `u` into the first `W` cells, remembering its last bit read (`false` if
`W = 0`, where the extension is `0`); then write that bit `a` times, counted in the state; then
return the heads. -/
theorem exists_wordSignExtendTM (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W + a →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (u.signExtend (W + a))) } := by
  sorry

/-- **The word of an integer constant.** For an integer `c` and `a ≥ 0`: from the entry, with a
word of `W + a` cells on tape `2` and blank scratch tapes, the row writes `BitVec.ofInt (W + a) c`
over it, within `C·(W + 1)` steps and radius `C·(W + 1)`, tapes `0` and `1` untouched. The
constant `C` depends on `c` and `a`. With `a = 0` and `c = 1` this writes the word `1`.
[AB09, Exercise 1.9]

**Proof sketch.** Let `b` be the bit length of `|c|` plus one. Bit `i` of `BitVec.ofInt n c` is
`c.testBit i` (two's complement), which for `i ≥ b` is the sign of `c`. Sweep the destination's
old word, writing `c.testBit i` from a table in the state for `i < b` and the sign beyond, and stop
at its right delimiter; then return the head. -/
theorem exists_wordIntTM (c : ℤ) (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 2 w → w.length = W + a → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (BitVec.ofInt (W + a) c)) } := by
  sorry

/-! ## Tests -/

/-- **The sign test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u` is negative read signed (`u.toInt < 0`) and at `no` otherwise, within `C·(W + 1)`
steps and radius `C·(W + 1)`, writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** Sweep `u`, remembering the last bit read (`false` for `W = 0`); at the right
delimiter that bit is the sign (`BitVec.toInt_neg_iff`, `u.msb`); return the head and branch. -/
theorem exists_wordSignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u.toInt < 0 then yes else no) } := by
  sorry

/-- **The zero test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u ≠ 0` and at `no` otherwise, within `C·(W + 1)` steps and radius `C·(W + 1)`,
writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** Sweep `u`, remembering whether a `1` was read; return the head and branch.
`u ≠ 0` exactly when some bit is set (`bvBits_injective` with the zero word). -/
theorem exists_wordNonzeroTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u ≠ 0 then yes else no) } := by
  sorry

end Turing
