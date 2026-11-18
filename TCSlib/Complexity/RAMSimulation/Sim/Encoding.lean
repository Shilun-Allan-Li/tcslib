/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.TuringMachine.Build.KeyTable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: how tapes encode a configuration of the extended word RAM

The simulating machine of `WordRAM.exists_simulation` keeps a configuration `c : XCfg W` of the
extended word RAM on eight work tapes, its program position in its finite control. This file
defines that encoding, `WordRAM.Sim.Encodes`, shared by the start-up (`Sim/Startup`), the
instruction phases (`Sim/Phases`) and the simulation's induction. The declarations of the
`WordRAM.Sim` namespace are the simulation's internal interfaces: public so that the pieces can
live in separate files, not meant for other consumers.

**The eight tapes.**
* `0`: the memory, a keyed table (`Turing.KeyTableAt`) of the written cells and their words.
* `1`: the key register, `W + a` cells.
* `2`, `3`, `4`: three word registers of `W` cells.
* `5`: the input length in binary, `Nat.bits |x|`.
* `6`, `7`: blank scratch tapes.

**Keys.** The memory is indexed by integers. A cell `z` is stored under the `W + a` bits of
`z` in two's complement, `keyBits a W z`. Every address the program touches is in that range:
a computed address is a word's signed value, and the program's own addresses (its immediates)
are below `2^(a-1)` in absolute value (`WordRAM.Sim.ImmBound`). In that range distinct cells
have distinct keys.

## Main definitions

* `WordRAM.Sim.keyBits`, `WordRAM.Sim.immediates`, `WordRAM.Sim.ImmBound`.
* `WordRAM.Sim.TableOf`: a list of entries stores a memory over a set of cells.
* `WordRAM.Sim.Encodes`: the tapes encode a configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- **The key of a cell**: the `W + a` bits of the integer `z` in two's complement, least
significant first. -/
def keyBits (a W : ℕ) (z : ℤ) : List Bool := bvBits (BitVec.ofInt (W + a) z)

/-- The key of a cell, as an equation. -/
theorem keyBits_def (a W : ℕ) (z : ℤ) : keyBits a W z = bvBits (BitVec.ofInt (W + a) z) := rfl

/-- **The addresses written in an instruction**: its integer arguments, which name cells (the
label of `bltz` is a position, not a cell, and is not one of them). -/
def immediates : XInstr → List ℤ
  | .base (.one i) => [i]
  | .base (.add i j k) => [i, j, k]
  | .base (.sub i j k) => [i, j, k]
  | .base (.mul i j k) => [i, j, k]
  | .base (.load i j) => [i, j]
  | .base (.store i j) => [i, j]
  | .base (.bltz i _) => [i]
  | .base .accept => []
  | .base .reject => []
  | .rdIn i j => [i, j]
  | .emit i => [i]
  | .coin i => [i]
  | .half i j => [i, j]

/-- The addresses written in an instruction, as an equation. -/
theorem immediates_def (ins : XInstr) :
    immediates ins =
      match ins with
      | .base (.one i) => [i]
      | .base (.add i j k) => [i, j, k]
      | .base (.sub i j k) => [i, j, k]
      | .base (.mul i j k) => [i, j, k]
      | .base (.load i j) => [i, j]
      | .base (.store i j) => [i, j]
      | .base (.bltz i _) => [i]
      | .base .accept => []
      | .base .reject => []
      | .rdIn i j => [i, j]
      | .emit i => [i]
      | .coin i => [i]
      | .half i j => [i, j] := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **Small immediates**: every address written in `ins` is in the signed range of `a` bits
(`WordRAM.InRange a`), so that it has a key of `W + a` bits for every `W`. -/
def ImmBound (a : ℕ) (ins : XInstr) : Prop := ∀ z ∈ immediates ins, InRange a z

/-- `ImmBound`, as an equivalence with its definition. -/
theorem immBound_iff (a : ℕ) (ins : XInstr) :
    ImmBound a ins ↔ ∀ z ∈ immediates ins, InRange a z := Iff.rfl

/-- **A table stores a memory over a set of cells.** `TableOf a W T m es`: the keys of `es` are
distinct; every entry is the key of some cell `z ∈ T` in the range of `W + a` bits, with `m z`'s
bits as its value; and every cell in that range where `m` is nonzero has an entry. So a lookup of
a cell in range finds its word, or nothing exactly when the word is `0`, and `es` has at most
`|T|` entries. -/
def TableOf (a W : ℕ) (T : Finset ℤ) (m : ℤ → BitVec W) (es : List (List Bool × List Bool)) :
    Prop :=
  (es.map Prod.fst).Nodup ∧
    (∀ e ∈ es, ∃ z ∈ T, InRange (W + a) z ∧ e = (keyBits a W z, bvBits (m z))) ∧
    ∀ z : ℤ, InRange (W + a) z → m z ≠ 0 → keyBits a W z ∈ es.map Prod.fst

/-- `TableOf`, as an equivalence with its definition. -/
theorem tableOf_iff (a W : ℕ) (T : Finset ℤ) (m : ℤ → BitVec W)
    (es : List (List Bool × List Bool)) :
    TableOf a W T m es ↔ (es.map Prod.fst).Nodup ∧
      (∀ e ∈ es, ∃ z ∈ T, InRange (W + a) z ∧ e = (keyBits a W z, bvBits (m z))) ∧
      ∀ z : ℤ, InRange (W + a) z → m z ≠ 0 → keyBits a W z ∈ es.map Prod.fst :=
  Iff.rfl

/-- **The tapes encode a configuration.** `Encodes a fn T c σ o d`, for the eight tapes placed in
`d`'s tapes by `σ`, with origins `o`:
* every one of the eight heads is at its origin;
* tape `0` holds a keyed table that stores `c.mem` over the cells `T` (`TableOf`);
* tape `1` holds a word of `W + a` cells, tapes `2` to `4` words of `W` cells;
* tape `5` holds `Nat.bits |x|`;
* tapes `6` and `7` are blank;
* the output is `c.out` in function mode (`fn = true`) and empty in verdict mode.

The program position `c.pc` and the coin count `c.rd` are not on the tapes: the position is the
phase of the machine's finite control, and the coin count is a property of the run. -/
def Encodes {K : ℕ} {S : Type} (a : ℕ) (fn : Bool) {x : List Bool} {W : ℕ} (T : Finset ℤ)
    (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x) : Prop :=
  (∀ j : Fin 8, d.workTapePos (σ j) = o j) ∧
    (∃ es, KeyTableAt d (σ 0) (o 0) es ∧ TableOf a W T c.mem es) ∧
    (∃ w, WordAt d (σ 1) w ∧ w.length = W + a) ∧
    (∀ r : Fin 8, 2 ≤ r.val → r.val ≤ 4 → ∃ w, WordAt d (σ r) w ∧ w.length = W) ∧
    WordAt d (σ 5) (Nat.bits x.length) ∧
    (∀ r : Fin 8, 6 ≤ r.val → ∀ q : ℤ, d.workTapes (σ r) q = none) ∧
    d.output = if fn then c.out else []

/-- `Encodes`, as an equivalence with its definition. -/
theorem encodes_iff {K : ℕ} {S : Type} (a : ℕ) (fn : Bool) {x : List Bool} {W : ℕ}
    (T : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x) :
    Encodes a fn T c σ o d ↔
      (∀ j : Fin 8, d.workTapePos (σ j) = o j) ∧
      (∃ es, KeyTableAt d (σ 0) (o 0) es ∧ TableOf a W T c.mem es) ∧
      (∃ w, WordAt d (σ 1) w ∧ w.length = W + a) ∧
      (∀ r : Fin 8, 2 ≤ r.val → r.val ≤ 4 → ∃ w, WordAt d (σ r) w ∧ w.length = W) ∧
      WordAt d (σ 5) (Nat.bits x.length) ∧
      (∀ r : Fin 8, 6 ≤ r.val → ∀ q : ℤ, d.workTapes (σ r) q = none) ∧
      d.output = if fn then c.out else [] :=
  Iff.rfl

end WordRAM.Sim
