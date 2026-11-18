/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.InputBit
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: one phase per instruction

The simulating machine runs one phase for each instruction it executes. A phase is a machine on
the eight tapes of `WordRAM.Sim.Encodes`: from tapes encoding a configuration `c` whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep … c`, and its exit
tells the host where the program goes next. The host (a phase host over the program's positions)
and the induction over a run are built from these phases.

Every phase is a nondeterministic machine whose two transitions agree everywhere except at the
entry of a `coin` phase, where the choice is the coin. Fixing the choice gives a deterministic
machine (`Turing.NDTM.fixChoice`), and the phase's run is stated for each fixed choice; the
deterministic simulation fixes it to `false`, so that coins read `0`.

## Main definitions

* `WordRAM.Sim.isCoin`, `WordRAM.Sim.isVerdict`, `WordRAM.Sim.jumpTarget`.

## Main results

* `WordRAM.Sim.exists_phase`: the phase of an instruction other than `accept` and `reject`.
* `WordRAM.Sim.exists_verdictPhase`: the phase of `accept` and `reject`, which writes the output
  and halts.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2: nondeterministic machines.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- Whether an instruction is a `coin`. -/
def isCoin : XInstr → Bool
  | .coin _ => true
  | _ => false

/-- Whether an instruction is a `coin`, as an equation. -/
theorem isCoin_def (ins : XInstr) :
    isCoin ins = match ins with
      | .coin _ => true
      | _ => false := by
  cases ins <;> rfl

/-- Whether an instruction gives a verdict: `accept` or `reject`. -/
def isVerdict : XInstr → Bool
  | .base .accept => true
  | .base .reject => true
  | _ => false

/-- Whether an instruction gives a verdict, as an equation. -/
theorem isVerdict_def (ins : XInstr) :
    isVerdict ins = match ins with
      | .base .accept => true
      | .base .reject => true
      | _ => false := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- The position a taken jump goes to: the label of `bltz`, and `0` for any other instruction
(which never jumps). -/
def jumpTarget : XInstr → ℕ
  | .base (.bltz _ l) => l
  | _ => 0

/-- The position a taken jump goes to, as an equation. -/
theorem jumpTarget_def (ins : XInstr) :
    jumpTarget ins = match ins with
      | .base (.bltz _ l) => l
      | _ => 0 := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **The phase of an instruction.** For `a`, an output mode `fn` and an instruction `ins` that is
not a verdict and whose addresses are below `2^(a-1)` in absolute value, there is a
nondeterministic machine `N` on eight tapes, with an entry and two exits `next` and `jump`, and a
constant `C`, such that:
* the entry is never re-entered, and the two transitions of `N` agree at every state except the
  entry, and at the entry too unless `ins` is a `coin`;
* for each choice `b`: whenever the instruction at `c.pc` of a program `P` is `ins` (and, for a
  `coin`, the coin `ρ.getD c.rd false` is `b`), and `d`, at the entry, encodes `c` over the cells
  `T` with origins `o`, then `xstep P x ρ c` is a configuration `c'`, and the machine with the
  choice fixed to `b` reaches, within `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
  `C·((|T| + 1)·(W + 1) + log |x| + 1)`, a configuration `d'` encoding `c'` over the cells
  `T ∪ touches` with the same origins, at `next` if the program goes on to `c.pc + 1` and at
  `jump` if it jumps to `jumpTarget ins`.

[AB09, Exercise 1.9; §2.1.2]

**Proof sketch.** By cases on `ins`, each phase a sequence of the rows of
`Build/WordArith`, `Build/KeyTable` and `Build/InputBit`, placed on the eight tapes by
`Turing.embedEmitTM` and composed by `Turing.Contract.ofReaches` and `Turing.Contract.seq`:
* an address `i` written in `ins` is written as a key on tape `1` (`Turing.exists_wordIntTM`
  with `c = i`); a computed address `[j]` is looked up into a register and sign-extended into tape
  `1` (`Turing.exists_wordSignExtendTM`);
* operands are looked up into registers `2` and `3` (`Turing.exists_keyLookupTM`), the result is
  computed into register `4` by the arithmetic rows (`one`, `add`, `sub`, `mul`, `half`), read
  from the input (`rdIn`, `Turing.exists_inputBitTM`) or written from the coin (`coin`: one
  choice step, then `Turing.exists_wordIntTM` with `c = 0` or `1`), and stored back
  (`Turing.exists_keyAssignTM`);
* `bltz` looks up its cell and branches on `Turing.exists_wordSignTM`; `emit` looks up its cell,
  tests it with `Turing.exists_wordNonzeroTM`, and in function mode emits the bit.
The table stays a `TableOf` because every key written is that of a cell of `T ∪ touches` in
range (`ImmBound`; a word's signed value is in range), and keys of cells in range are distinct.
The table has at most `|T|` entries of `O(W + a)` cells, which gives the bounds; the seek adds
`O(|x|)` steps and the multiplication `O(W²)`. -/
theorem exists_phase (a : ℕ) (fn : Bool) (ins : XInstr) (hins : ImmBound a ins)
    (hv : isVerdict ins = false) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : NDTM 8 Bool S) (entry next jump : S)
      (C : ℕ), next ≠ jump ∧
      (∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry) ∧
      (∀ q : S, q ≠ entry ∨ isCoin ins = false → N.tr false q = N.tr true q) ∧
      ∀ (b : Bool) {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool) (T : Finset ℤ)
        (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x),
        P.getD c.pc (.base .reject) = ins → (isCoin ins = true → ρ.getD c.rd false = b) →
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ (c' : XCfg W) (d' : Turing.Cfg 8 Bool S x), xstep P x ρ c = .inl c' ∧
          Encodes a fn (T ∪ ins.touches c.mem) c' (Function.Embedding.refl _) o d' ∧
          ((d'.state = some next ∧ c'.pc = c.pc + 1) ∨
            (d'.state = some jump ∧ c'.pc = jumpTarget ins)) ∧
          ReachesWithin (N.fixChoice b) d {some next, some jump}
            (C * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1))
            (C * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1)) d' := by
  sorry

/-- **The phase of a verdict.** For an output mode `fn` and a verdict `v`, there is a deterministic
machine on eight tapes, with an entry, and a constant `C`, such that from tapes at the entry
encoding `c`, the machine halts within `C` steps with the output `c.out` in function mode and
`[v]` in verdict mode, every head fixed. [AB09, Exercise 1.9]

**Proof sketch.** One step: in verdict mode emit `v` (the output was empty, `Encodes`), and halt.
-/
theorem exists_verdictPhase (fn v : Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 8 Bool S) (entry : S)
      (C : ℕ),
      ∀ (a : ℕ) {x : List Bool} {W : ℕ} (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
        (d : Turing.Cfg 8 Bool S x),
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ t ≤ C, (M.runFrom d t).state = none ∧
          (M.runFrom d t).output = (if fn then c.out else [v]) ∧
          ∀ s ≤ t, (M.runFrom d s).workTapePos = d.workTapePos := by
  sorry

end WordRAM.Sim
