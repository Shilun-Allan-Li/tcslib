/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), the specification `MachineCode` of a representation scheme with
[AB09]'s two properties, and the self-delimiting input pairing used by the universal
machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation ("the list of all inputs and outputs of the
  transition function") and standing conventions. We specify the representation
  *abstractly* as a `MachineCode` structure carrying exactly the properties the
  development uses, state the universal machine relative to an arbitrary `MachineCode`
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation (`exists_machineCode`). This keeps every
  downstream theorem independent of encoding details.
* Property (2) is stated as invariance under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "representations ending with
  arbitrarily many 1s are ignored" convention. We do not demand that padding be
  ignored on *arbitrary* strings — appending `true`s to an invalid code may complete
  it — only on codes, which suffices for infinitely many representations per machine.
* Totality of `decode` (property (1)) is enforced by its type: invalid strings decode
  to whatever canonical machine the scheme chooses [AB09, §1.4, property 1].

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`.
* `Turing.pairEncode` — self-delimiting pairing of an input with a code.
* `Turing.MachineCode` — a representation scheme with [AB09, §1.4]'s properties.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.exists_machineCode` — a concrete scheme exists.
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the first string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Used as
the universal machine's input convention `⟨x, α⟩` [AB09, §1.4]. -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- A representation scheme for coded machines [AB09, §1.4]: a total decoding (every
string represents some machine — property 1), an encoding, and recovery of the
machine from its code under arbitrary `true`-padding (hence every machine has
infinitely many representations — property 2). -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- A concrete representation scheme exists.

**Proof sketch.** Encode `numStates` in self-delimiting doubled-bit form (as in
`pairEncode`), then the transition table as a sequence of fixed-width records: the
domain `Fin (numStates + 1) × Option Bool × Option Bool` is enumerated canonically,
and each `Action 1 Bool (Fin (numStates + 1))` value is serialized with fixed-width
binary fields (head move, optional write, optional output, optional successor state).
`decode` parses this format and returns the machine; on any parse failure — including
extra non-`true` material after a complete table — it returns a canonical trivial
machine, making it total. Because the parse consumes a self-delimited prefix of
determined length and ignores a trailing all-`true` suffix, appending `true`-padding
to a valid code does not change the parse, giving `decode_encode_pad`. -/
theorem exists_machineCode : Nonempty MachineCode := by
  sorry

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  sorry

end Turing
