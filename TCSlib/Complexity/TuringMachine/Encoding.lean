/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.TMToPartrec
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.StateRenaming
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
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim).
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_effectiveMachineCode` — a concrete effective scheme exists.
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

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
private def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
private lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
private def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
private def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
private def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
private def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
private def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
private def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
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

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- Read a unary natural, stopping at its first false bit. -/
private def codeReadUnary : List Bool → Option (ℕ × List Bool)
  | false :: xs => some (0, xs)
  | true :: xs => (codeReadUnary xs).map fun p => (p.1 + 1, p.2)
  | [] => none

/-- The unary reader leaves an arbitrary suffix untouched. -/
private lemma codeReadUnary_append (n : ℕ) (xs : List Bool) :
    codeReadUnary (List.replicate n true ++ false :: xs) = some (n, xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, codeReadUnary] using
      congrArg (Option.map fun p : ℕ × List Bool => (p.1 + 1, p.2)) ih

/-- A unary index is accepted only when it belongs to the declared state space. -/
private def codeReadFin (n : ℕ) (xs : List Bool) : Option (Fin n × List Bool) := do
  let (i, rest) ← codeReadUnary xs
  if h : i < n then some (⟨i, h⟩, rest) else none

/-- Decode the fixed dictionary for a head movement. -/
private def codeReadSign : List Bool → Option (SignType × List Bool)
  | true :: true :: xs => some (.neg, xs)
  | false :: false :: xs => some (.zero, xs)
  | true :: false :: xs => some (.pos, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional output bit. -/
private def codeReadOutput : List Bool → Option (Option Bool × List Bool)
  | false :: false :: xs => some (none, xs)
  | true :: false :: xs => some (some false, xs)
  | true :: true :: xs => some (some true, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional work-tape write. -/
private def codeReadWrite : List Bool → Option (Option (Option Bool) × List Bool)
  | false :: false :: xs => some (none, xs)
  | false :: true :: xs => some (some none, xs)
  | true :: false :: xs => some (some (some false), xs)
  | true :: true :: xs => some (some (some true), xs)
  | _ => none

/-- Read the halt tag or a range-checked live successor state. -/
private def codeReadState (n : ℕ) : List Bool → Option (Option (Fin n) × List Bool)
  | false :: xs => some (none, xs)
  | true :: xs => (codeReadFin n xs).map fun p => (some p.1, p.2)
  | [] => none

/-- Read the five fields of a transition, failing as soon as any field fails. -/
private def codeReadAction (n : ℕ) (xs : List Bool) :
    Option (Action 1 Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, fun _ => (wr, wm), out, q⟩, xs)

/-- Read one entry for each tape symbol, in blank/false/true order. -/
private def codeReadSymbols {A : Type} (read : List Bool → Option (A × List Bool))
    (xs : List Bool) : Option ((Option Bool → A) × List Bool) := do
  let (a, xs) ← read xs
  let (b, xs) ← read xs
  let (c, xs) ← read xs
  pure ((fun s => match s with | none => a | some false => b | some true => c), xs)

/-- Read a fixed-size vector. Its caller checks the minimum total input length
before invoking it; a malformed field also aborts immediately. -/
private def codeReadVec {A : Type} (read : List Bool → Option (A × List Bool)) :
    (n : ℕ) → List Bool → Option ((Fin n → A) × List Bool)
  | 0, xs => some (Fin.elim0, xs)
  | n + 1, xs => do
    let (a, xs) ← read xs
    let (as, xs) ← codeReadVec read n xs
    pure (Fin.cases a as, xs)

/-- Interpret a least-significant-bit-first word. Canonical syntax is checked
separately, so this function also has a value on noncanonical words. -/
private def codeBitsNat (xs : List Bool) : ℕ := xs.foldr Nat.bit 0

/-- The fallback is the one-state, immediately halting, silent machine. -/
private def codeFallback : CodeTM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- Parse the exact serialization grammar of the phase-3 re-audit, Argument A.
The length guard precedes vector recursion: every state requires nine records,
each containing at least nine bits. The suffix must consist entirely of true bits. -/
private def codeParse (xs : List Bool) : Option CodeTM := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure ⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩
      else none

/-- Total decoding: every malformed string denotes the fixed fallback. -/
private def codeDecode (xs : List Bool) : CodeTM := (codeParse xs).getD codeFallback

/-- Reading an encoded bounded index is an exact prefix inverse. -/
private lemma codeReadFin_append {n : ℕ} (i : Fin n) (xs : List Bool) :
    codeReadFin n (unaryFin i ++ xs) = some (i, xs) := by
  simp [codeReadFin, unaryFin, List.append_assoc, codeReadUnary_append, i.isLt]

/-- Reading an encoded head movement is an exact prefix inverse. -/
private lemma codeReadSign_append (s : SignType) (xs : List Bool) :
    codeReadSign (signBits s ++ xs) = some (s, xs) := by
  cases s <;> rfl

/-- Reading an encoded optional output is an exact prefix inverse. -/
private lemma codeReadOutput_append (b : Option Bool) (xs : List Bool) :
    codeReadOutput (optBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

/-- Reading an encoded optional write is an exact prefix inverse. -/
private lemma codeReadWrite_append (b : Option (Option Bool)) (xs : List Bool) :
    codeReadWrite (optOptBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | (_ | b)
  · rfl
  · rfl
  · cases b <;> rfl

/-- Reading an encoded successor is an exact prefix inverse. -/
private lemma codeReadState_append {n : ℕ} (s : Option (Fin n)) (xs : List Bool) :
    codeReadState n (optStateBits s ++ xs) = some (s, xs) := by
  cases s with
  | none => rfl
  | some s => simp [optStateBits, codeReadState, codeReadFin_append]

/-- All five fields round-trip, including the unique work-tape coordinate. -/
private lemma codeReadAction_append {n : ℕ} (a : Action 1 Bool (Fin (n + 1)))
    (xs : List Bool) : codeReadAction n (actionBits a ++ xs) = some (a, xs) := by
  simp only [actionBits, List.append_assoc, codeReadAction, codeReadSign_append,
    codeReadWrite_append, codeReadOutput_append, codeReadState_append,
    bind, Option.bind, pure]
  congr 2
  cases a
  congr
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- Three prefix inverses assemble in the required blank/false/true order. -/
private lemma codeReadSymbols_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs))
    (f : Option Bool → A) (xs : List Bool) :
    codeReadSymbols read
      (([none, some false, some true] : List (Option Bool)).flatMap
        (fun s => write (f s)) ++ xs) = some (f, xs) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, codeReadSymbols, h, bind, Option.bind, pure]
  congr 2
  funext s
  rcases s with _ | b
  · rfl
  · cases b <;> rfl

/-- Fixed-size vector parsing is a prefix inverse of enumeration-order writing.
**Proof sketch.** Induct on the vector length. Read its first entry using the
supplied inverse, then its tail by induction. Finite-function extensionality
identifies the reconstructed head/tail function with the original vector.

**Proof sketch.** Induct on the vector length. The first field reader recovers the head and leaves the concatenated tail; the induction hypothesis recovers the remaining vector. Extensionality identifies the reconstructed function on bounded indices. -/
private lemma codeReadVec_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs)) :
    ∀ n (f : Fin n → A) xs,
      codeReadVec read n ((List.finRange n).flatMap (fun i => write (f i)) ++ xs) =
        some (f, xs) := by
  intro n
  induction n with
  | zero =>
    intro f xs
    simp only [List.finRange_zero, List.flatMap_nil, List.nil_append, codeReadVec]
    congr 2
    funext i
    exact i.elim0
  | succ n ih =>
    intro f xs
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      List.append_assoc, codeReadVec, h, bind, Option.bind, ih, pure]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Binary reconstruction inverts the canonical little-endian representation,
including the empty representation of zero. -/
private lemma codeBitsNat_bits (n : ℕ) : codeBitsNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [codeBitsNat]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simpa only [codeBitsNat, List.foldr_cons] using congrArg (Nat.bit b) ih

/-- Every record has eight fixed bits and a nonempty successor field. -/
private lemma codeAction_length {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    9 ≤ (actionBits a).length := by
  have hs (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have ho (b : Option Bool) : (optBoolBits b).length = 2 := by
    rcases b with _ | b
    · rfl
    · cases b <;> rfl
  have hw (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    rcases b with _ | (_ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  have hq : 1 ≤ (optStateBits a.state).length := by
    cases a.state <;> simp [optStateBits, unaryFin]
  simp only [actionBits, List.length_append, hs, ho, hw]
  omega

/-- Concatenating words with a common length lower bound preserves that bound. -/
private lemma codeFlatMap_length {A : Type} (xs : List A) (f : A → List Bool)
    (c : ℕ) (h : ∀ a ∈ xs, c ≤ (f a).length) :
    c * xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

/-- The complete table contains at least 81 bits per live state.

**Proof sketch.** Every action contains eight fixed field bits and at least one successor bit. Summing this lower bound over the three work symbols, three input symbols, and all states gives at least 81 bits per state. -/
private lemma codeTable_length (M : CodeTM) :
    81 * (M.numStates + 1) ≤
      ((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)).length := by
  have h := codeFlatMap_length (List.finRange (M.numStates + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)) 81 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (M.tm.tr q inp fun _ => w)) 27 (by
            intro inp _
            simpa using codeFlatMap_length
              ([none, some false, some true] : List (Option Bool))
              (fun w => actionBits (M.tm.tr q inp fun _ => w)) 9
              (fun _ _ => codeAction_length _))
      simpa using h)
  simpa using h

/-- The table reader recovers every transition. Blank/false/true exhaust each
read alphabet; a one-work-tape read vector is determined by its zero coordinate. -/
private lemma codeReadTable_append (M : CodeTM) (xs : List Bool) :
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadAction M.numStates)))
      (M.numStates + 1)
      (((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)) ++ xs) =
      some ((fun q inp w => M.tm.tr q inp (fun _ => w)), xs) :=
  codeReadVec_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadAction_append _ _) _ _) _ _ _

/-- The complete parser recovers a serialized machine under arbitrary true padding.
**Proof sketch.** The doubled header recovers the canonical binary count. The
minimum table-length lemma discharges the short-circuit guard. The unary initial
state and enumerated records then round-trip with the padding left untouched.
All remaining bits are true, and extensionality recovers the transition function.

**Proof sketch.** The doubled-bit parser first recovers the canonical state-count bits. The table length bound discharges the early guard; the field and vector inverse laws then recover the initial state and every transition. The remaining replicated true bits pass the suffix test. -/
private lemma codeParse_serialize_pad (M : CodeTM) (m : ℕ) :
    codeParse (M.serialize ++ List.replicate m true) = some M := by
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  unfold CodeTM.serialize
  rw [hp]
  unfold codeParse
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := codeTable_length M
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
    codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
    ite_self, ↓reduceIte, pure]
  congr 1
  cases M with
  | mk n tm =>
    congr 1
    cases tm with
    | mk q tr =>
      congr 1
      funext s inp w
      apply congrArg (tr s inp)
      funext i
      exact congrArg w (Subsingleton.elim _ _)

/-- The total decoder satisfies the required exact padded round-trip law. -/
private lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
    codeDecode (M.serialize ++ List.replicate m true) = M := by
  simp only [codeDecode, codeParse_serialize_pad, Option.getD_some]

/-- Successful unary parsing characterizes the exact consumed prefix.

**Proof sketch.** Induct on the input. A false bit terminates the number immediately; a true bit increments the recursively recovered number. Empty input cannot succeed. -/
private lemma codeReadUnary_sound (xs : List Bool) (n : ℕ) (rest : List Bool)
    (h : codeReadUnary xs = some (n, rest)) :
    xs = List.replicate n true ++ false :: rest := by
  induction xs generalizing n with
  | nil => simp [codeReadUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [codeReadUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadUnary xs with
      | none => simp [codeReadUnary, hr] at h
      | some p =>
        rcases p with ⟨k, tail⟩
        simp only [codeReadUnary, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [List.replicate_succ, ih k hr]

/-- Successful bounded-index parsing determines its complete unary prefix. -/
private lemma codeReadFin_sound {n : ℕ} (xs : List Bool) (i : Fin n) (rest : List Bool)
    (h : codeReadFin n xs = some (i, rest)) : xs = unaryFin i ++ rest := by
  obtain ⟨⟨j, tail⟩, hj, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [unaryFin, List.append_assoc] using codeReadUnary_sound xs j tail hj
  · contradiction

/-- A successful doubled header has exactly the paired form, including empty data.

**Proof sketch.** Induct by the same two-bit steps as the aligned parser. Equal bits extend the doubled prefix, the false/true separator ends it, and all incomplete or forbidden pairs are rejected. -/
private lemma codePairDecode_sound (xs a rest : List Bool)
    (h : pairDecode xs = some (a, rest)) : xs = pairEncode a rest := by
  induction xs using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode, h₁, h₂, h₃] at h

/-- A successful movement read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadSign_sound (xs : List Bool) (s : SignType) (rest : List Bool)
    (h : codeReadSign xs = some (s, rest)) : xs = signBits s ++ rest := by
  rcases xs with _ | ⟨b, _ | ⟨c, tail⟩⟩
  · simp [codeReadSign] at h
  · cases b <;> simp [codeReadSign] at h
  · cases b <;> cases c <;>
      simp only [codeReadSign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful output read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadOutput_sound (xs : List Bool) (b : Option Bool) (rest : List Bool)
    (h : codeReadOutput xs = some (b, rest)) : xs = optBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadOutput] at h
  · cases a <;> simp [codeReadOutput] at h
  · cases a <;> cases c <;>
      simp only [codeReadOutput, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful write read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadWrite_sound (xs : List Bool) (b : Option (Option Bool)) (rest : List Bool)
    (h : codeReadWrite xs = some (b, rest)) : xs = optOptBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadWrite] at h
  · cases a <;> simp [codeReadWrite] at h
  · cases a <;> cases c <;>
      simp only [codeReadWrite, Option.some.injEq, Prod.mk.injEq] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- A successful successor read consumes exactly its halt/live unary field.

**Proof sketch.** Split the leading tag. A false tag is exactly the halted state encoding; a true tag delegates to the soundness of the bounded unary reader. Empty input is rejected. -/
private lemma codeReadState_sound {n : ℕ} (xs : List Bool) (s : Option (Fin n))
    (rest : List Bool) (h : codeReadState n xs = some (s, rest)) :
    xs = optStateBits s ++ rest := by
  rcases xs with _ | ⟨b, tail⟩
  · simp [codeReadState] at h
  · cases b with
    | false =>
      simp only [codeReadState, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadFin n tail with
      | none => simp [codeReadState, hr] at h
      | some p =>
        rcases p with ⟨i, suffix⟩
        simp only [codeReadState, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [optStateBits, List.cons_append]
        exact congrArg (List.cons true) (codeReadFin_sound tail i suffix hr)

/-- Successful record parsing characterizes its complete serialized prefix.
**Proof sketch.** Decompose the five successful reads, apply the dictionary
inverse to each, and concatenate their consumed prefixes in order. -/
private lemma codeReadAction_sound {n : ℕ} (xs : List Bool)
    (a : Action 1 Bool (Fin (n + 1))) (rest : List Bool)
    (h : codeReadAction n xs = some (a, rest)) : xs = actionBits a ++ rest := by
  simp only [codeReadAction, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨wr, r₂⟩, h₂, ⟨⟨wm, r₃⟩, h₃,
    ⟨⟨out, r₄⟩, h₄, ⟨⟨q, r₅⟩, h₅, h⟩⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁, codeReadWrite_sound r₁ wr r₂ h₂,
    codeReadSign_sound r₂ wm r₃ h₃, codeReadOutput_sound r₃ out r₄ h₄,
    codeReadState_sound r₄ q r₅ h₅]
  simp [actionBits, List.append_assoc]

/-- Three sound prefix readers reconstruct the symbol-indexed row they consumed. -/
private lemma codeReadSymbols_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest)
    (xs : List Bool) (f : Option Bool → A) (rest : List Bool)
    (h : codeReadSymbols read xs = some (f, rest)) :
    xs = ([none, some false, some true] : List (Option Bool)).flatMap
      (fun s => write (f s)) ++ rest := by
  simp only [codeReadSymbols, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨b, r₂⟩, h₂, ⟨⟨c, r₃⟩, h₃, h⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [sound xs a r₁ h₁, sound r₁ b r₂ h₂, sound r₂ c r₃ h₃]
  simp [List.append_assoc]

/-- Sound vector parsing reconstructs the entire consumed enumeration.
**Proof sketch.** Induct on the requested vector length. The first successful
entry determines a prefix and the induction hypothesis determines the tail;
the finite-vector constructor enumerates them in exactly that order.

**Proof sketch.** Induct on the number of entries. Successful parsing splits into a successful head parse and a successful tail parse. Their soundness equations concatenate in the same order as the bounded-state enumeration. -/
private lemma codeReadVec_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest) :
    ∀ n xs (f : Fin n → A) rest, codeReadVec read n xs = some (f, rest) →
      xs = (List.finRange n).flatMap (fun i => write (f i)) ++ rest := by
  intro n
  induction n with
  | zero =>
    intro xs f rest h
    simpa only [codeReadVec, Option.some.injEq, Prod.mk.injEq,
      List.finRange_zero, List.flatMap_nil, List.nil_append] using
      (show xs = rest from congrArg Prod.snd (Option.some.inj h))
  | succ n ih =>
    intro xs f rest h
    simp only [codeReadVec, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨as, r₂⟩, h₂, h⟩⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [sound xs a r₁ h₁, ih r₁ as r₂ h₂]
    simp [List.finRange_succ, List.flatMap_map, List.append_assoc]

/-- An all-true suffix is exactly true padding of its own length. -/
private lemma codeAllTrue_eq (xs : List Bool) (h : xs.all id = true) :
    xs = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp at h
    | true =>
      simp only [List.all_cons, id_eq, Bool.true_and] at h
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih h)

/-- Acceptance characterizes a canonical serialization followed by true padding.
**Proof sketch.** Successful parsing fixes the count's canonical binary syntax,
the initial state, and every table record. Apply the soundness lemma for each
reader to reconstruct the consumed prefix; the final all-true test reconstructs
the padding. The one-work-tape read function is constant at its zero coordinate.

**Proof sketch.** Decompose a successful parse into its count, initial state, and table. Field soundness reconstructs each consumed prefix. The canonical-bits check fixes the count representation, and the final all-true check identifies the remainder as true padding. -/
private lemma codeParse_sound (xs : List Bool) (M : CodeTM)
    (h : codeParse xs = some M) :
    ∃ m, xs = M.serialize ++ List.replicate m true := by
  unfold codeParse at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq] at h
        subst M
        refine ⟨r₂.length, ?_⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable hpad
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq,
          htable, codeAllTrue_eq r₂ hpad]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        simp only [List.length_replicate]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- Erased readers keep only the unconsumed suffix. -/
private def codeSkipPair (valid : Bool → Bool → Bool) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun a ys => ys.casesOn none fun b zs => if valid a b then some zs else none

private def codeSkipFin (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  (codeReadUnary xs).bind fun p => if p.1 < n then some p.2 else none

private def codeSkipState (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun b ys => if b then codeSkipFin n ys else some ys

private def codeSkipAction (n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun _ _ => true) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs

private def codeSkipRepeat (r : List Bool → Option (List Bool)) : ℕ → List Bool → Option (List Bool)
  | 0, xs => some xs
  | n + 1, xs => (r xs).bind (codeSkipRepeat r n)

private lemma codeEraseFin (n : ℕ) (xs : List Bool) :
    (codeReadFin n xs).map Prod.snd = codeSkipFin n xs := by
  simp only [codeReadFin, codeSkipFin, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  split <;> rfl

private lemma codeEraseSign (xs : List Bool) :
    (codeReadSign xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseOutput (xs : List Bool) :
    (codeReadOutput xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseWrite (xs : List Bool) :
    (codeReadWrite xs).map Prod.snd = codeSkipPair (fun _ _ => true) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseState (n : ℕ) (xs : List Bool) :
    (codeReadState n xs).map Prod.snd = codeSkipState n xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b
    · rfl
    · simpa only [codeReadState, codeSkipState, ↓reduceIte,
        Option.map_map, Function.comp_def] using codeEraseFin n xs

private lemma codeErase_bind {A B : Type} (r : Option (A × List Bool))
    (f : List Bool → Option B) :
    r.bind (fun p => f p.2) = (r.map Prod.snd).bind f := by
  cases r <;> rfl

private lemma codeEraseAction (n : ℕ) (xs : List Bool) :
    (codeReadAction n xs).map Prod.snd = codeSkipAction n xs := by
  simp only [codeReadAction, codeSkipAction, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseWrite p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseSign p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

private lemma codeEraseSymbols {A : Type} (r : List Bool → Option (A × List Bool)) (xs : List Bool) :
    (codeReadSymbols r xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) 3 xs := by
  simp only [codeReadSymbols, bind, Option.map_bind, Function.comp_def, pure, Option.map_some,
    codeSkipRepeat, Option.bind_map]

private lemma codeEraseVec {A : Type} (r : List Bool → Option (A × List Bool)) (n : ℕ) :
    ∀ xs, (codeReadVec r n xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) n xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs
    simp only [codeReadVec, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
    have inner (p : A × List Bool) :
        (codeReadVec r n p.2).bind (fun q => some q.2) = codeSkipRepeat (fun s => (r s).map Prod.snd) n p.2 := by
      simpa only [Option.map_eq_bind, Function.comp_def] using ih p.2
    simp only [inner, codeErase_bind, codeSkipRepeat]

private def codeParseFull (xs : List Bool) : Option (CodeTM × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure (⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩, rest)
      else none

private def codeScan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1) rest
      if rest.all id then pure rest else none

private lemma codeParse_full (xs : List Bool) : codeParse xs = (codeParseFull xs).map Prod.fst := by
  simp only [codeParse, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  congr 1; funext q
  congr 1; funext t
  dsimp only
  split <;> rfl

private lemma codeScan_full (xs : List Bool) : codeScan xs = (codeParseFull xs).map Prod.snd := by
  simp only [codeScan, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool)
      (t : (Fin (codeBitsNat p.1 + 1) → Option Bool → Option Bool → Action 1 Bool (Fin (codeBitsNat p.1 + 1))) × List Bool) :
      (if t.2.all id then some ((⟨codeBitsNat p.1, ⟨q.1, fun s inp w => t.1 s inp (w 0)⟩⟩ : CodeTM), t.2) else none).map Prod.snd =
        (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadAction (codeBitsNat p.1))))
    (codeBitsNat p.1 + 1) q.2
  simp only [codeEraseSymbols, codeEraseAction] at ht
  rw [← ht, ← codeErase_bind]

/-- **Proof sketch.** Use the same decomposition as parser soundness, retaining the exact unconsumed suffix. The field soundness equations and the canonical count check reconstruct the original input as the machine serialization followed by that suffix. -/
private lemma codeParseFull_sound (xs : List Bool) (M : CodeTM) (tail : List Bool)
    (h : codeParseFull xs = some (M, tail)) : xs = M.serialize ++ tail := by
  unfold codeParseFull at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq, htable]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

private def codeCanonical (xs : List Bool) : List Bool :=
  (codeScan xs).casesOn codeFallback.serialize fun tail => xs.take (xs.length - tail.length)

private lemma codeCanonical_eq (xs : List Bool) : codeCanonical xs = (codeDecode xs).serialize := by
  unfold codeCanonical codeDecode
  rw [codeScan_full, codeParse_full]
  cases h : codeParseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [codeParseFull_sound xs M tail h]
    simp

private lemma codePrimUnary : Primrec codeReadUnary := by
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id (Primrec.const (none : Option (ℕ × List Bool)))
    (Primrec.to₂ (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.to₂ (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const 0) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    dsimp only [id, List.recOn] at ih ⊢
    cases b <;> simp [codeReadUnary, ih]

private lemma codePrimBit : Primrec₂ Nat.bit := by
  apply (Primrec.cond Primrec.fst
    (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
    (Primrec.nat_double.comp Primrec.snd)).of_eq
  intro p
  rcases p with ⟨b, n⟩
  cases b <;> simp [Nat.bit]

private lemma codePrimBitsNat : Primrec codeBitsNat :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

/-- **Proof sketch.** A list recursion stores the aligned-parser results for both the current suffix and its tail. Adding one input bit can therefore inspect the next bit and reuse the result two positions ahead. This realizes the two-bit recursion using primitive recursive list operations. -/
private lemma codePrimPair : Primrec pairDecode := by
  let step : Bool × List Bool × (Option (List Bool × List Bool) × Option (List Bool × List Bool)) →
      Option (List Bool × List Bool) × Option (List Bool × List Bool) := fun p =>
    ((p.2.1.head?).bind fun b =>
      bif p.1 == b then p.2.2.2.map (fun q => (p.1 :: q.1, q.2))
      else bif p.1 then none else some ([], p.2.1.tail), p.2.2.1)
  have hstep : Primrec step := by
    apply Primrec.pair
    · apply Primrec.option_bind (Primrec.list_head?.comp (Primrec.fst.comp Primrec.snd))
      change Primrec _
      apply Primrec.cond (Primrec.beq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      · apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        exact (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂
      · exact Primrec.cond (Primrec.fst.comp Primrec.fst) (Primrec.const none)
          (Primrec.option_some.comp (Primrec.pair (Primrec.const [])
            (Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))
    · exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id
    (Primrec.const (none, none)) (hstep.comp Primrec.snd).to₂
  have he (xs : List Bool) :
      List.recOn xs (none, none) (fun b xs ih => step (b, xs, ih)) =
        (pairDecode xs, pairDecode xs.tail) := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      dsimp only [List.recOn] at ih ⊢
      rw [ih]
      cases xs with
      | nil => cases b <;> rfl
      | cons a xs => cases b <;> cases a <;> rfl
  exact (Primrec.fst.comp h).of_eq fun xs => congrArg Prod.fst (he xs)

/-- **Proof sketch.** Use well-founded primitive recursion with the natural number itself as measure and its half as the sole recursive dependency. The zero case emits no bits; otherwise prepend the parity bit to the recursively computed bits of the half. -/
private lemma codePrimBits : Primrec Nat.bits := by
  let deps : ℕ → List ℕ := fun n => if n = 0 then [] else [n.div2]
  let step : ℕ → List (List Bool) → Option (List Bool) := fun n vals =>
    if n = 0 then some [] else vals.head?.map (fun xs => n.bodd :: xs)
  have hd : Primrec deps := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const []) (Primrec.list_cons.comp Primrec.nat_div2 (Primrec.const []))
  have hs : Primrec₂ step := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const (some [])) (Primrec.option_map (Primrec.list_head?.comp Primrec.snd)
      (Primrec.to₂ (Primrec.list_cons.comp (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
  apply Primrec.nat_omega_rec' Nat.bits (m := id) (l := deps) (g := step) Primrec.id hd hs
  · intro n a ha
    by_cases hn : n = 0
    · simp [deps, hn] at ha
    · simp only [deps, hn, ↓reduceIte, List.mem_singleton] at ha
      subst a
      exact Nat.binaryRec_decreasing hn
  · intro n
    by_cases hn : n = 0
    · simp [step, deps, hn]
    · have hb : n.div2 = 0 → n.bodd = true := by
        intro h
        have he := Nat.bit_bodd_div2 n
        rw [h] at he
        cases hh : n.bodd
        · simp [hh] at he
          exact (hn he.symm).elim
        · rfl
      simp only [deps, step, hn, ↓reduceIte, List.map_cons, List.map_nil, List.head?_cons, Option.map_some]
      congr 1
      exact (Nat.bits_append_bit n.div2 n.bodd hb).symm.trans (congrArg Nat.bits (Nat.bit_bodd_div2 n))

private lemma codePrimSkipPair (valid : Bool → Bool → Bool) : Primrec (codeSkipPair valid) := by
  have hi : Primrec₂ (fun p : Bool × List Bool => fun q : Bool × List Bool =>
      if valid p.1 q.1 then some q.2 else none) :=
    Primrec.ite (Primrec.eq.comp ((Primrec.dom_bool₂ valid).comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  have ho := Primrec.list_casesOn Primrec.snd (Primrec.const none) hi
  exact Primrec.list_casesOn Primrec.id (Primrec.const none) (ho.comp Primrec.snd).to₂

private lemma codePrimSkipFin : Primrec₂ codeSkipFin := by
  unfold codeSkipFin
  apply Primrec.option_bind (codePrimUnary.comp Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)

private lemma codePrimSkipState : Primrec₂ codeSkipState := by
  have h : Primrec₂ (fun p : ℕ × List Bool => fun q : Bool × List Bool =>
      if q.1 then codeSkipFin p.1 q.2 else some q.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
      (codePrimSkipFin.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_casesOn Primrec.snd (Primrec.const none) h

private lemma codePrimSkipAction : Primrec₂ codeSkipAction := by
  unfold codeSkipAction
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  exact codePrimSkipState.comp (Primrec.succ.comp
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd

private lemma codeSkipRepeat_iter (r : List Bool → Option (List Bool)) (n : ℕ) (xs : List Bool) :
    codeSkipRepeat r n xs = (fun o => o.bind r)^[n] (some xs) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [codeSkipRepeat, Function.iterate_succ_apply]
    cases h : r xs with
    | none =>
      simp only [Option.bind_none, Option.bind_some, h]
      clear ih xs h
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
    | some ys => simpa only [Option.bind_some, Option.bind_some, h] using ih ys

private lemma codePrimRepeat {A : Type} [Primcodable A]
    (r : A → List Bool → Option (List Bool)) (hr : Primrec₂ r)
    (count : A → ℕ) (hn : Primrec count) :
    Primrec₂ (fun a xs => codeSkipRepeat (r a) (count a) xs) := by
  have h := Primrec.nat_iterate (hn.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)
    (Primrec.option_bind Primrec.snd
      (hr.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂
  exact h.of_eq fun p => (codeSkipRepeat_iter (r p.1) (count p.1) p.2).symm

private lemma codePrimAll : Primrec (fun xs : List Bool => xs.all id) := by
  have h := Primrec.list_foldr (α := List Bool) (β := Bool) Primrec.id (Primrec.const true)
    ((Primrec.dom_bool₂ Bool.and).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun xs => by
    dsimp only [id]
    induction xs with
    | nil => rfl
    | cons b xs ih => simpa only [List.foldr_cons, List.all_cons, id_eq] using congrArg (fun z => b && z) ih

/-- **Proof sketch.** Compose primitive recursive readers, comparisons, and fixed-count iterations in the exact order of the erased parser. The canonical-count check and minimum-length check surround the state and record scans. The final branch accepts precisely an all-true suffix. -/
private lemma codePrimScan : Primrec codeScan := by
  unfold codeScan
  apply Primrec.option_bind codePrimPair
  change Primrec _
  apply Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
    (codePrimBits.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))).not)
    (Primrec.const none)
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const 81) (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))))
    (Primrec.const none)
  apply Primrec.option_bind (codePrimSkipFin.comp
    (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  change Primrec _
  have hr := codePrimRepeat _ (codePrimRepeat _ (codePrimRepeat _ codePrimSkipAction (fun _ => 3) (Primrec.const 3))
    (fun _ => 3) (Primrec.const 3)) (fun n => n + 1) Primrec.succ
  apply Primrec.option_bind (hr.comp
    (codePrimBitsNat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.eq.comp (codePrimAll.comp Primrec.snd) (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

private lemma codePrimDrop : Primrec₂ (fun xs : List Bool => fun n => xs.drop n) := by
  have h := Primrec.nat_iterate (α := List Bool × ℕ) (β := List Bool) Primrec.snd Primrec.fst (Primrec.list_tail.comp Primrec.snd).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨xs, n⟩
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases xs <;> simp

private lemma codePrimPrefix : Primrec₂ (fun xs : List Bool => fun n => xs.take (xs.length - n)) := by
  have h := Primrec.list_reverse.comp (codePrimDrop.comp (Primrec.list_reverse.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => by simp only [List.reverse_drop, List.reverse_reverse, List.length_reverse]

private lemma codePrimCanonical : Primrec codeCanonical :=
  Primrec.option_casesOn codePrimScan (Primrec.const codeFallback.serialize)
    (codePrimPrefix.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))


private abbrev BridgeAlphabet := Bool ⊕ PartrecToTM2.Γ'

private def bridgeIndex : PartrecToTM2.K' → Fin 4
  | .main => 0
  | .rev => 1
  | .aux => 2
  | .stack => 3

private def bridgeStack (xs : List PartrecToTM2.Γ') (z : ℤ) : Option BridgeAlphabet :=
  if 0 ≤ z + xs.length then (xs[(z + xs.length).toNat]?).map Sum.inr else none

private lemma bridgeStack_read (xs : List PartrecToTM2.Γ') :
    bridgeStack xs (-(xs.length : ℤ)) = xs.head?.map Sum.inr := by
  simp only [bridgeStack, neg_add_cancel, le_refl, if_pos, Int.toNat_zero]
  cases xs <;> rfl

private lemma bridgeStack_nil : bridgeStack [] = fun _ => none := by
  funext z
  simp [bridgeStack]

private lemma bridgeStack_push (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack xs) (-(xs.length : ℤ) - 1) (some (.inr a)) =
      bridgeStack (a :: xs) := by
  funext z
  by_cases hz : z = -(xs.length : ℤ) - 1
  · subst z
    simp [bridgeStack]
  · rw [Function.update_of_ne hz]
    by_cases h : 0 ≤ z + xs.length
    · have h' : 0 ≤ z + (a :: xs).length := by simp; omega
      have hi : (z + (a :: xs).length).toNat = (z + xs.length).toNat + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      simp only [bridgeStack, if_pos h, if_pos h', hi, List.getElem?_cons_succ]
    · have h' : ¬0 ≤ z + (a :: xs).length := by simp; omega
      simp only [bridgeStack, if_neg h, if_neg h']

private lemma bridgeStack_pop (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack (a :: xs)) (-((a :: xs).length : ℤ)) none =
      bridgeStack xs := by
  rw [← bridgeStack_push]
  have hi : -((a :: xs).length : ℤ) = -(xs.length : ℤ) - 1 := by simp; omega
  rw [hi, Function.update_idem]
  have hr : bridgeStack xs (-(xs.length : ℤ) - 1) = none := by
    have h : ¬0 ≤ -(xs.length : ℤ) - 1 + xs.length := by omega
    simp only [bridgeStack, if_neg h]
  rw [← hr, Function.update_eq_self]

private def bridgeKey : Fin 4 → PartrecToTM2.K' :=
  Fin.cases .main (Fin.cases .rev (Fin.cases .aux (fun _ => .stack)))

private lemma bridgeKey_index (k : PartrecToTM2.K') : bridgeKey (bridgeIndex k) = k := by
  cases k <;> rfl

private lemma bridgeIndex_key (i : Fin 4) : bridgeIndex (bridgeKey i) = i := by
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private inductive BridgeState (Q : Type)
  | scan | startCons | startBit | back
  | pushInput (b : Bool)
  | exec (q : Q) (v : Option PartrecToTM2.Γ')
  | push (q : Q) (v : Option PartrecToTM2.Γ')
  | emit (carry : Option Bool)
  deriving Fintype, DecidableEq

private noncomputable def bridgeSupp (c : ToPartrec.Code) :=
  TM2.stmts PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt)

private abbrev BridgeQ (c : ToPartrec.Code) := {q // q ∈ bridgeSupp c}

private def bridgeBit : Bool → PartrecToTM2.Γ'
  | false => .bit0
  | true => .bit1

private noncomputable def bridgeExec (c : ToPartrec.Code)
    (q : Option PartrecToTM2.Stmt') (v : Option PartrecToTM2.Γ') :
    Option (BridgeState (BridgeQ c)) := by
  classical
  exact if h : q ∈ bridgeSupp c then some (.exec ⟨q, h⟩ v) else none

private def bridgeIdle {Q : Type} (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun _ => (none, .zero), none, q⟩

private def bridgeOne {Q : Type} (k : Fin 4) (wr : Option (Option BridgeAlphabet))
    (d : SignType) (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun i => if i = k then (wr, d) else (none, .zero), none, q⟩

/-- A four-work-tape controller for Mathlib's proved partial-recursive compiler.
Each source stack occupies the negative cells ending at -1; its head points to the
stack top, and an empty stack has a blank head at zero. Source statements range
over the finite support of the selected program. Input bits live in the left
summand of the finite alphabet and stack symbols in the right summand. -/
private noncomputable def bridgeTM (c : ToPartrec.Code) : FinTM BridgeAlphabet := by
  classical
  exact {
    k := 4
    State := BridgeState (BridgeQ c)
    tm := {
      q₀ := .scan
      tr := fun q inp work =>
        match q with
        | .scan =>
          if inp.isSome then ⟨.pos, fun _ => (none, .zero), none, some .scan⟩
          else bridgeOne 0 none .neg (some .startCons)
        | .startCons => bridgeOne 0 (some (some (.inr .cons))) .neg (some .startBit)
        | .startBit => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr .bit1)), .zero) else (none, .zero), none, some .back⟩
        | .back => match inp with
          | some (.inl b) => bridgeOne 0 none .neg (some (.pushInput b))
          | _ => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        | .pushInput b => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr (bridgeBit b))), .zero) else (none, .zero), none, some .back⟩
        | .exec q v =>
          match q.val with
          | none => bridgeIdle (some (.emit none))
          | some stmt => match stmt with
            | .push k _ _ => bridgeOne (bridgeIndex k) none .neg (some (.push q v))
            | .peek k f tail => bridgeIdle (bridgeExec c (some tail) (f v ((work (bridgeIndex k)).bind Sum.getRight?)))
            | .pop k f tail =>
              let w := work (bridgeIndex k)
              bridgeOne (bridgeIndex k) (some none) (if w.isSome then .pos else .zero)
                (bridgeExec c (some tail) (f v (w.bind Sum.getRight?)))
            | .load f tail => bridgeIdle (bridgeExec c (some tail) (f v))
            | .branch f yes no => bridgeIdle (bridgeExec c (some (if f v then yes else no)) v)
            | .goto f => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (f v))) v)
            | .halt => bridgeIdle (bridgeExec c none v)
        | .push q v =>
          match q.val with
          | some (.push k f tail) =>
            bridgeOne (bridgeIndex k) (some (some (.inr (f v)))) .zero (bridgeExec c (some tail) v)
          | _ => bridgeIdle none
        | .emit carry =>
          match work 0 with
          | some (.inr .bit0) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some false))) with output := carry.map Sum.inl }
          | some (.inr .bit1) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some true))) with output := carry.map Sum.inl }
          | _ => bridgeIdle none } }

private def bridgeCfg (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    Cfg 4 BridgeAlphabet (BridgeState (BridgeQ c)) x :=
  ⟨q, p, fun i => bridgeStack (st (bridgeKey i)),
    fun i => -((st (bridgeKey i)).length : ℤ), out⟩

private lemma bridgeCfg_read (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeCfg c q p st out).workTapeSymbols (bridgeIndex k) =
      (st k).head?.map Sum.inr := by
  simp only [Cfg.workTapeSymbols, bridgeCfg, bridgeKey_index, bridgeStack_read]

private def bridgeReach {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a b : Cfg k A Q x) : Prop := ∃ t, M.runFrom a t = b

private lemma bridgeReach_refl {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a a := ⟨0, rfl⟩

private lemma bridgeReach_step {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a (M.step a) := ⟨1, rfl⟩

private lemma bridgeReach_trans {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) {a b d : Cfg k A Q x}
    (h : bridgeReach M a b) (h' : bridgeReach M b d) : bridgeReach M a d := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  exact ⟨s + t, by rw [MultiTapeTM.runFrom_add, hs, ht]⟩

private lemma bridgeCfg_idle (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeIdle q').apply (bridgeCfg c q p st out) = bridgeCfg c q' p st out := by
  apply Cfg.ext <;> simp [bridgeIdle, bridgeCfg]

/-- **Proof sketch.** On the selected tape, erasing the current top cell and moving right gives the representation of the tail stack. Other tapes and the input head stay fixed; configuration extensionality combines these field equations. -/
private lemma bridgeCfg_pop (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) :
    (bridgeOne (bridgeIndex k) (some none) .pos q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) out := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero p
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_pop xs a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs, SignType.pos_eq_one, SignType.coe_one, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** Move the selected work head one cell left, then write the pushed symbol. The stack representation lemma identifies the resulting tape with the extended stack. All other tapes and the input/output components are unchanged. -/
private lemma bridgeCfg_push (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') :
    (bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q').apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' p (Function.update st k (a :: st k)) out := by
  apply Cfg.ext
  · rfl
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_push (st k) a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one,
        SignType.zero_eq_zero, SignType.coe_zero, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      simp
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** For an empty stack the tape is blank, so the machine erases a blank and stays. For a nonempty stack, apply the pop configuration lemma. These two cases match the stack machine pop semantics. -/
private lemma bridgeCfg_pop_any (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeOne (bridgeIndex k) (some none)
      (if (st k).head?.isSome then .pos else .zero) q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k (st k).tail) out := by
  cases hs : st k with
  | nil =>
    have hu : Function.update st k [] = st := by rw [← hs, Function.update_eq_self]
    simp only [List.head?_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.tail_nil, hu]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext i
      by_cases hi : i = bridgeIndex k
      · subst i
        simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, hs,
          bridgeStack_nil]
        funext z
        simp
      · simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · funext i
      by_cases hi : i = bridgeIndex k <;> simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · simp [Action.apply, bridgeOne, bridgeCfg]
  | cons a xs =>
    simp only [List.head?_cons, Option.isSome_some, ↓reduceIte, List.tail_cons]
    exact bridgeCfg_pop c q q' p st out k a xs hs

private lemma bridgeExec_mem (c : ToPartrec.Code) (q : Option PartrecToTM2.Stmt')
    (v : Option PartrecToTM2.Γ') (h : q ∈ bridgeSupp c) :
    bridgeExec c q v = some (.exec ⟨q, h⟩ v) := by
  classical
  simp [bridgeExec, h]

private lemma bridge_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : BridgeState (BridgeQ c)) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeTM c).tm.step (bridgeCfg c (some q) p st out) =
      ((bridgeTM c).tm.tr q (bridgeCfg c (some q) p st out).inputSymbol
        (bridgeCfg c (some q) p st out).workTapeSymbols).apply
          (bridgeCfg c (some q) p st out) := rfl

private lemma bridge_sub (c : ToPartrec.Code) (q tail : PartrecToTM2.Stmt')
    (hq : some q ∈ bridgeSupp c) (h : tail ∈ TM2.stmts₁ q) :
    some tail ∈ bridgeSupp c := TM2.stmts_trans h hq

private lemma bridge_none (c : ToPartrec.Code) : none ∈ bridgeSupp c := by
  classical
  simp [bridgeSupp, TM2.stmts]

/-- **Proof sketch.** Induct on the stack-machine statement. Push uses two native transitions; pop, peek, and register load use one before continuing recursively. Branch executes its chosen substatement. Goto and halt update the control label directly. The finite support lemma ensures every recursive substatement remains an available native state. -/
private lemma bridge_statement (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet) (q : PartrecToTM2.Stmt') :
    ∀ (v : Option PartrecToTM2.Γ') (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
      (_hq : some q ∈ bridgeSupp c),
    bridgeReach (bridgeTM c).tm (bridgeCfg c (bridgeExec c (some q) v) p st out)
      (bridgeCfg c (bridgeExec c ((TM2.stepAux q v st).l.map PartrecToTM2.tr)
        (TM2.stepAux q v st).var) p (TM2.stepAux q v st).stk out) := by
  classical
  induction q with
  | push k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) v)
      p (Function.update st k (f v :: st k)) out) ?_ (ih v _ ht)
    refine ⟨2, ?_⟩
    rw [bridgeExec_mem c _ v hq, show 2 = 1 + 1 from rfl,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    change (bridgeTM c).tm.step
      ((bridgeOne (bridgeIndex k) none .neg (some (.push ⟨some (.push k f tail), hq⟩ v))).apply
        (bridgeCfg c (some (.exec ⟨some (.push k f tail), hq⟩ v)) p st out)) = _
    unfold MultiTapeTM.step
    dsimp only [Action.apply, bridgeTM]
    exact bridgeCfg_push c _ _ _ p st out k (f v)
  | peek k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p st out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    exact bridgeCfg_idle c _ _ p st out
  | pop k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p (Function.update st k (st k).tail) out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    simp only [Option.isSome_map]
    exact bridgeCfg_pop_any c _ _ p st out k
  | load f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v)) p st out)
      ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    exact bridgeCfg_idle c _ _ p st out
  | branch f yes no ihy ihn =>
    intro v st hq
    cases hv : f v with
    | false =>
      have ht := bridge_sub c _ no hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some no) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihn v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, Bool.false_eq_true, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
    | true =>
      have ht := bridge_sub c _ yes hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some yes) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihy v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
  | goto f =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_some]
    exact bridgeCfg_idle c _ _ p st out
  | halt =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_none]
    exact bridgeCfg_idle c _ _ p st out

private lemma bridge_label (c : ToPartrec.Code) (l : Option PartrecToTM2.Λ')
    (h : l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    l.map PartrecToTM2.tr ∈ bridgeSupp c := by
  classical
  cases l with
  | none => exact bridge_none c
  | some l =>
    have hl := Finset.some_mem_insertNone.mp h
    apply Finset.some_mem_insertNone.mpr
    exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_self⟩

/-- **Proof sketch.** Induct on finite reachability of the compiled stack machine. Its support theorem preserves membership in the finite label set. For each source step, the statement simulation supplies a finite native execution, and transitivity concatenates these executions. -/
private lemma bridge_simulate (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet)
    (a b : PartrecToTM2.Cfg') (h : TM2.Reaches PartrecToTM2.tr a b)
    (ha : a.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    b.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt) ∧
    bridgeReach (bridgeTM c).tm
      (bridgeCfg c (bridgeExec c (a.l.map PartrecToTM2.tr) a.var) p a.stk out)
      (bridgeCfg c (bridgeExec c (b.l.map PartrecToTM2.tr) b.var) p b.stk out) := by
  classical
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c .halt⟩
  have support := PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt
  induction h with
  | refl => exact ⟨ha, bridgeReach_refl _ _⟩
  | @tail b d h hd ih =>
    refine ⟨TM2.step_supports _ support hd ih.1, bridgeReach_trans _ ih.2 ?_⟩
    rcases b with ⟨l, v, st⟩
    cases l with
    | none => simp [TM2.step] at hd
    | some l =>
      simp only [TM2.step, Option.mem_def, Option.some.injEq] at hd
      subst d
      exact bridge_statement c p out (PartrecToTM2.tr l) v st (bridge_label c _ ih.1)

private def bridgeNumber (xs : List Bool) : ℕ := xs.foldr Nat.bit 1

private def bridgeWord (xs : List Bool) : List PartrecToTM2.Γ' :=
  xs.map bridgeBit ++ [.bit1, .cons]

private lemma bridgeNumber_pos (xs : List Bool) : 0 < bridgeNumber xs := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp only [bridgeNumber, List.foldr_cons, Nat.bit_val] at * <;> omega

/-- **Proof sketch.** Encode a bit string as its low-to-high bits followed by a high true sentinel. Induction on the string matches each binary numeral constructor with the corresponding stack symbol; positivity rules out the zero numeral case. Append the compiled list terminator. -/
private lemma bridgeWord_number (xs : List Bool) :
    PartrecToTM2.trList [bridgeNumber xs] = bridgeWord xs := by
  suffices h : PartrecToTM2.trNat (bridgeNumber xs) = xs.map bridgeBit ++ [.bit1] by
    simpa [PartrecToTM2.trList, bridgeWord, List.append_assoc] using
      congrArg (fun zs => zs ++ [PartrecToTM2.Γ'.cons]) h
  induction xs with
  | nil => simp [bridgeNumber, PartrecToTM2.trNat, PartrecToTM2.trNum,
      PartrecToTM2.trPosNum]
  | cons b xs ih =>
    have hp := bridgeNumber_pos xs
    cases hn : (bridgeNumber xs : Num) with
    | zero =>
      have hz := congrArg (fun n : Num => (n : ℕ)) hn
      simp only [Num.to_of_nat, Num.cast_zero] at hz
      change bridgeNumber xs = 0 at hz
      omega
    | pos n =>
      have hword : PartrecToTM2.trPosNum n = xs.map bridgeBit ++ [.bit1] := by
        simpa only [PartrecToTM2.trNat, hn, PartrecToTM2.trNum] using ih
      change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b (bridgeNumber xs))) = _
      rw [Num.ofNat'_bit, Num.ofNat'_eq, hn]
      cases b <;> simp [Num.bit0, Num.bit1, PartrecToTM2.trNum,
        PartrecToTM2.trPosNum, hword, bridgeBit]

private lemma bridgeCfg_push_input (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (d : SignType) :
    ({ bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q' with inputTape := d }).apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' (moveInputPos p d) (Function.update st k (a :: st k)) out := by
  have h := bridgeCfg_push c q qm q' p st out k a
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.output h

private def bridgeStore (xs : List PartrecToTM2.Γ') : PartrecToTM2.K' → List PartrecToTM2.Γ' :=
  PartrecToTM2.K'.elim xs [] [] []

private lemma bridgeStore_push (xs : List PartrecToTM2.Γ') (b : PartrecToTM2.Γ') :
    Function.update (bridgeStore xs) .main (b :: bridgeStore xs .main) = bridgeStore (b :: xs) := by
  funext k
  cases k <;> simp [bridgeStore, PartrecToTM2.K'.elim]

/-- **Proof sketch.** Induct on the input head position while scanning backward. Each bit is pushed onto the main stack in two steps, extending the already loaded suffix. At the left endmarker the complete word is present and execution enters the compiled program. -/
private lemma bridge_back (c : ToPartrec.Code) (x : List Bool) :
    ∀ j (hj : j ≤ x.length),
    bridgeReach (bridgeTM c).tm
      (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j, by simp; omega⟩
        (bridgeStore (bridgeWord (x.drop j))) [])
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨0, by simp⟩
      (bridgeStore (bridgeWord (x.drop 0))) []).inputSymbol = none := by
      simp [bridgeCfg, Cfg.inputSymbol]
    rw [hi]
    simp only [bridgeTM, List.drop_zero]
    rw [bridgeCfg_idle]
    congr 1
  | succ j ih =>
    intro hj
    apply bridgeReach_trans _ (b := bridgeCfg (x := x.map Sum.inl) c (some .back)
      ⟨j, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop j))) []) ?_ (ih (by omega))
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
      (bridgeStore (bridgeWord (x.drop (j + 1)))) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .back)
        ⟨j + 1, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop (j + 1)))) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM]
    change ({ bridgeOne (bridgeIndex .main) (some (some (.inr (bridgeBit x[j]))))
      .zero (some (BridgeState.back : BridgeState (BridgeQ c))) with inputTape := .neg }).apply
        ((bridgeOne (bridgeIndex .main) none .neg (some (BridgeState.pushInput (Q := BridgeQ c) x[j]))).apply
          (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
            (bridgeStore (bridgeWord (x.drop (j + 1)))) [])) = _
    rw [bridgeCfg_push_input]
    simp only [bridgeStore_push]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    have hw : bridgeBit x[j] :: bridgeWord (x.drop (j + 1)) = bridgeWord (x.drop j) := by
      rw [List.drop_eq_getElem_cons (by omega : j < x.length)]
      rfl
    rw [hw]
    apply Cfg.ext
    · rfl
    · apply Fin.ext; simp
    · rfl
    · rfl
    · rfl

private lemma bridgeStore_nil : bridgeStore [] = fun _ => [] := by
  funext k
  cases k <;> rfl

private lemma bridgeStore_at (xs : List PartrecToTM2.Γ') (i : Fin 4) :
    bridgeStore xs (bridgeKey i) = if i = 0 then xs else [] := by
  by_cases hi : i = 0
  · subst i; rfl
  · have hk : bridgeKey i ≠ .main := by
      intro h
      apply hi
      rw [← bridgeIndex_key i, h]
      rfl
    cases h : bridgeKey i <;> simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk, h] at *

/-- **Proof sketch.** Induct on the number of input symbols passed. Before the right endmarker every symbol is nonblank, so the controller moves right without changing any work tape or output. -/
private lemma bridge_scan (c : ToPartrec.Code) (x : List Bool) : ∀ j (hj : j ≤ x.length),
    (bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg (x.map Sum.inl)) j =
      bridgeCfg c (some .scan) ⟨j + 1, by simp; omega⟩ (bridgeStore []) [] := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Cfg.ext <;> simp [MultiTapeTM.runFrom, bridgeTM, bridgeCfg, bridgeStore_nil,
      bridgeStack_nil, MultiTapeTM.initCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨j + 1, by simp; omega⟩
      (bridgeStore []) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .scan)
        ⟨j + 1, by simp; omega⟩ (bridgeStore []) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM, Option.isSome_some, ↓reduceIte]
    apply Cfg.ext
    · rfl
    · change moveInputPos ⟨j + 1, _⟩ .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
      rfl
    · rfl
    · funext i; simp [Action.apply, bridgeCfg]
    · rfl

/-- **Proof sketch.** At the right endmarker, three transitions create the list terminator and high true sentinel on the main tape, then move the input head left. Extensionality verifies the empty stacks on the other tapes and the exact two-cell main stack. -/
private lemma bridge_seed (c : ToPartrec.Code) (x : List Bool) :
    (bridgeTM c).tm.runFrom
      (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩ (bridgeStore []) []) 3 =
      bridgeCfg c (some .back) ⟨x.length, by simp⟩ (bridgeStore [.bit1, .cons]) [] := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
  have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩
    (bridgeStore []) []).inputSymbol = none := by
    simp [bridgeCfg, Cfg.inputSymbol, Fin.ext_iff]
  rw [hi]
  simp only [bridgeTM, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  unfold MultiTapeTM.step
  dsimp only [Action.apply, bridgeOne, bridgeTM]
  apply Cfg.ext
  · rfl
  · simp only [Action.apply, bridgeCfg, bridgeOne, SignType.zero_eq_zero,
      moveInputPos_zero]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    apply Fin.ext
    simp
  · funext i
    by_cases hi : i = 0
    · subst i
      simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero,
        neg_zero, SignType.zero_eq_zero, SignType.coe_zero, SignType.neg_eq_neg_one,
        SignType.coe_neg_one, zero_add]
      change Function.update (Function.update (bridgeStack []) (-1) (some (.inr .cons)))
        (-2) (some (.inr .bit1)) = bridgeStack [.bit1, .cons]
      rw [show (-1 : ℤ) = -(([] : List PartrecToTM2.Γ').length : ℤ) - 1 from rfl,
        bridgeStack_push, show (-2 : ℤ) = -(([PartrecToTM2.Γ'.cons]).length : ℤ) - 1 from rfl,
        bridgeStack_push]
    · simp [bridgeCfg, bridgeStore_at, hi]
  · funext i
    by_cases hi : i = 0 <;> simp [bridgeCfg, bridgeStore_at, hi]
  · rfl

private lemma bridge_start (c : ToPartrec.Code) (x : List Bool) :
    bridgeReach (bridgeTM c).tm ((bridgeTM c).tm.initCfg (x.map Sum.inl))
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  apply bridgeReach_trans _ ⟨x.length, bridge_scan c x _ (le_refl _)⟩
  apply bridgeReach_trans _ ⟨3, bridge_seed c x⟩
  simpa only [List.drop_length, bridgeWord, List.map_nil, List.nil_append] using
    bridge_back c x x.length (le_refl _)

private lemma bridgeCfg_pop_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) (e : Option BridgeAlphabet) :
    ({ bridgeOne (bridgeIndex k) (some none) .pos q' with output := e }).apply
      (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) (out ++ e.toList) := by
  have h := bridgeCfg_pop c q q' p st out k a xs hs
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · exact moveInputPos_zero p
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · rfl

private lemma bridge_emit_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
    (out : List BridgeAlphabet) (carry : Option Bool) (b : Bool)
    (xs : List PartrecToTM2.Γ') (hs : st .main = bridgeBit b :: xs) :
    (bridgeTM c).tm.step (bridgeCfg c (some (.emit carry)) p st out) =
      bridgeCfg c (some (.emit (some b))) p (Function.update st .main xs)
        (out ++ carry.toList.map Sum.inl) := by
  rw [bridge_step]
  have hr := bridgeCfg_read c (some (.emit carry)) p st out .main
  rw [hs] at hr
  change (bridgeCfg c (some (.emit carry)) p st out).workTapeSymbols 0 = some (.inr (bridgeBit b)) at hr
  cases b <;> simp only [bridgeTM, hr, bridgeBit]
  all_goals
    simpa only [Option.toList_map] using bridgeCfg_pop_emit c (some (.emit carry)) _ p st out
      .main _ xs hs (carry.map Sum.inl)

/-- **Proof sketch.** Induct on the output bit string. The controller keeps one pending bit and emits the previous bit while advancing, so the last pending high sentinel is discarded at the list terminator. The empty-string case still consumes the sentinel and terminator without emitting a bit. -/
private lemma bridge_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (xs : List Bool) :
    ∀ (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) (carry : Option Bool),
    st .main = bridgeWord xs →
    bridgeReach (bridgeTM c).tm (bridgeCfg c (some (.emit carry)) p st out)
      (bridgeCfg c none p (Function.update st .main [.cons])
        (out ++ carry.toList.map Sum.inl ++ xs.map Sum.inl)) := by
  induction xs with
  | nil =>
    intro st out carry hs
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_emit_step c p st out carry true [.cons] hs, bridge_step]
    have hr := bridgeCfg_read c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl) .main
    simp only [Function.update_self, List.head?_cons, Option.map_some] at hr
    change (bridgeCfg c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl)).workTapeSymbols 0 = some (.inr .cons) at hr
    simp only [bridgeTM, hr, List.map_nil, List.append_nil]
    exact bridgeCfg_idle c _ none p (Function.update st .main [.cons]) _
  | cons b xs ih =>
    intro st out carry hs
    have hs' : st .main = bridgeBit b :: bridgeWord xs := hs
    apply bridgeReach_trans _ (b := bridgeCfg c (some (.emit (some b))) p
      (Function.update st .main (bridgeWord xs)) (out ++ carry.toList.map Sum.inl))
    · exact ⟨1, by simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] using
        bridge_emit_step c p st out carry b (bridgeWord xs) hs'⟩
    · have h := ih (Function.update st .main (bridgeWord xs))
        (out ++ carry.toList.map Sum.inl) (some b) (Function.update_self _ _ _)
      simp only [Function.update_idem, Option.toList_some, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] at h
      simpa only [List.map_cons, List.append_assoc] using h

/-- **Proof sketch.** The proved partial-recursive compiler gives a terminating stack-machine execution with the specified result. Load the sentinel-coded input, simulate that finite execution, then emit its result with the sentinel removed. The resulting halted native configuration has exactly the requested output. -/
private lemma bridge_compiles (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) (x : List Bool) :
    ∃ t, (bridgeTM c).ComputesInTime (x.map Sum.inl) ((f x).map Sum.inl) t := by
  classical
  have he := PartrecToTM2.tr_eval c [bridgeNumber x]
  rw [hc x] at he
  have hm : PartrecToTM2.halt [bridgeNumber (f x)] ∈
      Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c [bridgeNumber x]) := by
    rw [he]
    simp
  have hr := (Turing.mem_eval.mp hm).1
  have ha : (PartrecToTM2.init c [bridgeNumber x]).l ∈
      Finset.insertNone (PartrecToTM2.codeSupp c .halt) := by
    apply Finset.some_mem_insertNone.mpr
    exact PartrecToTM2.codeSupp_self _ _ (PartrecToTM2.trStmts₁_self _)
  have hs := (bridge_simulate c (x := x.map Sum.inl) 0 [] _ _ hr ha).2
  simp only [PartrecToTM2.init, PartrecToTM2.halt, Option.map_some, Option.map_none,
    bridgeWord_number, bridgeExec_mem c none none (bridge_none c)] at hs
  have hstart := bridge_start c x
  have hem : bridgeReach (bridgeTM c).tm
      (bridgeCfg c (some (.exec ⟨none, bridge_none c⟩ none)) (x := x.map Sum.inl) 0
        (bridgeStore (bridgeWord (f x))) [])
      (bridgeCfg c (some (.emit none)) 0 (bridgeStore (bridgeWord (f x))) []) := by
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    exact bridgeCfg_idle c _ _ _ _ _
  have hf := bridge_emit c (x := x.map Sum.inl) 0 (f x)
    (bridgeStore (bridgeWord (f x))) [] none rfl
  have hall := bridgeReach_trans _ hstart (bridgeReach_trans _ hs (bridgeReach_trans _ hem hf))
  obtain ⟨t, ht⟩ := hall
  refine ⟨t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
  change ((bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg _) t).state = none ∧ _
  rw [ht]
  exact ⟨rfl, rfl⟩

private lemma bridge_binary (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  classical
  choose t ht using bridge_compiles c f hc
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Bool n)).sup fun x => t x.val
  have hT : (bridgeTM c).ComputesFunInTimeVia ⟨Sum.inl, Sum.inl_injective⟩ f T := by
    intro x
    exact (ht x).mono (Finset.le_sup (f := fun y : List.Vector Bool x.length => t y.val)
      (Finset.mem_univ (α := List.Vector Bool x.length) ⟨x, rfl⟩))
  obtain ⟨a, M, _, hM⟩ := FinTM.alphabet_reduction ⟨Sum.inl, Sum.inl_injective⟩ (bridgeTM c) f T hT
  exact ⟨M, _, hM⟩


private lemma bridgeNumber_bits (xs : List Bool) : (bridgeNumber xs).bits = xs ++ [true] := by
  induction xs with
  | nil => exact Nat.one_bits
  | cons b xs ih =>
    change (Nat.bit b (bridgeNumber xs)).bits = (b :: xs) ++ [true]
    rw [Nat.bits_append_bit _ _ (fun h => (Nat.ne_of_gt (bridgeNumber_pos xs) h).elim), ih]
    rfl

private def bridgeUnnumber (n : ℕ) : List Bool := n.bits.reverse.tail.reverse

private lemma bridgeUnnumber_number (xs : List Bool) : bridgeUnnumber (bridgeNumber xs) = xs := by
  simp [bridgeUnnumber, bridgeNumber_bits]

private lemma bridgePrimNumber : Primrec bridgeNumber :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

private lemma bridgePrimUnnumber : Primrec bridgeUnnumber :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp codePrimBits))

/-- A primitive recursive string operation has an actual finite binary machine.
The sentinel number code preserves trailing false bits and the empty word. -/
private lemma codePrim_machine (f : List Bool → List Bool) (hf : Primrec f) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  have hn := bridgePrimNumber.comp (hf.comp (bridgePrimUnnumber.comp
    (Primrec.vector_head (n := 0))))
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.of_prim hn)
  apply bridge_binary c f
  intro x
  have hx := hc (List.Vector.ofFn (fun _ : Fin 1 => bridgeNumber x))
  simpa [List.Vector.ofFn, bridgeUnnumber_number] using hx

/-- The verified suffix scanner computes exactly the fixed serialization of decode. -/
private lemma codeCanonical_machine :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun xs => (codeDecode xs).serialize) T := by
  have he : codeCanonical = fun xs => (codeDecode xs).serialize := funext codeCanonical_eq
  rw [← he]
  exact codePrim_machine codeCanonical codePrimCanonical

/-- A concrete effective representation scheme exists.

**Proof sketch.** Take `encode := CodeTM.serialize` — which records the state count,
the initial state, and the table (finding 5) — and let `decode` run the aligned-pair
parser of `pairEncode_injective` on the doubled-bit region to recover `numStates`,
then parse the unary initial state and the `9 · (numStates + 1)` fixed-format records;
any malformation (including trailing non-`true` junk) yields a canonical trivial
machine, making `decode` total. The parser **short-circuits on the first incomplete
record** (equivalently, rejects up front any state count whose minimum table length
exceeds the remaining input), so a short malformed string declaring a huge binary
state count is rejected in time polynomial in the string, not by enumerating its
missing records (round-2 audit, finding 8). A complete serialization determines its own length,
and the parser ignores a trailing all-`true` suffix, giving `decode_encode_pad`. The
`canonizer` is a machine implementing exactly this parse followed by re-serialization
(on valid codes, the identity up to padding removal; on invalid ones, the trivial
machine's serialization), with a polynomial `canonizerTime`; its construction uses
the composition combinators of `TCSlib.Complexity.TuringMachine.Composition`.

**Epoch 3 implementation note.** The parser and erased suffix scanner implement
the grammar above, including the up-front minimum-length guard. For the canonizer,
this implementation takes the brief's arbitrary-time route: it proves the scanner
and prefix operation primitive recursive, uses Mathlib's proved partial-recursive
to stack-machine compiler, and supplies a private simulation by an actual finite
four-work-tape machine. A sentinel number encoding preserves empty strings and
trailing false bits. The proved alphabet-reduction theorem then gives a binary
machine. A finite maximum of the individual halting times at each input length
supplies the bound; no polynomial claim is made for this implementation. This
replaces the suggested composition-based implementation, not the fixed
serialization or its effectivity contract. No universal-machine admission is used. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  obtain ⟨M, T, h⟩ := codeCanonical_machine
  exact ⟨{
    encode := CodeTM.serialize
    decode := codeDecode
    decode_encode_pad := codeDecode_serialize_pad
    canonizer := M
    canonizerTime := T
    canonizer_computes := h }⟩

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing
