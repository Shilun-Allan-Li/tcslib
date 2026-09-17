/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
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
identifies the reconstructed head/tail function with the original vector. -/
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

/-- The complete table contains at least 81 bits per live state. -/
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
All remaining bits are true, and extensionality recovers the transition function. -/
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

/-- Successful unary parsing characterizes the exact consumed prefix. -/
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

/-- A successful doubled header has exactly the paired form, including empty data. -/
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

/-- A successful successor read consumes exactly its halt/live unary field. -/
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
the finite-vector constructor enumerates them in exactly that order. -/
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
the padding. The one-work-tape read function is constant at its zero coordinate. -/
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
the composition combinators of `TCSlib.Complexity.TuringMachine.Composition`. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  sorry

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
