/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.VirtualInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The uniform code simulator

One format-parameterized simulator for deterministic machine codes: on
`⟨⟨bits t, α⟩, x⟩` it decides whether the machine that `α` denotes halts on `x`
with output exactly `[true]` within `t` steps, in time **one polynomial in
`|α| + |x| + t + 1` jointly**. The parameter is a `Turing.MachineFormat`: a
`Turing.CodeFormat` (12.2c item 8's parse layer) whose codes denote `k`-work-tape
binary machines in the fixed `k`-record serialization. The one-work-tape codes
(`Turing.oneTapeMachineFormat`) and the two-work-tape codes of `Codes2Tape` are
instances; they supply `Turing.exists_uniformMachineCode` (`Diagonalization/EXPCOM`)
and `Turing.exists_uniformMachineCode2` (`Codes2Tape`). [AB09, §1.4.1, Theorem 1.9;
the uniform form required by Example 3.6(3), audited at phase P3.2 round 2]

## Design

* **One interpreter, parameterized by the record grammar.** The table of a
  `k`-tape code is `3^(k+1)` `Turing.actionBitsK` records per state
  (`Turing.tableBitsK`); a single finite machine per format interprets it.
* **Canonize first, then interpret.** The decoded machine's serialization is
  computed in polynomial time (`Turing.MachineFormat.exists_polyCanonizer`):
  the binary state count and the minimum-length guard are checked before any
  state-indexed work, so a huge declared count is never expanded in unary.
* **The clock is §12.7's counter loop** (`Turing.counterLoopTM`) over the
  deadline's binary word; a simulated halt is a live body exit.
* **Statements only.** The two headline contracts are sorried with sketches
  (pre-issue statement phase of batch B5a); the definitions and the
  one-work-tape instance are proved.

## Main definitions

* `Turing.workReadsK`, `Turing.tableBitsK`, `Turing.serializeK`,
  `Turing.codeSkipTableK` — the fixed `k`-record layout and grammar.
* `Turing.MachineFormat`, `Turing.MachineFormat.toFinTM` — the format parameter.
* `Turing.oneTapeMachineFormat` — the one-work-tape instance.

## Main results

* `Turing.tableBitsK_two`, `Turing.codeSkipTable2_eq_codeSkipTableK` — the
  two-work-tape bridges to `CodeFormat`'s frozen table writer and skipper.
* `Turing.MachineFormat.exists_polyCanonizer` — a polynomial-time canonizer.
* `Turing.MachineFormat.exists_uniformSimulator` — the uniform simulator.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §1.4.1, Theorem 1.9; Example 3.6(3).)
-/

namespace Turing

/-! ## The `k`-record layout -/

/-- The fixed enumeration of the work reads of `k` work tapes: tape `0`
outermost, each read over `none`, `some false`, `some true`. [AB09, §1.4] -/
def workReadsK : (k : ℕ) → List (Fin k → Option Bool)
  | 0 => [Fin.elim0]
  | k + 1 => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
      (workReadsK k).map fun r => (Fin.cons w r : Fin (k + 1) → Option Bool)

/-- The fixed serialization of a `k`-work-tape transition table: states in `Fin`
order, then the input read, then the work reads in `Turing.workReadsK` order,
one `Turing.actionBitsK` record each. [AB09, §1.4] -/
def tableBitsK {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1))) :
    List Bool :=
  (List.finRange (n + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      (workReadsK k).flatMap fun w => actionBitsK (tr q inp w)

/-- The canonical serialization of a `k`-work-tape binary machine with `n + 1`
states: the binary state count, the unary initial state, the table. [AB09, §1.4] -/
def serializeK {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))) : List Bool :=
  pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)

/-- The table skipper of the `k`-record grammar: `n + 1` states of `3^(k+1)`
records each. [AB09, §1.4] -/
def codeSkipTableK (k n : ℕ) : List Bool → Option (List Bool) :=
  codeSkipRepeat ((fun r => codeSkipRepeat r 3)^[k + 1] (codeSkipActionK k n)) (n + 1)

/-- A one-tape read vector built by `Fin.cons` is the constant function. -/
private lemma fin_cons_one (w : Option Bool) :
    (Fin.cons w Fin.elim0 : Fin 1 → Option Bool) = fun _ => w := by
  funext i; fin_cases i; rfl

/-- A two-tape read vector built by `Fin.cons` is the `Turing.workPair` of its entries. -/
private lemma fin_cons_two (w₀ w₁ : Option Bool) :
    (Fin.cons w₀ (fun _ : Fin 1 => w₁) : Fin 2 → Option Bool) = workPair w₀ w₁ := by
  funext i; fin_cases i <;> rfl

/-- The one-work-tape reads are the constant functions, in table order. -/
lemma workReadsK_one : workReadsK 1 =
    ([none, some false, some true] : List (Option Bool)).map fun w => fun _ => w := by
  simp [workReadsK, fin_cons_one]

/-- The two-work-tape reads are the `Turing.workPair`s, in table order. -/
lemma workReadsK_two : workReadsK 2 =
    ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
      ([none, some false, some true] : List (Option Bool)).map fun w₁ => workPair w₀ w₁ := by
  simp [workReadsK, fin_cons_one, fin_cons_two]

/-- At two work tapes the generic table writer is `Turing.codeTable2Bits`. -/
lemma tableBitsK_two {n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin 2 → Option Bool) → Action 2 Bool (Fin (n + 1))) :
    tableBitsK tr = codeTable2Bits (fun q inp w₀ w₁ => tr q inp (workPair w₀ w₁)) := by
  unfold tableBitsK codeTable2Bits
  rw [workReadsK_two]
  simp only [List.flatMap_assoc, List.flatMap_map]

/-- At two work tapes the generic table skipper is `Turing.codeSkipTable2`. -/
lemma codeSkipTable2_eq_codeSkipTableK (n : ℕ) (xs : List Bool) :
    codeSkipTable2 n xs = codeSkipTableK 2 n xs := rfl

/-! ## Machine formats -/

/-- A **deterministic machine format**: a `Turing.CodeFormat` whose codes denote
`k`-work-tape binary machines, serialized in the fixed `k`-record layout and
parsed by the fixed `k`-record grammar. [AB09, §1.4] -/
structure MachineFormat extends CodeFormat where
  /-- the work-tape count of the coded machines -/
  k : ℕ
  /-- the machine a code denotes -/
  machine : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))
  /-- the format's serialization is the fixed `k`-record serialization -/
  serialize_eq : ∀ M, serialize M = serializeK (machine M)
  /-- the format's table skipper is the fixed `k`-record skipper -/
  skipTable_eq : ∀ n xs, skipTable n xs = codeSkipTableK k n xs

/-- The bundled machine a code of a machine format denotes. -/
def MachineFormat.toFinTM (F : MachineFormat) (M : F.Code) : FinTM Bool where
  k := F.k
  State := Fin (F.numStates M + 1)
  tm := F.machine M

/-- The one-tape format's table skipper is the generic skipper at one work tape: the
framed one-tape action skipper is `Turing.codeSkipActionK 1`. -/
private lemma oneTape_skipTable_eq (n : ℕ) (xs : List Bool) :
    oneTapeFormat.skipTable n xs = codeSkipTableK 1 n xs := by
  have h : codeSkipAction n = codeSkipActionK 1 n :=
    funext (codeSkipAction_eq_codeSkipActionK n)
  show codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1) xs = _
  rw [h]; rfl

/-- The frozen one-tape serialization is the generic one at one work tape, record for
record (`Turing.workReadsK_one`, `Turing.actionBits_eq_actionBitsK`). -/
private lemma oneTape_serialize_eq (M : CodeTM) : M.serialize = serializeK M.tm := by
  unfold CodeTM.serialize serializeK tableBitsK
  rw [workReadsK_one]
  simp only [List.flatMap_map, actionBits_eq_actionBitsK]

/-- The one-work-tape code format `Turing.oneTapeFormat` as a machine format.
Its decoder is `Turing.codeDecode` and its bundled machines are
`Turing.CodeTM.toFinTM`, both definitionally. [AB09, §1.4] -/
def oneTapeMachineFormat : MachineFormat :=
  { oneTapeFormat with
    k := 1
    machine := fun M => M.tm
    serialize_eq := oneTape_serialize_eq
    skipTable_eq := oneTape_skipTable_eq }

namespace MachineFormat

variable (F : MachineFormat)

/-- **A polynomial-time canonizer** (spec, fill pending — batch B5a): one finite
binary machine computes the fixed serialization of the decoded machine within
`d · (|α| + 1)^d` steps. [AB09, §1.4; the P3.2 round-2 construction]

**Proof sketch.** Implement `F.scan` and emit `F.canonical`
(`Turing.CodeFormat.canonical_eq`). Copy `α` to a work tape. Parse the doubled
state count (`pairDecode`) and check that it is canonical. Check the guard
`F.guard · (n + 1) ≤ |rest|` in binary **before** any state-indexed work: count
`rest` in blocks of `F.guard` cells against a decrementing copy of `bits n`
(`Turing.decrementTM`, `Turing.counterLoopTM`), never expanding `n` in unary.
Then skip the unary initial state with its range check, and the table by the
fixed grammar (`F.skipTable_eq`, `Turing.codeSkipTableK`): `n + 1` rounds of
`3^(k+1)` records, each field by a finite-state check and each successor field
by a binary range check. After the guard every round consumes at least
`4k + 5` cells (`Turing.codeActionK_length`), so there are at most `|α|` rounds.
**The guard may be `0`** (wave-1 statement gate, round 1, finding 5). `F.guard` is
unconstrained, and a zero guard bounds nothing, so the guard check alone does not bound
`n`. Add the grammar-derived necessary check: a successful parse consumes at least
`(4k + 5) · 3^(k+1) · (n + 1)` table bits, a positive multiple of `n + 1`. Run it in binary
against a decrementing copy of `bits n`, failing fast once the suffix is exhausted. Early
rejection by this check or by the guard yields exactly the prescribed fallback, because
`F.scan` fails on the same inputs (`Turing.CodeFormat.canonical_eq`). No stronger
`MachineFormat` hypothesis is needed.
Check the all-`true` suffix. On success copy the consumed prefix to the output;
on failure emit the constant `F.serialize F.fallback`. Every phase is polynomial
in `|α|`; take `d` at least the coefficient and the exponent. -/
theorem exists_polyCanonizer :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => F.serialize (F.decode α)) fun n => d * (n + 1) ^ d := by
  sorry

/-- **The uniform bounded-acceptance simulator** (spec, fill pending — batch
B5a): one finite binary machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the machine answers `[true]` if the machine `α` denotes
halts on `x` with output exactly `[true]` within `t` steps, and `[false]`
otherwise, within `d · (|α| + |x| + t + 1)^d` steps. [AB09, §1.4.1, Theorem 1.9,
time-bounded form; Example 3.6(3)'s uniformity]

**Proof sketch.** Parse the nested input onto tapes: the deadline word
`bits t` on a counter tape, `α` on a table tape, `x` on a buffer tape. Canonize
`α` in place by `Turing.MachineFormat.exists_polyCanonizer` through
`Turing.FinTM.exists_installCallTM`; by `F.serialize_eq` the table is
`serializeK (F.machine (F.decode α))`, of length at most
`max |α| |F.serialize F.fallback|` (`Turing.CodeFormat.serialize_decode_length_le`).
The body is **one step block**: for the current simulated state (unary on a
state tape), input read and `k` work reads, seek the record at index
`q · 3^(k+1) + rank(inp, w)`, read it by the `Turing.codeReadActionK` grammar
(`Turing.codeReadActionK_append`), apply it to `k` mirrored work tapes and the
simulated input head, and update a finite output summary (empty, exactly
`[true]`, other) instead of emitting. Its cost is at most `B · (|table| + 1)`,
independent of `t`, `x` and the tape contents. The block reads the simulated
input through its own input head and is hosted on the buffer by
`Turing.vhostEmitTM` (`Turing.vhostEmitTM_runFrom`); the clock is
`Turing.counterLoopTM` over `bits t` (`Turing.counterLoopTM_run_done`,
`Turing.counterLoopTM_run_escape`), a simulated halt being the live exit. At
`done` the simulated machine is live after `t` steps, so the answer is `false`;
at `escape` it has halted within `t`, and the answer is the summary's
`[true]` test. The ledger: polynomial startup, `t` rounds of at most
`B · (|table| + 1)` (`Turing.counterLoop_time_le`), and the verdict, all at most
`d · (|α| + |x| + t + 1)^d`. -/
theorem exists_uniformSimulator :
    ∃ (S : FinTM Bool) (d : ℕ), ∀ (α x : List Bool) (t : ℕ),
      ((F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (d * (α.length + x.length + t + 1) ^ d)) ∧
      (¬(F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (d * (α.length + x.length + t + 1) ^ d)) := by
  sorry

end MachineFormat

end Turing
