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

/-! ### Positive grammar bound (B5a fill preparation)

These lemmas justify the extra fail-fast guard even when `F.guard = 0`.
They concern the specified parser; the finite binary implementation and its
polynomial time ledger remain the canonizer's continuation obligation.
-/

/-- Iterated skipping consumes the sum of the per-record lower bounds.

**Proof sketch.** Split off the first successful skip, apply the induction
hypothesis to its suffix, and add the two length inequalities. -/
private lemma skipRepeat_consumes (r : List Bool → Option (List Bool)) (b : ℕ)
    (hr : ∀ xs ys, r xs = some ys → b + ys.length ≤ xs.length)
    (m : ℕ) (xs ys : List Bool) (h : codeSkipRepeat r m xs = some ys) :
    b * m + ys.length ≤ xs.length := by
  induction m generalizing xs with
  | zero =>
    have heq : xs = ys := Option.some.inj h
    simp [heq]
  | succ m ih =>
    obtain ⟨zs, hz, hy⟩ := Option.bind_eq_some_iff.mp h
    have hfirst := hr xs zs hz
    have hrest := ih zs hy
    rw [Nat.mul_succ]
    omega

/-- Nesting a three-symbol reader multiplies its consumption bound by three. -/
private lemma skipSymbols_consumes (r : List Bool → Option (List Bool)) (b : ℕ)
    (hr : ∀ xs ys, r xs = some ys → b + ys.length ≤ xs.length)
    (j : ℕ) (xs ys : List Bool)
    (h : ((fun f => codeSkipRepeat f 3)^[j] r) xs = some ys) :
    b * 3 ^ j + ys.length ≤ xs.length := by
  induction j generalizing xs ys with
  | zero => simpa using hr xs ys h
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h
    have hb := skipRepeat_consumes _ (b * 3 ^ j) (fun u v huv => ih u v huv)
      3 xs ys h
    simpa only [Nat.pow_succ, Nat.mul_assoc] using hb

/-- A successful table skip consumes a positive number of bits per state,
independently of the format's optional guard. -/
private lemma skipTable_consumes (k n : ℕ) (xs ys : List Bool)
    (h : codeSkipTableK k n xs = some ys) :
    (4 * k + 5) * 3 ^ (k + 1) * (n + 1) + ys.length ≤ xs.length := by
  have ha (u v : List Bool) (hu : codeSkipActionK k n u = some v) :
      4 * k + 5 + v.length ≤ u.length := by
    rw [← codeEraseActionK] at hu
    obtain ⟨⟨a, rest⟩, hread, rfl⟩ := Option.map_eq_some_iff.mp hu
    rw [codeReadActionK_sound u a rest hread, List.length_append]
    exact Nat.add_le_add_right (codeActionK_length a) _
  exact skipRepeat_consumes _ _ (fun u v huv =>
    skipSymbols_consumes _ _ ha (k + 1) u v huv) (n + 1) xs ys h

/-- A successful scanner satisfies the positive grammar guard already on the
suffix following the binary header. This holds also for a zero format guard.

**Proof sketch.** Decompose the successful scanner into its header, initial-state
and table checks. Erasure and initial-state reader soundness show that the table
input is a suffix of the header remainder. Apply the generic table-skip bound
and discard the nonnegative final-suffix length. -/
private lemma scan_grammar_guard (α bits rest tail : List Bool)
    (hp : pairDecode α = some (bits, rest)) (hs : F.scan α = some tail) :
    (4 * F.k + 5) * 3 ^ (F.k + 1) * (codeBitsNat bits + 1) ≤ rest.length := by
  unfold CodeFormat.scan at hs
  rw [hp] at hs
  dsimp only [bind, Option.bind] at hs
  split at hs
  · contradiction
  split at hs
  · contradiction
  obtain ⟨table, hq, ht⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨suffix, htable, _⟩ := Option.bind_eq_some_iff.mp ht
  rw [F.skipTable_eq] at htable
  have hlen := skipTable_consumes F.k (codeBitsNat bits) table suffix htable
  rw [← codeEraseFin] at hq
  obtain ⟨⟨q, r⟩, hread, rfl⟩ := Option.map_eq_some_iff.mp hq
  have hword := codeReadFin_sound rest q r hread
  have hrest : r.length ≤ rest.length := by
    rw [hword, List.length_append]
    omega
  dsimp only at hlen
  omega

/-- Reject a binary header whose declared table cannot fit in the remaining
input, before evaluating the format scanner. This is a specification function,
not yet a certified finite-machine implementation. -/
private def guardedScan (α : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode α
  if rest.length < (4 * F.k + 5) * 3 ^ (F.k + 1) * (codeBitsNat bits + 1)
    then none else F.scan α

/-- The additional positive guard preserves the scanner exactly.

**Proof sketch.** Header failure already fails the scanner. If the new guard
fails, any hypothetical successful scan contradicts `scan_grammar_guard`;
otherwise the guarded scanner calls the original scanner. -/
private lemma guardedScan_eq (α : List Bool) : guardedScan F α = F.scan α := by
  unfold guardedScan
  cases hp : pairDecode α with
  | none => simp [CodeFormat.scan, hp]
  | some p =>
    rcases p with ⟨bits, rest⟩
    dsimp only [bind, Option.bind]
    split
    next hg =>
      cases hs : F.scan α with
      | none => rfl
      | some tail =>
        have := scan_grammar_guard F α bits rest tail hp hs
        omega
    · rfl

/-- Early failure of the positive grammar guard selects exactly the prescribed
fallback, including for a zero guard and a potentially accepting fallback. -/
private lemma decode_of_grammar_guard (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest))
    (hg : rest.length < (4 * F.k + 5) * 3 ^ (F.k + 1) * (codeBitsNat bits + 1)) :
    F.decode α = F.fallback := by
  have hs : F.scan α = none := by
    rw [← guardedScan_eq]
    simp [guardedScan, hp, hg]
  have hparse : F.parseFull α = none := by
    rw [F.scan_full] at hs
    exact Option.map_eq_none_iff.mp hs
  exact F.decode_of_parseFull_none α hparse

/-- Passing the positive guard bounds state-count work by the available input. -/
private lemma grammar_guard_states (n s : ℕ)
    (h : (4 * F.k + 5) * 3 ^ (F.k + 1) * (n + 1) ≤ s) : n + 1 ≤ s := by
  have hc : 1 ≤ (4 * F.k + 5) * 3 ^ (F.k + 1) :=
    Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hs : n + 1 ≤ (4 * F.k + 5) * 3 ^ (F.k + 1) * (n + 1) := by
    simpa using Nat.mul_le_mul_right (n + 1) hc
  exact hs.trans h

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
in `|α|`; take `d` at least the coefficient and the exponent.

**Fill appendix (B5a partial).** The positive grammar bound, `guardedScan_eq`,
and `decode_of_grammar_guard` are proved below the format layer, without a
positivity premise on `F.guard`. The finite binary parser and its polynomial
runtime proof remain open; this target retains its original admission. -/
theorem exists_polyCanonizer :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => F.serialize (F.decode α)) fun n => d * (n + 1) ^ d := by
  sorry

/-! ### Finite output summary (D4 move, generalized from Codes2Tape)

The seven output-summary and clock declarations below replace their specialized
ZF-B3 counterparts. This is the semantic specification of the future step block,
not a finite-machine interpreter or a claim about its running time.
-/

/-- Output summary: `none` means empty, `some true` means exactly `[true]`,
and `some false` means any other output. The last class is irreversible. -/
private def outputSummary : List Bool → Option Bool
  | [] => none
  | [true] => some true
  | _ => some false

/-- Update the three-way summary for the emission of one source transition. -/
private def summaryEmit : Option Bool → Option Bool → Option Bool
  | s, none => s
  | none, some true => some true
  | _, some _ => some false

/-- Summary update accounts for the symbol on a halting transition as well. -/
private lemma outputSummary_append (w : List Bool) (b : Option Bool) :
    outputSummary (w ++ b.toList) = summaryEmit (outputSummary w) b := by
  cases b with
  | none => simp [summaryEmit]
  | some b =>
    cases w with
    | nil => cases b <;> rfl
    | cons a w =>
      cases w with
      | nil => cases a <;> cases b <;> rfl
      | cons c w => cases a <;> cases b <;> rfl

/-- The summary's accepting value characterizes the exact singleton output. -/
private lemma outputSummary_true (w : List Bool) :
    outputSummary w = some true ↔ w = [true] := by
  cases w with
  | nil => simp [outputSummary]
  | cons b w =>
    cases w with
    | nil => cases b <;> simp [outputSummary]
    | cons c w => cases b <;> simp [outputSummary]

/-- Once the summary is other, no subsequent emission can repair it. -/
private lemma summaryEmit_other (b : Option Bool) :
    summaryEmit (some false) b = some false := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

/-- Semantic clock for any finite-tape binary machine. It performs exactly the
permitted number of source steps, maintaining only the finite output summary,
and then inspects halting and exact output. This is a specification function,
not a finite-machine construction or a claim about machine time. -/
private def summaryClock {k : ℕ} {Q : Type} (M : MultiTapeTM k Bool Q)
    {x : List Bool} : ℕ → Cfg k Bool Q x → Option Bool → Bool
  | 0, c, s => c.state.isNone && (s == some true)
  | t + 1, c, s =>
    summaryClock M t (M.step c) (summaryEmit s (M.outputSymbol c))

/-- The clock's final inspection includes the last permitted transition.
Halted configurations are allowed, so the equation also covers padding an
early halt to the deadline.

**Proof sketch.** Induct on the deadline. The output-summary update is
exactly append by the step's optional emission; cite the public run and
output-step equations to identify the residual run. -/
private lemma summaryClock_correct {k : ℕ} {Q : Type} (M : MultiTapeTM k Bool Q)
    {x : List Bool} (c : Cfg k Bool Q x) (t : ℕ) :
    summaryClock M t c (outputSummary c.output) =
      ((M.runFrom c t).state.isNone &&
        (outputSummary (M.runFrom c t).output == some true)) := by
  induction t generalizing c <;>
    simp only [summaryClock, ← outputSummary_append, ← MultiTapeTM.step_output,
      MultiTapeTM.runFrom_zero, MultiTapeTM.runFrom_succ_eq_step, *]

/-- Inspecting the semantic clock at the deadline is exactly bounded acceptance,
including a halt on the last permitted transition. -/
private lemma summaryClock_accepts (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    summaryClock M.tm t (M.tm.initCfg x) none = true ↔ M.ComputesInTime x [true] t := by
  change summaryClock M.tm t (M.tm.initCfg x)
    (outputSummary (M.tm.initCfg x).output) = true ↔ _
  rw [summaryClock_correct, FinTM.computesInTime_iff]
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq, outputSummary_true]

/-- The zero-deadline clock rejects every initialized machine. -/
private lemma summaryClock_zero (M : FinTM Bool) (x : List Bool) :
    summaryClock M.tm 0 (M.tm.initCfg x) none = false := rfl

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
`d · (|α| + |x| + t + 1)^d`.

**Fill appendix (B5a partial, D4).** The seven output-summary/clock declarations
have moved from `Codes2Tape` and are generalized to arbitrary tape and state
counts. `summaryClock_accepts` identifies the inclusive-deadline predicate;
`summaryClock_zero` handles zero. These are semantic specifications only.
The one physical step block, its relation-level trace, the counter/virtual-input
host assembly, and its ledger remain open; this target retains its admission. -/
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
