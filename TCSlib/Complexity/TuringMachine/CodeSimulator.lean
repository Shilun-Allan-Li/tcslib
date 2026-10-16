/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.StepBlockLoop
-- B5a continuation: sanctioned imports for the physical binary-header loader.
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.InputCall

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
* **Status update (fills-8, 2026-10-13; H2-M, 2026-10-14): partial.** The two
  headline contracts retain their original admissions. Proved so far:
  - for the canonizer: the native-input binary-header loader and the physical
    fail-fast binary length guard; the canonical-header check, the
    nonoverflowing successor counter and its specialized guard; the guard
    front end, which prepares the header, the successor count and the native
    remainder address from blank tapes, seeks there, runs the guard and seeks
    back on success; and the total two-port parse front end
    (`exists_canonParseFront`), which joins header validity to the guard with
    a fallback rejection port and a ready-for-grammar port, in linear time;
  - for the simulator: the complete generic step block `Turing.StepBlock.roundTM`,
    one finite machine per work-tape count `k` whose control is independent of
    the coded state count (record lookup, the selected record's payload,
    successor installation and the round seam), with its exact time bound and
    head envelope (`Turing.StepBlock.roundTM_effect`), promoted on 2026-10-14
    (H2-M) to the public module `Build/StepBlock` (gate
    `audits/h2-promotion-r2-findings.md`); and the binary deadline clock around
    it, hosted on the virtual input, with its one-bit verdict
    (`h1HostedVerdict_accepts`). The clock itself is the public loop of
    `Build/StepBlockLoop` (`Turing.StepBlock.hostedLoopTM_run`; H1 harvest, gate
    `audits/h1-harvest-statements-findings.md`).

  Proved in the canonizer's continuation 4 (2026-10-15), as private components:
  the restored binary bound (the bounded unary reader `exists_canonUnaryTM`) and
  the generic action-record validator (`exists_canonRecordTM`).

  Still open: the canonizer's grammar loop, its complete validator and the
  emission; the simulator's nested-input startup, canonizer installation and
  joint ledger.

## Main definitions

* `Turing.serializeK`, `Turing.codeSkipTableK` — the fixed `k`-record serialization
  and grammar, over the table layout `Turing.workReadsK`, `Turing.tableBitsK` of
  `Build/StepBlock`.
* `Turing.serializeK_eq` — the serialization as an equation, the specification API (user,
  2026-10-16).
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

/-- The canonical serialization of a `k`-work-tape binary machine with `n + 1`
states: the binary state count, the unary initial state, the table. [AB09, §1.4] -/
def serializeK {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))) : List Bool :=
  pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)

/-- **The serialization as an equation** (the specification API, user 2026-10-16): the doubled
binary state count, the separator, the unary initial state, then the table. Consumers read the
captured serialization through this equation (with `Turing.pairEncode_eq` and
`Turing.unaryFin_eq`), not by unfolding `Turing.serializeK`. -/
theorem serializeK_eq {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))) :
    serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr) :=
  rfl

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

/-! ### Physical binary-header loading (B5a continuation) -/

/-- The undoubled header, or the empty word when the pair grammar fails.
The later validation phase must distinguish failure from a valid zero header. -/
private def canonHeader (α : List Bool) : List Bool :=
  ((pairDecode α).map Prod.fst).getD []

/-- Loading a doubled header never produces more bits than the source input. -/
private lemma canonHeader_length (α : List Bool) : (canonHeader α).length ≤ α.length := by
  cases hp : pairDecode α with
  | none => simp [canonHeader, hp]
  | some p =>
    rcases p with ⟨bits, rest⟩
    have he := congrArg List.length (eq_pairEncode_of_pairDecode α bits rest hp)
    rw [length_pairEncode] at he
    simp only [canonHeader, hp, Option.map_some, Option.getD_some]
    omega

/-- A physical linear-time header loader installs the binary header on tape
zero and restores a clean seam with the original native input available.

**Proof sketch.** Install the public pair-first extractor through the public
native-input call row. The header length is at most the original input length,
so the call row's ledger is linear as well. No parsing or host trace is copied. -/
private lemma exists_canonHeaderCall :
    ∃ (C : FinTM Bool) (entry exit : C.State) (a : ℕ), 0 < C.k ∧
      ∀ α : List Bool, ∃ t ≤ a * (α.length + 1), 0 < t ∧
        (∀ u, 0 < u → u < t →
          (C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) u).state ≠
            some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) t =
          Cfg.ofWords exit (stateWord C.k (canonHeader α)) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairFst
  obtain ⟨C, entry, exit, c, hk, hC⟩ :=
    FinTM.exists_inputCallTM M canonHeader (fun n => a * (n + 1)) hM
  refine ⟨C, entry, exit, c * (a + 2), hk, ?_⟩
  intro α
  obtain ⟨t, ht, hpos, hcut, hrun⟩ := hC α
  refine ⟨t, ht.trans ?_, hpos, hcut, hrun⟩
  have hlen := canonHeader_length α
  calc
    c * (a * (α.length + 1) + α.length + (canonHeader α).length + 1) ≤
        c * (a * (α.length + 1) + 2 * (α.length + 1)) :=
      Nat.mul_le_mul_left c (by omega)
    _ = _ := by ring

/-! ### Physical fail-fast length guard (B5a continuation)

The catalog has whole-input scans but no fixed-block input scan with a short-input
exit. The following body supplies that missing finite controller; the binary
countdown itself is the public `counterLoopTM`, not a new loop implementation.
The body has no work tapes and never emits. Its block length is `b + 1`, so
even the zero-format-guard case can use the positive grammar minimum.
-/

/-- Progress through a fixed positive block; `none` is the short-input exit. -/
private def guardPhase (b u : ℕ) : Option (Fin (b + 1)) :=
  some ⟨u % (b + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Read at most `b + 1` actual input symbols, returning to the anchor after
one whole block and taking a distinct live exit on a boundary blank. -/
private def guardBlockTM (b : ℕ) : MultiTapeTM 0 Bool (Option (Fin (b + 1))) where
  q₀ := guardPhase b 0
  tr := fun q inp _ => match q with
    | none => inputMoveAction 0 none
    | some i => if inp.isSome then
        inputMoveAction 1 (guardPhase b (i.val + 1))
      else inputMoveAction 0 none

/-- A block-scan configuration after `j` input cells have been consumed. -/
private def guardCfg (b : ℕ) (x : List Bool) (q : Option (Fin (b + 1)))
    (j : ℕ) (hj : j ≤ x.length) (out : List Bool) :
    Cfg 0 Bool (Option (Fin (b + 1))) x :=
  ⟨some q, ⟨j + 1, by omega⟩, Fin.elim0, Fin.elim0, out⟩

/-- The finite block controller advances one cell without writing or emitting.
The input-only action law supplies all unchanged configuration fields. -/
private lemma guardBlock_step (b : ℕ) (x : List Bool) (u j : ℕ)
    (hu : u < b + 1) (hj : j < x.length) (out : List Bool) :
    (guardBlockTM b).step (guardCfg b x (guardPhase b u) j (by omega) out) =
      guardCfg b x (guardPhase b (u + 1)) (j + 1) (by omega) out := by
  have hr := inputSymbolInner
    (cfg := guardCfg b x (guardPhase b u) j (by omega) out) j (by dsimp [guardCfg]; omega) hj
  rw [step_of_inputMoveAction (guardBlockTM b) _ (q' := guardPhase b (u + 1)) 1 rfl (by
    change (if (guardCfg b x (guardPhase b u) j (by omega) out).inputSymbol.isSome then
      inputMoveAction 1 (guardPhase b (u % (b + 1) + 1)) else inputMoveAction 0 none) = _
    rw [hr]
    simp only [Option.isSome_some, if_true, Nat.mod_eq_of_lt hu])]
  apply Cfg.ext_zero_tapes
  · rfl
  · apply Fin.ext
    change (moveInputPos (guardCfg b x (guardPhase b u) j (by omega) out).inputPos
      SignType.pos).val = j + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by dsimp [guardCfg]; omega)]
    rfl
  · rfl

/-- Every available prefix of one block is traversed in exactly its length.

**Proof sketch.** Induct on the traversed prefix and apply the input-only
one-step contract. The upper bound prevents an intermediate anchor return. -/
private lemma guardBlock_run (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out : List Bool) (u : ℕ)
    (hu : u ≤ b + 1) (hlen : j + u ≤ x.length) :
    (guardBlockTM b).runFrom (guardCfg b x (guardPhase b 0) j hj out) u =
      guardCfg b x (guardPhase b u) (j + u) hlen out := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) (by omega)]
    simpa only [Nat.add_assoc] using
      guardBlock_step b x u (j + u) (by omega) (by omega) out

/-- At the right input blank, the next transition takes the short-input exit. -/
private lemma guardBlock_blank (b : ℕ) (x : List Bool) (u : ℕ) (out : List Bool) :
    (guardBlockTM b).step
        (guardCfg b x (guardPhase b u) x.length le_rfl out) =
      guardCfg b x none x.length le_rfl out := by
  rw [step_of_inputMoveAction (guardBlockTM b) _ (q' := none) 0 rfl (by
    simp [guardBlockTM, guardPhase, Cfg.inputSymbol, guardCfg])]
  simp only [moveInputPos_zero]
  rfl

/-- A short block exits immediately after reading its remaining symbols.
In particular the running time does not depend on the declared state count. -/
private lemma guardBlock_short (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (hshort : x.length - j < b + 1) (out : List Bool) :
    (guardBlockTM b).runFrom (guardCfg b x (guardPhase b 0) j hj out)
        (x.length - j + 1) = guardCfg b x none x.length le_rfl out := by
  rw [MultiTapeTM.runFrom_succ_eq_step',
    guardBlock_run b x j hj out (x.length - j) (by omega) (by omega)]
  have hpos : j + (x.length - j) = x.length := by omega
  simpa only [hpos] using guardBlock_blank b x (x.length - j) out

/-- Exact duration of a block: its fixed size, or the available suffix plus
one transition detecting the blank, whichever is smaller. -/
private def guardTime (b : ℕ) {x : List Bool}
    (c : Cfg 0 Bool (Option (Fin (b + 1))) x) : ℕ :=
  min (b + 1) (x.length + 2 - c.inputPos.val)

/-- Before the end of a block, neither live exit has been reached.

**Proof sketch.** Every strict-interior time is smaller than the block size
and traverses only existing input cells. Its progress index is strictly
positive and below the modulus, so it is neither the anchor nor the failure. -/
private lemma guardBlock_interior (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out : List Bool) (u : ℕ) (hu : 0 < u)
    (ht : u < guardTime b (guardCfg b x (guardPhase b 0) j hj out)) :
    ∃ s, ((guardBlockTM b).runFrom
        (guardCfg b x (guardPhase b 0) j hj out) u).state = some s ∧
      s ≠ guardPhase b 0 ∧ s ≠ none := by
  have hb : u < b + 1 := lt_of_lt_of_le ht (Nat.min_le_left _ _)
  have hl : j + u ≤ x.length := by
    have := lt_of_lt_of_le ht (Nat.min_le_right _ _)
    dsimp [guardCfg] at this
    omega
  rw [guardBlock_run b x j hj out u (by omega) hl]
  refine ⟨guardPhase b u, rfl, ?_, Option.some_ne_none _⟩
  intro he
  have hv := congrArg (fun q => q.map Fin.val) he
  simp [guardPhase, Nat.mod_eq_of_lt hb] at hv
  omega

/-- The physical binary guard is the shared counter loop with the block
controller as body. It has exactly one work tape, holding the binary count. -/
private def binaryGuardTM (b : ℕ) :
    MultiTapeTM 1 Bool (CounterLoopState (Option (Fin (b + 1)))) :=
  counterLoopTM (guardBlockTM b) (guardPhase b 0) (some none)

/-- Guard entry with the binary counter delimited at the origin. The original
input remains native, so the caller can rewind and parse it after the guard. -/
private def binaryGuardStart (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out w : List Bool) :
    Cfg 1 Bool (CounterLoopState (Option (Fin (b + 1)))) x :=
  counterLoopCfg (some (.dec .run))
    (guardCfg b x (guardPhase b 0) j hj out) (FinTM.bufferTape w) 0

/-- While whole blocks fit, the body orbit advances by their combined length.

**Proof sketch.** Induct on the number of blocks. The next full block takes
`b + 1` transitions by `guardBlock_run`, returns its finite progress index to
zero, and preserves the output. This is a body-orbit calculation; the physical
counter is handled solely by the public counter-loop contracts. -/
private lemma guardBlock_orbit (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out : List Bool) (r : ℕ)
    (hr : j + (b + 1) * r ≤ x.length) :
    counterLoopOrbit (guardBlockTM b) (guardTime b)
        (guardCfg b x (guardPhase b 0) j hj out) r =
      guardCfg b x (guardPhase b 0) (j + (b + 1) * r) hr out := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hprev : j + (b + 1) * r ≤ x.length := by
      rw [Nat.mul_succ] at hr
      omega
    change (fun c => (guardBlockTM b).runFrom c (guardTime b c))^[r + 1] _ = _
    rw [Function.iterate_succ_apply']
    change (guardBlockTM b).runFrom
      (counterLoopOrbit (guardBlockTM b) (guardTime b)
        (guardCfg b x (guardPhase b 0) j hj out) r)
      (guardTime b (counterLoopOrbit (guardBlockTM b) (guardTime b)
        (guardCfg b x (guardPhase b 0) j hj out) r)) = _
    rw [ih hprev]
    have ht : guardTime b
        (guardCfg b x (guardPhase b 0) (j + (b + 1) * r) hprev out) = b + 1 := by
      dsimp [guardTime, guardCfg]
      rw [Nat.min_eq_left]
      rw [Nat.mul_succ] at hr
      omega
    rw [ht, guardBlock_run b x _ hprev out (b + 1) le_rfl (by
      rw [Nat.mul_succ] at hr
      omega)]
    simp only [guardPhase, Nat.mod_self, Nat.zero_mod, Nat.mul_succ, Nat.add_assoc]

/-- Each block is a positive first-return-or-exit segment, including an empty
suffix. This is the hypothesis shared by the returning and escaping host rows. -/
private lemma guardBlock_segment (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out : List Bool) :
    let c := guardCfg b x (guardPhase b 0) j hj out
    c.state = some (guardPhase b 0) ∧ 0 < guardTime b c ∧
      (∀ u, 0 < u → u < guardTime b c →
        ∃ s, ((guardBlockTM b).runFrom c u).state = some s ∧
          s ≠ guardPhase b 0 ∧ s ≠ none) := by
  refine ⟨rfl, ?_, guardBlock_interior b x j hj out⟩
  dsimp [guardTime, guardCfg]
  omega

/-- If the requested whole blocks fit, the physical guard reaches `done`,
silently, in linear time in the input length and the binary counter width.

**Proof sketch.** The body orbit supplies the counter host's first-return
hypotheses. Its exact run is the existing `counterLoopTM_run_done`; its
ledger is `counterLoop_time_le`. Both the number of rounds and their total
input consumption are bounded by the actual input length. -/
private lemma binaryGuard_done (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out w : List Bool)
    (hfit : j + (b + 1) * Nat.ofDigits 2 (w.map Bool.toNat) ≤ x.length) :
    ∃ T ≤ 5 * x.length + 2 * w.length + 2,
      let c := (binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) T
      c.state = some .done ∧ c.output = out ∧
        c.inputPos.val = j + (b + 1) * Nat.ofDigits 2 (w.map Bool.toNat) + 1 ∧
        (∀ u < T,
          ((binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) u).state ≠
            some .done ∧
          ((binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) u).state ≠
            some .escape) := by
  let d := Nat.ofDigits 2 (w.map Bool.toNat)
  let c := guardCfg b x (guardPhase b 0) j hj out
  have hpos (r : ℕ) (hr : r ≤ d) : j + (b + 1) * r ≤ x.length :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (b + 1) hr) j).trans hfit
  have horbit (r : ℕ) (hr : r ≤ d) :
      counterLoopOrbit (guardBlockTM b) (guardTime b) c r =
        guardCfg b x (guardPhase b 0) (j + (b + 1) * r) (hpos r hr) out :=
    guardBlock_orbit b x j hj out r (hpos r hr)
  let T := (∑ r ∈ Finset.range d,
    guardTime b (counterLoopOrbit (guardBlockTM b) (guardTime b) c r)) +
      counterOverhead w (d + 1)
  have hrun := counterLoopTM_run_done (guardBlockTM b) (guardPhase b 0) (some none)
    (guardTime b) c w (FinTM.bufferTape w) 0 (by intro p _ _; simp) d rfl
    (by
      intro r hr
      rw [horbit r (by omega), horbit (r + 1) (by omega)]
      obtain ⟨hs, ht, hi⟩ := guardBlock_segment b x _ (hpos r (by omega)) out
      refine ⟨hs, ht, ?_, rfl⟩
      intro u hu hut
      obtain ⟨s, hsu, hsa, hse⟩ := hi u hu hut
      exact ⟨s, hsu, hsa, fun he => hse (Option.some.inj he).symm⟩) T rfl
  have ht := counterLoop_time_le (guardBlockTM b) (guardTime b) c w d rfl (b + 1)
    (fun _ _ => Nat.min_le_left _ _)
  have hd : d ≤ (b + 1) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ b + 1 by omega)
  refine ⟨T, ?_, ?_⟩
  · dsimp [T]
    rw [Nat.mul_comm d (b + 1)] at ht
    dsimp [d] at ht hd ⊢
    omega
  · dsimp only
    have he : (binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) T = _ := hrun.1
    rw [he, horbit d le_rfl]
    exact ⟨rfl, rfl, rfl, hrun.2.1⟩

/-- If the requested blocks do not fit, the physical guard reaches `escape`
in time independent of the value represented by the binary counter.

**Proof sketch.** Divide the available input length by the positive block
size. Exactly that many full body rounds fit, and the next round detects the
right blank. Apply the public escaping counter-host contract and its prefix
amortization bound; there are at most `|x| + 1` attempted rounds. -/
private lemma binaryGuard_escape (b : ℕ) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (out w : List Bool)
    (hshort : x.length < j + (b + 1) * Nat.ofDigits 2 (w.map Bool.toNat)) :
    ∃ T ≤ (b + 5) * (x.length + 1) + 2 * w.length,
      let c := (binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) T
      c.state = some .escape ∧ c.output = out ∧ c.inputPos.val = x.length + 1 ∧
        (∀ u < T,
          ((binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) u).state ≠
            some .done ∧
          ((binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) u).state ≠
            some .escape) := by
  let r₀ := (x.length - j) / (b + 1)
  let c := guardCfg b x (guardPhase b 0) j hj out
  have hdiv := Nat.mod_add_div (x.length - j) (b + 1)
  have hmod := Nat.mod_lt (x.length - j) (Nat.succ_pos b)
  have hstart : j + (b + 1) * r₀ ≤ x.length := by dsimp [r₀]; omega
  have hlast : x.length - (j + (b + 1) * r₀) < b + 1 := by
    rw [← Nat.sub_sub]
    change (x.length - j) - (b + 1) * ((x.length - j) / (b + 1)) < b + 1
    rw [← Nat.mod_eq_sub_mul_div]
    exact hmod
  have hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat) := by
    by_contra hn
    have hm := Nat.mul_le_mul_left (b + 1) (Nat.le_of_not_gt hn)
    omega
  have hpos (r : ℕ) (hr : r ≤ r₀) : j + (b + 1) * r ≤ x.length :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (b + 1) hr) j).trans hstart
  have horbit (r : ℕ) (hr : r ≤ r₀) :
      counterLoopOrbit (guardBlockTM b) (guardTime b) c r =
        guardCfg b x (guardPhase b 0) (j + (b + 1) * r) (hpos r hr) out :=
    guardBlock_orbit b x j hj out r (hpos r hr)
  have hexit : counterLoopOrbit (guardBlockTM b) (guardTime b) c (r₀ + 1) =
      guardCfg b x none x.length le_rfl out := by
    change (fun z => (guardBlockTM b).runFrom z (guardTime b z))^[r₀ + 1] c = _
    rw [Function.iterate_succ_apply']
    change (guardBlockTM b).runFrom
      (counterLoopOrbit (guardBlockTM b) (guardTime b) c r₀)
      (guardTime b (counterLoopOrbit (guardBlockTM b) (guardTime b) c r₀)) = _
    rw [horbit r₀ le_rfl]
    have ht : guardTime b
        (guardCfg b x (guardPhase b 0) (j + (b + 1) * r₀) hstart out) =
        x.length - (j + (b + 1) * r₀) + 1 := by
      dsimp [guardTime, guardCfg]
      omega
    rw [ht]
    exact guardBlock_short b x _ hstart hlast out
  let T := (∑ r ∈ Finset.range (r₀ + 1),
    guardTime b (counterLoopOrbit (guardBlockTM b) (guardTime b) c r)) +
      counterOverhead w (r₀ + 1)
  have hrun := counterLoopTM_run_escape (guardBlockTM b) (guardPhase b 0) none
    (by simp [guardPhase]) (guardTime b) c w (FinTM.bufferTape w) 0
    (by intro p _ _; simp) r₀ hr₀ (by
      intro r hr
      rw [horbit r hr]
      exact guardBlock_segment b x _ (hpos r hr) out)
    (by rw [hexit]; rfl) T rfl
  have hs : (∑ r ∈ Finset.range (r₀ + 1),
      guardTime b (counterLoopOrbit (guardBlockTM b) (guardTime b) c r)) ≤
        (r₀ + 1) * (b + 1) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range (r₀ + 1), (b + 1) :=
        Finset.sum_le_sum (fun _ _ => Nat.min_le_left _ _)
      _ = _ := by simp
  have hc := counterOverhead_le_of_le w (r₀ + 1) (by omega)
  have hn : r₀ + 1 ≤ x.length + 1 := by
    have := Nat.mul_le_mul_right r₀ (show 1 ≤ b + 1 by omega)
    simp only [one_mul] at this
    omega
  refine ⟨T, ?_, ?_⟩
  · calc
      T ≤ (r₀ + 1) * (b + 1) + (4 * (r₀ + 1) + 2 * w.length) :=
        Nat.add_le_add hs hc
      _ = (b + 5) * (r₀ + 1) + 2 * w.length := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left (b + 5) hn) _
  · dsimp only
    have he : (binaryGuardTM b).runFrom (binaryGuardStart b x j hj out w) T = _ := hrun.1
    rw [he, hexit]
    exact ⟨rfl, rfl, rfl, hrun.2.1⟩



/-- The last bit, with the empty word accepted as canonical zero. -/
private def canonBitsOK (w : List Bool) : Bool := w.getLast?.getD true

/-- A last-symbol fold has exactly the finite scan's canonicality verdict. -/
private lemma canonBits_fold (w : List Bool) (a : Bool) :
    w.foldl (fun _ b => b) a = w.getLast?.getD a := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons, ih, List.getLast?_cons, Option.getD_some]

/-- A finite last-bit check suffices to recover the canonical binary word.

**Proof sketch.** Remove the low bit. A nonempty canonical tail has positive
value, so adjoining either low bit is exactly the binary constructor law;
the singleton case admits only the bit one. -/
private lemma canonBits_of_last (w : List Bool) :
    canonBitsOK w = true → (w.foldr Nat.bit 0).bits = w := by
  induction w with
  | nil => intro _; simp
  | cons b w ih =>
    intro h
    cases w with
    | nil => cases b <;> simp_all [canonBitsOK, Nat.bit]
    | cons c w =>
      have htail : canonBitsOK (c :: w) = true := by
        simpa only [canonBitsOK, List.getLast?_cons_cons] using h
      have he := ih htail
      have hne : (c :: w).foldr Nat.bit 0 ≠ 0 := by
        intro hz
        simp only [hz, Nat.zero_bits] at he
        contradiction
      rw [List.foldr_cons, Nat.bits_append_bit _ b (fun hz => (hne hz).elim), he]

/-- Canonical natural-number digits pass the finite last-bit check.

**Proof sketch.** Use the public binary recursion from zero and one, so every
extension has a nonzero tail. The public decoding identity shows that such
a tail has nonempty digits; its last bit is unchanged by the extension. -/
private lemma canonBits_bits (n : ℕ) : canonBitsOK n.bits = true := by
  refine Nat.binaryRecFromOne (motive := fun m => canonBitsOK m.bits = true)
    (by simp [canonBitsOK]) (by simp [canonBitsOK]) ?_ n
  intro low tail nonzero canonical
  have nonempty : tail.bits ≠ [] := by
    intro hempty
    have decoded := codeBitsNat_bits tail
    rw [hempty] at decoded
    exact nonzero decoded.symm
  rw [Nat.bits_append_bit tail low (fun hz => (nonzero hz).elim)]
  cases htail : tail.bits with
  | nil => exact (nonempty htail).elim
  | cons first rest =>
    simpa only [canonBitsOK, htail, List.getLast?_cons_cons] using canonical

/-- The finite check recognizes exactly the canonical little-endian words. -/
private lemma canonBitsOK_iff (w : List Bool) :
    canonBitsOK w = true ↔ w = (w.foldr Nat.bit 0).bits := by
  constructor
  · intro h
    exact (canonBits_of_last w h).symm
  · intro h
    calc
      canonBitsOK w = canonBitsOK (w.foldr Nat.bit 0).bits := congrArg canonBitsOK h
      _ = true := canonBits_bits _

/-- A spare high zero makes the state-count successor nonoverflowing. -/
private def canonCount (w : List Bool) : List Bool :=
  (incFixed (w ++ [false])).getD []

/-- Incrementing with a spare high zero preserves the enlarged width and
represents one more than the original header, including the empty header.

**Proof sketch.** Follow the carry through the low one bits. At the first
zero the increment stops; the appended zero guarantees that this happens.
Each recursive carry doubles the value equation. -/
private lemma canonCount_spec (w : List Bool) :
    incFixed (w ++ [false]) = some (canonCount w) ∧
      (canonCount w).length = w.length + 1 ∧
      (canonCount w).foldr Nat.bit 0 = w.foldr Nat.bit 0 + 1 := by
  induction w with
  | nil => simp [canonCount, incFixed, Nat.bit]
  | cons b w ih =>
    cases b with
    | false =>
      simp [canonCount, incFixed, List.foldr_append, Nat.bit]
    | true =>
      have he : canonCount (true :: w) = false :: canonCount w := by
        change ((incFixed (w ++ [false])).map (false :: ·)).getD [] = _
        rw [ih.1]
        rfl
      rw [he]
      simp only [List.cons_append, incFixed, ih.1, Option.map_some,
        List.length_cons, ih.2.1, List.foldr_cons, ih.2.2, Nat.bit]
      simp [Nat.mul_add, Nat.add_assoc]

/-- The canonical-bit checker is the public two-pass scan, with the last
symbol as accumulator and an identity return pass. -/
private def canonBitsTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool (ScanPhase Bool) :=
  scanTM k i (scanFold (fun _ b => b)) scanKeep true

/-- The canonicality scan preserves every seam word, the native input
position and the empty output, and avoids both verdict anchors until its
exact linear-time return.

**Proof sketch.** Specialize the public scan contract to the last-bit fold.
Its pure result preserves the scanned word, so the interval rewrite is the
original buffer at every cell. The shared contract supplies both exit cuts. -/
private lemma canonBitsTM_run (k : ℕ) (i : Fin k) (α : List Bool)
    (w : Fin k → List Bool) :
    (canonBitsTM k i).runFrom (Cfg.ofWords (input := α) (.fwd true) w)
        (2 * (w i).length + 2) = Cfg.ofWords (.done (canonBitsOK (w i))) w ∧
      (∀ t < 2 * (w i).length + 2, ∀ b,
        ((canonBitsTM k i).runFrom (Cfg.ofWords (input := α) (.fwd true) w) t).state ≠
          some (.done b)) := by
  let d := Cfg.ofWords (input := α) (ScanPhase.fwd true) w
  have h := scanTM_run_ofCfg i (scanFold (fun (_ : Bool) b => b)) scanKeep true
    (w i) d rfl (by intro p _ _; simp [d, Cfg.ofWords])
  rw [scanResult_fold, canonBits_fold] at h
  refine ⟨h.1.trans ?_, h.2.1⟩
  apply Cfg.ext <;> try rfl
  funext j z
  dsimp only [d, Cfg.ofWords]
  split_ifs with hz
  · rcases hz with ⟨rfl, _, _⟩
    simp
  · rfl

/-- A strict first-return form of the inherited physical header call, ready
for the public seam combinator even when the original anchors coincide.

**Proof sketch.** If the original anchors differ, time zero is excluded by
that inequality. If they coincide, apply the public release adapter, whose
fresh entry executes the call before any return can be dispatched. The
machine and all tape/output data are otherwise those of the inherited call. -/
private lemma exists_canonHeaderSeam :
    ∃ (C : FinTM Bool) (entry exit : C.State) (a : ℕ), 0 < C.k ∧
      ∀ α : List Bool, ∃ t ≤ a * (α.length + 1), 0 < t ∧
        (∀ u < t,
          (C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) u).state ≠
            some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) t =
          Cfg.ofWords exit (stateWord C.k (canonHeader α)) := by
  classical
  obtain ⟨C, entry, exit, a, hk, hC⟩ := exists_canonHeaderCall
  by_cases he : entry = exit
  · subst exit
    let R : FinTM Bool := {
      k := C.k
      State := Unit ⊕ C.State
      tm := seamReleaseTM C.tm entry }
    refine ⟨R, Sum.inl (), Sum.inr entry, a, hk, ?_⟩
    intro α
    obtain ⟨t, ht, hpos, hcut, hrun⟩ := hC α
    have hr := seamReleaseTM_firstReturn C.tm entry rfl hpos hrun rfl hcut
    refine ⟨t, ht, hpos, ?_, ?_⟩
    · simpa only [R, Cfg.ofWords, Cfg.mapState, Option.map_some] using hr.2
    · simpa only [R, Cfg.ofWords, Cfg.mapState, Option.map_some] using hr.1
  · refine ⟨C, entry, exit, a, hk, ?_⟩
    intro α
    obtain ⟨t, ht, hpos, hcut, hrun⟩ := hC α
    refine ⟨t, ht, hpos, ?_, hrun⟩
    intro u hu
    by_cases hz : u = 0
    · subst u
      change some entry ≠ some exit
      exact fun h => he (Option.some.inj h)
    · exact hcut u (by omega) hu

/-- The nonoverflowing count word is computed in linear time by two public
primitives: append a zero, then increment at that fixed width.

**Proof sketch.** Compose the append-bit and fixed-width increment machines.
Their linear budgets compose to a linear budget; the added constant is
absorbed using the positive input-length offset. -/
private lemma exists_canonCountTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime canonCount (fun n => a * (n + 1)) := by
  obtain ⟨A, a, hA⟩ := FinTM.computesFunInTime_appendBit false
  obtain ⟨B, b, hB⟩ := FinTM.computesFunInTime_incFixed
  obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_comp hA hB
    (fun _ _ h => Nat.mul_le_mul_left b (by omega))
  refine ⟨M, c * (a + b * (a + 1) + 1), ?_⟩
  intro w
  apply (hM w).mono
  calc
    c * (a * (w.length + 1) + b * (a * (w.length + 1) + 1) + 1) ≤
        c * ((a * (w.length + 1) + b * (a * (w.length + 1) + 1) + 1) +
          (b + 1) * w.length) := Nat.mul_le_mul_left c (Nat.le_add_right _ _)
    _ = _ := by ring

/-- Emit the scan's verdict on its final transition. All scanning transitions
are the existing public scan; only its live exits receive a halting action. -/
private def canonVerdictTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool (ScanPhase Bool) where
  q₀ := .fwd true
  tr := fun q inp work => match q with
    | .done b => ⟨0, fun _ => (none, 0), some b, none⟩
    | _ => (canonBitsTM k i).tr q inp work

/-- From a loaded word, the verdict wrapper halts with exactly its canonicality
bit after the public scan and one emitting transition.

**Proof sketch.** The scan avoids both verdict states until its return. Apply
the public guarded-agreement transfer on those states, then execute the one
new halting action. No scan trace is re-proved. -/
private lemma canonVerdictTM_run (k : ℕ) (i : Fin k) (α : List Bool)
    (w : Fin k → List Bool) :
    let c := (canonVerdictTM k i).runFrom
      (Cfg.ofWords (input := α) (.fwd true) w) (2 * (w i).length + 3)
    c.state = none ∧ c.output = [canonBitsOK (w i)] := by
  obtain ⟨hscan, hcut⟩ := canonBitsTM_run k i α w
  have hid : ⇑(Function.Embedding.refl (ScanPhase Bool)) = id := rfl
  have hpre := MultiTapeTM.runFrom_mapState_of_agreeOn
    (canonBitsTM k i) (canonVerdictTM k i) (Function.Embedding.refl _)
    (fun q => ∀ b, q ≠ ScanPhase.done b)
    (by
      intro q hq inp work
      simp only [hid, id_eq]
      cases q with
      | fwd a => simp [canonVerdictTM, Action.mapState]
      | bwd a => simp [canonVerdictTM, Action.mapState]
      | done b => exact (hq b rfl).elim)
    (Cfg.ofWords (input := α) (.fwd true) w) (2 * (w i).length + 2)
    (by
      intro u hu q hq b he
      exact hcut u hu b (hq.trans (congrArg some he)))
  simp only [hid, Cfg.mapState, Option.map_id, id_eq] at hpre
  change ((canonVerdictTM k i).runFrom _ ((2 * (w i).length + 2) + 1)).state = none ∧ _
  rw [MultiTapeTM.runFrom_succ_eq_step', hpre, hscan]
  simp [MultiTapeTM.step, Cfg.ofWords, canonVerdictTM, Action.apply]


/-- The loaded-header scan, reached through the inherited native-input call,
computes the canonicality bit in linear time.

**Proof sketch.** Use the strict loader seam, then the public scan with its
single emitting exit. The loader restores the native input and clean work
heads. Its returned header has length at most the input length, so the two
linear ledgers and the one dispatch step have a common linear bound. -/
private lemma exists_canonHeaderBitsTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun α => [canonBitsOK (canonHeader α)])
        (fun n => a * (n + 1)) := by
  classical
  obtain ⟨C, entry, exit, a, hk, hC⟩ := exists_canonHeaderSeam
  let i : Fin C.k := ⟨0, hk⟩
  let V := canonVerdictTM C.k i
  let L := seamCompTM C.tm exit V (ScanPhase.fwd true)
  let M : FinTM Bool := {
    k := C.k
    State := C.State ⊕ ScanPhase Bool
    tm := { L with q₀ := Sum.inl entry } }
  refine ⟨M, a + 4, ?_⟩
  intro α
  obtain ⟨t, ht, _, hcut, hload⟩ := hC α
  let w := stateWord C.k (canonHeader α)
  have hw : w i = canonHeader α := by simp [w, stateWord, i]
  let v := V.runFrom (Cfg.ofWords (input := α) (.fwd true) w)
    (2 * (w i).length + 3)
  have hv : v.state = none ∧ v.output = [canonBitsOK (w i)] :=
    canonVerdictTM_run C.k i α w
  have hrun := seamCompTM_run_ofCfg C.tm exit V (.fwd true)
    (c₃ := v) hload rfl hcut (by
      simp only [Cfg.ofWords, Cfg.mapState, Option.map_some]
      rfl)
  have hinit : M.tm.initCfg α =
      (Cfg.ofWords (input := α) entry (fun _ => [])).mapState Sum.inl := by
    simp [M, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, Cfg.mapState,
      FinTM.bufferTape_nil]
  have hbase : M.ComputesInTime α [canonBitsOK (canonHeader α)]
      (t + 1 + (2 * (w i).length + 3)) := by
    apply (FinTM.computesInTime_iff M _ _ _).mpr
    rw [hinit]
    change (L.runFrom _ _).state = none ∧ (L.runFrom _ _).output = _
    rw [hrun]
    simpa only [Cfg.mapState, hv.1, Option.map_none, hw] using hv
  apply hbase.mono
  have hlen := canonHeader_length α
  rw [hw]
  calc
    t + 1 + (2 * (canonHeader α).length + 3) ≤
        a * (α.length + 1) + 2 * α.length + 4 := by omega
    _ ≤ (a + 4) * (α.length + 1) := by
      rw [Nat.add_mul]
      omega

/-- Header validity keeps pair-grammar failure separate from the loader's
empty-word fallback; a successfully decoded empty header is canonical zero. -/
private def canonHeaderOK (α : List Bool) : Bool :=
  (pairDecode α).isSome && canonBitsOK (canonHeader α)

/-- The physical header predicate tests precisely successful pair decoding
and canonical binary state-count digits. -/
private lemma canonHeaderOK_iff (α : List Bool) :
    canonHeaderOK α = true ↔
      ∃ bits rest, pairDecode α = some (bits, rest) ∧ bits = (codeBitsNat bits).bits := by
  cases hp : pairDecode α with
  | none => simp [canonHeaderOK, hp]
  | some p =>
    rcases p with ⟨bits, rest⟩
    simp [canonHeaderOK, canonHeader, hp, canonBitsOK_iff, codeBitsNat]

/-- Header rejection is a genuine scanner failure, never an accidental
acceptance of the loader's default empty word.

**Proof sketch.** Pair failure is the scanner's first failure. For a decoded
pair, failure of the last-bit test is equivalent to failure of the scanner's
canonical-binary equality. -/
private lemma scan_eq_none_of_canonHeaderOK (F : MachineFormat) (α : List Bool)
    (h : canonHeaderOK α = false) : F.scan α = none := by
  cases hp : pairDecode α with
  | none => simp [CodeFormat.scan, hp]
  | some p =>
    rcases p with ⟨bits, rest⟩
    have hb : bits ≠ (codeBitsNat bits).bits := by
      intro he
      have ht : canonHeaderOK α = true :=
        (canonHeaderOK_iff α).mpr ⟨bits, rest, hp, he⟩
      simp [h] at ht
    simp [CodeFormat.scan, hp, hb]

/-- A total linear-time validator checks pair success separately and runs the
loaded-header checker only on successful pairs.

**Proof sketch.** Branch on the public pair-validity primitive. The positive
branch is the loader-plus-scan machine; the negative branch emits false. The
public conditional wrapper combines these computations, and the maximum of
the two branch budgets is bounded by their sum. -/
private lemma exists_canonHeaderOKTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun α => [canonHeaderOK α]) (fun n => a * (n + 1)) := by
  obtain ⟨D, a, hD⟩ := FinTM.computesFunInTime_pairValid
  obtain ⟨B, b, hB⟩ := exists_canonHeaderBitsTM
  obtain ⟨E, e, hE⟩ := FinTM.computesFunInTime_const [false]
  obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_cond hD hB hE
  refine ⟨M, c * (a + b + e + 1), ?_⟩
  intro α
  have hout : (if (pairDecode α).isSome then [canonBitsOK (canonHeader α)] else [false]) =
      [canonHeaderOK α] := by
    cases hb : (pairDecode α).isSome <;> simp [canonHeaderOK, hb]
  change M.ComputesInTime α [canonHeaderOK α] _
  rw [← hout]
  apply (hM α).mono
  change c * (a * (α.length + 1) + max (b * (α.length + 1)) (e * (α.length + 1)) + 1) ≤
    (c * (a + b + e + 1)) * (α.length + 1)
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left c
  calc
    a * (α.length + 1) + max (b * (α.length + 1)) (e * (α.length + 1)) + 1 ≤
        a * (α.length + 1) + (b + e) * (α.length + 1) + 1 := by
      rw [Nat.add_mul]
      omega
    _ ≤ (a + b + e + 1) * (α.length + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- One positive block size enforces both necessary length guards. Taking
its maximum combines the format guard and the grammar guard, including
formats whose own guard is zero. -/
private def canonGuardBlock (F : MachineFormat) : ℕ :=
  max F.guard ((4 * F.k + 5) * 3 ^ (F.k + 1))

/-- The grammar component makes the combined guard strictly positive. -/
private lemma canonGuardBlock_pos (F : MachineFormat) : 0 < canonGuardBlock F := by
  have h : 0 < (4 * F.k + 5) * 3 ^ (F.k + 1) := by positivity
  exact h.trans_le (Nat.le_max_right _ _)

/-- Failure of the combined guard selects the specified fallback.

**Proof sketch.** The maximum is one of the two block sizes. In the format
case cite its public early-rejection law; in the grammar case cite the
inherited positive-grammar rejection law. -/
private lemma decode_of_canonGuard (F : MachineFormat) (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest))
    (hg : rest.length < canonGuardBlock F * (codeBitsNat bits + 1)) :
    F.decode α = F.fallback := by
  rcases le_total F.guard ((4 * F.k + 5) * 3 ^ (F.k + 1)) with h | h
  · rw [canonGuardBlock, max_eq_right h] at hg
    exact decode_of_grammar_guard F α bits rest hp hg
  · rw [canonGuardBlock, max_eq_left h] at hg
    exact F.toCodeFormat.decode_of_guard_lt α bits rest hp hg

/-- At the real post-header offset, a preloaded successor counter checks
both guards with a bound independent of the header's numerical value.
The result retains the inherited strict cuts at both live exits.

**Proof sketch.** Pair-reader soundness identifies the native remainder
position. The spare-bit increment supplies exactly `n + 1` in the binary
value convention of the inherited guard. Select its proved success or
escape contract by the remainder-length comparison, then enlarge both
budgets to the same linear bound. Loading, bank preservation and native
seeking are separate composition obligations, not hypotheses hidden here. -/
private lemma canonGuard_run (F : MachineFormat) (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest)) :
    let B := canonGuardBlock F
    let j := 2 * bits.length + 2
    ∃ hj : j ≤ α.length, ∃ T ≤ (B + 4) * (α.length + 1) + 2 * (bits.length + 1),
      let c := (binaryGuardTM (B - 1)).runFrom
        (binaryGuardStart (B - 1) α j hj [] (canonCount bits)) T
      c.state = some (if B * (codeBitsNat bits + 1) ≤ rest.length then .done else .escape) ∧
        c.output = [] ∧
        c.inputPos.val = (if B * (codeBitsNat bits + 1) ≤ rest.length
          then j + B * (codeBitsNat bits + 1) + 1 else α.length + 1) ∧
        (∀ u < T,
          ((binaryGuardTM (B - 1)).runFrom
            (binaryGuardStart (B - 1) α j hj [] (canonCount bits)) u).state ≠ some .done ∧
          ((binaryGuardTM (B - 1)).runFrom
            (binaryGuardStart (B - 1) α j hj [] (canonCount bits)) u).state ≠ some .escape) := by
  dsimp only
  set B := canonGuardBlock F
  set j := 2 * bits.length + 2
  have hpos : 0 < B := canonGuardBlock_pos F
  have hblock : B - 1 + 1 = B := by omega
  have hlen : α.length = j + rest.length := by
    rw [eq_pairEncode_of_pairDecode α bits rest hp, length_pairEncode]
  have hj : j ≤ α.length := by omega
  have hcount : Nat.ofDigits 2 ((canonCount bits).map Bool.toNat) = codeBitsNat bits + 1 := by
    rw [← foldr_bit_eq_ofDigits]
    exact (canonCount_spec bits).2.2
  have hwidth := (canonCount_spec bits).2.1
  refine ⟨hj, ?_⟩
  by_cases hg : B * (codeBitsNat bits + 1) ≤ rest.length
  · have hfit : j + (B - 1 + 1) * Nat.ofDigits 2 ((canonCount bits).map Bool.toNat) ≤
        α.length := by rw [hblock, hcount]; omega
    obtain ⟨T, hT, hs, ho, hi, hcut⟩ :=
      binaryGuard_done (B - 1) α j hj [] (canonCount bits) hfit
    refine ⟨T, hT.trans ?_, ?_⟩
    · rw [hwidth]
      have hm := Nat.mul_le_mul_right (α.length + 1) (show 5 ≤ B + 4 by omega)
      omega
    · simp only [if_pos hg]
      refine ⟨hs, ho, ?_, hcut⟩
      simpa only [hblock, hcount] using hi
  · have hshort : α.length < j + (B - 1 + 1) * Nat.ofDigits 2 ((canonCount bits).map Bool.toNat) := by
      rw [hblock, hcount]
      omega
    obtain ⟨T, hT, hs, ho, hi, hcut⟩ :=
      binaryGuard_escape (B - 1) α j hj [] (canonCount bits) hshort
    refine ⟨T, ?_, ?_⟩
    · simpa only [show B - 1 + 5 = B + 4 by omega, hwidth] using hT
    · simp only [if_neg hg]
      exact ⟨hs, ho, hi, hcut⟩


/-- A clean install call with a cut that includes time zero. The public
release adapter handles coincident entry and exit anchors; otherwise their
inequality supplies the only missing case.

**Proof sketch.** Apply the install row, preserving its exact ledger. If
its anchors coincide, use the public positive-return adapter. Otherwise
separate zero from the positive times already covered by the row. -/
private lemma canonStrictInstall (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (a : ℕ), 0 < C.k ∧
      ∀ x arg : List Bool,
        ∃ t ≤ a * (T arg.length + arg.length + (f arg).length + 1),
          0 < t ∧
          (∀ u < t, (C.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord C.k arg)) u).state ≠ some exit) ∧
          C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
            Cfg.ofWords exit (stateWord C.k (f arg)) := by
  classical
  obtain ⟨C, entry, exit, a, hk, hC⟩ := FinTM.exists_installCallTM M f T hM
  by_cases he : entry = exit
  · subst exit
    let R : FinTM Bool := {
      k := C.k
      State := Unit ⊕ C.State
      tm := seamReleaseTM C.tm entry }
    refine ⟨R, Sum.inl (), Sum.inr entry, a, hk, ?_⟩
    intro x arg
    obtain ⟨t, bound, pos, cut, run⟩ := hC x arg
    obtain ⟨released, first⟩ := seamReleaseTM_firstReturn C.tm entry rfl pos run rfl cut
    exact ⟨t, bound, pos, by
      simpa only [Cfg.ofWords, Cfg.mapState, Option.map_some] using first, by
      simpa only [Cfg.ofWords, Cfg.mapState, Option.map_some] using released⟩
  · refine ⟨C, entry, exit, a, hk, ?_⟩
    intro x arg
    obtain ⟨t, bound, pos, cut, run⟩ := hC x arg
    refine ⟨t, bound, pos, ?_, run⟩
    intro u hu
    cases u with
    | zero => exact fun h => he (Option.some.inj h)
    | succ u => exact cut (u + 1) (Nat.succ_pos _) hu

/-- Configuration assembly from the public selected-tape and frame laws.
This is the common extensionality step for word banks and native seeks.

**Proof sketch.** Split each host tape by membership in the embedded bank;
use the public selected projections there and the public frame at time zero
elsewhere. The other three fields are supplied by the caller. -/
private lemma canonEmbedEq {m k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k)
    (c : Cfg m Bool S x) (d : Cfg k Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (hs : c.state = d.state) (hp : c.inputPos = d.inputPos) (ho : c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (ι i) ∧
      c.workTapePos i = d.workTapePos (ι i))
    (outside : ∀ j, j ∉ Set.range ι →
      tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    embedEmitCfg ι tapes heads [] c = d := by
  apply Cfg.ext hs hp ?_ ?_ (by simpa only [embedEmitCfg, List.nil_append] using ho)
  all_goals
    funext j
    by_cases located : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := located
      first
      | exact (embedEmitCfg_selected_tape ι tapes heads [] c i).trans (selected i).1
      | exact (embedEmitCfg_selected_pos ι tapes heads [] c i).trans (selected i).2
    · have fixed := (embedEmitTM_frame ι M tapes heads [] c 0).1 j located
      first
      | exact fixed.1.trans (outside j located).1
      | exact fixed.2.trans (outside j located).2


/-- The public selected-tape and frame laws identify an embedded clean bank
with the requested whole-bank word layout. No private slot inverse is used.

**Proof sketch.** On the image of the tape embedding use its selected-tape
laws; off that image use its frame law at time zero. Configuration
extensionality then identifies the words and heads simultaneously. -/
private lemma canonEmbedWords {m k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (q : S)
    (v : Fin m → List Bool) (ambient wanted : Fin k → List Bool)
    (selected : ∀ i, wanted (ι i) = v i)
    (outside : ∀ j, j ∉ Set.range ι → ambient j = wanted j) :
    embedEmitCfg ι (fun j => FinTM.bufferTape (ambient j)) (fun _ => 0) []
        (Cfg.ofWords (input := x) q v) = Cfg.ofWords q wanted := by
  apply canonEmbedEq M ι _ _ _ _ rfl rfl rfl
  · intro i
    exact ⟨congrArg FinTM.bufferTape (selected i).symm, rfl⟩
  · intro j hj
    exact ⟨congrArg FinTM.bufferTape (outside j hj), rfl⟩

/-- A clean tape-resident argument can be preserved on tape zero while a
public install call puts its transformed value on tape one. Every other
tape is blank again on return. This is a composition of the public copy,
embedding and seam rows, not an additional call host.

**Proof sketch.** Reserve tape zero, copy its word to the first tape of a
fresh install bank, and run the strict install there by public embedding.
The bank frame preserves the original word. The copy and dispatch costs
are absorbed into four times the argument-length part of the call ledger. -/
private lemma canonPreserveInstall (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (dst : Fin C.k) (entry exit : C.State) (a : ℕ),
      dst.val = 1 ∧ ∀ x arg : List Bool,
        ∃ t ≤ a * (T arg.length + arg.length + (f arg).length + 1),
          (∀ u < t, (C.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord C.k arg)) u).state ≠ some exit) ∧
          C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
            Cfg.ofWords exit (Function.update (stateWord C.k arg) dst (f arg)) := by
  classical
  obtain ⟨I, enter, leave, a, positive, installed⟩ := canonStrictInstall M f T hM
  let zero : Fin I.k := ⟨0, positive⟩
  let dst : Fin (I.k + 1) := zero.succ
  let bank : Fin I.k ↪ Fin (I.k + 1) := Fin.succEmb I.k
  let P := copyTM (Symbol := Bool) (I.k + 1) 0 dst
  let E := embedEmitTM bank I.tm
  let C : FinTM Bool := {
    k := I.k + 1
    State := SweepPhase ⊕ I.State
    tm := { seamCompTM P .done E enter with q₀ := Sum.inl .sweep } }
  refine ⟨C, dst, Sum.inl .sweep, Sum.inr leave, a + 4, rfl, ?_⟩
  intro x arg
  let w := stateWord (I.k + 1) arg
  let copied := Function.update w dst arg
  let result := Function.update w dst (f arg)
  have source : w 0 = arg := by simp [w, stateWord]
  have fresh : w dst = [] := by simp [w, stateWord, dst]
  have distinct : (0 : Fin (I.k + 1)) ≠ dst := by
    intro h
    have := congrArg Fin.val h
    simp [dst] at this
  have onBank (v : List Bool) (i : Fin I.k) :
      (Function.update w dst v) (bank i) = stateWord I.k v i := by
    simp [w, stateWord, dst, bank, zero, Function.update_apply, Fin.ext_iff]
  have offBank (j : Fin (I.k + 1)) (hj : j ∉ Set.range bank) : copied j = result j := by
    have ne : j ≠ dst := fun eq => hj ⟨zero, eq.symm⟩
    simp only [copied, result, Function.update_of_ne ne]
  obtain ⟨t₀, budget₀, cut₀, run₀⟩ :=
    copyTM_run (x := x) (I.k + 1) 0 dst distinct w fresh
  rw [source] at budget₀ run₀
  obtain ⟨t₁, budget₁, _, cut₁, run₁⟩ := installed x arg
  have lift (u : ℕ) : E.runFrom (Cfg.ofWords (input := x) enter copied) u =
      embedEmitCfg bank (fun j => FinTM.bufferTape (copied j)) (fun _ => 0) []
        (I.tm.runFrom (Cfg.ofWords (input := x) enter (stateWord I.k arg)) u) := by
    rw [← canonEmbedWords I.tm bank enter (stateWord I.k arg) copied copied
      (onBank arg) (fun _ _ => rfl)]
    exact embedEmitTM_runFrom bank I.tm _ _ _ _ u
  have second : E.runFrom (Cfg.ofWords (input := x) enter copied) t₁ =
      Cfg.ofWords leave result := by
    rw [lift, run₁]
    exact canonEmbedWords I.tm bank leave (stateWord I.k (f arg)) copied result
      (onBank (f arg)) offBank
  have secondCut (u : ℕ) (hu : u < t₁) :
      (E.runFrom (Cfg.ofWords (input := x) enter copied) u).state ≠ some leave := by
    rw [lift]
    exact cut₁ u hu
  have second' : E.runFrom
      ((Cfg.ofWords (input := x) SweepPhase.done copied).mapState fun _ => enter) t₁ =
      Cfg.ofWords leave result := second
  have cut' (u : ℕ) (hu : u < t₁) :
      (E.runFrom ((Cfg.ofWords (input := x) SweepPhase.done copied).mapState
        fun _ => enter) u).state ≠ some leave := secondCut u hu
  have whole := seamCompTM_run_ofCfg P .done E enter run₀ rfl cut₀ second'
  have first := seamCompTM_firstReturn_ofCfg P .done E enter leave
    run₀ rfl cut₀ second' rfl cut'
  refine ⟨t₀ + 1 + t₁, ?_, ?_, ?_⟩
  · calc
      t₀ + 1 + t₁ ≤ 3 * arg.length + 4 +
          a * (T arg.length + arg.length + (f arg).length + 1) := by omega
      _ ≤ (a + 4) * (T arg.length + arg.length + (f arg).length + 1) := by
        rw [Nat.add_mul]
        omega
  · simpa only [C, Cfg.ofWords, Cfg.mapState, Option.map_some] using first
  · simpa only [C, result, w, Cfg.ofWords, Cfg.mapState, Option.map_some] using whole


/-- Load the undoubled header and install its nonoverflowing successor on
a separate tape. The original header remains on tape zero, tape one holds
`canonCount`, all other tapes are blank, and the native head is restored.
The contract retains a strict first-exit cut for subsequent seam composition.

**Proof sketch.** Extract the count-computing machine before applying the
preserving install construction. Embed that construction and the inherited
header loader into one bank of the larger tape count, then join them with
the public seam. The successor width is the header width plus one, so the
complete loading, copying and installation ledger is linear in the input. -/
private lemma exists_canonHeaderCountSeam :
    ∃ (C : FinTM Bool) (dst : Fin C.k) (entry exit : C.State) (a : ℕ),
      dst.val = 1 ∧ ∀ α : List Bool, ∃ t ≤ a * (α.length + 1),
        (∀ u < t, (C.tm.runFrom
          (Cfg.ofWords (input := α) entry (fun _ => [])) u).state ≠ some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) t =
          Cfg.ofWords exit (Function.update (stateWord C.k (canonHeader α)) dst
            (canonCount (canonHeader α))) := by
  classical
  obtain ⟨L, lentry, lexit, a, hl, load⟩ := exists_canonHeaderSeam
  obtain ⟨N, b, count⟩ := exists_canonCountTM
  obtain ⟨P, pdst, pentry, pexit, c, hdst, install⟩ :=
    canonPreserveInstall N canonCount (fun n => b * (n + 1)) count
  let K := max L.k P.k
  let lb : Fin L.k ↪ Fin K := Fin.castLEEmb (Nat.le_max_left _ _)
  let pb : Fin P.k ↪ Fin K := Fin.castLEEmb (Nat.le_max_right _ _)
  let A := embedEmitTM lb L.tm
  let B := embedEmitTM pb P.tm
  let C : FinTM Bool := {
    k := K
    State := L.State ⊕ P.State
    tm := { seamCompTM A lexit B pentry with q₀ := Sum.inl lentry } }
  refine ⟨C, pb pdst, Sum.inl lentry, Sum.inr pexit, a + c * (b + 2) + 1, hdst, ?_⟩
  intro α
  let header := canonHeader α
  let w := stateWord K header
  let result := Function.update w (pb pdst) (canonCount header)
  obtain ⟨t₀, bound₀, _, cut₀, run₀⟩ := load α
  obtain ⟨t₁, bound₁, cut₁, run₁⟩ := install α header
  have loadLift (u : ℕ) :
      A.runFrom (Cfg.ofWords (input := α) lentry (fun _ => [])) u =
        embedEmitCfg lb (fun _ => FinTM.bufferTape []) (fun _ => 0) []
          (L.tm.runFrom (Cfg.ofWords (input := α) lentry (fun _ => [])) u) := by
    rw [← canonEmbedWords L.tm lb lentry (fun _ => []) (fun _ => []) (fun _ => [])
      (fun _ => rfl) (fun _ _ => rfl)]
    exact embedEmitTM_runFrom lb L.tm _ _ _ _ u
  have loaded : A.runFrom (Cfg.ofWords (input := α) lentry (fun _ => [])) t₀ =
      Cfg.ofWords lexit w := by
    rw [loadLift, run₀]
    apply canonEmbedWords L.tm lb lexit (stateWord L.k header) (fun _ => []) w
    · intro i
      rfl
    · intro j hj
      have nonzero : j.val ≠ 0 := by
        intro hz
        apply hj
        exact ⟨⟨0, hl⟩, Fin.ext hz.symm⟩
      simp [w, stateWord, nonzero]
  have first₀ (u : ℕ) (hu : u < t₀) :
      (A.runFrom (Cfg.ofWords (input := α) lentry (fun _ => [])) u).state ≠ some lexit := by
    rw [loadLift]
    exact cut₀ u hu
  have installLift (u : ℕ) : B.runFrom (Cfg.ofWords (input := α) pentry w) u =
      embedEmitCfg pb (fun j => FinTM.bufferTape (w j)) (fun _ => 0) []
        (P.tm.runFrom (Cfg.ofWords (input := α) pentry (stateWord P.k header)) u) := by
    rw [← canonEmbedWords P.tm pb pentry (stateWord P.k header) w w
      (fun _ => rfl) (fun _ _ => rfl)]
    exact embedEmitTM_runFrom pb P.tm _ _ _ _ u
  have installed : B.runFrom (Cfg.ofWords (input := α) pentry w) t₁ =
      Cfg.ofWords pexit result := by
    rw [installLift, run₁]
    apply canonEmbedWords P.tm pb pexit
      (Function.update (stateWord P.k header) pdst (canonCount header)) w result
    · intro i
      exact congrFun (Function.update_comp_eq_of_injective w pb.injective pdst
        (canonCount header)) i
    · intro j hj
      have ne : j ≠ pb pdst := fun h => hj ⟨pdst, h.symm⟩
      exact (Function.update_of_ne ne _ _).symm
  have first₁ (u : ℕ) (hu : u < t₁) :
      (B.runFrom (Cfg.ofWords (input := α) pentry w) u).state ≠ some pexit := by
    rw [installLift]
    exact cut₁ u hu
  have installed' : B.runFrom
      ((Cfg.ofWords (input := α) lexit w).mapState fun _ => pentry) t₁ =
      Cfg.ofWords pexit result := installed
  have first₁' (u : ℕ) (hu : u < t₁) :
      (B.runFrom ((Cfg.ofWords (input := α) lexit w).mapState fun _ => pentry) u).state ≠
        some pexit := first₁ u hu
  have run := seamCompTM_run_ofCfg A lexit B pentry loaded rfl first₀ installed'
  have cut := seamCompTM_firstReturn_ofCfg A lexit B pentry pexit
    loaded rfl first₀ installed' rfl first₁'
  have boundCount : t₁ ≤ c * (b + 2) * (α.length + 1) := by
    have width := (canonCount_spec header).2.1
    rw [width] at bound₁
    calc
      t₁ ≤ c * (b * (header.length + 1) + header.length + (header.length + 1) + 1) := bound₁
      _ = c * (b + 2) * (header.length + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right (canonHeader_length α) 1)
  refine ⟨t₀ + 1 + t₁, ?_, ?_, ?_⟩
  · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  · simpa only [C, Cfg.ofWords, Cfg.mapState, Option.map_some] using cut
  · simpa only [C, result, w, header, Cfg.ofWords, Cfg.mapState, Option.map_some] using run


/-- Binary address of the first bit after the doubled header and its separator.
A low one below the successor of the header's length represents `2|w|+3`.
The seek contract accepts the harmless spare high zero. -/
private def canonOffset (w : List Bool) : List Bool :=
  true :: canonCount w.length.bits

/-- The offset word represents the actual native-input address and has
length at most the original header length plus two.

**Proof sketch.** The existing successor-word law gives the length plus
one. Prepending a low one doubles that value and adds one. The public
binary-size inequality bounds the length of the length counter. -/
private lemma canonOffset_spec (w : List Bool) :
    Nat.ofDigits 2 ((canonOffset w).map Bool.toNat) = 2 * w.length + 3 ∧
      (canonOffset w).length ≤ w.length + 2 := by
  constructor
  · rw [← foldr_bit_eq_ofDigits]
    change Nat.bit true ((canonCount w.length.bits).foldr Nat.bit 0) = _
    rw [(canonCount_spec w.length.bits).2.2]
    change Nat.bit true (codeBitsNat w.length.bits + 1) = _
    rw [codeBitsNat_bits]
    simp [Nat.bit]
    omega
  · have small : w.length.bits.length ≤ w.length := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [canonOffset, List.length_cons, (canonCount_spec w.length.bits).2.1]
    omega

/-- The native remainder address is computed in linear time, using only
public length/prepend primitives and the inherited successor machine.

**Proof sketch.** Compose binary length with the successor, then prepend
one. Each application of the public composition theorem gives a linear
ledger; distribute the products to absorb its fixed dispatch cost. -/
private lemma exists_canonOffsetTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime canonOffset (fun n => a * (n + 1)) := by
  obtain ⟨L, a, length⟩ := FinTM.computesFunInTime_lengthBits
  obtain ⟨N, b, count⟩ := exists_canonCountTM
  obtain ⟨A, c, comp⟩ := FinTM.computesFunInTime_comp length count
    (fun _ _ h => Nat.mul_le_mul_left b (Nat.add_le_add_right h 1))
  have first : A.ComputesFunInTime (fun w => canonCount w.length.bits)
      (fun n => c * (a + 1) * (b + 1) * (n + 1)) := by
    intro w
    apply (comp w).mono
    have room : 0 ≤ (b + 1) * w.length := Nat.zero_le _
    calc
      c * (a * (w.length + 1) + b * (a * (w.length + 1) + 1) + 1) ≤
          c * (a * (w.length + 1) + b * (a * (w.length + 1) + 1) + 1 +
            (b + 1) * w.length) := Nat.mul_le_mul_left c (by omega)
      _ = _ := by ring
  obtain ⟨P, e, prepend⟩ := FinTM.computesFunInTime_prepend [true]
  obtain ⟨M, d, combined⟩ := FinTM.computesFunInTime_comp first prepend
    (fun _ _ h => Nat.mul_le_mul_left e (Nat.add_le_add_right h 1))
  let z := c * (a + 1) * (b + 1)
  refine ⟨M, d * (z + 1) * (e + 1), ?_⟩
  intro w
  apply (combined w).mono
  change d * (z * (w.length + 1) + e * (z * (w.length + 1) + 1) + 1) ≤ _
  calc
    d * (z * (w.length + 1) + e * (z * (w.length + 1) + 1) + 1) ≤
        d * (z * (w.length + 1) + e * (z * (w.length + 1) + 1) + 1 +
          (e + 1) * w.length) := Nat.mul_le_mul_left d (Nat.le_add_right _ _)
    _ = _ := by ring


/-- The canonizer's prepared bank: original header, successor count and
native remainder address on tapes zero, one and two, with blank scratch. -/
private def canonReadyWords (k : ℕ) (header : List Bool) : Fin k → List Bool :=
  fun j => if j.val = 0 then header else if j.val = 1 then canonCount header
    else if j.val = 2 then canonOffset header else []

/-- A physical front end prepares both binary words without changing the
original header. At least one additional blank tape is reserved for the
public native-input seek. The native head and every work head are at home.

**Proof sketch.** Run the proved header/count seam in a larger bank. Copy
and install the offset through a second preserving call whose embedding
skips the live count tape. The embedding frame protects that count; the
call protects the header. Compose their strict seams and add the two
linear ledgers, charging the offset's width by `canonOffset_spec`. -/
private lemma exists_canonReadySeam :
    ∃ (C : FinTM Bool) (entry exit : C.State) (a : ℕ), 4 ≤ C.k ∧
      ∀ α : List Bool, ∃ t ≤ a * (α.length + 1),
        (∀ u < t, (C.tm.runFrom
          (Cfg.ofWords (input := α) entry (fun _ => [])) u).state ≠ some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) t =
          Cfg.ofWords exit (canonReadyWords C.k (canonHeader α)) := by
  classical
  obtain ⟨H, hdst, hentry, hexit, a, hv, headerRun⟩ := exists_canonHeaderCountSeam
  obtain ⟨O, b, offsetRun⟩ := exists_canonOffsetTM
  obtain ⟨P, pdst, pentry, pexit, c, pv, prepare⟩ :=
    canonPreserveInstall O canonOffset (fun n => b * (n + 1)) offsetRun
  have hp : 2 ≤ P.k := by have := pdst.isLt; omega
  let K := max H.k (P.k + 1) + 1
  have hK : 4 ≤ K := by dsimp [K]; omega
  let hb : Fin H.k ↪ Fin K := Fin.castLEEmb (by dsimp [K]; omega)
  let pb : Fin P.k ↪ Fin K :=
    (Fin.succAboveEmb (⟨1, by omega⟩ : Fin (P.k + 1))).trans (Fin.castLEEmb (by dsimp [K]; omega))
  have pval (i : Fin P.k) : (pb i).val = if i.val = 0 then 0 else i.val + 1 := by
    change ((⟨1, by omega⟩ : Fin (P.k + 1)).succAbove i).val = _
    dsimp only [Fin.succAbove]
    split_ifs <;> simp_all [Fin.lt_def]
  let A := embedEmitTM hb H.tm
  let B := embedEmitTM pb P.tm
  let C : FinTM Bool := {
    k := K
    State := H.State ⊕ P.State
    tm := { seamCompTM A hexit B pentry with q₀ := Sum.inl hentry } }
  refine ⟨C, Sum.inl hentry, Sum.inr pexit, a + c * (b + 3) + 1, hK, ?_⟩
  intro α
  let head := canonHeader α
  let mid := Function.update (stateWord K head) (hb hdst) (canonCount head)
  let out := canonReadyWords K head
  have hv' : (hb hdst).val = 1 := hv
  have imageCount (j : Fin K) (hj : j ∉ Set.range hb) : j.val ≠ 0 ∧ j ≠ hb hdst := by
    refine ⟨?_, fun h => hj ⟨hdst, h.symm⟩⟩
    intro hz
    apply hj
    exact ⟨⟨0, by have := hdst.isLt; omega⟩, Fin.ext hz.symm⟩
  have sourceP (i : Fin P.k) : mid (pb i) = stateWord P.k head i := by
    have neq : pb i ≠ hb hdst := by
      intro eq
      have := congrArg Fin.val eq
      rw [pval, hv'] at this
      split at this <;> omega
    dsimp only [mid]
    rw [Function.update_of_ne neq]
    dsimp only [stateWord]
    rw [pval]
    split <;> simp_all
  have finalP (i : Fin P.k) :
      out (pb i) = Function.update (stateWord P.k head) pdst (canonOffset head) i := by
    have eqv : i = pdst ↔ i.val = 1 := by
      constructor
      · rintro rfl; exact pv
      · intro hi; exact Fin.ext (hi.trans pv.symm)
    simp only [out, canonReadyWords, pval, Function.update_apply, eqv, stateWord]
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
  have outsideP (j : Fin K) (hj : j ∉ Set.range pb) : mid j = out j := by
    have notzero : j.val ≠ 0 := by
      intro hz
      apply hj
      refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
      rw [pval]
      simp [hz]
    have nottwo : j.val ≠ 2 := by
      intro hz
      apply hj
      refine ⟨pdst, Fin.ext ?_⟩
      rw [pval, pv, hz]
      rfl
    by_cases h1 : j = hb hdst
    · subst j
      simp [mid, out, canonReadyWords, hv']
    · have valne : j.val ≠ 1 := fun h => h1 (Fin.ext (h.trans hv'.symm))
      simp [mid, out, Function.update_of_ne h1, canonReadyWords, stateWord,
        notzero, valne, nottwo]
  obtain ⟨t₀, time₀, cut₀, run₀⟩ := headerRun α
  obtain ⟨t₁, time₁, cut₁, run₁⟩ := prepare α head
  have hlift (u : ℕ) :
      A.runFrom (Cfg.ofWords (input := α) hentry (fun _ => [])) u =
        embedEmitCfg hb (fun _ => FinTM.bufferTape []) (fun _ => 0) []
          (H.tm.runFrom (Cfg.ofWords (input := α) hentry (fun _ => [])) u) := by
    rw [← canonEmbedWords H.tm hb hentry (fun _ => []) (fun _ => []) (fun _ => [])
      (fun _ => rfl) (fun _ _ => rfl)]
    exact embedEmitTM_runFrom hb H.tm _ _ _ _ u
  have first : A.runFrom (Cfg.ofWords (input := α) hentry (fun _ => [])) t₀ =
      Cfg.ofWords hexit mid := by
    rw [hlift, run₀]
    apply canonEmbedWords H.tm hb hexit
      (Function.update (stateWord H.k head) hdst (canonCount head)) (fun _ => []) mid
    · intro i
      exact Function.update_apply_of_injective (stateWord K head) hb.injective
        hdst (canonCount head) i
    · intro j hj
      obtain ⟨nz, ne⟩ := imageCount j hj
      simp [mid, Function.update_of_ne ne, stateWord, nz]
  have firstCut (u : ℕ) (hu : u < t₀) :
      (A.runFrom (Cfg.ofWords (input := α) hentry (fun _ => [])) u).state ≠ some hexit := by
    rw [hlift]; exact cut₀ u hu
  have plift (u : ℕ) : B.runFrom (Cfg.ofWords (input := α) pentry mid) u =
      embedEmitCfg pb (fun j => FinTM.bufferTape (mid j)) (fun _ => 0) []
        (P.tm.runFrom (Cfg.ofWords (input := α) pentry (stateWord P.k head)) u) := by
    rw [← canonEmbedWords P.tm pb pentry (stateWord P.k head) mid mid
      sourceP (fun _ _ => rfl)]
    exact embedEmitTM_runFrom pb P.tm _ _ _ _ u
  have second : B.runFrom ((Cfg.ofWords (input := α) hexit mid).mapState
      fun _ => pentry) t₁ = Cfg.ofWords pexit out := by
    change B.runFrom (Cfg.ofWords pentry mid) t₁ = _
    rw [plift, run₁]
    exact canonEmbedWords P.tm pb pexit
      (Function.update (stateWord P.k head) pdst (canonOffset head)) mid out finalP outsideP
  have secondCut (u : ℕ) (hu : u < t₁) :
      (B.runFrom ((Cfg.ofWords (input := α) hexit mid).mapState
        fun _ => pentry) u).state ≠ some pexit := by
    change (B.runFrom (Cfg.ofWords pentry mid) u).state ≠ _
    rw [plift]; exact cut₁ u hu
  have whole := seamCompTM_run_ofCfg A hexit B pentry first rfl firstCut second
  have firstExit := seamCompTM_firstReturn_ofCfg A hexit B pentry pexit
    first rfl firstCut second rfl secondCut
  have budget : t₁ ≤ c * (b + 3) * (α.length + 1) := by
    calc
      t₁ ≤ c * (b * (head.length + 1) + head.length + (canonOffset head).length + 1) := time₁
      _ ≤ c * (b * (head.length + 1) + head.length + (head.length + 2) + 1) :=
        Nat.mul_le_mul_left c (by have := (canonOffset_spec head).2; omega)
      _ ≤ c * (b + 3) * (head.length + 1) := by
        rw [Nat.mul_assoc]
        apply Nat.mul_le_mul_left c
        rw [Nat.add_mul]
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right (canonHeader_length α) 1)
  refine ⟨t₀ + 1 + t₁, ?_, ?_, ?_⟩
  · simp only [Nat.add_mul, Nat.one_mul]
    omega
  · simpa only [C, Cfg.ofWords, Cfg.mapState, Option.map_some] using firstExit
  · simpa only [C, out, head, Cfg.ofWords, Cfg.mapState, Option.map_some] using whole


/-- The public native-input seek, embedded in a caller-selected bank. All
host tapes, all heads and the output are restored, including the frame.
This contract can therefore be used again after a destructive guard.

**Proof sketch.** Project the two selected tapes to the public seek row,
then transport its run and strict cut by forwarding embedding. Assemble
the returned host configuration by `canonEmbedEq`; the selected projections
come from the seek and the remaining tapes come from the public frame. -/
private lemma exists_canonSeekOnBank {k : ℕ} (ι : Fin 2 ↪ Fin k) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM k Bool S) (entry exit : S) (a : ℕ),
      ∀ {x : List Bool} (p : ℕ) (w : List Bool),
        Nat.ofDigits 2 (w.map Bool.toNat) = p → ∀ hp : p ≤ x.length + 1,
        ∀ d : Cfg k Bool S x, d.state = some entry →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes (ι 0) (d.workTapePos (ι 0) + q) = FinTM.bufferTape w q) →
        (∀ q, d.workTapes (ι 1) q = none) →
        ∃ t ≤ a * (w.length + d.inputPos.val + p + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          R.runFrom d t = { d with state := some exit, inputPos := ⟨p, by omega⟩ } := by
  classical
  obtain ⟨S, finite, equal, M, entry, exit, a, seek⟩ := exists_inputSeekTM
  letI : Fintype S := finite
  letI : DecidableEq S := equal
  refine ⟨S, finite, equal, embedEmitTM ι M, entry, exit, a, ?_⟩
  intro x p w hw hp d hd word blank
  let src : Cfg 2 Bool S x :=
    ⟨d.state, d.inputPos, fun i => d.workTapes (ι i), fun i => d.workTapePos (ι i), d.output⟩
  have start : embedEmitCfg ι d.workTapes d.workTapePos [] src = d := by
    exact canonEmbedEq M ι src d _ _ rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩)
  have lift (u : ℕ) : (embedEmitTM ι M).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos [] (M.runFrom src u) := by
    conv_lhs => rw [← start]
    exact embedEmitTM_runFrom ι M _ _ [] src u
  obtain ⟨t, time, cut, _, state, pos, tapes, heads, out⟩ := seek p w hw hp src hd word blank
  refine ⟨t, time, ?_, ?_⟩
  · intro u hu
    rw [lift]
    exact cut u hu
  · rw [lift]
    refine canonEmbedEq M ι (M.runFrom src t)
      ({ d with state := some exit, inputPos := ⟨p, by omega⟩ })
      d.workTapes d.workTapePos state (Fin.ext pos) out ?_ ?_
    · intro i
      exact ⟨congrFun tapes i, congrFun heads i⟩
    · exact fun _ _ => ⟨rfl, rfl⟩


/-- From blank work tapes, prepare the header bank, seek to the native
remainder, run the positive guard, and seek back on success. All tapes
except the guard counter are preserved from the prepared bank. Rejection
is at the right input blank. This is a guard front end, not a grammar verdict.

**Proof sketch.** The preparation seam feeds an embedded public seek. The
inherited guard runs only on tape one, leaving the saved offset and its
scratch tape intact. A public seam dispatches its successful exit to the
same seek again; a failed guard is observed before that dispatch. Two more
public seams join the first seek and preparation. Every copy, installation,
seek and dispatch is included in the displayed linear coefficient. -/
private lemma exists_canonGuardFront (F : MachineFormat) :
    ∃ (C : FinTM Bool) (entry yes no : C.State) (a : ℕ), 4 ≤ C.k ∧ yes ≠ no ∧
      ∀ α bits rest : List Bool, pairDecode α = some (bits, rest) →
        ∃ t ≤ a * (α.length + 1),
          let d := C.tm.runFrom (Cfg.ofWords (input := α) entry (fun _ => [])) t
          d.state = some (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
            then yes else no) ∧ d.output = [] ∧
          d.inputPos.val = (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
            then 2 * bits.length + 3 else α.length + 1) ∧
          ∀ i : Fin C.k, i.val ≠ 1 →
            d.workTapes i = FinTM.bufferTape (canonReadyWords C.k bits i) ∧
              d.workTapePos i = 0 := by
  classical
  obtain ⟨P, pentry, pexit, a, hk, prep⟩ := exists_canonReadySeam
  let sb : Fin 2 ↪ Fin P.k := ⟨fun i => ⟨i.val + 2, by have := i.isLt; omega⟩,
    fun i j h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  let gb : Fin 1 ↪ Fin P.k := ⟨fun _ => ⟨1, by omega⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨S, finite, equal, R, enter, leave, b, seek⟩ := exists_canonSeekOnBank sb
  letI : Fintype S := finite
  letI : DecidableEq S := equal
  let B := canonGuardBlock F
  let G := embedEmitTM gb (binaryGuardTM (B - 1))
  let U := seamCompTM G .done R enter
  let V := seamCompTM R leave U (Sum.inl (.dec .run))
  let C : FinTM Bool := {
    k := P.k
    State := P.State ⊕ (S ⊕ ((CounterLoopState (Option (Fin (B - 1 + 1))))) ⊕ S)
    tm := { seamCompTM P.tm pexit V (Sum.inl enter) with q₀ := Sum.inl pentry } }
  -- The parentheses below record the actual three seam summands.
  let yes : C.State := Sum.inr (Sum.inr (Sum.inr leave))
  let no : C.State := Sum.inr (Sum.inr (Sum.inl .escape))
  have distinct : yes ≠ no := by
    intro h
    cases Sum.inr.inj (Sum.inr.inj h)
  refine ⟨C, Sum.inl pentry, yes, no, a + 10 * b + B + 9, hk, distinct, ?_⟩
  intro α bits rest pair
  have header : canonHeader α = bits := by simp [canonHeader, pair]
  have size : bits.length ≤ α.length := header ▸ canonHeader_length α
  let p := 2 * bits.length + 3
  have inRange : p ≤ α.length + 1 := by
    rw [eq_pairEncode_of_pairDecode α bits rest pair, length_pairEncode]
    dsimp [p]
    omega
  let w := canonReadyWords P.k bits
  have address : w (sb 0) = canonOffset bits := by simp [w, canonReadyWords, sb]
  have scratch : w (sb 1) = [] := by simp [w, canonReadyWords, sb]
  let s₀ := Cfg.ofWords (input := α) enter w
  obtain ⟨ts, timeS, cutS, runS⟩ := seek p (canonOffset bits) (canonOffset_spec bits).1
    inRange s₀ rfl (by intro q _ _; simp [s₀, Cfg.ofWords, address])
    (by intro q; simp [s₀, Cfg.ofWords, scratch, FinTM.bufferTape])
  let s₁ : Cfg P.k Bool S α := { s₀ with state := some leave, inputPos := ⟨p, by omega⟩ }
  change R.runFrom s₀ ts = s₁ at runS
  obtain ⟨hj, tg, timeG, stateG, outG, posG, cutG⟩ := canonGuard_run F α bits rest pair
  let g₀ := binaryGuardStart (B - 1) α (2 * bits.length + 2) hj [] (canonCount bits)
  let g₁ := (binaryGuardTM (B - 1)).runFrom g₀ tg
  let d₀ : Cfg P.k Bool (CounterLoopState (Option (Fin (B - 1 + 1)))) α :=
    s₁.mapState (fun _ => CounterLoopState.dec FlagPhase.run)
  have startG : embedEmitCfg gb s₁.workTapes s₁.workTapePos [] g₀ = d₀ := by
    apply canonEmbedEq (binaryGuardTM (B - 1)) gb g₀ d₀ _ _ rfl
      (Fin.ext (by simp [g₀, binaryGuardStart, counter_cfg_eq, guardCfg,
        d₀, s₁, p, Cfg.mapState])) rfl
    · intro i
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      simp only [g₀, binaryGuardStart, counter_cfg_eq, Fin.lastCases_last]
      exact ⟨rfl, rfl⟩
    · exact fun _ _ => ⟨rfl, rfl⟩
  have liftG (u : ℕ) : G.runFrom d₀ u =
      embedEmitCfg gb s₁.workTapes s₁.workTapePos []
        ((binaryGuardTM (B - 1)).runFrom g₀ u) := by
    conv_lhs => rw [← startG]
    exact embedEmitTM_runFrom gb (binaryGuardTM (B - 1)) _ _ [] g₀ u
  let d₁ := embedEmitCfg gb s₁.workTapes s₁.workTapePos [] g₁
  have runG : G.runFrom d₀ tg = d₁ := liftG tg
  have cutDone (u : ℕ) (hu : u < tg) : (G.runFrom d₀ u).state ≠ some .done := by
    rw [liftG]
    exact (cutG u hu).1
  have framed (i : Fin P.k) (hi : i.val ≠ 1) :
      d₁.workTapes i = FinTM.bufferTape (w i) ∧ d₁.workTapePos i = 0 := by
    have outside : i ∉ Set.range gb := by
      rintro ⟨j, hj⟩
      exact hi (congrArg Fin.val hj.symm)
    have frame := (embedEmitTM_frame gb (binaryGuardTM (B - 1))
      s₁.workTapes s₁.workTapePos [] g₀ tg).1 i outside
    rw [embedEmitTM_runFrom] at frame
    exact frame
  have stateD : d₁.state = some (if B * (codeBitsNat bits + 1) ≤ rest.length
      then .done else .escape) := stateG
  have outputD : d₁.output = [] := by simpa only [d₁, embedEmitCfg, List.nil_append] using outG
  have posD : d₁.inputPos.val = (if B * (codeBitsNat bits + 1) ≤ rest.length
      then 2 * bits.length + 2 + B * (codeBitsNat bits + 1) + 1 else α.length + 1) := posG
  have seekBudget (pos : ℕ) (hpos : pos ≤ α.length + 1) :
      b * ((canonOffset bits).length + pos + p + 1) ≤ 5 * b * (α.length + 1) := by
    have width := (canonOffset_spec bits).2
    calc
      _ ≤ b * (5 * (α.length + 1)) := Nat.mul_le_mul_left b (by omega)
      _ = _ := by ring
  have boundS : ts ≤ 5 * b * (α.length + 1) :=
    timeS.trans (seekBudget 1 (by omega))
  have boundG : tg ≤ (B + 6) * (α.length + 1) := by
    calc
      _ ≤ (B + 4) * (α.length + 1) + 2 * (bits.length + 1) := timeG
      _ ≤ _ := by simp only [Nat.add_mul]; omega
  obtain ⟨tp, timeP, cutP, runP⟩ := prep α
  rw [header] at runP
  -- Package the conditional return segment before joining its two callers.
  have tail : ∃ tu ≤ (5 * b + B + 7) * (α.length + 1),
      let z := U.runFrom (d₀.mapState Sum.inl) tu
      z.state = some (if B * (codeBitsNat bits + 1) ≤ rest.length
        then Sum.inr leave else Sum.inl .escape) ∧ z.output = [] ∧
      z.inputPos.val = (if B * (codeBitsNat bits + 1) ≤ rest.length then p else α.length + 1) ∧
      ∀ i, i.val ≠ 1 → z.workTapes i = FinTM.bufferTape (w i) ∧ z.workTapePos i = 0 := by
    by_cases good : B * (codeBitsNat bits + 1) ≤ rest.length
    · have done : d₁.state = some .done := by simpa [good] using stateD
      let r₀ := d₁.mapState (fun _ => enter)
      obtain ⟨tr, timeR, _, runR⟩ := seek p (canonOffset bits) (canonOffset_spec bits).1
        inRange r₀ (by simp [r₀, Cfg.mapState, done])
        (by intro q _ _; simp [r₀, Cfg.mapState, (framed (sb 0) (by simp [sb])).1,
          (framed (sb 0) (by simp [sb])).2, address])
        (by intro q; simp [r₀, Cfg.mapState, (framed (sb 1) (by simp [sb])).1,
          scratch, FinTM.bufferTape])
      have whole := seamCompTM_run_ofCfg G .done R enter runG done cutDone runR
      have boundR : tr ≤ 5 * b * (α.length + 1) :=
        timeR.trans (seekBudget r₀.inputPos.val (by have := r₀.inputPos.isLt; omega))
      refine ⟨tg + 1 + tr, ?_, ?_⟩
      · rw [show 5 * b + B + 7 = (B + 6) + 5 * b + 1 by omega, Nat.add_mul,
          Nat.add_mul, Nat.one_mul]
        omega
      · dsimp only [U]
        rw [whole]
        simp only [good, if_true, Cfg.mapState, Option.map_some]
        exact ⟨True.intro, outputD, True.intro, framed⟩
    · have whole := seamCompTM_runFrom_left G .done R enter cutDone tg le_rfl
      rw [runG] at whole
      refine ⟨tg, boundG.trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
      dsimp only [U]
      rw [whole]
      simp only [good, if_false, Cfg.mapState, stateD, Option.map_some]
      exact ⟨True.intro, outputD, by simpa [good] using posD, framed⟩
  obtain ⟨tu, timeU, stateU, outU, posU, frameU⟩ := tail
  have firstSeek := seamCompTM_run_ofCfg R leave U (Sum.inl (.dec .run)) runS rfl cutS
    (rfl : U.runFrom (d₀.mapState Sum.inl) tu = _)
  have loaded := seamCompTM_run_ofCfg P.tm pexit V (Sum.inl enter) runP rfl cutP firstSeek
  have loadedC : C.tm.runFrom (Cfg.ofWords (input := α) (Sum.inl pentry) (fun _ => []))
      (tp + 1 + (ts + 1 + tu)) =
      (U.runFrom (d₀.mapState Sum.inl) tu).mapState (fun s => (Sum.inr (Sum.inr s) : C.State)) := by
    simpa only [C, Cfg.ofWords, Cfg.mapState, Option.map_some, Option.map_map,
      Function.comp_def] using loaded
  refine ⟨tp + 1 + (ts + 1 + tu), ?_, ?_⟩
  · have budget := Nat.add_le_add (Nat.add_le_add timeP boundS) timeU
    ring_nf at budget ⊢
    omega
  · dsimp only
    rw [loadedC]
    refine ⟨?_, outU, posU, frameU⟩
    change (U.runFrom (d₀.mapState Sum.inl) tu).state.map
      (fun s => (Sum.inr (Sum.inr s) : C.State)) = _
    rw [stateU]
    split <;> rfl

/-- Read and erase a singleton Boolean result at the selected work head.
The two live exits retain the bit. This one-cell leaf is not supplied by
the catalog's whole-word scans; composition uses the public seam host. -/
private def canonBoolPopTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool (Option Bool) where
  q₀ := none
  tr := fun q _ w => match q with
    | none => tapeAction i 0 (some none) 0 (some ((w i).getD false))
    | some b => inputMoveAction 0 (some b)

/-- The singleton result is consumed in one silent stationary transition.
Every work tape is blank afterwards, and the native head remains home. -/
private lemma canonBoolPop_run (k : ℕ) (positive : 0 < k) (b : Bool) (x : List Bool) :
    (canonBoolPopTM k ⟨0, positive⟩).runFrom
        (Cfg.ofWords (input := x) none (stateWord k [b])) 1 =
      Cfg.ofWords (some b) (fun _ => []) := by
  have singleton : FinTM.bufferTape [b] =
      Function.update (fun _ : ℤ => (none : Option Bool)) 0 (some b) := by
    simpa using FinTM.bufferTape_append ([] : List Bool) b
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [MultiTapeTM.step, canonBoolPopTM, Cfg.ofWords, Cfg.workTapeSymbols,
      stateWord, tapeAction, Action.apply, FinTM.bufferTape]
  · funext j z
    by_cases hj : j.val = 0
    · have he : j = ⟨0, positive⟩ := Fin.ext hj
      subst j
      simp [singleton, Function.update_idem]
    · simp [hj, show j ≠ ⟨0, positive⟩ from fun h => hj (congrArg Fin.val h)]
  · funext j
    split <;> rfl

/-- Any linear-time native-input Boolean computation has a silent clean
branch seam, with distinct exits and cuts at both exits including time zero.
All work tapes are blank on return, and the native head is at one.

**Promotion candidate.** This is a Boolean-result adapter built from the
public input copier, the inherited strict install adapter and the one-cell
result leaf. It is independent of machine formats.

**Proof sketch.** Copy the native input to tape zero and install the singleton
result using the strict call. The final leaf reads and erases it. Until the
call finishes, both result exits lie in an unentered seam summand; the sole
remaining strict-prefix instant is the leaf's entry. All three costs and
the two dispatches are included in the linear bound. -/
private lemma exists_canonBoolBranch (M : FinTM Bool) (p : List Bool → Bool)
    (c : ℕ) (computes : M.ComputesFunInTime (fun x => [p x]) (fun n => c * (n + 1))) :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Bool → C.State) (a : ℕ),
      0 < C.k ∧ Function.Injective exit ∧
      ∀ x : List Bool, ∃ t ≤ a * (x.length + 1),
        (∀ u < t, ∀ b, (C.tm.runFrom
          (Cfg.ofWords (input := x) entry (fun _ => [])) u).state ≠ some (exit b)) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t =
          Cfg.ofWords (exit (p x)) (fun _ => []) := by
  classical
  obtain ⟨I, enter, leave, a, positive, install⟩ :=
    canonStrictInstall M (fun x => [p x]) (fun n => c * (n + 1)) computes
  let i : Fin I.k := ⟨0, positive⟩
  let P := seamCompTM (inputCopyTM I.k i) .done I.tm enter
  let V := canonBoolPopTM I.k i
  let C : FinTM Bool := {
    k := I.k
    State := (SweepPhase ⊕ I.State) ⊕ Option Bool
    tm := { seamCompTM P (Sum.inr leave) V none with
      q₀ := Sum.inl (Sum.inl .sweep) } }
  refine ⟨C, Sum.inl (Sum.inl .sweep), fun b => Sum.inr (some b),
    a * (c + 2) + 5, positive, ?_, ?_⟩
  · intro b d eq
    exact Option.some.inj (Sum.inr.inj eq)
  · intro x
    let initial : Cfg I.k Bool SweepPhase x :=
      Cfg.ofWords (input := x) SweepPhase.sweep (fun _ => [])
    have copy := inputCopyTM_run_ofCfg i initial rfl rfl
    have copied : (inputCopyTM I.k i).runFrom initial (2 * x.length + 2) =
        Cfg.ofWords .done (stateWord I.k x) := by
      rw [copy.1]
      apply Cfg.ext <;> try rfl
      funext j z
      by_cases hj : j = i
      · subst j
        simp only [initial, Cfg.ofWords, stateWord, i, ↓reduceIte, zero_add, sub_zero]
        split_ifs with hz
        · rfl
        · by_cases hn : 0 ≤ z
          · have outside : ¬(0 ≤ z ∧ z < (x.length : ℤ)) := by simpa using hz
            simp [FinTM.bufferTape, hn,
              List.getElem?_eq_none (by omega : x.length ≤ z.toNat)]
          · simp [FinTM.bufferTape, hn]
      · have nz : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [initial, Cfg.ofWords, stateWord, hj, nz]
    obtain ⟨t, time, _, cut, run⟩ := install x x
    have first := seamCompTM_run_ofCfg (inputCopyTM I.k i) .done I.tm enter
      copied rfl copy.2.1 run
    have firstCut := seamCompTM_firstReturn_ofCfg (inputCopyTM I.k i) .done I.tm enter leave
      copied rfl copy.2.1 run rfl cut
    let duration := 2 * x.length + 2 + 1 + t
    let middle := (Cfg.ofWords (input := x) leave (stateWord I.k [p x])).mapState
      (Sum.inr : I.State → SweepPhase ⊕ I.State)
    have pop : V.runFrom (middle.mapState (fun _ => none)) 1 =
        Cfg.ofWords (some (p x)) (fun _ => []) := canonBoolPop_run I.k positive (p x) x
    have whole := seamCompTM_run_ofCfg P (Sum.inr leave) V none
      first rfl firstCut pop
    refine ⟨duration + 1 + 1, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil, Nat.zero_add] at time
      have bound : t ≤ a * (c + 2) * (x.length + 1) := by
        apply time.trans
        rw [Nat.mul_assoc]
        apply Nat.mul_le_mul_left a
        rw [Nat.add_mul]
        omega
      dsimp only [duration]
      rw [Nat.add_mul]
      omega
    · intro u hu b
      change ((seamCompTM P (Sum.inr leave) V none).runFrom
        ((initial.mapState Sum.inl).mapState Sum.inl) u).state ≠ some (Sum.inr (some b))
      by_cases early : u ≤ duration
      · rw [seamCompTM_runFrom_left P (Sum.inr leave) V none firstCut u early]
        simp [Cfg.mapState]
      · have atLeaf : u = duration + 1 := by omega
        rw [atLeaf]
        have dispatch := seamCompTM_run_ofCfg P (Sum.inr leave) V none
          first rfl firstCut (rfl : V.runFrom (middle.mapState (fun _ => none)) 0 = _)
        simp only [Nat.add_zero] at dispatch
        rw [dispatch]
        simp [middle, Cfg.mapState, Cfg.ofWords]
    · simpa only [C, initial, duration, Cfg.ofWords, Cfg.mapState, Option.map_some] using whole

/-- The total header check returns a clean live verdict, so its successful
branch may start the existing blank-tape preparation without any cleanup. -/
private lemma exists_canonHeaderBranch :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Bool → C.State) (a : ℕ),
      0 < C.k ∧ Function.Injective exit ∧
      ∀ x : List Bool, ∃ t ≤ a * (x.length + 1),
        (∀ u < t, ∀ b, (C.tm.runFrom
          (Cfg.ofWords (input := x) entry (fun _ => [])) u).state ≠ some (exit b)) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t =
          Cfg.ofWords (exit (canonHeaderOK x)) (fun _ => []) := by
  obtain ⟨M, c, computes⟩ := exists_canonHeaderOKTM
  exact exists_canonBoolBranch M canonHeaderOK c computes

/-- A negative total header verdict has exactly the prescribed fallback
semantics, including malformed pairs whose extracted header is empty. -/
private lemma decode_of_canonHeader (F : MachineFormat) (x : List Bool)
    (invalid : canonHeaderOK x = false) : F.decode x = F.fallback := by
  apply F.decode_of_parseFull_none
  have scan := scan_eq_none_of_canonHeaderOK F x invalid
  rw [F.scan_full] at scan
  exact Option.map_eq_none_iff.mp scan

/-- Prefix avoidance in a public seam composition, for an arbitrary
composite control state. Both the chosen and the unchosen branch exits can
therefore be protected, without asserting that either is the final state.

**Promotion candidate.** This is a two-segment consequence of the public
seam run equations, not a new host or a second machine trace.

**Proof sketch.** Before dispatch use the public left-prefix identity;
after dispatch use its public run identity at the remaining time. Apply
the corresponding supplied avoidance predicate in the two intervals. -/
private lemma canonSeam_avoids {k : ℕ} {S R : Type} [DecidableEq S]
    {x : List Bool} (A : MultiTapeTM k Bool S) (leave : S)
    (B : MultiTapeTM k Bool R) (enter : R) (target : S ⊕ R)
    {d e : Cfg k Bool S x} {t v : ℕ}
    (run : A.runFrom d t = e) (atExit : e.state = some leave)
    (first : ∀ u < t, (A.runFrom d u).state ≠ some leave)
    (before : ∀ u ≤ t, ((A.runFrom d u).mapState (Sum.inl : S → S ⊕ R)).state ≠
      some target)
    (after : ∀ u < v,
      ((B.runFrom (e.mapState (fun _ => enter)) u).mapState (Sum.inr : R → S ⊕ R)).state ≠
        some target) :
    ∀ u < t + 1 + v,
      ((seamCompTM A leave B enter).runFrom (d.mapState Sum.inl) u).state ≠
        some target := by
  intro u hu
  by_cases left : u ≤ t
  · rw [seamCompTM_runFrom_left A leave B enter first u left]
    exact before u left
  · obtain ⟨r, hr⟩ : ∃ r, u = t + 1 + r := ⟨u - (t + 1), by omega⟩
    rw [hr, seamCompTM_run_ofCfg A leave B enter run atExit first rfl]
    exact after r (by omega)

/-- Select the guard counter alone; all other live words lie in the frame. -/
private def canonCounterBank {k : ℕ} (i : Fin k) : Fin 1 ↪ Fin k :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The inherited physical guard on one selected counter tape, with an
arbitrary ambient bank. No post-guard property of that counter is assumed.
Both exit cuts and the exact frame survive the public embedding.

**Proof sketch.** Identify the selected tape and native head with the
inherited guard's preloaded start using the existing configuration assembly
lemma. Transport its run by the public embedding equation, and project the
public frame. The predecessor's guard proof supplies all branch semantics,
positions, cuts and the numerical-value-independent time bound. -/
private lemma canonGuard_onBank {k : ℕ} (i : Fin k) (F : MachineFormat)
    (x bits rest : List Bool) (pair : pairDecode x = some (bits, rest))
    (d : Cfg k Bool (CounterLoopState (Option (Fin (canonGuardBlock F - 1 + 1)))) x)
    (control : d.state = some (.dec .run))
    (position : d.inputPos.val = 2 * bits.length + 3)
    (counter : d.workTapes i = FinTM.bufferTape (canonCount bits))
    (home : d.workTapePos i = 0) (silent : d.output = []) :
    let G := embedEmitTM (canonCounterBank i) (binaryGuardTM (canonGuardBlock F - 1))
    ∃ t ≤ (canonGuardBlock F + 6) * (x.length + 1),
      let e := G.runFrom d t
      e.state = some (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
        then .done else .escape) ∧ e.output = [] ∧
      e.inputPos.val = (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
        then 2 * bits.length + 3 + canonGuardBlock F * (codeBitsNat bits + 1)
        else x.length + 1) ∧
      (∀ u < t, (G.runFrom d u).state ≠ some .done ∧
        (G.runFrom d u).state ≠ some .escape) ∧
      ∀ j, j ≠ i → e.workTapes j = d.workTapes j ∧ e.workTapePos j = d.workTapePos j := by
  obtain ⟨hpos, elapsed, budget, finish, output, native, cuts⟩ := canonGuard_run F x bits rest pair
  let src := binaryGuardStart (canonGuardBlock F - 1) x (2 * bits.length + 2) hpos []
    (canonCount bits)
  have identified : embedEmitCfg (canonCounterBank i) d.workTapes d.workTapePos [] src = d := by
    apply canonEmbedEq (binaryGuardTM (canonGuardBlock F - 1)) (canonCounterBank i)
      src d _ _ control.symm (Fin.ext (by simpa [src, binaryGuardStart,
        counter_cfg_eq, guardCfg, Nat.add_assoc] using position.symm)) silent.symm
    · intro j
      have last : j = Fin.last 0 := Subsingleton.elim _ _
      subst j
      simp only [src, binaryGuardStart, counter_cfg_eq, Fin.lastCases_last]
      exact ⟨counter.symm, home.symm⟩
    · exact fun _ _ => ⟨rfl, rfl⟩
  have transported (u : ℕ) :
      (embedEmitTM (canonCounterBank i) (binaryGuardTM (canonGuardBlock F - 1))).runFrom d u =
        embedEmitCfg (canonCounterBank i) d.workTapes d.workTapePos []
          ((binaryGuardTM (canonGuardBlock F - 1)).runFrom src u) := by
    conv_lhs => rw [← identified]
    exact embedEmitTM_runFrom _ _ _ _ _ _ u
  have length : bits.length ≤ x.length := by
    have loaded := canonHeader_length x
    simpa [canonHeader, pair] using loaded
  refine ⟨elapsed, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Nat.add_mul] at budget ⊢
    omega
  · rw [transported]
    exact finish
  · rw [transported]
    exact output
  · rw [transported]
    change ((binaryGuardTM (canonGuardBlock F - 1)).runFrom src elapsed).inputPos.val = _
    change ((binaryGuardTM (canonGuardBlock F - 1)).runFrom src elapsed).inputPos.val = _ at native
    split_ifs at native ⊢ <;> omega
  · intro u hu
    rw [transported]
    exact cuts u hu
  · intro j hj
    have notSelected : j ∉ Set.range (canonCounterBank i) := by
      rintro ⟨q, eq⟩
      exact hj eq.symm
    have frame := (embedEmitTM_frame (canonCounterBank i)
      (binaryGuardTM (canonGuardBlock F - 1)) d.workTapes d.workTapePos [] src elapsed).1
        j notSelected
    rw [identified] at frame
    exact frame

/-- From the prepared bank, seek to the remainder, run the inherited guard
on tape one, and seek back on success. Both final ports have strict cuts;
the header, saved address and every non-counter tape are preserved.

**Proof sketch.** Use the public seek contract twice, with the framed guard
between them. The success branch dispatches to the second seek; the failure
branch stops before that dispatch. The arbitrary-target seam cut protects
both ports in either case. A second public seam attaches the first seek.
All seeks, guard work and dispatches are charged to a linear bound. -/
private lemma exists_canonGuardReady (F : MachineFormat) (k : ℕ) (hk : 4 ≤ k) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (C : MultiTapeTM k Bool S) (entry : S) (exit : Bool → S) (a : ℕ),
      Function.Injective exit ∧ ∀ x bits rest : List Bool,
        pairDecode x = some (bits, rest) → ∃ t ≤ a * (x.length + 1),
          let start := Cfg.ofWords (input := x) entry (canonReadyWords k bits)
          let e := C.runFrom start t
          e.state = some (exit (decide
            (canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length))) ∧
          e.output = [] ∧ e.inputPos.val =
            (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
              then 2 * bits.length + 3 else x.length + 1) ∧
          (∀ u < t, ∀ b, (C.runFrom start u).state ≠ some (exit b)) ∧
          ∀ j, j.val ≠ 1 →
            e.workTapes j = FinTM.bufferTape (canonReadyWords k bits j) ∧
              e.workTapePos j = 0 := by
  classical
  let addressBank : Fin 2 ↪ Fin k :=
    ⟨fun j => ⟨j.val + 2, by have := j.isLt; omega⟩,
      fun j l eq => Fin.ext (by have := congrArg Fin.val eq; dsimp at this; omega)⟩
  let counter : Fin k := ⟨1, by omega⟩
  obtain ⟨S, finite, equal, R, enter, leave, c, seek⟩ := exists_canonSeekOnBank addressBank
  letI : Fintype S := finite
  letI : DecidableEq S := equal
  let G := embedEmitTM (canonCounterBank counter) (binaryGuardTM (canonGuardBlock F - 1))
  let U := seamCompTM G .done R enter
  let C := seamCompTM R leave U (Sum.inl (.dec .run))
  let port (b : Bool) : CounterLoopState (Option (Fin (canonGuardBlock F - 1 + 1))) ⊕ S :=
    if b then Sum.inr leave else Sum.inl .escape
  refine ⟨_, inferInstance, inferInstance, C, Sum.inl enter,
    fun b => Sum.inr (port b), 10 * c + canonGuardBlock F + 8, ?_, ?_⟩
  · intro b d eq
    cases b <;> cases d <;> simp_all [port]
  · intro x bits rest pair
    let p := 2 * bits.length + 3
    let words := canonReadyWords k bits
    let beginning := Cfg.ofWords (input := x) enter words
    have size : bits.length ≤ x.length := by
      simpa [canonHeader, pair] using canonHeader_length x
    have range : p ≤ x.length + 1 := by
      rw [eq_pairEncode_of_pairDecode x bits rest pair, length_pairEncode]
      dsimp [p]
      omega
    have charge (pos : ℕ) (small : pos ≤ x.length + 1) :
        c * ((canonOffset bits).length + pos + p + 1) ≤ 5 * c * (x.length + 1) := by
      calc
        _ ≤ c * (5 * (x.length + 1)) :=
          Nat.mul_le_mul_left c (by have := (canonOffset_spec bits).2; omega)
        _ = _ := by ring
    obtain ⟨s, costS, firstS, ranS⟩ := seek p (canonOffset bits) (canonOffset_spec bits).1
      range beginning rfl
      (by intro z _ _; simp [beginning, Cfg.ofWords, words, canonReadyWords, addressBank])
      (by intro z; simp [beginning, Cfg.ofWords, words, canonReadyWords, addressBank])
    let afterSeek : Cfg k Bool S x :=
      { beginning with state := some leave, inputPos := ⟨p, by omega⟩ }
    change R.runFrom beginning s = afterSeek at ranS
    let guardStart : Cfg k Bool
        (CounterLoopState (Option (Fin (canonGuardBlock F - 1 + 1)))) x :=
      afterSeek.mapState (fun _ => CounterLoopState.dec FlagPhase.run)
    obtain ⟨g, costG, guardState, guardOutput, guardPos, guardCut, guardFrame⟩ :=
      canonGuard_onBank counter F x bits rest pair guardStart rfl rfl rfl rfl rfl
    let guarded := G.runFrom guardStart g
    have frame (j : Fin k) (hj : j.val ≠ 1) :
        guarded.workTapes j = FinTM.bufferTape (words j) ∧ guarded.workTapePos j = 0 :=
      guardFrame j (fun eq => hj (congrArg Fin.val eq))
    have cutDone : ∀ u < g, (G.runFrom guardStart u).state ≠ some .done :=
      fun u hu => (guardCut u hu).1
    have tail : ∃ v ≤ (5 * c + canonGuardBlock F + 7) * (x.length + 1),
        let e := U.runFrom (guardStart.mapState Sum.inl) v
        e.state = some (port (decide
          (canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length))) ∧
        e.output = [] ∧ e.inputPos.val =
          (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
            then p else x.length + 1) ∧
        (∀ u < v, ∀ b, (U.runFrom (guardStart.mapState Sum.inl) u).state ≠ some (port b)) ∧
        ∀ j, j.val ≠ 1 → e.workTapes j = FinTM.bufferTape (words j) ∧ e.workTapePos j = 0 := by
      by_cases fits : canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
      · have done : guarded.state = some .done := by simpa [fits] using guardState
        let rewind := guarded.mapState (fun _ => enter)
        obtain ⟨r, costR, firstR, ranR⟩ := seek p (canonOffset bits) (canonOffset_spec bits).1
          range rewind (by simp [rewind, Cfg.mapState, done])
          (by
            intro z _ _
            change guarded.workTapes (addressBank 0)
              (guarded.workTapePos (addressBank 0) + z) = _
            rw [(frame (addressBank 0) (by simp [addressBank])).1,
              (frame (addressBank 0) (by simp [addressBank])).2]
            simp [words, canonReadyWords, addressBank])
          (by
            intro z
            change guarded.workTapes (addressBank 1) z = _
            rw [(frame (addressBank 1) (by simp [addressBank])).1]
            simp [words, canonReadyWords, addressBank])
        have whole := seamCompTM_run_ofCfg G .done R enter rfl done cutDone ranR
        have budgetR := costR.trans (charge rewind.inputPos.val
          (by have := rewind.inputPos.isLt; omega))
        refine ⟨g + 1 + r, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Nat.add_mul] at costG ⊢
          omega
        · rw [whole]
          simp [fits, port, Cfg.mapState]
        · rw [whole]
          exact guardOutput
        · rw [whole]
          simp [fits, Cfg.mapState]
        · intro u hu b
          apply canonSeam_avoids G .done R enter (port b) rfl done cutDone
            (v := r) ?_ ?_ u hu
          · intro z hz
            cases b with
            | true => simp [port, Cfg.mapState]
            | false =>
              have avoids : (G.runFrom guardStart z).state ≠ some .escape := by
                by_cases strict : z < g
                · exact (guardCut z strict).2
                · have eq : z = g := by omega
                  rw [eq]
                  simp only [show G.runFrom guardStart g = guarded from rfl, done]
                  simp
              simpa [port, Cfg.mapState] using avoids
          · intro z hz
            cases b with
            | true => simpa [port, Cfg.mapState] using firstR z hz
            | false => simp [port, Cfg.mapState]
        · rw [whole]
          exact frame
      · have leftRun (u : ℕ) (hu : u ≤ g) :=
          seamCompTM_runFrom_left G .done R enter cutDone u hu
        refine ⟨g, costG.trans (Nat.mul_le_mul_right _ (by omega)), ?_, ?_, ?_, ?_, ?_⟩
        · rw [leftRun g le_rfl]
          simpa [fits, port, Cfg.mapState] using guardState
        · rw [leftRun g le_rfl]
          exact guardOutput
        · rw [leftRun g le_rfl]
          simpa [fits] using guardPos
        · intro u hu b
          rw [leftRun u hu.le]
          cases b with
          | true => simp [port, Cfg.mapState]
          | false => simpa [port, Cfg.mapState] using (guardCut u hu).2
        · rw [leftRun g le_rfl]
          exact frame
    obtain ⟨v, costV, stateV, outputV, posV, cutV, frameV⟩ := tail
    have all := seamCompTM_run_ofCfg R leave U (Sum.inl (.dec .run))
      ranS rfl firstS (rfl : U.runFrom (guardStart.mapState Sum.inl) v = _)
    change C.runFrom (Cfg.ofWords (input := x) (Sum.inl enter) words) (s + 1 + v) = _ at all
    have budgetS := costS.trans (charge 1 (by omega))
    refine ⟨s + 1 + v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have budget := Nat.add_le_add budgetS costV
      ring_nf at budget ⊢
      omega
    · rw [all]
      change ((U.runFrom (guardStart.mapState Sum.inl) v).state.map Sum.inr) = _
      rw [stateV]
      rfl
    · rw [all]
      exact outputV
    · rw [all]
      exact posV
    · intro u hu b
      apply canonSeam_avoids R leave U (Sum.inl (.dec .run)) (Sum.inr (port b))
        ranS rfl firstS (v := v) ?_ ?_ u hu
      · intro z _
        simp [Cfg.mapState]
      · intro z hz
        simpa [Cfg.mapState] using cutV z hz b
    · rw [all]
      exact frameV

/-- A separate strengthening of the frozen guard front end: both Boolean
ports are distinct and have cuts including time zero. Preparation starts
from blank tapes and the non-counter bank is retained on either verdict.

**Proof sketch.** Compose the inherited preparation seam with the prepared
bank guard. The public seam supplies the run; arbitrary-target avoidance
transports both cuts. The two component bounds and the dispatch are linear. -/
private lemma exists_canonGuardFrontStrict (F : MachineFormat) :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Bool → C.State) (a : ℕ),
      4 ≤ C.k ∧ Function.Injective exit ∧ ∀ x bits rest : List Bool,
        pairDecode x = some (bits, rest) → ∃ t ≤ a * (x.length + 1),
          let start := Cfg.ofWords (input := x) entry (fun _ => [])
          let e := C.tm.runFrom start t
          e.state = some (exit (decide
            (canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length))) ∧
          e.output = [] ∧ e.inputPos.val =
            (if canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length
              then 2 * bits.length + 3 else x.length + 1) ∧
          (∀ u < t, ∀ b, (C.tm.runFrom start u).state ≠ some (exit b)) ∧
          ∀ j, j.val ≠ 1 →
            e.workTapes j = FinTM.bufferTape (canonReadyWords C.k bits j) ∧
              e.workTapePos j = 0 := by
  classical
  obtain ⟨P, pentry, pexit, a, hk, prep⟩ := exists_canonReadySeam
  obtain ⟨S, finite, equal, G, enter, leave, b, distinct, guard⟩ :=
    exists_canonGuardReady F P.k hk
  letI : Fintype S := finite
  letI : DecidableEq S := equal
  let C : FinTM Bool := {
    k := P.k
    State := P.State ⊕ S
    tm := { seamCompTM P.tm pexit G enter with q₀ := Sum.inl pentry } }
  refine ⟨C, Sum.inl pentry, fun d => Sum.inr (leave d), a + b + 1, hk,
    fun _ _ eq => distinct (Sum.inr.inj eq), ?_⟩
  intro x bits rest pair
  obtain ⟨s, budgetS, firstS, ranS⟩ := prep x
  have header : canonHeader x = bits := by simp [canonHeader, pair]
  rw [header] at ranS
  obtain ⟨t, budgetT, stateT, outputT, posT, cutT, frameT⟩ := guard x bits rest pair
  have whole := seamCompTM_run_ofCfg P.tm pexit G enter ranS rfl firstS
    (rfl : G.runFrom (Cfg.ofWords (input := x) enter (canonReadyWords P.k bits)) t = _)
  change C.tm.runFrom (Cfg.ofWords (input := x) (Sum.inl pentry) (fun _ => []))
    (s + 1 + t) = _ at whole
  refine ⟨s + 1 + t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.add_mul, Nat.add_mul]
    omega
  · rw [whole]
    simp only [Cfg.mapState, stateT, Option.map_some]
  · rw [whole]
    exact outputT
  · rw [whole]
    exact posT
  · intro u hu d
    apply canonSeam_avoids P.tm pexit G enter (Sum.inr (leave d))
      ranS rfl firstS (v := t) ?_ ?_ u hu
    · intro z _
      simp [Cfg.mapState]
    · intro z hz
      simpa [Cfg.mapState] using cutT z hz d
  · rw [whole]
    exact frameT

/-- Transport a blank-tape start along any public bank embedding.
This is only a specialization of the existing word-configuration assembly
and public run transport, and adds no configuration reconstruction. -/
private lemma canonBlankLift {m k : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
    (bank : Fin m ↪ Fin k) (q : S) (x : List Bool) (t : ℕ) :
    (embedEmitTM bank M).runFrom (Cfg.ofWords (input := x) q (fun _ => [])) t =
      embedEmitCfg bank (fun _ => FinTM.bufferTape []) (fun _ => 0) []
        (M.runFrom (Cfg.ofWords (input := x) q (fun _ => [])) t) := by
  rw [← canonEmbedWords M bank q (fun _ => []) (fun _ => []) (fun _ => [])
    (fun _ => rfl) (fun _ _ => rfl)]
  exact embedEmitTM_runFrom bank M _ _ _ _ t

/-- Total header checking followed by the strong guard. Three distinct live
ports retain the cause of rejection: `none` is a malformed or noncanonical
header, `some false` is a failed positive guard, and `some true` is ready
for parsing. Every rejection decodes to the fixed fallback. Both guard
ports and the header-failure port have strict cuts including time zero.

**Proof sketch.** Embed the clean header branch and the strong guard into
the larger bank. A public seam dispatches only the valid-header exit.
Invalid headers stop before dispatch; valid headers use the guard contract.
The public selected-tape and frame projections retain the ready bank, and
the inherited scanner rejection laws identify both failures with fallback. -/
private lemma exists_canonCheckedFront (F : MachineFormat) :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Option Bool → C.State) (a : ℕ),
      4 ≤ C.k ∧ Function.Injective exit ∧ ∀ x : List Bool,
        ∃ t ≤ a * (x.length + 1), ∃ verdict : Option Bool,
          let start := Cfg.ofWords (input := x) entry (fun _ => [])
          let e := C.tm.runFrom start t
          e.state = some (exit verdict) ∧ e.output = [] ∧
          (∀ u < t, ∀ q, (C.tm.runFrom start u).state ≠ some (exit q)) ∧
          (verdict ≠ some true → F.decode x = F.fallback) ∧
          (verdict = some true → ∃ bits rest,
            pairDecode x = some (bits, rest) ∧ bits = (codeBitsNat bits).bits ∧
            canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length ∧
            e.inputPos.val = 2 * bits.length + 3 ∧
            ∀ j, j.val ≠ 1 →
              e.workTapes j = FinTM.bufferTape (canonReadyWords C.k bits j) ∧
                e.workTapePos j = 0) := by
  classical
  obtain ⟨H, hentry, hexit, a, _, hdistinct, header⟩ := exists_canonHeaderBranch
  obtain ⟨G, gentry, gexit, b, gsize, gdistinct, guard⟩ := exists_canonGuardFrontStrict F
  let K := max H.k G.k
  let hb : Fin H.k ↪ Fin K := Fin.castLEEmb (Nat.le_max_left _ _)
  let gb : Fin G.k ↪ Fin K := Fin.castLEEmb (Nat.le_max_right _ _)
  let A := embedEmitTM hb H.tm
  let B := embedEmitTM gb G.tm
  let C : FinTM Bool := {
    k := K
    State := H.State ⊕ G.State
    tm := { seamCompTM A (hexit true) B gentry with q₀ := Sum.inl hentry } }
  let exit : Option Bool → C.State
    | none => Sum.inl (hexit false)
    | some d => Sum.inr (gexit d)
  refine ⟨C, Sum.inl hentry, exit, a + b + 1,
    gsize.trans (Nat.le_max_right _ _), ?_, ?_⟩
  · intro p q eq
    cases p <;> cases q
    · rfl
    · cases eq
    · cases eq
    · exact congrArg some (gdistinct (Sum.inr.inj eq))
  · intro x
    obtain ⟨s, budgetH, cutH, ranH⟩ := header x
    let startH := Cfg.ofWords (input := x) hentry (fun _ : Fin K => [])
    have headerRun : A.runFrom startH s =
        Cfg.ofWords (hexit (canonHeaderOK x)) (fun _ => []) := by
      rw [canonBlankLift H.tm hb, ranH]
      exact canonEmbedWords H.tm hb _ (fun _ => []) (fun _ => []) (fun _ => [])
        (fun _ => rfl) (fun _ _ => rfl)
    have headerCut (u : ℕ) (hu : u < s) (d : Bool) :
        (A.runFrom startH u).state ≠ some (hexit d) := by
      rw [canonBlankLift H.tm hb]
      exact cutH u hu d
    cases valid : canonHeaderOK x with
    | false =>
      have leftRun := seamCompTM_runFrom_left A (hexit true) B gentry
        (fun u hu => headerCut u hu true) s le_rfl
      rw [headerRun, valid] at leftRun
      change C.tm.runFrom (Cfg.ofWords (input := x) (Sum.inl hentry) (fun _ => [])) s =
        Cfg.ofWords (exit none) (fun _ => []) at leftRun
      refine ⟨s, budgetH.trans (Nat.mul_le_mul_right _ (by omega)), none,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [leftRun]
        rfl
      · rw [leftRun]
        rfl
      · intro u hu q
        change ((seamCompTM A (hexit true) B gentry).runFrom (startH.mapState Sum.inl) u).state ≠ _
        rw [seamCompTM_runFrom_left A (hexit true) B gentry
          (fun z hz => headerCut z hz true) u hu.le]
        cases q with
        | none => simpa [exit, Cfg.mapState] using headerCut u hu false
        | some q => simp [exit, Cfg.mapState]
      · exact fun _ => decode_of_canonHeader F x valid
      · simp
    | true =>
      obtain ⟨bits, rest, pair, canonical⟩ := (canonHeaderOK_iff x).mp valid
      obtain ⟨t, budgetG, stateG, outputG, posG, cutG, frameG⟩ := guard x bits rest pair
      let result := decide (canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length)
      let startG := Cfg.ofWords (input := x) gentry (fun _ : Fin K => [])
      let endG := B.runFrom startG t
      have state : endG.state = some (gexit result) := by
        dsimp only [endG]
        rw [canonBlankLift G.tm gb]
        exact stateG
      have silent : endG.output = [] := by
        dsimp only [endG]
        rw [canonBlankLift G.tm gb]
        exact outputG
      have cut (u : ℕ) (hu : u < t) (d : Bool) :
          (B.runFrom startG u).state ≠ some (gexit d) := by
        rw [canonBlankLift G.tm gb]
        exact cutG u hu d
      rw [valid] at headerRun
      have whole := seamCompTM_run_ofCfg A (hexit true) B gentry headerRun rfl
        (fun u hu => headerCut u hu true) (rfl : B.runFrom startG t = endG)
      change C.tm.runFrom (Cfg.ofWords (input := x) (Sum.inl hentry) (fun _ => []))
        (s + 1 + t) = endG.mapState Sum.inr at whole
      refine ⟨s + 1 + t, ?_, some result, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Nat.add_mul, Nat.add_mul]
        omega
      · rw [whole]
        change endG.state.map Sum.inr = _
        rw [state]
        rfl
      · rw [whole]
        exact silent
      · intro u hu q
        apply canonSeam_avoids A (hexit true) B gentry (exit q) headerRun rfl
          (fun z hz => headerCut z hz true) (v := t) ?_ ?_ u hu
        · intro z hz
          cases q with
          | some d => simp [exit, Cfg.mapState]
          | none =>
            have avoids : (A.runFrom startH z).state ≠ some (hexit false) := by
              by_cases early : z < s
              · exact headerCut z early false
              · have eq : z = s := by omega
                rw [eq, headerRun]
                exact fun h => Bool.noConfusion (hdistinct (Option.some.inj h))
            simpa [exit, Cfg.mapState] using avoids
        · intro z hz
          cases q with
          | none => simp [exit, Cfg.mapState]
          | some d => simpa [exit, Cfg.mapState] using cut z hz d
      · intro rejected
        apply decode_of_canonGuard F x bits rest pair
        have denied : result ≠ true := fun eq => rejected (congrArg some eq)
        exact Nat.lt_of_not_ge (of_decide_eq_false (Bool.eq_false_iff.mpr denied))
      · intro accepted
        have fits : canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length :=
          of_decide_eq_true (Option.some.inj accepted)
        refine ⟨bits, rest, pair, canonical, fits, ?_, ?_⟩
        · rw [whole]
          change endG.inputPos.val = _
          dsimp only [endG]
          rw [canonBlankLift G.tm gb]
          simpa only [if_pos fits] using posG
        · intro j hj
          rw [whole]
          change endG.workTapes j = _ ∧ endG.workTapePos j = 0
          by_cases selected : j ∈ Set.range gb
          · obtain ⟨i, rfl⟩ := selected
            dsimp only [endG]
            rw [canonBlankLift G.tm gb, embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
            exact frameG i hj
          · have fixed := (embedEmitTM_frame gb G.tm (fun _ => FinTM.bufferTape [])
              (fun _ => 0) [] (Cfg.ofWords (input := x) gentry (fun _ => [])) t).1 j selected
            rw [canonEmbedWords G.tm gb gentry (fun _ => []) (fun _ => []) (fun _ => [])
              (fun _ => rfl) (fun _ _ => rfl)] at fixed
            have large : G.k ≤ j.val := by
              by_contra small
              exact selected ⟨⟨j.val, by omega⟩, rfl⟩
            simpa [canonReadyWords, show j.val ≠ 0 by omega,
              show j.val ≠ 1 by omega, show j.val ≠ 2 by omega] using fixed

/-- Merge the three checked-front ports into two ports with one public
phase-host dispatch. `some true` succeeds and the other two ports reject.
The dispatch preserves all data fields and gives strict cuts at both ports.

**Promotion candidate.** This finite verdict adapter is independent of
machine formats; it uses the public phase host, with no private host trace.

**Proof sketch.** Before the source exit, its three cuts disable every
redirect. The public phase contract therefore gives the whole prefix and
one stationary dispatch into the terminal phase. Distinct phase tags prove
both strict cuts. The terminal phase reuses the existing stationary Boolean
ports; no terminal transition is executed by this contract. -/
private lemma canonExitDispatch {k : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (positive : 0 < k) (M : MultiTapeTM k Bool S) (start : S)
    (exit : Option Bool → S) (distinct : Function.Injective exit) :
    ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (N : MultiTapeTM k Bool R)
      (entry : R) (leave : Bool → R), Function.Injective leave ∧
      ∀ (x : List Bool) (t : ℕ) (v : Option Bool),
        let d := Cfg.ofWords (input := x) start (fun _ => [])
        (M.runFrom d t).state = some (exit v) →
        (∀ u < t, ∀ q, (M.runFrom d u).state ≠ some (exit q)) →
        N.runFrom (Cfg.ofWords entry (fun _ => [])) (t + 1) =
          (M.runFrom d t).mapState (fun _ => leave (decide (v = some true))) ∧
        ∀ u < t + 1, ∀ b, (N.runFrom
          (Cfg.ofWords (input := x) entry (fun _ => [])) u).state ≠ some (leave b) := by
  classical
  let Ph : Bool → Type
    | false => S
    | true => Option Bool
  let family (b : Bool) : MultiTapeTM k Bool (Ph b) := match b with
    | false => M
    | true => canonBoolPopTM k ⟨0, positive⟩
  letI : ∀ b, Fintype (Ph b) := fun b => by cases b <;> exact inferInstance
  letI : ∀ b, DecidableEq (Ph b) := fun b => by cases b <;> exact inferInstance
  let base : (b : Bool) × Ph b := ⟨false, start⟩
  let leave (b : Bool) : (p : Bool) × Ph p := ⟨true, some b⟩
  let red (b : Bool) : Ph b → Option ((p : Bool) × Ph p) := match b with
    | false => fun q =>
      if q = exit none then some (leave false)
      else if q = exit (some false) then some (leave false)
      else if q = exit (some true) then some (leave true) else none
    | true => fun _ => none
  let N := phaseHostTM family base red
  refine ⟨_, inferInstance, inferInstance, N, base, leave, ?_, ?_⟩
  · intro b c eq
    exact Option.some.inj (eq_of_heq (Sigma.mk.inj_iff.mp eq).2)
  · intro x t v d control cuts
    have redirect : red false (exit v) = some (leave (decide (v = some true))) := by
      cases v with
      | none => simp [red]
      | some b => cases b <;> simp [red, distinct.eq_iff]
    have disabled (u : ℕ) (hu : u < t) (s : S) (hs : (M.runFrom d u).state = some s) :
        red false s = none := by
      have avoids (q : Option Bool) : s ≠ exit q :=
        fun eq => cuts u hu q (hs.trans (congrArg some eq))
      simp only [red, if_neg (avoids none), if_neg (avoids (some false)),
        if_neg (avoids (some true))]
    have phase := phaseHostTM_run family base red false d (M.runFrom d t) t rfl
      (exit v) control (leave (decide (v = some true))) redirect disabled
    refine ⟨phase.2, ?_⟩
    intro u hu b
    change ((phaseHostTM family base red).runFrom (d.mapState (Sigma.mk false)) u).state ≠ _
    rw [phase.1 u (by omega)]
    change ((M.runFrom d u).state.map (Sigma.mk false)) ≠ some (leave b)
    intro eq
    obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.mp eq
    have impossible := congrArg Sigma.fst hq
    cases impossible

/-- A total composable parser front end. The two strict live ports mean
rejection or ready-for-grammar; every rejection denotes the fixed fallback.
Success retains a canonical header and saved address, has passed the positive
guard, and positions the native head at the remainder. The destroyed guard
counter is deliberately absent from the preserved-bank contract.

**Proof sketch.** Use the total checked front and merge its three cause ports
through the public phase-host adapter. The dispatch is stationary and silent,
so every data invariant transfers unchanged; increase the coefficient by one. -/
private lemma exists_canonParseFront (F : MachineFormat) :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Bool → C.State) (a : ℕ),
      4 ≤ C.k ∧ Function.Injective exit ∧ ∀ x : List Bool,
        ∃ t ≤ a * (x.length + 1), ∃ verdict : Bool,
          let start := Cfg.ofWords (input := x) entry (fun _ => [])
          let e := C.tm.runFrom start t
          e.state = some (exit verdict) ∧ e.output = [] ∧
          (∀ u < t, ∀ q, (C.tm.runFrom start u).state ≠ some (exit q)) ∧
          (verdict = false → F.decode x = F.fallback) ∧
          (verdict = true → ∃ bits rest,
            pairDecode x = some (bits, rest) ∧ bits = (codeBitsNat bits).bits ∧
            canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length ∧
            e.inputPos.val = 2 * bits.length + 3 ∧
            ∀ j, j.val ≠ 1 →
              e.workTapes j = FinTM.bufferTape (canonReadyWords C.k bits j) ∧
                e.workTapePos j = 0) := by
  obtain ⟨H, hentry, hexit, a, enough, distinct, front⟩ := exists_canonCheckedFront F
  obtain ⟨S, finite, equal, N, entry, leave, separate, dispatch⟩ :=
    canonExitDispatch (by omega) H.tm hentry hexit distinct
  letI : Fintype S := finite
  letI : DecidableEq S := equal
  let C : FinTM Bool := { k := H.k, State := S, tm := N }
  refine ⟨C, entry, leave, a + 1, enough, separate, ?_⟩
  intro x
  obtain ⟨t, budget, v, control, silent, cuts, reject, ready⟩ := front x
  obtain ⟨ran, strict⟩ := dispatch x t v control cuts
  refine ⟨t + 1, ?_, decide (v = some true), ?_, ?_, strict, ?_, ?_⟩
  · rw [Nat.add_mul]
    omega
  · rw [ran]
    simp only [Cfg.mapState, control, Option.map_some]
  · rw [ran]
    exact silent
  · intro no
    exact reject (of_decide_eq_false no)
  · intro yes
    rw [ran]
    exact ready (of_decide_eq_true yes)

/-- The grammar the physical parser decides once the parse front end is ready: the unary
initial state below `n + 1` (`Turing.codeSkipFin`), the fixed `k`-record table
(`Turing.codeSkipTableK`), and the all-`true` suffix. It is the format scanner's residue
after the header, canonicality and guard checks (`scan_eq_canonGrammar`).
-/
private def canonGrammar (k n : ℕ) (rest : List Bool) : Option (List Bool) :=
  ((codeSkipFin (n + 1) rest).bind (codeSkipTableK k n)).bind
    fun tail => if tail.all id then some tail else none

/-- At the parse front end's ready port the format scanner is exactly the fixed grammar on
the header's remainder: the canonicality test and the format's own guard both pass, since
the combined block size dominates `F.guard`.

**Proof sketch.** Unfold the scanner at the decoded pair. Canonicality removes the first
branch; `F.guard ≤ canonGuardBlock F` removes the second; `F.skipTable_eq` turns the
format's table skipper into the fixed one. -/
private lemma scan_eq_canonGrammar (F : MachineFormat) (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest)) (hb : bits = (codeBitsNat bits).bits)
    (hg : canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length) :
    F.scan α = canonGrammar F.k (codeBitsNat bits) rest := by
  have hguard : F.guard * (codeBitsNat bits + 1) ≤ rest.length :=
    (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)).trans hg
  unfold CodeFormat.scan canonGrammar
  rw [hp]
  dsimp only [bind, Option.bind]
  rw [if_neg (not_not.mpr hb), if_neg (not_lt.mpr hguard)]
  cases codeSkipFin (codeBitsNat bits + 1) rest with
  | none => rfl
  | some r =>
    dsimp only
    rw [F.skipTable_eq]
    rfl

/-- The verdict law of the physical validator at the ready port: deciding the fixed grammar
gives a bit whose rejection decodes to the fallback and whose acceptance is a successful
format scan.

**Proof sketch.** Rewrite the scanner by `scan_eq_canonGrammar`. A failed grammar is a
failed scan, hence a failed full parse (`Turing.CodeFormat.scan_full`), hence the fallback
(`Turing.CodeFormat.decode_of_parseFull_none`). -/
private lemma canonGrammar_verdict (F : MachineFormat) (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest)) (hb : bits = (codeBitsNat bits).bits)
    (hg : canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length) :
    ((canonGrammar F.k (codeBitsNat bits) rest).isSome = false → F.decode α = F.fallback) ∧
      ((canonGrammar F.k (codeBitsNat bits) rest).isSome = true →
        ∃ tail, F.scan α = some tail) := by
  rw [← scan_eq_canonGrammar F α bits rest hp hb hg]
  constructor
  · intro h
    have hs : F.scan α = none := Option.not_isSome_iff_eq_none.mp (by simp [h])
    rw [F.scan_full] at hs
    exact F.decode_of_parseFull_none α (Option.map_eq_none_iff.mp hs)
  · intro h
    exact Option.isSome_iff_exists.mp h

/-- The input with its maximal all-`true` suffix removed. On every input the format scanner
accepts it is the canonical serialization of the decoded machine (`canonStrip_of_scan`).
Format independent. -/
private def canonStrip (α : List Bool) : List Bool :=
  (α.reverse.dropWhile id).reverse

/-- A word ending in `false`, followed by an all-`true` suffix, is recovered by
`canonStrip`. -/
private lemma canonStrip_append (u tail : List Bool) (h : tail.all id = true) :
    canonStrip (u ++ [false] ++ tail) = u ++ [false] := by
  have hall : ∀ b ∈ tail.reverse, id b = true := by
    intro b hb
    exact List.all_eq_true.mp h b (List.mem_reverse.mp hb)
  unfold canonStrip
  rw [List.reverse_append, List.dropWhile_append_of_pos hall]
  simp

/-- A nonempty concatenation of words that each end in `false` ends in `false`.
-/
private lemma canonFlatMap_last {A : Type} (L : List A) (f : A → List Bool) (hL : L ≠ [])
    (hf : ∀ a ∈ L, ∃ u, f a = u ++ [false]) : ∃ u, L.flatMap f = u ++ [false] := by
  obtain ⟨L', a, rfl⟩ := (List.eq_nil_or_concat L).resolve_left hL
  obtain ⟨u, hu⟩ := hf a (by simp)
  exact ⟨L'.flatMap f ++ u, by simp [List.flatMap_append, hu]⟩

/-- Every serialized record ends with its successor field's terminating `false`.
-/
private lemma actionBitsK_last {k n : ℕ} (a : Action k Bool (Fin (n + 1))) :
    ∃ u, actionBitsK a = u ++ [false] := by
  obtain ⟨v, hv⟩ : ∃ v, optStateBits a.state = v ++ [false] := by
    cases a.state with
    | none => exact ⟨[], rfl⟩
    | some s => exact ⟨true :: List.replicate s.val true, by simp [optStateBits, unaryFin]⟩
  refine ⟨signBits a.inputTape ++
    (List.finRange k).flatMap
      (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) ++
    optBoolBits a.output ++ v, ?_⟩
  simp only [actionBitsK, hv, List.append_assoc]

/-- The fixed `k`-record serialization ends with `false`: its table is nonempty and its last
record ends with a successor field. -/
private lemma serializeK_last {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))) :
    ∃ u, serializeK M = u ++ [false] := by
  have hw : workReadsK k ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [StepBlock.length_workReadsK]
    exact Nat.pow_pos (by omega)
  have hq : List.finRange (n + 1) ≠ [] := List.ne_nil_of_length_pos (by simp)
  obtain ⟨u, hu⟩ := canonFlatMap_last (List.finRange (n + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      (workReadsK k).flatMap fun w => actionBitsK (M.tr q inp w)) hq fun q _ =>
    canonFlatMap_last ([none, some false, some true] : List (Option Bool))
      (fun inp => (workReadsK k).flatMap fun w => actionBitsK (M.tr q inp w)) (by simp)
      fun inp _ => canonFlatMap_last (workReadsK k) (fun w => actionBitsK (M.tr q inp w)) hw
        fun w _ => actionBitsK_last (M.tr q inp w)
  refine ⟨(n.bits.flatMap fun b => [b, b]) ++ [false, true] ++ unaryFin M.q₀ ++ u, ?_⟩
  have ht : tableBitsK M.tr = u ++ [false] := hu
  simp only [serializeK, pairEncode, ht, List.append_assoc]

/-- The suffix retained by a successful format scan is all `true`. -/
private lemma canonScan_all (F : MachineFormat) (α tail : List Bool)
    (hs : F.scan α = some tail) : tail.all id = true := by
  unfold CodeFormat.scan at hs
  obtain ⟨⟨bits, rest⟩, _, hs⟩ := Option.bind_eq_some_iff.mp hs
  dsimp only at hs
  split at hs
  · contradiction
  split at hs
  · contradiction
  obtain ⟨r, _, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨r', _, hs⟩ := Option.bind_eq_some_iff.mp hs
  split at hs
  next hall =>
    cases hs
    exact hall
  · contradiction

/-- On every input the format scanner accepts, stripping the all-`true` suffix yields the
canonical serialization of the decoded machine.

**Proof sketch.** The scanner is the projected full parse (`Turing.CodeFormat.scan_full`),
so the input is the decoded machine's serialization followed by the retained suffix
(`Turing.CodeFormat.parseFull_sound`). That serialization ends in `false`
(`serializeK_last`) and the suffix is all `true` (`canonScan_all`). -/
private lemma canonStrip_of_scan (F : MachineFormat) (α tail : List Bool)
    (hs : F.scan α = some tail) : canonStrip α = F.serialize (F.decode α) := by
  have hall := canonScan_all F α tail hs
  rw [F.scan_full] at hs
  obtain ⟨⟨M, tail'⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hdec : F.decode α = M := by
    simp [CodeFormat.decode, hp]
  have hα := F.parseFull_sound α M tail' hp
  obtain ⟨u, hu⟩ := serializeK_last (F.machine M)
  rw [hdec, F.serialize_eq M, hu]
  rw [hα, F.serialize_eq M, hu]
  exact canonStrip_append u tail' hall

/-- Removing the trailing `true` bits leaves an empty word or a word ending in `false`.

**Proof sketch.** Append the last bit. A `true` extends the removed suffix; a `false`
ends that suffix and keeps the whole word. -/
private lemma canonStrip_split (w : List Bool) :
    ∃ r, w = canonStrip w ++ List.replicate r true ∧
      (canonStrip w = [] ∨ ∃ u, canonStrip w = u ++ [false]) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨0, rfl, Or.inl rfl⟩
  | append_singleton w b ih =>
    obtain ⟨r, hr, last⟩ := ih
    cases b with
    | false =>
      have strip : canonStrip (w ++ [false]) = w ++ [false] := by
        simp [canonStrip]
      exact ⟨0, by simp [strip], Or.inr ⟨w, strip⟩⟩
    | true =>
      have strip : canonStrip (w ++ [true]) = canonStrip w := by
        simp [canonStrip]
      refine ⟨r + 1, ?_, by simpa only [strip] using last⟩
      rw [strip, List.replicate_succ', ← List.append_assoc]
      exact congrArg (fun v => v ++ [true]) hr

/-- The strip boundary is a prefix boundary, followed only by `true` cells; its final
retained cell, if present, is `false`.

**Proof sketch.** Decompose the word at its stripped prefix, then read either side of the
append boundary. The last retained cell is the terminating `false` of that prefix. -/
private lemma canonStrip_boundary (w : List Bool) :
    (canonStrip w).length ≤ w.length ∧
      w.take (canonStrip w).length = canonStrip w ∧
      (∀ (r : ℕ) (hr : r < w.length), (canonStrip w).length ≤ r → w[r] = true) ∧
      (∀ (r : ℕ) (hr : r < w.length), (canonStrip w).length = r + 1 → w[r] = false) := by
  obtain ⟨t, word, last⟩ := canonStrip_split w
  generalize hu : canonStrip w = u at *
  subst w
  refine ⟨by simp, List.take_left, ?_, ?_⟩
  · intro r hr past
    rw [List.getElem_append_right past]
    simp
  · intro r hr boundary
    rcases last with rfl | ⟨v, rfl⟩
    · simp at boundary
    · have index : r = v.length := by simp at boundary; omega
      subst r
      simp

/-- A trailing-`true` eraser on one selected work tape. No catalog row erases only a suffix:
the two-pass scan rewrites each symbol to a symbol, so it cannot replace a bit by blank.
The forward pass finds the right blank. The return pass erases until the first `false`,
then preserves the remaining prefix, reaching the origin at its live exit. -/
private def canonTrimTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool (ScanPhase Bool) where
  q₀ := .fwd false
  tr := fun q _ w =>
    let (write, move, next) : Option (Option Bool) × SignType × ScanPhase Bool :=
      match q, w i with
      | .fwd _, some _ => (none, .pos, .fwd false)
      | .fwd _, none => (none, .neg, .bwd true)
      | .bwd clean, some b =>
        (if clean && b then some none else none, .neg, .bwd (clean && b))
      | .bwd _, none => (none, .pos, .done false)
      | .done _, _ => (none, 0, .done false)
    tapeAction i 0 write move next

/-- Erasing the last cell of a finite buffer removes precisely its final symbol.

**Proof sketch.** The append law installs the last cell with a point update. A second
update to blank restores the original buffer, which is blank at its own length. -/
private lemma canonEraseLast (w : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (w ++ [b])) (w.length : ℤ) none =
      FinTM.bufferTape w := by
  rw [FinTM.bufferTape_append, Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  simp

/-- The eraser returns at the origin with exactly the stripped word and has no earlier
visit to its exit. All other tape words, the native head and the output are unchanged.

**Proof sketch.** Apply the public two-pass trace theorem. On the backward pass at position
`r - 1`, the retained buffer is the original prefix of length `max r |canonStrip w|`.
The finite flag records whether the strip boundary has been crossed. The boundary facts
identify the cell that switches the flag, and the one-cell erase law shortens only the suffix.
This also covers an empty input and a word consisting entirely of `true` bits. -/
private lemma canonTrim_run (k : ℕ) (i : Fin k) (x : List Bool)
    (words : Fin k → List Bool) :
    (canonTrimTM k i).runFrom (Cfg.ofWords (input := x) (.fwd false) words)
        (2 * (words i).length + 2) =
      Cfg.ofWords (.done false) (Function.update words i (canonStrip (words i))) ∧
      ∀ t < 2 * (words i).length + 2,
        ((canonTrimTM k i).runFrom (Cfg.ofWords (input := x) (.fwd false) words) t).state ≠
          some (.done false) := by
  let w := words i
  let m := (canonStrip w).length
  obtain ⟨small, pref, past, boundary⟩ := canonStrip_boundary w
  let base := Cfg.ofWords (input := x) (ScanPhase.fwd false) words
  let fwd (r : ℕ) : Cfg k Bool (ScanPhase Bool) x :=
    { base with workTapePos := Function.update base.workTapePos i r }
  let back (r : ℕ) : Cfg k Bool (ScanPhase Bool) x :=
    { base with state := some (.bwd (decide (m ≤ r)))
                workTapes := Function.update base.workTapes i
                  (FinTM.bufferTape (w.take (max r m)))
                workTapePos := Function.update base.workTapePos i ((r : ℤ) - 1) }
  let done : Cfg k Bool (ScanPhase Bool) x :=
    Cfg.ofWords (.done false) (Function.update words i (canonStrip w))
  have start : fwd 0 = base := by simp [fwd, base, Cfg.ofWords]
  have forward (r : ℕ) (hr : r < w.length) :
      (canonTrimTM k i).step (fwd r) = fwd (r + 1) := by
    have read : (fwd r).workTapeSymbols i = some w[r] := by
      simp [fwd, base, Cfg.ofWords, Cfg.workTapeSymbols, w, hr]
    rw [step_of_tapeAction_move _ _ i 0 .pos rfl
      (q' := ScanPhase.fwd false) (by simp [canonTrimTM, read])]
    apply Cfg.ext <;> try rfl
    · simp [fwd, moveInputPos_zero]
    · simp [fwd, Function.update_idem, Nat.cast_add]
  have turn : (canonTrimTM k i).step (fwd w.length) = back w.length := by
    have read : (fwd w.length).workTapeSymbols i = none := by
      simp [fwd, base, Cfg.ofWords, Cfg.workTapeSymbols, w]
    rw [step_of_tapeAction_move _ _ i 0 .neg rfl
      (q' := ScanPhase.bwd true) (by simp [canonTrimTM, read])]
    apply Cfg.ext <;>
      simp [fwd, back, m, small, Function.update_idem, base, Cfg.ofWords, w,
        sub_eq_add_neg]
  have backward (r : ℕ) (hr : r < w.length) :
      (canonTrimTM k i).step (back (r + 1)) = back r := by
    have read : (back (r + 1)).workTapeSymbols i = some w[r] := by
      simp only [back, Cfg.workTapeSymbols, Function.update_self, Nat.cast_add,
        Nat.cast_one, add_sub_cancel_right, FinTM.bufferTape_nat]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hr]
    by_cases erase : m ≤ r
    · have bit : w[r] = true := past r hr erase
      have flag : decide (m ≤ r + 1) = true := by simp; omega
      have cells : Function.update (FinTM.bufferTape (w.take (max (r + 1) m)))
          (r : ℤ) none = FinTM.bufferTape (w.take (max r m)) := by
        rw [max_eq_left (by omega), max_eq_left erase,
          List.take_succ_eq_append_getElem hr]
        have len : (w.take r).length = r := List.length_take_of_le (by omega)
        simpa only [len] using canonEraseLast (w.take r) w[r]
      rw [step_of_tapeAction_write _ _ i 0 none .neg rfl
        (q' := ScanPhase.bwd true) (by simp only [canonTrimTM, read, flag, bit]; rfl)]
      apply Cfg.ext <;>
        simp only [back, Function.update_self, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right, cells, Function.update_idem, moveInputPos_zero,
          decide_eq_true erase]
      simp [sub_eq_add_neg]
    · have notzero : r + 1 ≤ m := by omega
      have value : (decide (m ≤ r + 1) && w[r]) = false := by
        by_cases edge : m = r + 1
        · simp [edge, boundary r hr edge]
        · rw [decide_eq_false (by omega : ¬m ≤ r + 1)]
          rfl
      have same : max (r + 1) m = max r m := by omega
      rw [step_of_tapeAction_move _ _ i 0 .neg rfl
        (q' := ScanPhase.bwd false) (by simp only [canonTrimTM, read, value]; rfl)]
      apply Cfg.ext <;>
        simp [back, same, erase, Function.update_idem, Nat.cast_add, sub_eq_add_neg]
  have enter : (canonTrimTM k i).step (back 0) = done := by
    have read : (back 0).workTapeSymbols i = none := by
      simp [back, Cfg.workTapeSymbols]
    rw [step_of_tapeAction_move _ _ i 0 .pos rfl
      (q' := ScanPhase.done false) (by simp [canonTrimTM, read])]
    apply Cfg.ext
    all_goals simp [back, done, base, Cfg.ofWords, m, pref, Function.update_idem]
    funext j
    by_cases eq : j = i
    · subst j; simp
    · simp only [Function.update_of_ne eq]
  have stationary : (canonTrimTM k i).step done = done := by
    rw [step_of_tapeAction_move _ _ i 0 0 rfl (q' := ScanPhase.done false) rfl]
    simp [done, Cfg.ofWords]
  have trace (t : ℕ) :=
    catalog_trace_run (canonTrimTM k i) fwd back done w.length forward turn backward
      enter stationary t
  rw [start] at trace
  refine ⟨?_, ?_⟩
  · rw [trace]
    rw [catalogTrace, if_neg (by dsimp [w]; omega), if_neg (by dsimp [w]; omega)]
  · intro t ht
    rw [trace]
    simp only [catalogTrace]
    split_ifs with front rear
    · simp [fwd, base, Cfg.ofWords]
    · simp [back]
    · change t < 2 * w.length + 2 at ht
      omega

/-- **The polynomial-time strip machine.** One finite binary machine computes `canonStrip`
in polynomial time. Format independent; a promotion candidate.

**Proof sketch.** Copy the native input to a work tape (`Turing.inputCopyTM`). A one-tape
leaf walks to the word's right end, erases the trailing `true` cells moving left until a
`false` or the left delimiter, and returns to the origin. Forward the remaining word to the
output by the public emit call `Turing.FinTM.exists_emitCallTM` with the identity machine,
and halt. Every phase is linear. -/
private lemma exists_canonStripTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime canonStrip (fun n => a * (n + 1) ^ a) := by
  classical
  obtain ⟨I, a, identity⟩ := FinTM.computesFunInTime_id
  obtain ⟨E, entry, exit, c, positive, emit⟩ :=
    FinTM.exists_emitCallTM I id (fun n => a * (n + 1)) identity
  let i : Fin E.k := ⟨0, positive⟩
  let trim := canonTrimTM E.k i
  let prepare := seamCompTM (inputCopyTM E.k i) .done trim (.fwd false)
  let release := seamReleaseTM E.tm entry
  let halt : MultiTapeTM E.k Bool Unit :=
    ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let finish := seamCompTM release (Sum.inr exit) halt ()
  let machine : FinTM Bool := {
    k := E.k
    State := (SweepPhase ⊕ ScanPhase Bool) ⊕ ((Unit ⊕ E.State) ⊕ Unit)
    tm := { seamCompTM prepare (Sum.inr (.done false)) finish (Sum.inl (Sum.inl ())) with
      q₀ := Sum.inl (Sum.inl .sweep) } }
  let d := c * (a + 2) + 8
  refine ⟨machine, d, ?_⟩
  intro x
  let source := Cfg.ofWords (input := x) SweepPhase.sweep (fun _ : Fin E.k => [])
  have copied := inputCopyTM_run_ofCfg i source rfl rfl
  have copy : (inputCopyTM E.k i).runFrom source (2 * x.length + 2) =
      Cfg.ofWords .done (stateWord E.k x) := by
    rw [copied.1]
    apply Cfg.ext <;> try rfl
    funext j z
    have index : j = i ↔ j.val = 0 := Fin.ext_iff
    simp only [source, Cfg.ofWords, stateWord, index, zero_add, sub_zero,
      FinTM.bufferTape_nil]
    by_cases zero : j.val = 0
    · simp only [zero, if_true, true_and]
      by_cases nonneg : 0 ≤ z
      · by_cases inside : z < (x.length : ℤ)
        · simp [nonneg, inside]
        · simp [nonneg, inside, FinTM.bufferTape]
      · simp [nonneg, FinTM.bufferTape]
    · simp [zero]
  have word : stateWord E.k x i = x := by simp [stateWord, i]
  have restored : Function.update (stateWord E.k x) i (canonStrip x) =
      stateWord E.k (canonStrip x) := by
    funext j
    by_cases selected : j = i
    · subst j; simp [stateWord, i]
    · have other : j.val ≠ 0 := fun h => selected (Fin.ext h)
      simp [Function.update_of_ne selected, stateWord, other]
  obtain ⟨trimmed, trimCut⟩ := canonTrim_run E.k i x (stateWord E.k x)
  rw [word, restored] at trimmed
  rw [word] at trimCut
  have prepared := seamCompTM_run_ofCfg (inputCopyTM E.k i) .done trim (.fwd false)
    copy rfl copied.2.1 trimmed
  have prepareCut := seamCompTM_firstReturn_ofCfg (inputCopyTM E.k i) .done trim
    (.fwd false) (.done false) copy rfl copied.2.1 trimmed rfl trimCut
  let argument := canonStrip x
  let callStart := Cfg.ofWords (input := x) entry (stateWord E.k argument)
  obtain ⟨t, budget, nonzero, first, ran⟩ := emit x argument
  have released : release.runFrom (callStart.mapState (fun _ => Sum.inl ())) t =
      ({ Cfg.ofWords (input := x) exit (stateWord E.k argument)
          with output := argument } : Cfg E.k Bool E.State x).mapState Sum.inr := by
    rw [seamReleaseTM_runFrom_pos E.tm entry callStart rfl t nonzero]
    exact congrArg (Cfg.mapState Sum.inr) ran
  have releaseCut : ∀ u < t,
      (release.runFrom (callStart.mapState (fun _ => Sum.inl ())) u).state ≠
        some (Sum.inr exit) := by
    intro u hu
    cases u with
    | zero => simp [callStart, Cfg.ofWords, Cfg.mapState]
    | succ u =>
      rw [seamReleaseTM_runFrom_pos E.tm entry callStart rfl _ (Nat.succ_pos _)]
      intro h
      obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp h
      exact first (u + 1) (Nat.succ_pos _) hu
        (hq.trans (congrArg some (Sum.inr.inj eq)))
  let emitted : Cfg E.k Bool (Unit ⊕ E.State) x :=
    ({ Cfg.ofWords (input := x) exit (stateWord E.k argument)
        with output := argument } : Cfg E.k Bool E.State x).mapState Sum.inr
  let stopped := halt.runFrom (emitted.mapState (fun _ => ())) 1
  have stopped_eq : stopped =
      { emitted.mapState (fun _ => ()) with state := none } := by
    simp [stopped, halt, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step,
      emitted, Cfg.mapState, Cfg.ofWords, Action.apply]
  have finished := seamCompTM_run_ofCfg release (Sum.inr exit) halt ()
    released rfl releaseCut (rfl : halt.runFrom (emitted.mapState (fun _ => ())) 1 = stopped)
  have complete := seamCompTM_run_ofCfg prepare (Sum.inr (.done false)) finish
    (Sum.inl (Sum.inl ())) prepared rfl prepareCut finished
  let duration := (2 * x.length + 2 + 1 + (2 * x.length + 2)) + 1 + (t + 1 + 1)
  have computation : machine.ComputesInTime x argument duration := by
    apply (FinTM.computesInTime_iff machine _ _ _).mpr
    rw [initCfg_ofWords]
    change ((seamCompTM prepare (Sum.inr (.done false)) finish _).runFrom
      ((source.mapState Sum.inl).mapState Sum.inl) duration).state = none ∧
      ((seamCompTM prepare (Sum.inr (.done false)) finish _).runFrom
        ((source.mapState Sum.inl).mapState Sum.inl) duration).output = argument
    rw [complete]
    change (stopped.mapState Sum.inr |>.mapState Sum.inr).state = none ∧
      (stopped.mapState Sum.inr |>.mapState Sum.inr).output = argument
    rw [stopped_eq]
    exact ⟨rfl, rfl⟩
  apply computation.mono
  have length : argument.length ≤ x.length := (canonStrip_boundary x).1
  have cost : t ≤ c * (a + 2) * (x.length + 1) := by
    apply budget.trans
    dsimp only [id_eq]
    calc
      c * (a * (argument.length + 1) + argument.length + argument.length + 1)
          ≤ c * ((a + 2) * (argument.length + 1)) := by
        apply Nat.mul_le_mul_left c
        ring_nf
        omega
      _ ≤ c * ((a + 2) * (x.length + 1)) :=
        Nat.mul_le_mul_left c (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  have linear : duration ≤ d * (x.length + 1) := by
    dsimp [duration, d]
    nlinarith
  exact linear.trans (Nat.mul_le_mul_left d (by
    simpa using Nat.pow_le_pow_right (show 1 ≤ x.length + 1 by omega)
      (show 1 ≤ d by dsimp [d]; omega)))

/-- The bounded unary field: `codeSkipFin (n + 1)` accepts exactly `1^i 0` with `i ≤ n`.
 -/
private lemma canonSkipFin_iff (n : ℕ) (ys rest : List Bool) :
    codeSkipFin (n + 1) ys = some rest ↔
      ∃ i, i ≤ n ∧ ys = List.replicate i true ++ false :: rest := by
  constructor
  · intro h
    obtain ⟨⟨i, tail⟩, hu, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    next hi =>
      have e := Option.some.inj h
      exact ⟨i, by omega, by rw [← e]; exact codeReadUnary_sound ys i tail hu⟩
    · contradiction
  · rintro ⟨i, hi, rfl⟩
    simp [codeSkipFin, codeReadUnary_append, show i < n + 1 by omega]

/-- The fixed fields of one record: the input move, the `k` work-tape writes and moves, and
the output, each a two-bit field; the successor field follows.  -/
private def canonSkipFields (k : ℕ) : List Bool → Option (List Bool) :=
  let move : Bool → Bool → Bool := fun a b => a || !b
  fun xs => ((codeSkipPair move xs).bind (codeSkipRepeat codeSkipWork k)).bind (codeSkipPair move)

/-- A record is its fixed fields followed by its successor field.  -/
private lemma canonSkipAction_eq (k n : ℕ) (xs : List Bool) :
    codeSkipActionK k n xs = (canonSkipFields k xs).bind (codeSkipState (n + 1)) := by
  unfold codeSkipActionK canonSkipFields
  simp only [bind, Option.bind_assoc]

/-- A successful pair skip consumes exactly two cells.  -/
private lemma canonSkipPair_cells (v : Bool → Bool → Bool) (xs ys : List Bool)
    (h : codeSkipPair v xs = some ys) : ∃ a b, xs = a :: b :: ys := by
  match xs, h with
  | a :: b :: rest, h =>
    unfold codeSkipPair at h
    dsimp only at h
    split at h
    · cases h
      exact ⟨a, b, rfl⟩
    · contradiction

/-- Successful fixed fields consume exactly `4k + 4` cells.  -/
private lemma canonSkipFields_cells (k : ℕ) (xs ys : List Bool)
    (h : canonSkipFields k xs = some ys) : ∃ u, xs = u ++ ys ∧ u.length = 4 * k + 4 := by
  have work (j : ℕ) (us vs : List Bool) (hw : codeSkipRepeat codeSkipWork j us = some vs) :
      ∃ u, us = u ++ vs ∧ u.length = 4 * j := by
    induction j generalizing us with
    | zero =>
      cases hw
      exact ⟨[], rfl, rfl⟩
    | succ j ih =>
      obtain ⟨ws, hws, hrest⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨zs, hz, hz'⟩ := Option.bind_eq_some_iff.mp hws
      obtain ⟨a, b, rfl⟩ := canonSkipPair_cells _ _ _ hz
      obtain ⟨c, d, rfl⟩ := canonSkipPair_cells _ _ _ hz'
      obtain ⟨u, rfl, hu⟩ := ih ws hrest
      exact ⟨a :: b :: c :: d :: u, rfl, by simp only [List.length_cons, hu]; omega⟩
  obtain ⟨zs, hz, hout⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, hws, hrep⟩ := Option.bind_eq_some_iff.mp hz
  obtain ⟨a, b, rfl⟩ := canonSkipPair_cells _ _ _ hws
  obtain ⟨u, rfl, hu⟩ := work k ws zs hrep
  obtain ⟨c, d, rfl⟩ := canonSkipPair_cells _ _ _ hout
  exact ⟨a :: b :: (u ++ [c, d]), by simp,
    by simp only [List.length_cons, List.length_append, List.length_nil, hu]⟩

/-- Repetition counts add.  -/
private lemma canonSkipRepeat_add (r : List Bool → Option (List Bool)) (m n : ℕ)
    (xs : List Bool) :
    codeSkipRepeat r (m + n) xs = (codeSkipRepeat r m xs).bind (codeSkipRepeat r n) := by
  induction m generalizing xs with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    rw [Nat.succ_add]
    show (r xs).bind (codeSkipRepeat r (m + n)) =
      ((r xs).bind (codeSkipRepeat r m)).bind (codeSkipRepeat r n)
    cases r xs with
    | none => rfl
    | some ys => exact ih ys

/-- A repetition of repetitions is one repetition of the product length.
 -/
private lemma canonSkipRepeat_mul (r : List Bool → Option (List Bool)) (a b : ℕ)
    (xs : List Bool) :
    codeSkipRepeat (codeSkipRepeat r a) b xs = codeSkipRepeat r (a * b) xs := by
  induction b generalizing xs with
  | zero => rfl
  | succ b ih =>
    have e : a * (b + 1) = a + a * b := by ring
    rw [e, canonSkipRepeat_add r a (a * b)]
    show (codeSkipRepeat r a xs).bind (codeSkipRepeat (codeSkipRepeat r a) b) = _
    congr 1
    funext ys
    exact ih ys

/-- The fixed table grammar is `n + 1` states of `3^(k+1)` records each.
 -/
private lemma canonSkipTable_eq (k n : ℕ) (xs : List Bool) :
    codeSkipTableK k n xs =
      codeSkipRepeat (codeSkipRepeat (codeSkipActionK k n) (3 ^ (k + 1))) (n + 1) xs := by
  have iter (j : ℕ) (r : List Bool → Option (List Bool)) :
      (fun f => codeSkipRepeat f 3)^[j] r = codeSkipRepeat r (3 ^ j) := by
    induction j with
    | zero =>
      funext ys
      show r ys = (r ys).bind some
      cases r ys <;> rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      funext ys
      rw [canonSkipRepeat_mul, Nat.pow_succ]
  unfold codeSkipTableK
  rw [iter]

/-- Read one native cell, advancing exactly when it is the requested bit. The catalog's
native readers traverse the whole input, so this single-cell leaf supplies the local test.
No work tape is touched and no symbol is emitted. -/
private def canonCellTM (k : ℕ) (bit : Bool) : MultiTapeTM k Bool (Option Bool) where
  q₀ := none
  tr := fun _ inp _ =>
    inputMoveAction (if inp = some bit then 1 else 0) (some (decide (inp = some bit)))

/-- The native-cell leaf has exactly the public input-only action's effect. -/
private lemma canonCell_step {k : ℕ} {x : List Bool} (bit : Bool)
    (d : Cfg k Bool (Option Bool) x) (q : Option Bool) (hq : d.state = some q) :
    (canonCellTM k bit).step d =
      { d with
        state := some (some (decide (d.inputSymbol = some bit)))
        inputPos := moveInputPos d.inputPos (if d.inputSymbol = some bit then 1 else 0) } :=
  step_of_inputMoveAction _ _ _ hq rfl

/-- Every word has a maximal initial run of `true` cells, followed by either a
`false` or the right blank. Only existence is used by the physical reader.

**Proof sketch.** Specialize the public list decomposition into an initial constant
run and its first different cell. A leading false cell gives a zero-length true run. -/
private lemma canonTruePrefix (xs : List Bool) :
    ∃ r rest, xs = List.replicate r true ++ rest ∧
      (rest = [] ∨ ∃ ys, rest = false :: ys) := by
  rcases List.eq_replicate_or_eq_replicate_append_cons xs with
    rfl | ⟨n, b, rfl, positive⟩ | ⟨n, a, b, ys, rfl, positive, different⟩
  · exact ⟨0, [], rfl, Or.inl rfl⟩
  · cases b with
    | false =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact ⟨0, _, rfl, Or.inr ⟨List.replicate n false, rfl⟩⟩
    | true => exact ⟨n, [], by simp, Or.inl rfl⟩
  · cases a with
    | false =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact ⟨0, _, rfl, Or.inr ⟨List.replicate n false ++ b :: ys, rfl⟩⟩
    | true =>
      cases b
      · exact ⟨n, false :: ys, rfl, Or.inr ⟨ys, rfl⟩⟩
      · exact (different rfl).elim

/-- A true prefix gives the exact body orbit of the unary reader. This is only a
calculation of the one-cell body's orbit; the physical countdown uses the public host.

**Proof sketch.** At round `r` the native head is at the original position plus `r`.
The supplied prefix lookup makes the next one-cell action a right move and a return to
the same anchor. The shared round-orbit successor law gives the induction step. -/
private lemma canonTrueOrbit {k : ℕ} {x : List Bool}
    (d : Cfg k Bool (Option Bool) x) (hs : d.state = some (some true))
    (p r : ℕ) (hp : d.inputPos.val = p + 1) (hr : p + r ≤ x.length)
    (hprefix : ∀ i < r, x[p + i]? = some true) :
    counterLoopOrbit (canonCellTM k true) (fun _ => 1) d r =
      { d with state := some (some true), inputPos := ⟨p + r + 1, by omega⟩ } := by
  simp only [counterLoopOrbit]
  induction r with
  | zero =>
    change d = _
    refine Cfg.ext hs ?_ rfl rfl rfl
    exact Fin.ext hp
  | succ r ih =>
    rw [roundOrbit_succ, ih (by omega) (fun i hi => hprefix i (by omega))]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      canonCell_step true _ (some true) rfl]
    have read :
        ({ d with
          state := some (some true)
          inputPos := ⟨p + r + 1, by omega⟩ } : Cfg k Bool (Option Bool) x).inputSymbol =
          some true := (FinTM.inputSymbol_at _ (p + r) (by omega) rfl).trans (hprefix r (by omega))
    simp only [read, decide_true, if_true]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    change (moveInputPos (⟨p + r + 1, by omega⟩ : Fin (x.length + 2)) SignType.pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by
      change p + r + 1 ≠ x.length + 1
      omega)]
    rfl

/-- Replacing a buffered word by another word of the same width changes only its interval.
The two buffers are both blank outside that interval.

**Proof sketch.** Split at zero and the common length. Inside the interval use the
replacement branch; outside it both buffers are blank by the public list lookup bound. -/
private lemma canonPatchWord (w v : List Bool) (width : v.length = w.length) :
    (fun z : ℤ => if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape v z
      else FinTM.bufferTape w z) = FinTM.bufferTape v := by
  funext z
  by_cases nonneg : 0 ≤ z
  · by_cases inside : z < (w.length : ℤ)
    · simp [nonneg, inside]
    · have past : w.length ≤ z.toNat := by omega
      simp [nonneg, inside, FinTM.bufferTape,
        List.getElem?_eq_none (show v.length ≤ z.toNat by omega)]
  · simp [nonneg, FinTM.bufferTape]

/-- The countdown reads at most the initial true hprefix. Its result keeps the body tapes,
returns the counter head to zero, and retains a buffered counter word of the original width.

**Proof sketch.** If the bound is no larger than the true hprefix, every one-cell round
returns and the public done contract applies. Otherwise the first non-true cell is the
escaping round. Apply the public escape contract and its hprefix amortization bound.
Both cases use the same body-orbit calculation; no host transition is re-proved. -/
private lemma canonUnaryLoop {x : List Bool} (d : Cfg 1 Bool (Option Bool) x)
    (hs : d.state = some (some true)) (p r : ℕ) (hp : d.inputPos.val = p + 1)
    (hr : p + r ≤ x.length) (hprefix : ∀ i < r, x[p + i]? = some true)
    (stopped : x[p + r]? ≠ some true) (w : List Bool) :
    ∃ t ≤ 5 * x.length + 2 * w.length + 7, ∃ v q,
      v.length = w.length ∧ (q = CounterLoopState.done ∨ q = .escape) ∧
      (counterLoopTM (canonCellTM 1 true) (some true) (some (some false))).runFrom
          (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape w) 0) t =
        counterLoopCfg (some q)
          { d with inputPos := ⟨p + min (counterValue w) r + 1, by
              have := Nat.min_le_right (counterValue w) r; omega⟩ }
          (FinTM.bufferTape v) 0 ∧
      ∀ u < t,
        ((counterLoopTM (canonCellTM 1 true) (some true) (some (some false))).runFrom
          (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape w) 0) u).state ≠ some .done ∧
        ((counterLoopTM (canonCellTM 1 true) (some true) (some (some false))).runFrom
          (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape w) 0) u).state ≠ some .escape := by
  let M := canonCellTM 1 true
  let n := counterValue w
  have orbit (j : ℕ) (hj : j ≤ r) :
      counterLoopOrbit M (fun _ => 1) d j =
        { d with state := some (some true), inputPos := ⟨p + j + 1, by omega⟩ } :=
    canonTrueOrbit d hs p j hp (by omega) (fun i hi => hprefix i (by omega))
  by_cases fits : n ≤ r
  · let t := n + counterOverhead w (n + 1)
    have run := counterLoopTM_run_done M (some true) (some (some false)) (fun _ => 1)
      d w (FinTM.bufferTape w) 0 (by intro z _ _; simp) n rfl
      (by
        intro j hj
        rw [orbit j (by omega), orbit (j + 1) (by omega)]
        exact ⟨rfl, Nat.zero_lt_one, by intro u hu hut; change u < 1 at hut; omega,
          rfl⟩) t (by simp [t])
    have charge := counterLoop_time_le M (fun _ => 1) d w n rfl 1
      (by intros; exact le_rfl)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at charge
    have patch : (fun z : ℤ => if 0 ≤ z ∧ z < 0 + (w.length : ℤ) then some true
        else FinTM.bufferTape w z) = FinTM.bufferTape (List.replicate w.length true) := by
      rw [← canonPatchWord w (List.replicate w.length true) (by simp)]
      funext z
      simp only [zero_add]
      split_ifs with inside
      · simp [FinTM.bufferTape, inside.1,
          show z.toNat < w.length by omega]
      · rfl
    refine ⟨t, by dsimp [t] at *; omega, List.replicate w.length true, .done,
      by simp, Or.inl rfl, ?_, run.2.1⟩
    rw [run.1, patch, orbit n fits]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    change p + n + 1 = p + min (counterValue w) r + 1
    rw [Nat.min_eq_left fits]
  · have before : r < n := by omega
    have escape : counterLoopOrbit M (fun _ => 1) d (r + 1) =
        { d with state := some (some false), inputPos := ⟨p + r + 1, by omega⟩ } := by
      change roundOrbit M (fun _ => 1) d (r + 1) = _
      rw [roundOrbit_succ]
      change M.runFrom (counterLoopOrbit M (fun _ => 1) d r) 1 = _
      rw [orbit r le_rfl, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, canonCell_step true _ (some true) rfl]
      have read := FinTM.inputSymbol_at
        ({ d with state := some (some true), inputPos := ⟨p + r + 1, by omega⟩ })
        (p + r) hr rfl
      simp only [read, if_neg stopped, decide_eq_false stopped, moveInputPos_zero]
    let t := r + 1 + counterOverhead w (r + 1)
    have run := counterLoopTM_run_escape M (some true) (some false) (by decide)
      (fun _ => 1) d w (FinTM.bufferTape w) 0 (by intro z _ _; simp) r before
      (by
        intro j hj
        rw [orbit j hj]
        exact ⟨rfl, Nat.zero_lt_one, by intro u hu hut; change u < 1 at hut; omega⟩)
      (by rw [escape]) t (by simp [t])
    have width := counterWord_length w (r + 1)
    have charge := counterOverhead_le_of_le w (r + 1) (by exact Nat.succ_le_of_lt before)
    refine ⟨t, by dsimp [t]; omega, counterWord w (r + 1), .escape, width,
      Or.inr rfl, ?_, run.2.1⟩
    rw [run.1, escape]
    simp only [zero_add, sub_zero]
    rw [canonPatchWord w _ width]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    change p + r + 1 = p + min (counterValue w) r + 1
    rw [Nat.min_eq_right (by omega : r ≤ n)]

/-- The unary component has public-host phases for the countdown, terminating-cell test,
and scratch clearing with either verdict retained in the phase tag. -/
private abbrev canonUnaryPhase : Option (Option Bool) → Type
  | none => CounterLoopState (Option Bool)
  | some none => Option Bool
  | some (some _) => SweepPhase

/-- The unary phase family uses the public countdown and clearing machines. -/
private def canonUnaryFamily (p : Option (Option Bool)) :
    MultiTapeTM 2 Bool (canonUnaryPhase p) :=
  match p with
  | none => counterLoopTM (canonCellTM 1 true) (some true) (some (some false))
  | some none => canonCellTM 2 false
  | some (some _) => clearTM 2 1

/-- Both countdown exits share the terminating-cell test, which dispatches to the
cleanup phase with its Boolean verdict retained. The final ports are clearing's done ports. -/
private def canonUnaryNext (p : Option (Option Bool)) :
    canonUnaryPhase p → Option (Sigma canonUnaryPhase) := match p with
  | none => fun q =>
      if q = .done ∨ q = .escape then some ⟨some none, none⟩ else none
  | some none => fun q => q.map (fun b => ⟨some (some b), .sweep⟩)
  | some (some b) => fun q => if q = .done then some ⟨some (some b), .done⟩ else none

/-- The unary core starts with the copied bound on its last tape. It is a public phase
host, with no private controller for the transitions between the three phases. -/
private def canonUnaryCore : MultiTapeTM 2 Bool (Sigma canonUnaryPhase) :=
  phaseHostTM canonUnaryFamily ⟨none, .dec .run⟩ canonUnaryNext

/-- In a maximal true prefix, the bounded skipper returns the suffix after the first
false cell exactly when that cell is at or below the bound.

**Proof sketch.** A false-terminated field is the public unary-reader append law. A word
consisting only of true cells cannot satisfy `canonSkipFin_iff`, since that characterization
would place a false cell in the word. -/
private lemma canonUnaryField (n r : ℕ) (rest : List Bool)
    (stop : rest = [] ∨ ∃ ys, rest = false :: ys) :
    codeSkipFin (n + 1) (List.replicate r true ++ rest) =
      if r ≤ n then rest.tail? else none := by
  rcases stop with rfl | ⟨ys, rfl⟩
  · have absent : codeSkipFin (n + 1) (List.replicate r true) = none := by
      cases h : codeSkipFin (n + 1) (List.replicate r true) with
      | none => rfl
      | some ys =>
        obtain ⟨i, _, eq⟩ := (canonSkipFin_iff n _ ys).mp h
        have impossible : false ∈ List.replicate r true := by rw [eq]; simp
        simp at impossible
    simp [absent]
  · simp [codeSkipFin, codeReadUnary_append, show (r < n + 1) ↔ r ≤ n by omega]

/-- The unary core consumes a bounded unary field and then clears its scratch counter.
It preserves the other tape, every head, and the output, with a linear time bound.

**Proof sketch.** Split the suffix at its first false cell or right blank. Apply the
public countdown contract to the one-cell orbit, test the stopping cell, and clear the
residual word at its unchanged width. Public phase-host hprefix equations give the strict
exit cuts. No countdown or phase-host transition is re-proved. -/
private lemma canonUnaryCore_run {x : List Bool} (w : List Bool)
    (d : Cfg 2 Bool (Sigma canonUnaryPhase) x)
    (hs : d.state = some ⟨none, .dec .run⟩) (positive : 1 ≤ d.inputPos.val)
    (counter : d.workTapes 1 = FinTM.bufferTape w) (home : d.workTapePos 1 = 0) :
    ∃ t ≤ 12 * (x.length + w.length + 1),
      (canonUnaryCore.runFrom d t).state = some
        ⟨some (some (codeSkipFin (counterValue w + 1)
          (x.drop (d.inputPos.val - 1))).isSome), .done⟩ ∧
      (canonUnaryCore.runFrom d t).output = d.output ∧
      (∀ u < t, ∀ b,
        (canonUnaryCore.runFrom d u).state ≠ some ⟨some (some b), .done⟩) ∧
      (canonUnaryCore.runFrom d t).workTapes =
        Function.update d.workTapes 1 (FinTM.bufferTape []) ∧
      (canonUnaryCore.runFrom d t).workTapePos = d.workTapePos ∧
      ∀ ys, codeSkipFin (counterValue w + 1) (x.drop (d.inputPos.val - 1)) = some ys →
        (canonUnaryCore.runFrom d t).inputPos.val = x.length + 1 - ys.length := by
  let p := d.inputPos.val - 1
  have pos : d.inputPos.val = p + 1 := by dsimp [p]; omega
  have range : p ≤ x.length := by have := d.inputPos.isLt; omega
  obtain ⟨r, rest, parts, stop⟩ := canonTruePrefix (x.drop p)
  have size : x.length = p + r + rest.length := by
    have lengths := congrArg List.length parts
    simp only [List.length_drop, List.length_append, List.length_replicate] at lengths
    omega
  have fits : p + r ≤ x.length := by omega
  have lookup (i : ℕ) : x[p + i]? = (List.replicate r true ++ rest)[i]? := by
    rw [← parts]
    simp only [List.getElem?_drop]
  have hprefix (i : ℕ) (hi : i < r) : x[p + i]? = some true := by
    rw [lookup]
    simp [List.getElem?_append, hi]
  have last : x[p + r]? = rest.head? := by
    rw [lookup]
    simp [List.getElem?_append]
    cases rest <;> rfl
  have stopped : x[p + r]? ≠ some true := by
    rw [last]
    rcases stop with rfl | ⟨ys, rfl⟩ <;> simp
  let start : Cfg 2 Bool (CounterLoopState (Option Bool)) x :=
    d.mapState (fun _ => .dec .run)
  let body := counterLoopBody (some true) start
  have startState : start.state = some (.dec .run) := by simp [start, Cfg.mapState, hs]
  have layout : counterLoopCfg (some (.dec .run)) body (FinTM.bufferTape w) 0 = start := by
    rw [← startState]
    rw [← counter, ← home]
    exact counterLoopCfg_body (some true) start
  obtain ⟨l, boundL, v, q, width, which, runL, cutL⟩ :=
    canonUnaryLoop body rfl p r pos fits hprefix stopped w
  rw [layout] at runL cutL
  let afterLoop := (canonUnaryFamily none).runFrom start l
  have loopEq : afterLoop = _ := runL
  have stateL : afterLoop.state = some q := by rw [loopEq]; rfl
  have first := phaseHostTM_run canonUnaryFamily ⟨none, .dec .run⟩ canonUnaryNext
    none start afterLoop l rfl q stateL ⟨some none, none⟩
    (by simp [canonUnaryNext, which]) (by
      intro u hu s state
      have noDone : s ≠ .done := fun eq => (cutL u hu).1 (state.trans (congrArg some eq))
      have noEscape : s ≠ .escape := fun eq => (cutL u hu).2
        (state.trans (congrArg some eq))
      simp [canonUnaryNext, noDone, noEscape])
  have startEq : start.mapState (Sigma.mk none) = d := by
    apply Cfg.ext <;> simp [start, Cfg.mapState, hs]
  rw [startEq] at first
  let cellStart : Cfg 2 Bool (Option Bool) x := afterLoop.mapState (fun _ => none)
  have cellState : cellStart.state = some none := by simp [cellStart, Cfg.mapState, stateL]
  let bit := decide (cellStart.inputSymbol = some false)
  let afterCell := (canonCellTM 2 false).step cellStart
  have cellEq : afterCell = _ := canonCell_step false cellStart none cellState
  have stateT : afterCell.state = some (some bit) := by rw [cellEq]
  have second := phaseHostTM_run canonUnaryFamily ⟨none, .dec .run⟩ canonUnaryNext
    (some none) cellStart afterCell 1 rfl (some bit) stateT
    ⟨some (some bit), .sweep⟩ rfl (by
      intro u hu s state
      have zero : u = 0 := by omega
      subst u
      have eq : s = none := (Option.some.inj (cellState.symm.trans state)).symm
      subst s
      rfl)
  have cellJoin : afterLoop.mapState (fun _ => (⟨some none, none⟩ : Sigma canonUnaryPhase)) =
      cellStart.mapState (Sigma.mk (some none)) := by
    simp [cellStart, Cfg.mapState, Option.map_map, Function.comp_def]
  rw [← cellJoin] at second
  let clearStart : Cfg 2 Bool SweepPhase x := afterCell.mapState (fun _ => .sweep)
  have clearState : clearStart.state = some .sweep := by simp [clearStart, Cfg.mapState, stateT]
  have clearWord : clearStart.workTapes 1 = FinTM.bufferTape v ∧
      clearStart.workTapePos 1 = 0 := by
    change afterCell.workTapes 1 = _ ∧ afterCell.workTapePos 1 = _
    rw [cellEq]
    change afterLoop.workTapes 1 = _ ∧ afterLoop.workTapePos 1 = _
    rw [loopEq]
    simp only [counter_cfg_eq]
    change Fin.lastCases (motive := fun _ : Fin 2 => ℤ → Option Bool)
      (FinTM.bufferTape v) body.workTapes (Fin.last 1) = _ ∧
      Fin.lastCases (motive := fun _ : Fin 2 => ℤ) 0 body.workTapePos (Fin.last 1) = _
    simp only [Fin.lastCases_last, and_self]
  have clearing := clearTM_run_ofCfg (1 : Fin 2) v clearStart clearState
    (by intro z _ _; rw [clearWord.1, clearWord.2]; simp)
  let c := 2 * v.length + 2
  let afterClear := (clearTM 2 (1 : Fin 2)).runFrom clearStart c
  have clearEq : afterClear = _ := clearing.1
  have stateC : afterClear.state = some .done := by rw [clearEq]
  have third := phaseHostTM_run canonUnaryFamily ⟨none, .dec .run⟩ canonUnaryNext
    (some (some bit)) clearStart afterClear c rfl .done stateC
    ⟨some (some bit), .done⟩ (by rfl) (by
      intro u hu s state
      have notDone : s ≠ .done := fun eq =>
        clearing.2.1 u hu (state.trans (congrArg some eq))
      simp [canonUnaryNext, notDone])
  have clearJoin : afterCell.mapState
      (fun _ => (⟨some (some bit), .sweep⟩ : Sigma canonUnaryPhase)) =
      clearStart.mapState (Sigma.mk (some (some bit))) := by
    simp [clearStart, Cfg.mapState, Option.map_map, Function.comp_def]
  let duration := (l + 1) + 2 + c
  have whole : canonUnaryCore.runFrom d duration =
      afterClear.mapState (Sigma.mk (some (some bit))) := by
    change (phaseHostTM canonUnaryFamily ⟨none, .dec .run⟩ canonUnaryNext).runFrom d _ = _
    rw [MultiTapeTM.runFrom_add d (l + 1 + 2) c,
      MultiTapeTM.runFrom_add d (l + 1) 2, first.2, second.2, clearJoin,
      third.1 c le_rfl]
  have position : cellStart.inputPos.val = p + min (counterValue w) r + 1 := by
    change afterLoop.inputPos.val = _
    rw [loopEq]
    rfl
  have read : cellStart.inputSymbol = x[p + min (counterValue w) r]? :=
    FinTM.inputSymbol_at cellStart _
      (by have := Nat.min_le_right (counterValue w) r; omega) position
  have field := canonUnaryField (counterValue w) r rest stop
  rw [← parts] at field
  have verdict : (codeSkipFin (counterValue w + 1) (x.drop p)).isSome = bit := by
    rw [field]
    dsimp only [bit]
    rw [read]
    by_cases enough : r ≤ counterValue w
    · rw [if_pos enough, Nat.min_eq_right enough, last]
      rcases stop with rfl | ⟨ys, rfl⟩ <;> rfl
    · rw [if_neg enough, Nat.min_eq_left (by omega), hprefix _ (by omega)]
      rfl
  have tapes : afterClear.workTapes = Function.update d.workTapes 1 (FinTM.bufferTape []) := by
    rw [clearEq]
    funext j z
    fin_cases j
    · change clearStart.workTapes 0 z = d.workTapes 0 z
      change afterCell.workTapes 0 z = _
      rw [cellEq]
      change afterLoop.workTapes 0 z = _
      rw [loopEq]
      change Fin.lastCases (motive := fun _ : Fin 2 => ℤ → Option Bool)
        (FinTM.bufferTape v) body.workTapes (0 : Fin 1).castSucc z = _
      rw [Fin.lastCases_castSucc]
      rfl
    · simp only [FinTM.bufferTape_nil]
      change (if (1 : Fin 2) = 1 ∧ clearStart.workTapePos 1 ≤ z ∧
        z < clearStart.workTapePos 1 + (v.length : ℤ) then none
        else clearStart.workTapes 1 z) = none
      rw [clearWord.1, clearWord.2]
      simp only [true_and, zero_add]
      split_ifs with inside
      · rfl
      · by_cases nonneg : 0 ≤ z
        · simp [FinTM.bufferTape, nonneg,
            List.getElem?_eq_none (show v.length ≤ z.toNat by omega)]
        · simp [FinTM.bufferTape, nonneg]
  have heads : afterClear.workTapePos = d.workTapePos := by
    rw [clearEq]
    change afterCell.workTapePos = _
    rw [cellEq]
    change afterLoop.workTapePos = _
    rw [loopEq]
    funext j
    fin_cases j
    · change Fin.lastCases (motive := fun _ : Fin 2 => ℤ)
        0 body.workTapePos (0 : Fin 1).castSucc = _
      rw [Fin.lastCases_castSucc]
      rfl
    · change Fin.lastCases (motive := fun _ : Fin 2 => ℤ) 0 body.workTapePos (Fin.last 1) = _
      rw [Fin.lastCases_last]
      exact home.symm
  have output : afterClear.output = d.output := by
    rw [clearEq]
    change afterCell.output = _
    rw [cellEq]
    change afterLoop.output = _
    rw [loopEq]
    rfl
  refine ⟨duration, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [duration, c]
    rw [width]
    omega
  · rw [whole]
    change Option.map (fun s : SweepPhase =>
      (⟨some (some bit), s⟩ : Sigma canonUnaryPhase)) afterClear.state = _
    rw [stateC]
    change some (⟨some (some bit), SweepPhase.done⟩ : Sigma canonUnaryPhase) =
      some ⟨some (some (codeSkipFin (counterValue w + 1) (x.drop p)).isSome), .done⟩
    rw [verdict]
  · rw [whole]
    exact output
  · intro u hu b
    by_cases early : u ≤ l
    · rw [first.1 u early]
      intro eq
      obtain ⟨s, _, bad⟩ := Option.map_eq_some_iff.mp eq
      have impossible := congrArg Sigma.fst bad
      cases impossible
    · have index : u = l + 1 + (u - (l + 1)) := by omega
      rw [index, MultiTapeTM.runFrom_add, first.2]
      by_cases middle : u - (l + 1) ≤ 1
      · rw [second.1 _ middle]
        intro eq
        obtain ⟨s, _, bad⟩ := Option.map_eq_some_iff.mp eq
        have impossible := congrArg Sigma.fst bad
        cases impossible
      · have tailIndex : u - (l + 1) = 2 + (u - (l + 1) - 2) := by omega
        rw [tailIndex, MultiTapeTM.runFrom_add, second.2, clearJoin,
          third.1 _ (by dsimp [duration] at hu; omega)]
        intro eq
        obtain ⟨s, state, tag⟩ := Option.map_eq_some_iff.mp eq
        have equalBits : bit = b := by
          have e := congrArg Sigma.fst tag
          exact Option.some.inj (Option.some.inj e)
        subst b
        have same : s = .done := eq_of_heq (Sigma.mk.inj_iff.mp tag).2
        exact clearing.2.1 _ (by dsimp [duration, c] at *; omega)
          (state.trans (congrArg some same))
  · rw [whole]
    exact tapes
  · rw [whole]
    exact heads
  · intro ys accepted
    change codeSkipFin (counterValue w + 1) (x.drop p) = some ys at accepted
    rw [field] at accepted
    have enough : r ≤ counterValue w := by
      by_contra small
      simp [small] at accepted
    rw [if_pos enough] at accepted
    rcases stop with rfl | ⟨tail, rfl⟩
    · cases accepted
    · have same : tail = ys := Option.some.inj accepted
      subst ys
      have value : cellStart.inputSymbol = some false := by
        rw [read, Nat.min_eq_right enough, last]
        rfl
      rw [whole, clearEq]
      change afterCell.inputPos.val = _
      rw [cellEq]
      simp only [value, if_true]
      have beforeEnd : cellStart.inputPos.val ≠ x.length + 1 := by
        intro eq
        simp only [List.length_cons, Nat.min_eq_right enough] at size position
        omega
      change (moveInputPos cellStart.inputPos SignType.pos).val = _
      rw [moveInputPos_pos_of_ne_right _ beforeEnd]
      change cellStart.inputPos.val + 1 = x.length + 1 - tail.length
      simp only [List.length_cons, Nat.min_eq_right enough] at size position
      omega

/-- The bounded unary reader uses two tapes: the preserved bound and one restored scratch
counter. It consumes the field on acceptance and preserves every work tape and head.

**Proof sketch.** Copy the bound by the framed catalog row, then dispatch through the
public seam to the unary core. That core tests its stopping cell and clears its residual
counter. The untouched bound and blank scratch give exact restoration, and the
copy, seam, and core ledgers fit one linear bound. -/
private lemma exists_canonUnaryTM :
    ∃ (m : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (U : MultiTapeTM m Bool S)
      (entry : S) (exit : Bool → S) (bound : Fin m) (a : ℕ), Function.Injective exit ∧
      ∀ (x w : List Bool) (d : Cfg m Bool S x), d.state = some entry →
        1 ≤ d.inputPos.val →
        d.workTapes bound = FinTM.bufferTape w → d.workTapePos bound = 0 →
        (∀ j, j ≠ bound → d.workTapes j = FinTM.bufferTape [] ∧ d.workTapePos j = 0) →
        ∃ t ≤ a * (x.length + w.length + 1),
          (U.runFrom d t).state =
            some (exit (codeSkipFin (counterValue w + 1) (x.drop (d.inputPos.val - 1))).isSome) ∧
          (U.runFrom d t).output = d.output ∧
          (∀ u < t, ∀ v, (U.runFrom d u).state ≠ some (exit v)) ∧
          (U.runFrom d t).workTapes = d.workTapes ∧
          (U.runFrom d t).workTapePos = d.workTapePos ∧
          ∀ ys, codeSkipFin (counterValue w + 1) (x.drop (d.inputPos.val - 1)) = some ys →
            (U.runFrom d t).inputPos.val = x.length + 1 - ys.length := by
  letI : ∀ p, Fintype (canonUnaryPhase p) := fun p => by
    cases p with
    | none => exact inferInstance
    | some b => cases b <;> exact inferInstance
  letI : ∀ p, DecidableEq (canonUnaryPhase p) := fun p => by
    cases p with
    | none => exact inferInstance
    | some b => cases b <;> exact inferInstance
  let C := copyTM (Symbol := Bool) 2 0 1
  let U := seamCompTM C .done canonUnaryCore ⟨none, .dec .run⟩
  let exit (b : Bool) : SweepPhase ⊕ Sigma canonUnaryPhase := Sum.inr ⟨some (some b), .done⟩
  refine ⟨2, _, inferInstance, inferInstance, U, Sum.inl .sweep, exit, 0, 16, ?_, ?_⟩
  · intro a b eq
    have tagged := congrArg Sigma.fst (Sum.inr.inj eq)
    exact Option.some.inj (Option.some.inj tagged)
  · intro x w d state positive bound home blank
    let cp : Cfg 2 Bool SweepPhase x :=
      ⟨some .sweep, d.inputPos, d.workTapes, d.workTapePos, d.output⟩
    have start : cp.mapState Sum.inl = d := by
      exact Cfg.ext state.symm rfl rfl rfl rfl
    have scratch := blank 1 (by decide)
    have copied := copyTM_run_ofCfg (0 : Fin 2) 1 (by decide) w cp rfl
      (by intro z _ _; change d.workTapes 0 (d.workTapePos 0 + z) = _; rw [bound, home]; simp)
    let e := C.runFrom cp (2 * w.length + 2)
    have copyEq : e = _ := copied.1
    have atExit : e.state = some .done := by rw [copyEq]
    let next := e.mapState (fun _ => (⟨none, .dec .run⟩ : Sigma canonUnaryPhase))
    have counter : next.workTapes 1 = FinTM.bufferTape w := by
      change e.workTapes 1 = _
      rw [copyEq]
      funext z
      change (if (1 : Fin 2) = 1 ∧ d.workTapePos 1 ≤ z ∧
        z < d.workTapePos 1 + (w.length : ℤ) then FinTM.bufferTape w (z - d.workTapePos 1)
        else d.workTapes 1 z) = FinTM.bufferTape w z
      rw [scratch.1, scratch.2]
      simp only [true_and, zero_add, sub_zero, FinTM.bufferTape_nil]
      split_ifs with inside
      · rfl
      · by_cases nonneg : 0 ≤ z
        · simp [FinTM.bufferTape, nonneg,
            List.getElem?_eq_none (show w.length ≤ z.toNat by omega)]
        · simp [FinTM.bufferTape, nonneg]
    have nextPos : next.inputPos = d.inputPos := by change e.inputPos = _; rw [copyEq]
    have nextHeads : next.workTapePos = d.workTapePos := by
      change e.workTapePos = _
      rw [copyEq]
    have nextOutput : next.output = d.output := by change e.output = _; rw [copyEq]
    obtain ⟨t, budget, finish, silent, cuts, tapes, heads, suffix⟩ :=
      canonUnaryCore_run w next (by simp [next, Cfg.mapState, atExit])
        (by rw [nextPos]; exact positive) counter (by rw [nextHeads]; exact scratch.2)
    have whole := seamCompTM_run_ofCfg C .done canonUnaryCore ⟨none, .dec .run⟩
      (rfl : C.runFrom cp (2 * w.length + 2) = e) atExit copied.2.1
      (rfl : canonUnaryCore.runFrom next t = _)
    rw [start] at whole
    refine ⟨2 * w.length + 2 + 1 + t, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [whole]
      change Option.map Sum.inr (canonUnaryCore.runFrom next t).state = _
      rw [finish, nextPos]
      rfl
    · rw [whole]
      exact silent.trans nextOutput
    · intro u hu b
      change ((seamCompTM C .done canonUnaryCore ⟨none, .dec .run⟩).runFrom d u).state ≠ _
      rw [← start]
      apply canonSeam_avoids C .done canonUnaryCore ⟨none, .dec .run⟩ (exit b)
        (rfl : C.runFrom cp (2 * w.length + 2) = e) atExit copied.2.1 (v := t)
        (by intro z _; simp [exit, Cfg.mapState])
        (by intro z hz; simpa [exit, Cfg.mapState] using cuts z hz b) u hu
    · rw [whole]
      change (canonUnaryCore.runFrom next t).workTapes = _
      rw [tapes]
      funext j z
      fin_cases j
      · change next.workTapes 0 z = _
        change e.workTapes 0 z = _
        rw [copyEq]
        rfl
      · simpa only [Function.update_self] using congrFun scratch.1.symm z
    · rw [whole]
      exact heads.trans nextHeads
    · intro ys skipped
      rw [whole]
      exact suffix ys (by simpa only [nextPos] using skipped)

/-- A finite list of two-cell validators, in native reading order. -/
private def canonPairs : List (Bool → Bool → Bool) → List Bool → Option (List Bool)
  | [], xs => some xs
  | v :: vs, xs => (codeSkipPair v xs).bind (canonPairs vs)

/-- The native fixed-field leaf remembers the first cell of a pair and its finite pair
index. It rejects a blank immediately and validates each pair before proceeding.
The catalog's input folds require a whole-input traversal from position one; this local
fixed-width validator is the missing leaf. -/
private def canonPairsTM (m : ℕ) (vs : List (Bool → Bool → Bool)) :
    MultiTapeTM m Bool (Bool ⊕ (Fin (vs.length + 1) × Option Bool)) where
  q₀ := Sum.inr (0, none)
  tr := fun q inp _ => match q with
    | Sum.inl b => inputMoveAction 0 (Sum.inl b)
    | Sum.inr (j, a) =>
      if h : j.val < vs.length then
        match a, inp with
        | none, some b => inputMoveAction 1 (Sum.inr (j, some b))
        | some a, some b =>
          if vs[j.val] a b then
            inputMoveAction 1 (Sum.inr (⟨j.val + 1, by omega⟩, none))
          else inputMoveAction 0 (Sum.inl false)
        | _, none => inputMoveAction 0 (Sum.inl false)
      else inputMoveAction 0 (Sum.inl true)

/-- Native reads are lookups at the head of the current suffix. Advancing over a present
cell leaves precisely its tail. This is a use of the public input lookup and move laws. -/
private lemma canonNativeSuffix {m : ℕ} {S : Type} {x : List Bool}
    (d : Cfg m Bool S x) (p : ℕ) (pos : d.inputPos.val = p + 1)
    (range : p ≤ x.length) :
    d.inputSymbol = (x.drop p).head? ∧
      ∀ b ys, x.drop p = b :: ys →
        (moveInputPos d.inputPos 1).val = p + 2 ∧ x.drop (p + 1) = ys := by
  refine ⟨?_, ?_⟩
  · rw [FinTM.inputSymbol_at d p range pos, List.head?_drop]
  · intro b ys split
    have size := congrArg List.length split
    simp only [List.length_drop, List.length_cons] at size
    have beforeEnd : d.inputPos.val ≠ x.length + 1 := by omega
    constructor
    · change (moveInputPos d.inputPos SignType.pos).val = _
      rw [moveInputPos_pos_of_ne_right d.inputPos beforeEnd]
      simp only [pos]
    · have tail := congrArg (List.drop 1) split
      simpa only [List.drop_drop, Nat.add_comm 1 p, List.drop_succ_cons, List.drop_zero] using tail

/-- A native fixed-field scan is linear in the finite list of pair tests. The head never
returns to the left blank, and every work tape and head is unchanged.

**Proof sketch.** Induct on the number of remaining pairs. A missing first or second
cell rejects immediately. A failed predicate rejects after two tests; a successful pair
advances two cells and invokes the induction hypothesis at the next finite index.
Only the permitted native leaf is traced; there is no private phase or loop host. -/
private lemma canonPairs_run {m : ℕ} {x : List Bool} (vs : List (Bool → Bool → Bool))
    (j : Fin (vs.length + 1))
    (d : Cfg m Bool (Bool ⊕ (Fin (vs.length + 1) × Option Bool)) x)
    (p : ℕ) (pos : d.inputPos.val = p + 1) (range : p ≤ x.length)
    (state : d.state = some (Sum.inr (j, none))) :
    ∃ t ≤ 2 * (vs.length - j.val) + 1,
      ((canonPairsTM m vs).runFrom d t).state =
        some (Sum.inl (canonPairs (vs.drop j.val) (x.drop p)).isSome) ∧
      ((canonPairsTM m vs).runFrom d t).output = d.output ∧
      (∀ u < t, ∀ b, ((canonPairsTM m vs).runFrom d u).state ≠ some (Sum.inl b)) ∧
      ((canonPairsTM m vs).runFrom d t).workTapes = d.workTapes ∧
      ((canonPairsTM m vs).runFrom d t).workTapePos = d.workTapePos ∧
      1 ≤ ((canonPairsTM m vs).runFrom d t).inputPos.val ∧
      ∀ ys, canonPairs (vs.drop j.val) (x.drop p) = some ys →
        ((canonPairsTM m vs).runFrom d t).inputPos.val = x.length + 1 - ys.length := by
  generalize hn : vs.length - j.val = n
  induction n using Nat.strong_induction_on generalizing j d p with
  | h n ih =>
    let M := canonPairsTM m vs
    have native := canonNativeSuffix d p pos range
    have firstCut (b : Bool) : (M.runFrom d 0).state ≠ some (Sum.inl b) := by
      simpa only [MultiTapeTM.runFrom_zero, state] using
        (by simp : some (Sum.inr (j, none)) ≠
          (some (Sum.inl b) : Option (Bool ⊕ (Fin (vs.length + 1) × Option Bool))))
    by_cases more : j.val < vs.length
    · have parse : canonPairs (vs.drop j.val) (x.drop p) =
          (codeSkipPair vs[j.val] (x.drop p)).bind (canonPairs (vs.drop (j.val + 1))) := by
        rw [List.drop_eq_getElem_cons more]
        rfl
      cases suffix : x.drop p with
      | nil =>
        rw [← suffix]
        have read : d.inputSymbol = none := by rw [native.1, suffix]; rfl
        have step := step_of_inputMoveAction M d (q' := Sum.inl false) 0 state
          (by simp [M, canonPairsTM, more, read])
        have run : M.runFrom d 1 = { d with state := some (Sum.inl false) } := by
          simpa only [moveInputPos_zero] using step
        have verdict : canonPairs (vs.drop j.val) (x.drop p) = none := by
          rw [parse, suffix]
          rfl
        refine ⟨1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [run, verdict]; rfl
        · rw [run]
        · intro u hu b
          have zero : u = 0 := by omega
          subst u
          exact firstCut b
        · rw [run]
        · rw [run]
        · rw [run]; change 1 ≤ d.inputPos.val; omega
        · intro ys accepted; rw [verdict] at accepted; cases accepted
      | cons a tail =>
        rw [← suffix]
        have read : d.inputSymbol = some a := by rw [native.1, suffix]; rfl
        have advance := native.2 a tail suffix
        let d1 : Cfg m Bool (Bool ⊕ (Fin (vs.length + 1) × Option Bool)) x :=
          { d with
            state := some (Sum.inr (j, some a))
            inputPos := moveInputPos d.inputPos 1 }
        have run1 : M.runFrom d 1 = d1 :=
          step_of_inputMoveAction M d _ state
            (by simp [M, canonPairsTM, more, read])
        have pos1 : d1.inputPos.val = (p + 1) + 1 := by
          exact advance.1
        have range1 : p + 1 ≤ x.length := by have := d1.inputPos.isLt; omega
        have native1 := canonNativeSuffix d1 (p + 1) pos1 range1
        have d1state : d1.state = some (Sum.inr (j, some a)) := rfl
        have cut1 (b : Bool) : (M.runFrom d 1).state ≠ some (Sum.inl b) := by
          rw [run1, d1state]
          simp
        have fail (invalid : codeSkipPair vs[j.val] (x.drop p) = none)
            (tr : M.tr (Sum.inr (j, some a)) d1.inputSymbol d1.workTapeSymbols =
              inputMoveAction 0 (Sum.inl false)) :
            ∃ t ≤ 2 * n + 1,
              (M.runFrom d t).state =
                some (Sum.inl (canonPairs (vs.drop j.val) (x.drop p)).isSome) ∧
              (M.runFrom d t).output = d.output ∧
              (∀ u < t, ∀ b, (M.runFrom d u).state ≠ some (Sum.inl b)) ∧
              (M.runFrom d t).workTapes = d.workTapes ∧
              (M.runFrom d t).workTapePos = d.workTapePos ∧
              1 ≤ (M.runFrom d t).inputPos.val ∧
              ∀ ys, canonPairs (vs.drop j.val) (x.drop p) = some ys →
                (M.runFrom d t).inputPos.val = x.length + 1 - ys.length := by
          have step := step_of_inputMoveAction M d1 _ d1state tr
          have run2 : M.runFrom d 2 = { d1 with state := some (Sum.inl false) } := by
            rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_add (tm := M) d 1 1, run1]
            simpa only [moveInputPos_zero] using step
          have verdict : canonPairs (vs.drop j.val) (x.drop p) = none := by
            rw [parse, invalid]
            rfl
          refine ⟨2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [run2, verdict]; rfl
          · rw [run2]
          · intro u hu b
            have choices : u = 0 ∨ u = 1 := by omega
            rcases choices with rfl | rfl
            · exact firstCut b
            · exact cut1 b
          · rw [run2]
          · rw [run2]
          · rw [run2]; change 1 ≤ d1.inputPos.val; omega
          · intro ys accepted; rw [verdict] at accepted; cases accepted
        cases tail with
        | nil =>
          apply fail (by rw [suffix]; rfl)
          have read1 : d1.inputSymbol = none := by rw [native1.1, advance.2]; rfl
          simp [M, canonPairsTM, more, read1]
        | cons b ys =>
          have read1 : d1.inputSymbol = some b := by rw [native1.1, advance.2]; rfl
          by_cases valid : vs[j.val] a b = true
          · let j' : Fin (vs.length + 1) := ⟨j.val + 1, by omega⟩
            let d2 : Cfg m Bool (Bool ⊕ (Fin (vs.length + 1) × Option Bool)) x :=
              { d1 with
                state := some (Sum.inr (j', none))
                inputPos := moveInputPos d1.inputPos 1 }
            have run2 : M.runFrom d 2 = d2 := by
              rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_add (tm := M) d 1 1, run1]
              exact step_of_inputMoveAction M d1 _ d1state
                (by simp [M, canonPairsTM, more, read1, valid, j'])
            have advance1 := native1.2 b ys advance.2
            have pos2 : d2.inputPos.val = (p + 2) + 1 := advance1.1
            have range2 : p + 2 ≤ x.length := by have := d2.inputPos.isLt; omega
            have parser : canonPairs (vs.drop j.val) (x.drop p) =
                canonPairs (vs.drop j'.val) (x.drop (p + 2)) := by
              rw [parse, suffix]
              simp only [codeSkipPair, valid, if_true, Option.bind_some]
              exact congrArg (canonPairs (vs.drop j'.val)) advance1.2.symm
            obtain ⟨t, budget, finish, silent, cuts, tapes, heads, positive, consumed⟩ :=
              ih (vs.length - j'.val) (by dsimp [j']; omega) j' d2 (p + 2)
                pos2 range2 rfl rfl
            have whole : M.runFrom d (2 + t) = M.runFrom d2 t := by
              rw [MultiTapeTM.runFrom_add (tm := M), run2]
            refine ⟨2 + t, by dsimp [j'] at budget; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [whole, parser]; exact finish
            · rw [whole]; exact silent
            · intro u hu bit
              by_cases early : u < 2
              · have choices : u = 0 ∨ u = 1 := by omega
                rcases choices with rfl | rfl
                · exact firstCut bit
                · exact cut1 bit
              · have index : u = 2 + (u - 2) := by omega
                rw [index, MultiTapeTM.runFrom_add (tm := M), run2]
                exact cuts _ (by omega) bit
            · rw [whole]; exact tapes
            · rw [whole]; exact heads
            · rw [whole]; exact positive
            · intro zs accepted
              rw [whole]
              exact consumed zs (parser.symm.trans accepted)
          · apply fail (by simp [suffix, codeSkipPair, valid])
            simp [M, canonPairsTM, more, read1, valid]
    · have done : vs.drop j.val = [] := List.drop_eq_nil_of_le (by omega)
      have step := step_of_inputMoveAction M d (q' := Sum.inl true) 0 state
        (by simp [M, canonPairsTM, more])
      have run : M.runFrom d 1 = { d with state := some (Sum.inl true) } := by
        simpa only [moveInputPos_zero] using step
      refine ⟨1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run, done]; rfl
      · rw [run]
      · intro u hu b
        have zero : u = 0 := by omega
        subst u
        exact firstCut b
      · rw [run]
      · rw [run]
      · rw [run]; change 1 ≤ d.inputPos.val; omega
      · intro ys accepted
        have same : x.drop p = ys := Option.some.inj (by simpa [done, canonPairs] using accepted)
        have lengths := congrArg List.length same
        simp only [List.length_drop] at lengths
        rw [run]
        change d.inputPos.val = _
        omega

/-- Work-tape write/move pairs followed by the output pair. Every write pair is valid;
move and output pairs exclude precisely `false, true`. -/
private def canonWorkPairs : ℕ → List (Bool → Bool → Bool)
  | 0 => [fun a b => a || !b]
  | k + 1 => (fun _ _ => true) :: (fun a b => a || !b) :: canonWorkPairs k

/-- The finite pair list has exactly the grammar's fixed-field semantics.

**Proof sketch.** Induct on the number of work-tape pairs, using `codeSkipWork` for
each write/move pair and associativity of `Option.bind` for the output and input fields. -/
private lemma canonPairs_fields (k : ℕ) (xs : List Bool) :
    canonPairs ((fun a b => a || !b) :: canonWorkPairs k) xs = canonSkipFields k xs := by
  have work (j : ℕ) (ys : List Bool) : canonPairs (canonWorkPairs j) ys =
      (codeSkipRepeat codeSkipWork j ys).bind (codeSkipPair (fun a b => a || !b)) := by
    induction j generalizing ys with
    | zero => simp [canonWorkPairs, canonPairs, codeSkipRepeat]
    | succ j ih =>
      simp only [canonWorkPairs, canonPairs, ih, codeSkipRepeat, codeSkipWork, Option.bind_assoc]
  simp only [canonPairs, work, canonSkipFields, Option.bind_assoc]

/-- There are `2k + 2` fixed pairs in one action record. -/
private lemma canonWorkPairs_length (k : ℕ) : (canonWorkPairs k).length = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [canonWorkPairs, List.length_cons, ih]; omega

/-- One native tag test records blank, false, or true and advances exactly for a present
cell. It supplies the local successor tag check, absent from the whole-input catalog. -/
private def canonTagTM (m : ℕ) : MultiTapeTM m Bool (Option (Option Bool)) where
  q₀ := none
  tr := fun _ inp _ => inputMoveAction (if inp.isSome then 1 else 0) (some inp)

/-- The tag leaf's single step follows the public input-only action contract. -/
private lemma canonTag_step {m : ℕ} {x : List Bool}
    (d : Cfg m Bool (Option (Option Bool)) x) (hs : d.state = some none) :
    (canonTagTM m).runFrom d 1 =
      { d with
        state := some (some d.inputSymbol)
        inputPos := moveInputPos d.inputPos (if d.inputSymbol.isSome then 1 else 0) } :=
  step_of_inputMoveAction _ _ _ hs rfl

/-- The record's native finite pair list. -/
private abbrev canonRecordPairs (k : ℕ) : List (Bool → Bool → Bool) :=
  (fun a b => a || !b) :: canonWorkPairs k

/-- Fixed pairs, the successor tag, and the bounded unary component are the three
phases. The two final ports are in the tag phase. -/
private abbrev canonRecordPhase (k : ℕ) (S : Type) : Option Bool → Type
  | none => Bool ⊕ (Fin ((canonRecordPairs k).length + 1) × Option Bool)
  | some false => Option (Option Bool)
  | some true => S

/-- Each record phase is an existing component or one permitted native leaf. -/
private def canonRecordFamily {m : ℕ} {S : Type} (k : ℕ) (U : MultiTapeTM m Bool S)
    (p : Option Bool) : MultiTapeTM m Bool (canonRecordPhase k S p) := match p with
  | none => canonPairsTM m (canonRecordPairs k)
  | some false => canonTagTM m
  | some true => U

/-- The public phase host dispatches failures to the false port, a false successor tag
to the true port, and a true successor tag to the bounded unary reader. -/
private def canonRecordNext {S : Type} [DecidableEq S] (k : ℕ) (entry : S) (exit : Bool → S) :
    (p : Option Bool) → canonRecordPhase k S p → Option (Sigma (canonRecordPhase k S))
  | none, Sum.inl true => some ⟨some false, none⟩
  | none, Sum.inl false => some ⟨some false, some none⟩
  | none, Sum.inr _ => none
  | some false, none => none
  | some false, some none => some ⟨some false, some none⟩
  | some false, some (some false) => some ⟨some false, some (some false)⟩
  | some false, some (some true) => some ⟨some true, entry⟩
  | some true, q =>
    if q = exit true then some ⟨some false, some (some false)⟩
    else if q = exit false then some ⟨some false, some none⟩ else none

/-- The generic action-record validator preserves its binary bound and scratch bank.
It decides the fixed fields and successor field with strict Boolean exits and a linear
bound in the input length and binary width.

**Proof sketch.** The native pair leaf decides the prescribed fixed fields. A public
phase host then reads the successor tag: blank rejects, false accepts, and true dispatches
to the proved bounded unary reader on the same bank. The reader's framed contract restores
the bank. The fixed finite cost plus its linear ledger gives one linear bound. -/
private lemma exists_canonRecordTM (k : ℕ) :
    ∃ (m : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM m Bool S)
      (entry : S) (exit : Bool → S) (bound : Fin m) (a : ℕ), Function.Injective exit ∧
      ∀ (x w : List Bool) (d : Cfg m Bool S x), d.state = some entry →
        1 ≤ d.inputPos.val →
        d.workTapes bound = FinTM.bufferTape w → d.workTapePos bound = 0 →
        (∀ j, j ≠ bound → d.workTapes j = FinTM.bufferTape [] ∧ d.workTapePos j = 0) →
        ∃ t ≤ a * (x.length + w.length + 1),
          (R.runFrom d t).state =
            some (exit (codeSkipActionK k (counterValue w) (x.drop (d.inputPos.val - 1))).isSome) ∧
          (R.runFrom d t).output = d.output ∧
          (∀ u < t, ∀ v, (R.runFrom d u).state ≠ some (exit v)) ∧
          (R.runFrom d t).workTapes = d.workTapes ∧
          (R.runFrom d t).workTapePos = d.workTapePos ∧
          ∀ ys, codeSkipActionK k (counterValue w) (x.drop (d.inputPos.val - 1)) = some ys →
            (R.runFrom d t).inputPos.val = x.length + 1 - ys.length := by
  obtain ⟨m, S, fS, dS, U, ue, ux, bound, a, injective, unary⟩ := exists_canonUnaryTM
  letI : Fintype S := fS
  letI : DecidableEq S := dS
  letI : ∀ p, Fintype (canonRecordPhase k S p) := fun p => by
    cases p with
    | none => exact inferInstance
    | some b => cases b <;> exact inferInstance
  letI : ∀ p, DecidableEq (canonRecordPhase k S p) := fun p => by
    cases p with
    | none => exact inferInstance
    | some b => cases b <;> exact inferInstance
  let family := canonRecordFamily k U
  let red := canonRecordNext k ue ux
  let entry : Sigma (canonRecordPhase k S) := ⟨none, Sum.inr (0, none)⟩
  let R := phaseHostTM family entry red
  let exit (b : Bool) : Sigma (canonRecordPhase k S) :=
    ⟨some false, some (if b then some false else none)⟩
  refine ⟨m, _, inferInstance, inferInstance, R, entry, exit, bound, a + 4 * k + 9, ?_, ?_⟩
  · intro b c eq
    cases b <;> cases c <;> simp_all [exit]
  · intro x w d state positive word origin blank
    let p := d.inputPos.val - 1
    have pos : d.inputPos.val = p + 1 := by dsimp [p]; omega
    have range : p ≤ x.length := by have := d.inputPos.isLt; omega
    let f : Cfg m Bool (canonRecordPhase k S none) x :=
      d.mapState (fun _ => Sum.inr (0, none))
    have fState : f.state = some (Sum.inr (0, none)) := by simp [f, Cfg.mapState, state]
    obtain ⟨ft, fixedBudget, fixedExit, fixedOutput, fixedCuts, fixedTapes, fixedHeads,
      fixedPositive, fixedConsumed⟩ :=
      canonPairs_run (canonRecordPairs k) 0 f p pos range fState
    simp only [Fin.val_zero, Nat.sub_zero, canonRecordPairs, List.length_cons,
      canonWorkPairs_length] at fixedBudget
    simp only [Fin.val_zero, List.drop_zero, canonRecordPairs, canonPairs_fields]
      at fixedExit fixedConsumed
    let fEnd := (family none).runFrom f ft
    have fExit : fEnd.state = some (Sum.inl (canonSkipFields k (x.drop p)).isSome) := fixedExit
    have fOutput : fEnd.output = d.output := fixedOutput
    have fTapes : fEnd.workTapes = d.workTapes := fixedTapes
    have fHeads : fEnd.workTapePos = d.workTapePos := fixedHeads
    let target : Sigma (canonRecordPhase k S) :=
      if (canonSkipFields k (x.drop p)).isSome then ⟨some false, none⟩ else exit false
    have first := phaseHostTM_run family entry red none f fEnd ft rfl _ fExit target
      (by cases h : (canonSkipFields k (x.drop p)).isSome <;>
          simp [red, canonRecordNext, target, h, exit]) (by
        intro u hu s hs
        cases s with
        | inr pair => rfl
        | inl b => exact (fixedCuts u hu b hs).elim)
    have start : f.mapState (Sigma.mk none) = d := by
      apply Cfg.ext <;> simp [f, Cfg.mapState, state, entry]
    rw [start] at first
    have safeFirst (u : ℕ) (hu : u ≤ ft) (b : Bool) :
        (R.runFrom d u).state ≠ some (exit b) := by
      rw [first.1 u hu]
      intro eq
      obtain ⟨s, _, tagged⟩ := Option.map_eq_some_iff.mp eq
      have impossible := congrArg Sigma.fst tagged
      cases impossible
    cases fields : canonSkipFields k (x.drop p) with
    | none =>
      have record : codeSkipActionK k (counterValue w) (x.drop p) = none := by
        rw [canonSkipAction_eq, fields]
        rfl
      have run : R.runFrom d (ft + 1) = fEnd.mapState (fun _ => exit false) := by
        simpa only [target, fields, Option.isSome_none, Bool.false_eq_true, if_false] using first.2
      refine ⟨ft + 1, by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run]
        change Option.map (fun _ => exit false) fEnd.state = _
        rw [fExit]
        change some (exit false) =
          some (exit (codeSkipActionK k (counterValue w) (x.drop p)).isSome)
        rw [record]
        rfl
      · rw [run]; exact fOutput
      · intro u hu b; exact safeFirst u (by omega) b
      · rw [run]; exact fTapes
      · rw [run]; exact fHeads
      · intro ys accepted
        change codeSkipActionK k (counterValue w) (x.drop p) = some ys at accepted
        rw [record] at accepted
        cases accepted
    | some ys =>
      have record : codeSkipActionK k (counterValue w) (x.drop p) =
          codeSkipState (counterValue w + 1) ys := by
        rw [canonSkipAction_eq, fields]
        rfl
      obtain ⟨pre, split, width⟩ := canonSkipFields_cells k (x.drop p) ys fields
      have size : x.length = p + pre.length + ys.length := by
        have lengths := congrArg List.length split
        simp only [List.length_drop, List.length_append] at lengths
        omega
      have tail : x.drop (p + pre.length) = ys := by
        have e := congrArg (List.drop pre.length) split
        simpa only [List.drop_drop, List.drop_left] using e
      let tagStart : Cfg m Bool (Option (Option Bool)) x := fEnd.mapState (fun _ => none)
      have tagState : tagStart.state = some none := by simp [tagStart, Cfg.mapState, fExit]
      have tagPos : tagStart.inputPos.val = p + pre.length + 1 := by
        have h := fixedConsumed ys fields
        change fEnd.inputPos.val = _ at h ⊢
        omega
      have native := canonNativeSuffix tagStart (p + pre.length) tagPos (by omega)
      have tagRead : tagStart.inputSymbol = ys.head? := by rw [native.1, tail]
      let tagEnd := (canonTagTM m).runFrom tagStart 1
      have tagEq : tagEnd = _ := canonTag_step tagStart tagState
      have tagExit : tagEnd.state = some (some ys.head?) := by rw [tagEq, tagRead]
      let tagNext : Sigma (canonRecordPhase k S) := match ys.head? with
        | some true => ⟨some true, ue⟩
        | some false => exit true
        | none => exit false
      have second := phaseHostTM_run family entry red (some false) tagStart tagEnd 1 rfl
        (some ys.head?) tagExit tagNext (by
          cases h : ys.head? with
          | none => simp [red, canonRecordNext, tagNext, h, exit]
          | some b => cases b <;> simp [red, canonRecordNext, tagNext, h, exit]) (by
          intro u hu s hs
          have zero : u = 0 := by omega
          subst u
          have eq : s = none := (Option.some.inj (tagState.symm.trans hs)).symm
          subst s
          rfl)
      have join : fEnd.mapState (fun _ => target) =
          tagStart.mapState (Sigma.mk (some false)) := by
        simp [tagStart, target, fields, Cfg.mapState, Option.map_map, Function.comp_def]
      have firstRun : R.runFrom d (ft + 1) = tagStart.mapState (Sigma.mk (some false)) := by
        rw [first.2, join]
      have tagRun : R.runFrom d (ft + 2) = tagEnd.mapState (Sigma.mk (some false)) := by
        rw [show ft + 2 = ft + 1 + 1 by omega,
          MultiTapeTM.runFrom_add d (ft + 1) 1, firstRun, second.1 1 le_rfl]
      have tagDispatch : R.runFrom d (ft + 3) = tagEnd.mapState (fun _ => tagNext) := by
        rw [show ft + 3 = ft + 1 + (1 + 1) by omega,
          MultiTapeTM.runFrom_add d (ft + 1) (1 + 1), firstRun, second.2]
      have tagOutput : tagEnd.output = d.output := by rw [tagEq]; exact fOutput
      have tagTapes : tagEnd.workTapes = d.workTapes := by rw [tagEq]; exact fTapes
      have tagHeads : tagEnd.workTapePos = d.workTapePos := by rw [tagEq]; exact fHeads
      have safeTag (u : ℕ) (hu : u ≤ ft + 1) (b : Bool) :
          (R.runFrom d u).state ≠ some (exit b) := by
        by_cases early : u ≤ ft
        · exact safeFirst u early b
        · have eq : u = ft + 1 := by omega
          rw [eq, firstRun]
          simp [Cfg.mapState, tagState, exit]
      cases ys with
      | nil =>
        refine ⟨ft + 2, by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [tagRun]
          change Option.map (fun s : Option (Option Bool) =>
            (⟨some false, s⟩ : Sigma (canonRecordPhase k S))) tagEnd.state = _
          rw [tagExit]
          change some (exit false) =
            some (exit (codeSkipActionK k (counterValue w) (x.drop p)).isSome)
          rw [record]
          rfl
        · rw [tagRun]; exact tagOutput
        · intro u hu b; exact safeTag u (by omega) b
        · rw [tagRun]; exact tagTapes
        · rw [tagRun]; exact tagHeads
        · intro zs accepted
          change codeSkipActionK k (counterValue w) (x.drop p) = some zs at accepted
          rw [record] at accepted
          cases accepted
      | cons b ys =>
        cases b with
        | false =>
          refine ⟨ft + 2, by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [tagRun]
            change Option.map (fun s : Option (Option Bool) =>
              (⟨some false, s⟩ : Sigma (canonRecordPhase k S))) tagEnd.state = _
            rw [tagExit]
            change some (exit true) =
              some (exit (codeSkipActionK k (counterValue w) (x.drop p)).isSome)
            rw [record]
            rfl
          · rw [tagRun]; exact tagOutput
          · intro u hu bit; exact safeTag u (by omega) bit
          · rw [tagRun]; exact tagTapes
          · rw [tagRun]; exact tagHeads
          · intro zs accepted
            change codeSkipActionK k (counterValue w) (x.drop p) = some zs at accepted
            rw [record] at accepted
            have same : ys = zs := Option.some.inj accepted
            subst zs
            rw [tagRun, tagEq]
            change (moveInputPos tagStart.inputPos
              (if tagStart.inputSymbol.isSome then 1 else 0)).val = _
            rw [tagRead]
            have advance := (native.2 false ys tail).1
            simp only [List.head?_cons, Option.isSome_some, if_true]
            simp only [List.length_cons] at size
            omega
        | true =>
          let uStart : Cfg m Bool S x := tagEnd.mapState (fun _ => ue)
          have uState : uStart.state = some ue := by simp [uStart, Cfg.mapState, tagExit]
          have advance := native.2 true ys tail
          have uPos : uStart.inputPos.val = p + pre.length + 2 := by
            change tagEnd.inputPos.val = _
            rw [tagEq, tagRead]
            exact advance.1
          have uTail : x.drop (uStart.inputPos.val - 1) = ys := by
            rw [uPos]
            simpa only [Nat.add_sub_cancel] using advance.2
          obtain ⟨ut, unaryBudget, uExit, uOutput, uCuts, uTapes, uHeads, uConsumed⟩ :=
            unary x w uStart uState (by omega)
              (by change tagEnd.workTapes bound = _; rw [tagTapes]; exact word)
              (by change tagEnd.workTapePos bound = _; rw [tagHeads]; exact origin)
              (by intro j hj; change tagEnd.workTapes j = _ ∧ tagEnd.workTapePos j = _
                  rw [tagTapes, tagHeads]; exact blank j hj)
          let uEnd := U.runFrom uStart ut
          let verdict := (codeSkipFin (counterValue w + 1) ys).isSome
          have uFinal : uEnd.state = some (ux verdict) := by simpa only [uTail] using uExit
          have third := phaseHostTM_run family entry red (some true) uStart uEnd ut rfl
            (ux verdict) uFinal (exit verdict) (by
              have different : ux false ≠ ux true := fun eq => Bool.false_ne_true (injective eq)
              cases verdict <;> simp [red, canonRecordNext, exit, different]) (by
              intro u hu s hs
              have noTrue : s ≠ ux true := fun eq => uCuts u hu true (hs.trans (congrArg some eq))
              have noFalse : s ≠ ux false := fun eq =>
                uCuts u hu false (hs.trans (congrArg some eq))
              simp [red, canonRecordNext, noTrue, noFalse])
          have uJoin : tagEnd.mapState (fun _ => tagNext) =
              uStart.mapState (Sigma.mk (some true)) := by
            simp [uStart, tagNext, Cfg.mapState, Option.map_map, Function.comp_def]
          have whole : R.runFrom d (ft + 3 + (ut + 1)) =
              uEnd.mapState (fun _ => exit verdict) := by
            rw [MultiTapeTM.runFrom_add d (ft + 3) (ut + 1), tagDispatch, uJoin, third.2]
          have semantics : (codeSkipActionK k (counterValue w) (x.drop p)).isSome = verdict := by
            rw [record]
            rfl
          refine ⟨ft + 3 + (ut + 1), by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [whole]
            change Option.map (fun _ => exit verdict) uEnd.state = _
            rw [uFinal]
            change some (exit verdict) =
              some (exit (codeSkipActionK k (counterValue w) (x.drop p)).isSome)
            rw [semantics]
          · rw [whole]
            exact uOutput.trans tagOutput
          · intro u hu b
            by_cases early : u ≤ ft + 1
            · exact safeTag u early b
            · by_cases onTag : u = ft + 2
              · rw [onTag, tagRun]
                simp [Cfg.mapState, tagExit, exit]
              · have index : u = ft + 3 + (u - (ft + 3)) := by omega
                rw [index, MultiTapeTM.runFrom_add d (ft + 3) (u - (ft + 3)), tagDispatch,
                  uJoin, third.1 _ (by omega)]
                intro eq
                obtain ⟨s, _, tagged⟩ := Option.map_eq_some_iff.mp eq
                have impossible := congrArg Sigma.fst tagged
                cases impossible
          · rw [whole]
            exact uTapes.trans tagTapes
          · rw [whole]
            exact uHeads.trans tagHeads
          · intro zs accepted
            rw [whole]
            apply uConsumed zs
            rw [uTail]
            change codeSkipActionK k (counterValue w) (x.drop p) = some zs at accepted
            rw [record] at accepted
            exact accepted

/-- **The physical grammar stage.** Started on one bank whose tape `header` holds the
canonical binary header `bits` (head at the origin), every other tape blank, the native head
at the remainder's first cell and the output empty, it decides the fixed grammar on the
remainder with two distinct live exits, silently, within a polynomial bound that does not
depend on the header's numerical value.

**Proof sketch.** Copy the header to scratch counters as needed (framed copy rows; its value
`n` serves as the binary bound of every unary range check). Check the unary initial state
below `n + 1`; run one public counter loop over the `n + 1` states, each of `3^(k+1)`
records, with the generic record validator as its body; check the all-`true` suffix to the
right input blank. Every record consumes at least `4k + 5` cells and every round fails fast
on input exhaustion, so at most `|x| + 1` rounds run, each charged `O(|x| + |bits|)`. -/
private lemma exists_canonGrammarStage (F : MachineFormat) :
    ∃ (m : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (G : MultiTapeTM m Bool S)
      (entry : S) (exit : Bool → S) (a : ℕ) (header : Fin m), Function.Injective exit ∧
      ∀ (x bits rest : List Bool), pairDecode x = some (bits, rest) →
        bits = (codeBitsNat bits).bits →
        canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length →
        ∀ d : Cfg m Bool S x, d.state = some entry → d.output = [] →
          d.inputPos.val = 2 * bits.length + 3 →
          d.workTapes header = FinTM.bufferTape bits → d.workTapePos header = 0 →
          (∀ j, j ≠ header → d.workTapes j = FinTM.bufferTape [] ∧ d.workTapePos j = 0) →
          ∃ t ≤ a * (x.length + 1) ^ a,
            (G.runFrom d t).state =
              some (exit (canonGrammar F.k (codeBitsNat bits) rest).isSome) ∧
            (G.runFrom d t).output = [] ∧
            ∀ u < t, ∀ v, (G.runFrom d u).state ≠ some (exit v) := by
  sorry

/-- **The physical validator.** One finite binary machine halts on every input within a
polynomial bound with a single verdict bit; a rejection decodes to the fallback, and an
acceptance is a successful format scan.

**Proof sketch.** Run the total parse front end `exists_canonParseFront`. Its reject port
emits `false` and halts. At its ready port tape `0` holds the canonical header `bits`, the
native head is at the remainder, and the positive guard has passed; run the physical grammar
on a fresh bank around tape `0`, deciding `(canonGrammar F.k n rest).isSome`, then emit the
bit and halt. `canonGrammar_verdict` is the verdict law; the front end's linear ledger and
the grammar's quadratic ledger add. -/
private lemma exists_canonDecider (F : MachineFormat) :
    ∃ (D : FinTM Bool) (a : ℕ), ∀ α : List Bool, ∃ b : Bool,
      D.ComputesInTime α [b] (a * (α.length + 1) ^ a) ∧
        (b = false → F.decode α = F.fallback) ∧
        (b = true → ∃ tail, F.scan α = some tail) := by
  -- The composition, as prescribed: the frozen front end and the grammar stage, joined by
  -- public seams on one bank, each verdict sent to a one-step emitting halt. Semantic laws:
  -- the front end's reject clause and `canonGrammar_verdict`.
  obtain ⟨_C, _entry, _exit, _a, _wide, _distinct, _front⟩ := exists_canonParseFront F
  obtain ⟨_m, _S, _, _, _G, _gentry, _gexit, _b, _header, _gdistinct, _grammar⟩ :=
    exists_canonGrammarStage F
  have _law := canonGrammar_verdict F
  sorry

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
runtime proof remain open; this target retains its original admission.

**Fill appendix (B5a continuation, partial).** `exists_canonHeaderCall` loads
the undoubled header through the two public call/extraction rows in linear
time. `binaryGuard_done` and `binaryGuard_escape` prove the physical positive
block-length comparison from a preloaded binary counter, including the first
exit, silence, native-input position and a linear bound independent of the
counter's value. The host is the existing `counterLoopTM`. Loading and guard
are not yet composed: header validity/canonicality, the `n + 1` setup, the
format guard, record grammar and output/fallback phases remain open. No new
private admission is introduced.

**Fill appendix (B5a canonizer continuation, partial).** The inherited loader
now composes with a physical canonical-bit scan, and `exists_canonHeaderOKTM`
checks pair success separately from the empty-header fallback in linear time.
`exists_canonCountTM` prepares a nonoverflowing binary `n + 1` counter.
`canonGuard_run` specializes the inherited guard to the native post-header
offset and this successor count, retaining its two strict exit cuts. A single
positive block size, `max F.guard ((4 * F.k + 5) * 3^(F.k + 1))`, enforces both
necessary guards; `decode_of_canonGuard` proves its rejection law. These new
helpers are proved without admissions. The preloaded guard still needs to be
connected to the loader with a preserved header bank and a native-input seek.
The physical record parser, suffix check, prefix/fallback emission and complete
polynomial ledger remain open; this target retains its original admission.
Note 50's full-canonizer regression remains pending. Component regressions are
reported separately in the delivery evidence.

**Fill appendix (canonizer continuation).** The blank-tape preparation now
preserves the original header and installs its successor count on a separate
bank through the public install call. `canonOffset` supplies the binary native
address; `exists_canonGuardFront` composes preparation, the public input seek,
the inherited positive guard, and a second seek on success, with an explicit
linear ledger and the non-counter frame preserved. Its contract assumes a
successful pair decode and is only a guard verdict. The header-validity branch,
strict cuts for both composite exits, generic record validation, grammar loop,
suffix/prefix emission and final polynomial assembly remain pending. No new
private admission is introduced, and this headline retains its original
`sorry`; full physical note-50 regressions remain pending.


**Fill appendix (canonizer continuation 2, partial).** The total header
check now has a clean silent Boolean branch contract. A separate stronger
guard front exposes strict cuts for both ports while preserving the header
and saved native address. `exists_canonCheckedFront` composes the header
check with this guard, keeping pair failure distinct from an encoded empty
header and proving that either rejection decodes to the fixed fallback.
`exists_canonParseFront` merges the failure causes through the public phase
host into two strict live ports, preserving the successful ready bank and
remainder position. All fourteen new private declarations are proved without
admissions. The guard's destructive counter is not claimed to be restored.
Recreating the parser bound, the generic physical action validator, the
record loop, suffix/prefix emission and complete polynomial assembly remain
open. This headline retains its original admission; the full physical
note-50 cases remain pending.


**Fill appendix (canonizer continuation 3).** Phase 1 is complete: the format-independent
strip machine copies the native input, erases its maximal trailing `true` suffix, returns
its work head to the origin, and emits the retained word through the public identity emit
call. Its two-pass leaf uses the public catalog trace, and public seams compose the phases;
the release adapter handles coincident emit-call anchors. The prescribed timed-conditional
glue now proves this headline modulo `exists_canonDecider` and `exists_canonGrammarStage`,
which remain the named admissions. This refines the earlier prefix-copy emission route to
validation followed by stripping or the constant fallback. The grammar and validator, and
therefore the complete physical canonizer's note-50 checks, remain pending.

**Fill appendix (canonizer continuation 4).** Phase 2 is complete: the prescribed grammar
bridges, the generic bounded unary reader `exists_canonUnaryTM`, and the generic record
validator `exists_canonRecordTM` are proved. Both components are silent, restore their
binary-bound bank, have strict Boolean exit cuts, and run in time linear in the native
input length and binary width. Their contracts are the recommended statements unchanged.
The physical grammar stage and validator remain the two frozen open stubs; the headline
statement and conditional-composition proof are unchanged. -/
theorem exists_polyCanonizer :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => F.serialize (F.decode α)) fun n => d * (n + 1) ^ d := by
  obtain ⟨D, a, decider⟩ := exists_canonDecider F
  choose verdict spec using decider
  obtain ⟨M, b, strip⟩ := exists_canonStripTM
  obtain ⟨E, e, fallback⟩ := FinTM.computesFunInTime_const (F.serialize F.fallback)
  have decides : D.ComputesFunInTime (fun α => [verdict α]) fun n => a * (n + 1) ^ a :=
    fun α => (spec α).1
  obtain ⟨C, c, branch⟩ := FinTM.computesFunInTime_cond decides strip fallback
  refine ⟨C, c * (a + b + e + 1) + a + b + 1, ?_⟩
  intro α
  have output : (if verdict α then canonStrip α else F.serialize F.fallback) =
      F.serialize (F.decode α) := by
    cases hv : verdict α with
    | false =>
      rw [(spec α).2.1 hv]
      rfl
    | true =>
      obtain ⟨tail, hs⟩ := (spec α).2.2 hv
      exact canonStrip_of_scan F α tail hs
  have run := branch α
  dsimp only at run ⊢
  rw [output] at run
  apply run.mono
  set d := c * (a + b + e + 1) + a + b + 1
  set P := (α.length + 1) ^ d
  have base : 1 ≤ α.length + 1 := by omega
  have pa : (α.length + 1) ^ a ≤ P := Nat.pow_le_pow_right base (by omega)
  have pb : (α.length + 1) ^ b ≤ P := Nat.pow_le_pow_right base (by omega)
  have p1 : α.length + 1 ≤ P := by
    simpa using Nat.pow_le_pow_right base (show 1 ≤ d by omega)
  have p0 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have inner : a * (α.length + 1) ^ a +
      max (b * (α.length + 1) ^ b) (e * (α.length + 1)) + 1 ≤ (a + b + e + 1) * P := by
    have ha := Nat.mul_le_mul_left a pa
    have hb := Nat.mul_le_mul_left b pb
    have he := Nat.mul_le_mul_left e p1
    have hm : max (b * (α.length + 1) ^ b) (e * (α.length + 1)) ≤ b * P + e * P :=
      max_le (by omega) (by omega)
    nlinarith
  calc
    c * (a * (α.length + 1) ^ a + max (b * (α.length + 1) ^ b) (e * (α.length + 1)) + 1)
        ≤ c * ((a + b + e + 1) * P) := Nat.mul_le_mul_left c inner
    _ = (c * (a + b + e + 1)) * P := by ring
    _ ≤ d * P := Nat.mul_le_mul_right P (by omega)

/-! ### Finite output summary (D4 move, generalized from Codes2Tape)

The four clock declarations below, with the five output-summary declarations now
in `Build/StepBlock` (`Turing.StepBlock.outputSummary` and its lemmas, H2-M),
replace their specialized ZF-B3 counterparts. This is the semantic specification
of the step block, not a finite-machine interpreter or a claim about its running
time.
-/

section StepBlockClients

open StepBlock

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

/-- The hosted clock `StepBlock.hostedLoopTM` with its two live exits replaced by the
one-step verdict. Timeout emits false; simulated halt tests the restored summary
cell. Every other transition is the existing hosted clock transition. -/
private def h1HostedVerdictTM (k : ℕ) :
    MultiTapeTM (1 + (k + 2 + 1)) Bool (CounterLoopState (Σ key, Ph k key) × Bool) :=
  { hostedLoopTM k with tr := fun q inp work =>
      if q.1 = .done ∨ q.1 = .escape then
        ⟨0, fun _ => (none, 0),
          some (if q.1 = .escape then
            work (vhostBank (summaryTape k).castSucc) == some true else false), none⟩
      else (hostedLoopTM k).tr q inp work }

/-- The physical hosted clock and its verdict, from the prepared round
seam. The endpoint is halted and emits precisely the inherited semantic
clock's answer, after the arbitrary prior physical output prefix.

**Proof sketch.** The public agreement theorem transports the hosted clock
run because its strict prefixes avoid both verdict exits. At the endpoint,
the representation places the output summary under its head. One stationary
halting step reads it. The frozen semantic clock equation identifies this
bit; neither the physical run nor the acceptance argument is re-proved. -/
private theorem h1HostedVerdict_effect {k n : ℕ} {x z : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true))
    (rel : Rep M.tr (M.initCfg x) d) (t : ℕ)
    (p : Fin (z.length + 2)) :
    ∃ T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * t.bits.length + 3,
      let e := (h1HostedVerdictTM k).runFrom
        (vhostCfg (counterLoopCfg (some (.dec .run)) d
          (FinTM.bufferTape t.bits) 0) true p []) T
      e.state = none ∧ e.inputPos = p ∧
        e.output = d.output ++ [summaryClock M t (M.initCfg x) none] := by
  obtain ⟨T, e, ct, b, bound, -, related, output, -, _, run, cut⟩ :=
    hostedLoopTM_run M (M.initCfg x) (by simp [MultiTapeTM.initCfg, Cfg.init]) d entry rel
      t.bits (FinTM.bufferTape t.bits) 0 (by intro p _ _; simp) t (counterValue_bits t) true
      (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p []
  let start := vhostCfg (counterLoopCfg (some (.dec .run)) d
    (FinTM.bufferTape t.bits) 0) true p []
  have agree : (hostedLoopTM k).AgreeOn (h1HostedVerdictTM k)
      {q | q.1 ≠ .done ∧ q.1 ≠ .escape} := by
    intro q hq inp work
    simp only [h1HostedVerdictTM, hq.1, hq.2, or_self, ↓reduceIte]
  have transfer := MultiTapeTM.runFrom_eq_of_agreeOn agree start T (by
    intro u hu q hq
    constructor
    · intro bad
      exact (cut u hu q.2).1 (hq.trans (congrArg some (Prod.ext bad rfl)))
    · intro bad
      exact (cut u hu q.2).2 (hq.trans (congrArg some (Prod.ext bad rfl))))
  have semantic : summaryClock M t (M.initCfg x) none =
      ((M.runFrom (M.initCfg x) t).state.isNone &&
        (outputSummary (M.runFrom (M.initCfg x) t).output == some true)) :=
    summaryClock_correct M (M.initCfg x) t
  obtain ⟨hs, -, -, cell⟩ := hostedLoop_read M.tr (M.runFrom (M.initCfg x) t) e related
    (if (M.runFrom (M.initCfg x) t).state.isSome then .done else .escape) ct 0 b p []
  refine ⟨T + 1, by omega, ?_⟩
  change ((h1HostedVerdictTM k).runFrom start (T + 1)).state = none ∧ _
  rw [MultiTapeTM.runFrom_succ_eq_step', transfer, run, semantic]
  unfold MultiTapeTM.step
  rw [hs]
  simp only [h1HostedVerdictTM, cell]
  cases state : (M.runFrom (M.initCfg x) t).state <;>
    simp [Action.apply, vhostCfg, counter_cfg_eq, output, moveInputPos_zero]

/-- The hosted verdict's bit is bounded acceptance, by the inherited
semantic bridge. This specializes only the prepared-seam contract: parsing
and canonizer installation are separate startup obligations. -/
private theorem h1HostedVerdict_accepts (F : MachineFormat) (α x z : List Bool)
    (d : Cfg (F.k + 2) Bool (Σ key, Ph F.k key) x)
    (entry : d.state = some (exit F.k true))
    (rel : Rep (F.machine (F.decode α)).tr
      ((F.machine (F.decode α)).initCfg x) d) (t : ℕ)
    (p : Fin (z.length + 2)) :
    ∃ T ≤ t * (50 * ((tableBitsK (F.machine (F.decode α)).tr).length + 1)) +
        4 * t + 2 * t.bits.length + 3, ∃ answer : Bool,
      ((h1HostedVerdictTM F.k).runFrom
        (vhostCfg (counterLoopCfg (some (.dec .run)) d
          (FinTM.bufferTape t.bits) 0) true p []) T).state = none ∧
      ((h1HostedVerdictTM F.k).runFrom
        (vhostCfg (counterLoopCfg (some (.dec .run)) d
          (FinTM.bufferTape t.bits) 0) true p []) T).output = d.output ++ [answer] ∧
      (answer = true ↔ (F.toFinTM (F.decode α)).ComputesInTime x [true] t) := by
  obtain ⟨T, bound, halted, _, output⟩ :=
    h1HostedVerdict_effect (F.machine (F.decode α)) d entry rel t p
  exact ⟨T, bound, _, halted, output, summaryClock_accepts (F.toFinTM (F.decode α)) x t⟩

end StepBlockClients

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
host assembly, and its ledger remain open; this target retains its admission.

**Fill appendix (B5a H1, selected-record partial).** The fixed-field reader
`StepBlock.recordTM` (then private) reads the fixed action fields into finite
control and executes them on the mirrored bank and native input, recording the
emission by `summaryEmit`. `StepBlock.recordTM_read`,
`StepBlock.recordTM_execute`, and `StepBlock.recordTM_effect` prove its framed
physical trace, source-action relation, silence, first live exit, and exact
`4k + 5` time bound. Its control depends only on `k`; the
public `codeReadActionK_append` supplies the decoding proof. The table head
is left at the actual successor field. Record lookup, successor installation,
restoration of the round seam, nested-input setup, canonizer installation,
and the complete hosted counter loop remain open. This target keeps its
original admission; these new private components contain no admissions.
Addendum 1 is proved for this component by `StepBlock.recordTM_envelope` and is
included in `StepBlock.recordTM_effect`: only the final payload step moves a
mirrored or native input head, each by at most one; the summary head stays fixed
and the table head advances by at most `4k + 4`. The full round's auxiliary-home
restoration and head envelope remain part of the open step-block construction.

**Fill appendix (H1 continuation, partial; complete generic step block).**
The inherited frontier's items 1–3 are now proved in `StepBlock.roundTM_effect`
for the single finite machine `StepBlock.roundFinTM k`. Its control is
independent of the coded state count. Whole-record lookup follows `tableBitsK`'s
exact read order,
executes the inherited fixed payload, installs the variable-length successor,
and restores both auxiliary heads to zero. The relation-level contract includes
a live halt exit after applying the halting action, silence at every prefix,
first-return cuts, a `50 * (|table| + 1)` bound, and the whole-round head envelope.
The unary state shares the summary auxiliary: summary at zero, blank at one,
and the state word at two. This layout preserves the inherited summary cell.
All new helpers are proved without admissions. This partial does not discharge
the headline: nested-input startup and canonizer installation, Z1 hosting and
the counter loop, the joint polynomial ledger, and note 50's physical H1
exact-deadline checks remain. The original statement and pending tag are unchanged.
**Fill appendix (H1 continuation 2, partial; complete hosted clock and verdict).**
The frozen `StepBlock.roundTM_effect` now feeds the public binary counter loop
through the round index, the orbit invariant and `StepBlock.loopTM_run`. The counter
loop is inside the public virtual-input host: its round anchor is fixed while
the host's boundary tag may change. `StepBlock.hostedLoopTM_run` proves the valid arrival
tag and strict cuts at both exits, including an escape on the last permitted
round. `h1HostedVerdict_effect` adds one stationary halting emission and gives
the inherited `summaryClock` answer in at most
`t * (50 * (|table| + 1)) + 4 * t + 2 * |bits t| + 3` physical steps.
`h1HostedVerdict_accepts` cites `summaryClock_accepts` for bounded acceptance.
These contracts start at the prepared round seam and introduce no admissions.
Nested-input startup, installation of the frozen canonizer, the joint
polynomial startup ledger, and the end-to-end raw-code note-50 checks remain
open. The headline retains its original admission and pending tag.

**H2-M (2026-10-14).** The step block and its components moved, renamed, to the
public module `Build/StepBlock` (namespace `Turing.StepBlock`; rename map in
`audits/evidence/h2/r2/H2-design-r2.md`, Appendix A); the appendices above use the
new names. This headline's statement and admission are unchanged.

**H1 harvest.** The hosted clock moved, generalized to any represented live start and
renamed, to the public module `Build/StepBlockLoop` (gate
`audits/h1-harvest-statements-findings.md`): `h1ClockTM` and `h1HostedClockTM` are
`StepBlock.loopTM` and `StepBlock.hostedLoopTM`; `h1Clock_effect` and
`h1HostedClock_effect` are the cases of `StepBlock.loopTM_run` and
`StepBlock.hostedLoopTM_run` at the initial configuration; the round index and the orbit
lemmas moved as private helpers. The word-value bridge `canonBits_value` moved to
`Build/CounterLoop` as `Turing.foldr_bit_eq_ofDigits`, beside `Turing.counterValue_bits`.
The appendices above use the new names; this headline's statement and admission are
unchanged.

-/
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
