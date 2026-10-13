/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
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
* **Status update (fills-7, 2026-10-12): partial.** The two headline contracts
  retain their original admissions. Proved so far:
  - for the canonizer: the native-input binary-header loader and the physical
    fail-fast binary length guard; the canonical-header check, the
    nonoverflowing successor counter and its specialized guard; and the guard
    front end, which prepares the header, the successor count and the native
    remainder address from blank tapes, seeks there, runs the guard and seeks
    back on success;
  - for the simulator: the complete generic step block `h1RoundTM`, one finite
    machine per work-tape count `k` whose control is independent of the coded
    state count (record lookup, the selected record's payload, successor
    installation and the round seam), with its exact time bound and head
    envelope (`h1Round_effect`).

  Still open: the canonizer's header-validity branch, the record parser and
  the emission; the simulator's nested-input setup, canonizer installation,
  and the hosted, clocked assembly with its ledger.

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

/-- The parser's binary value is the counter host's binary value. -/
private lemma canonBits_value (w : List Bool) :
    w.foldr Nat.bit 0 = Nat.ofDigits 2 (w.map Bool.toNat) := by
  rw [Nat.ofDigits_eq_foldr, List.foldr_map]
  have step : (fun (bit : Bool) (tail : ℕ) => (bit.toNat : ℕ) + 2 * tail) = Nat.bit := by
    funext bit tail
    cases bit <;> simp [Nat.bit, Nat.add_comm]
  simpa only [Nat.cast_id] using
    congrArg (fun f : Bool → ℕ → ℕ => w.foldr f 0) step.symm

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
    rw [← canonBits_value]
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
  · rw [← canonBits_value]
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
 -/
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

/-- Number of fixed bits before a transition's variable-length successor field. -/
private abbrev h1RecordWidth (k : ℕ) : ℕ := 4 * k + 4

/-- Finite control for the selected-record component of H1. The pair stores
the number of bits read and a fixed-size bit buffer; `none` is its live exit.
This type depends only on the work-tape count, never on the coded state count. -/
private abbrev h1RecordState (k : ℕ) :=
  Option (Fin (h1RecordWidth k + 1) × (Fin (h1RecordWidth k) → Bool))

/-- The record tape follows the mirrored work bank. -/
private def h1TableTape (k : ℕ) : Fin (k + 2) := Fin.natAdd k (0 : Fin 2)

/-- A stationary cell after the record tape stores the three-valued output summary. -/
private def h1SummaryTape (k : ℕ) : Fin (k + 2) := Fin.natAdd k (1 : Fin 2)

/-- Every mirrored work tape is distinct from the record tape. -/
private lemma h1Mirror_ne_table (k : ℕ) (i : Fin k) :
    Fin.castAdd 2 i ≠ h1TableTape k := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  dsimp [h1TableTape] at hv
  omega

/-- The summary cell and the record head lie on distinct auxiliary tapes. -/
private lemma h1Summary_ne_table (k : ℕ) : h1SummaryTape k ≠ h1TableTape k := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [h1SummaryTape, h1TableTape] at hv
  omega

/-- Interpret the fixed fields with the public record reader. A dummy halt
field makes the parsed successor irrelevant; the actual successor remains
on the record tape for the next component. Only canonized records are used. -/
private def h1Payload (k : ℕ) (bits : Fin (h1RecordWidth k) → Bool) :
    Action k Bool (Fin 1) :=
  ((codeReadActionK k 0 (List.ofFn bits ++ [false])).map Prod.fst).getD
    ⟨0, fun _ => (none, 0), none, none⟩

/-- Apply the fixed fields to the mirrored bank and native input head,
updating the summary cell instead of physically emitting. The record tape
and both auxiliary heads remain fixed, and the next control is a live exit. -/
private def h1ApplyPayload {k : ℕ} (a : Action k Bool (Fin 1)) (s : Option Bool) :
    Action (k + 2) Bool (h1RecordState k) :=
  ⟨a.inputTape, Fin.addCases a.workTapes
    (fun i : Fin 2 => if i = 0 then (none, 0) else (some (summaryEmit s a.output), 0)),
    none, some none⟩

/-- H1's physical selected-record component: read the fixed fields, then
execute their work/input actions and summary update. Its exit points at the
successor field; selecting the record and installing its successor are separate
remaining parts of the single interpreter block. [AB09, Theorem 1.9]

No catalog row reads a fixed-length, non-delimited prefix into finite control:
the two-pass scan requires delimiters. This small controller supplies that
part, using `tapeAction` and the existing `codeReadActionK`, without a new
grammar validator, host, or clock. -/
private def h1RecordTM (k : ℕ) : MultiTapeTM (k + 2) Bool (h1RecordState k) where
  q₀ := some (0, fun _ => false)
  tr := fun q _ w => match q with
    | none => inputMoveAction 0 none
    | some (p, bits) =>
      if h : p.val < h1RecordWidth k then
        tapeAction (h1TableTape k) 0 none .pos
          (some (⟨p.val + 1, by omega⟩,
            Function.update bits ⟨p.val, h⟩ ((w (h1TableTape k)).getD false)))
      else h1ApplyPayload (h1Payload k bits) (w (h1SummaryTape k))

/-- Configuration during the fixed-prefix read, with the first `r` bits
installed in finite control and every tape content unchanged. -/
private def h1ReadCfg {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (bits : Fin (h1RecordWidth k) → Bool) (r : ℕ) (hr : r ≤ h1RecordWidth k) :
    Cfg (k + 2) Bool (h1RecordState k) x :=
  { d with
    state := some (some (⟨r, by omega⟩, fun i => if i.val < r then bits i else false))
    workTapePos := Function.update d.workTapePos (h1TableTape k)
      (d.workTapePos (h1TableTape k) + r) }

/-- The public record reader recovers exactly the fixed action fields from
their finite buffer, regardless of the actual successor's state space.

**Proof sketch.** The movement, work actions and emission occupy exactly
`4k + 4` bits. Replace only the remaining successor field by the halt tag,
then invoke `codeReadActionK_append` at the one-state type. -/
private lemma h1Payload_correct {k n : ℕ} (a : Action k Bool (Fin (n + 1)))
    (bits : Fin (h1RecordWidth k) → Bool)
    (hbits : List.ofFn bits = (actionBitsK a).take (h1RecordWidth k)) :
    h1Payload k bits = ⟨a.inputTape, a.workTapes, a.output, none⟩ := by
  have moves (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have writes (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    cases b with
    | none => rfl
    | some b => cases b with
      | none => rfl
      | some b => cases b <;> rfl
  have emits (b : Option Bool) : (optBoolBits b).length = 2 := by
    cases b with
    | none => rfl
    | some b => cases b <;> rfl
  let fixed := signBits a.inputTape ++
    (List.finRange k).flatMap (fun i => optOptBoolBits (a.workTapes i).1 ++
      signBits (a.workTapes i).2) ++ optBoolBits a.output
  have plen : fixed.length = h1RecordWidth k := by
    simp [fixed, h1RecordWidth, List.length_flatMap, moves, writes, emits]
    omega
  have he : List.ofFn bits ++ [false] =
      actionBitsK (⟨a.inputTape, a.workTapes, a.output, none⟩ : Action k Bool (Fin 1)) := by
    rw [hbits]
    change (fixed ++ optStateBits a.state).take (h1RecordWidth k) ++ [false] =
      fixed ++ [false]
    rw [← plen, List.take_left]
  have hp := codeReadActionK_append
    (⟨a.inputTape, a.workTapes, a.output, none⟩ : Action k Bool (Fin 1)) []
  simp only [List.append_nil] at hp
  simp only [h1Payload, he, hp, Option.map_some, Option.getD_some]

/-- The physical reader consumes any permitted prefix in exactly its length,
without changing the native input, any work-tape cell, or the physical output.
Only the record head advances. This is a framed statement: all unmentioned
tape cells, mirrored tape positions, and the prior output may be arbitrary.

**Proof sketch.** Induct on the number of consumed bits. The public single-tape
movement law advances the record head; updating the next finite buffer slot
extends precisely the prefix already read. There is no delimiter assumption. -/
private lemma h1Record_read {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (bits : Fin (h1RecordWidth k) → Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i))
    (r : ℕ) (hr : r ≤ h1RecordWidth k) :
    (h1RecordTM k).runFrom d r = h1ReadCfg d bits r hr := by
  induction r with
  | zero =>
    apply Cfg.ext <;> simp [h1ReadCfg, hq, h1RecordTM]
  | succ r ih =>
    have hlt : r < h1RecordWidth k := by omega
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread : (h1ReadCfg d bits r (by omega)).workTapeSymbols (h1TableTape k) =
        some (bits ⟨r, hlt⟩) := by
      simpa [h1ReadCfg, Cfg.workTapeSymbols] using hw ⟨r, hlt⟩
    have hbuffer : Function.update (fun i : Fin (h1RecordWidth k) =>
        if i.val < r then bits i else false) ⟨r, hlt⟩ (bits ⟨r, hlt⟩) =
        fun i => if i.val < r + 1 then bits i else false := by
      funext i
      by_cases he : i = ⟨r, hlt⟩
      · subst i
        simp
      · have hv : i.val ≠ r := fun h => he (Fin.ext h)
        rw [Function.update_of_ne he]
        by_cases hi : i.val < r <;> simp [hi, show (i.val < r + 1) ↔ (i.val < r) by omega]
    rw [step_of_tapeAction_move (h1RecordTM k) (h1ReadCfg d bits r (by omega))
      (q' := some (⟨r + 1, by omega⟩,
        fun i => if i.val < r + 1 then bits i else false))
      (h1TableTape k) 0 .pos rfl (by
        simp only [h1RecordTM, dif_pos hlt, hread, Option.getD_some, hbuffer])]
    apply Cfg.ext
    · rfl
    · simp [h1ReadCfg]
    · rfl
    · funext i
      by_cases he : i = h1TableTape k
      · subst i
        simp [h1ReadCfg, Nat.cast_add, SignType.pos_eq_one, add_assoc]
      · simp [h1ReadCfg, he]
    · rfl

/-- A selected, canonized record executes its fixed action fields in exactly
`4k + 5` physical steps. The table head then points at its successor field.
The equality includes the native-input movement, all mirrored writes/moves,
the finite summary update, and preservation of the physical output prefix.

**Proof sketch.** Apply the prefix trace at its full width. Its finite buffer
is the record's fixed prefix, so `h1Payload_correct` identifies the public
reader's result. The next transition executes that payload silently. -/
private lemma h1Record_execute {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (a : Action k Bool (Fin (n + 1))) (bits : Fin (h1RecordWidth k) → Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i))
    (hbits : List.ofFn bits = (actionBitsK a).take (h1RecordWidth k)) :
    (h1RecordTM k).runFrom d (h1RecordWidth k + 1) =
      (h1ApplyPayload (⟨a.inputTape, a.workTapes, a.output, none⟩ : Action k Bool (Fin 1))
        (d.workTapeSymbols (h1SummaryTape k))).apply
        (h1ReadCfg d bits (h1RecordWidth k) le_rfl) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', h1Record_read d bits hq hw _ le_rfl]
  have hbuf : (fun i : Fin (h1RecordWidth k) =>
      if i.val < h1RecordWidth k then bits i else false) = bits := by
    funext i
    exact if_pos i.isLt
  have hne := h1Summary_ne_table k
  have hs : (h1ReadCfg d bits (h1RecordWidth k) le_rfl).workTapeSymbols
      (h1SummaryTape k) = d.workTapeSymbols (h1SummaryTape k) := by
    simp [h1ReadCfg, Cfg.workTapeSymbols, hne]
  simp only [MultiTapeTM.step, h1ReadCfg, h1RecordTM, lt_self_iff_false,
    hbuf, h1Payload_correct a bits hbits]
  change (h1ApplyPayload _
    ((h1ReadCfg d bits (h1RecordWidth k) le_rfl).workTapeSymbols (h1SummaryTape k))).apply _ = _
  rw [hs]

/-- Addendum 1's head envelope for the selected-record component. Mirrored
heads and the native input head remain at their starting positions until the
single payload transition, then move exactly as the source action does. Thus
they stay between their start and end positions, with displacement at most
one. The table head advances by the consumed fixed prefix; the summary head
never moves. The table head is not yet restored to a round home.

**Proof sketch.** Before the payload, project `h1Record_read`; at the payload,
project `h1Record_execute`. Use the public one-action work-head bound. The
native input movement is clamped at either boundary. -/
private lemma h1Record_envelope {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (a : Action k Bool (Fin (n + 1))) (bits : Fin (h1RecordWidth k) → Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i))
    (hbits : List.ofFn bits = (actionBitsK a).take (h1RecordWidth k)) :
    ∀ u ≤ h1RecordWidth k + 1,
      let e := (h1RecordTM k).runFrom d u
      (∀ i : Fin k, e.workTapePos (Fin.castAdd 2 i) =
        d.workTapePos (Fin.castAdd 2 i) +
          if u = h1RecordWidth k + 1 then ((a.workTapes i).2 : ℤ) else 0) ∧
      e.inputPos = (if u = h1RecordWidth k + 1 then moveInputPos d.inputPos a.inputTape
        else d.inputPos) ∧
      (∀ j : Fin (k + 2), |e.workTapePos j - d.workTapePos j| ≤
        if j.val < k then 1 else (h1RecordWidth k : ℤ)) ∧
      |(e.inputPos.val : ℤ) - d.inputPos.val| ≤ 1 ∧
      e.workTapePos (h1TableTape k) = d.workTapePos (h1TableTape k) + min u (h1RecordWidth k) ∧
      e.workTapePos (h1SummaryTape k) = d.workTapePos (h1SummaryTape k) := by
  intro u hu
  dsimp only
  by_cases hend : u = h1RecordWidth k + 1
  · subst u
    rw [h1Record_execute d a bits hq hw hbits]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp [h1ApplyPayload, h1ReadCfg, h1Mirror_ne_table k i]
    · simp [h1ApplyPayload, h1ReadCfg]
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [h1ReadCfg, h1Mirror_ne_table k i, i.isLt] using
          workTapePos_apply_le
            (h1ApplyPayload (⟨a.inputTape, a.workTapes, a.output, none⟩ : Action k Bool (Fin 1))
              (d.workTapeSymbols (h1SummaryTape k)))
            (h1ReadCfg d bits (h1RecordWidth k) le_rfl) (Fin.castAdd 2 i)
      · fin_cases i <;>
          simp [h1ApplyPayload, h1ReadCfg, h1TableTape, h1RecordWidth, abs_le] <;> omega
    · change |((moveInputPos d.inputPos a.inputTape).val : ℤ) - d.inputPos.val| ≤ 1
      have hp := d.inputPos.isLt
      cases a.inputTape <;> simp only [moveInputPos, SignType.cast] <;>
        split <;> simp_all [abs_le] <;> omega
    · simp [h1ApplyPayload, h1ReadCfg, h1TableTape]
    · simp [h1ApplyPayload, h1ReadCfg, h1SummaryTape, h1TableTape]
  · have hread : u ≤ h1RecordWidth k := by omega
    rw [h1Record_read d bits hq hw u hread]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp [h1ReadCfg, h1Mirror_ne_table k i, hend]
    · simp [h1ReadCfg, hend]
    · intro j
      by_cases hj : j = h1TableTape k
      · subst j
        simpa [h1ReadCfg, h1TableTape, abs_of_nonneg (Int.natCast_nonneg u)] using
          (show (u : ℤ) ≤ h1RecordWidth k by omega)
      · simp [h1ReadCfg, hj]
        split <;> omega
    · simp [h1ReadCfg]
    · simp [h1ReadCfg, min_eq_left hread]
    · simp [h1ReadCfg, h1Summary_ne_table k]

/-- The selected-record component has finite, decidable control for every
fixed tape count; it is a single physical machine for all coded state counts. -/
private def h1RecordFinTM (k : ℕ) : FinTM Bool where
  k := k + 2
  State := h1RecordState k
  tm := h1RecordTM k

/-- Relation-level effect of the selected record's fixed fields. The first
`k` work tapes mirror an arbitrary source configuration, and a stationary
auxiliary cell stores its output summary. After exactly `4k + 5` steps the
input/work fields mirror the source action, its emission has been included
in the summary, and the physical output is unchanged. The live exit is
first reached at that time, whose bound is the selected record's length.

This is the fixed-field part of H1's step block, not yet a full simulated
transition: the coded successor must still be installed by the caller.

**Promotion candidate (host H2, step block; machine-library-design.md §14).**
This component's contract includes Addendum 1's head envelope: at every
intermediate time each mirrored head and the native input head is still at
its start or has made exactly the source action's move, with displacement at
most one. Auxiliary work-head displacement is bounded by `4k + 4`; the table
head advances by `min u (4k + 4)`, and the summary head stays at home. Lookup,
successor installation and table-head restoration remain outside this partial
contract; promotion as a complete step block must wait for those parts.

**Proof sketch.** Project the proved execution equality onto the input,
mirrored bank and summary cell. The summary identity is the inherited
`outputSummary_append`, including when the source action halts. Before the
last step the prefix trace has a reading state, never the live exit. -/
private lemma h1Record_effect {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (bits : Fin (h1RecordWidth k) → Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i))
    (hbits : List.ofFn bits = (actionBitsK a).take (h1RecordWidth k))
    (hin : d.inputPos = c.inputPos)
    (htapes : ∀ i : Fin k, d.workTapes (Fin.castAdd 2 i) = c.workTapes i)
    (hheads : ∀ i : Fin k, d.workTapePos (Fin.castAdd 2 i) = c.workTapePos i)
    (hsum : d.workTapeSymbols (h1SummaryTape k) = outputSummary c.output) :
    let e := (h1RecordTM k).runFrom d (h1RecordWidth k + 1)
    e.state = some none ∧ e.inputPos = (a.apply c).inputPos ∧
      (∀ i : Fin k, e.workTapes (Fin.castAdd 2 i) = (a.apply c).workTapes i ∧
        e.workTapePos (Fin.castAdd 2 i) = (a.apply c).workTapePos i) ∧
      e.workTapeSymbols (h1SummaryTape k) = outputSummary (a.apply c).output ∧
      e.output = d.output ∧
      (∀ u < h1RecordWidth k + 1, ((h1RecordTM k).runFrom d u).state ≠ some none) ∧
      h1RecordWidth k + 1 ≤ (actionBitsK a).length ∧
      (∀ u ≤ h1RecordWidth k + 1,
        let f := (h1RecordTM k).runFrom d u
        (∀ i : Fin k, f.workTapePos (Fin.castAdd 2 i) =
          d.workTapePos (Fin.castAdd 2 i) +
            if u = h1RecordWidth k + 1 then ((a.workTapes i).2 : ℤ) else 0) ∧
        f.inputPos = (if u = h1RecordWidth k + 1 then moveInputPos d.inputPos a.inputTape
          else d.inputPos) ∧
        (∀ j : Fin (k + 2), |f.workTapePos j - d.workTapePos j| ≤
          if j.val < k then 1 else (h1RecordWidth k : ℤ)) ∧
        |(f.inputPos.val : ℤ) - d.inputPos.val| ≤ 1 ∧
        f.workTapePos (h1TableTape k) =
          d.workTapePos (h1TableTape k) + min u (h1RecordWidth k) ∧
        f.workTapePos (h1SummaryTape k) = d.workTapePos (h1SummaryTape k)) := by
  dsimp only
  have he := h1Record_execute d a bits hq hw hbits
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, codeActionK_length a,
    h1Record_envelope d a bits hq hw hbits⟩
  · rw [he]
    rfl
  · rw [he]
    exact congrArg (fun p => moveInputPos p a.inputTape) hin
  · intro i
    rw [he]
    simp [h1ApplyPayload, h1ReadCfg, Fin.addCases_left, h1Mirror_ne_table k i, htapes i, hheads i]
  · rw [he]
    simp [Cfg.workTapeSymbols, h1ApplyPayload, h1ReadCfg, h1SummaryTape,
      ← hsum, outputSummary_append]
  · rw [he]
    simp [h1ApplyPayload, h1ReadCfg]
  · intro u hu
    rw [h1Record_read d bits hq hw u (by omega)]
    simp [h1ReadCfg]

/-- Every vector of work reads occurs in the serializer's fixed enumeration.
The proof follows its tape-zero-first recursion, independently of coded states. -/
private lemma h1WorkReads_mem (k : ℕ) (w : Fin k → Option Bool) :
    w ∈ workReadsK k := by
  induction k with
  | zero =>
    have hw : w = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [workReadsK, hw]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨w 0, ?_, ?_⟩
    · cases w 0 with
      | none => simp
      | some b => cases b <;> simp
    · apply List.mem_map.mpr
      refine ⟨Fin.tail w, ih (Fin.tail w), ?_⟩
      exact Fin.cons_self_tail w

/-- There are exactly three possible reads on each mirrored tape. -/
private lemma h1WorkReads_length (k : ℕ) : (workReadsK k).length = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [workReadsK, ih, Nat.pow_succ]; omega

/-- Work-read rank is the index in the actual serializer order. -/
private def h1WorkRank {k : ℕ} (w : Fin k → Option Bool) : Fin (3 ^ k) :=
  ⟨(workReadsK k).idxOf w, by
    rw [← h1WorkReads_length]
    exact List.idxOf_lt_length_iff.mpr (h1WorkReads_mem k w)⟩

/-- Input symbols use the same blank/false/true order as the table writer. -/
private def h1InputRank : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

/-- The read-vector rank within a state block. Its bound depends only on
`k`, so a physical controller may retain it in finite control. -/
private def h1ReadRank {k : ℕ} (inp : Option Bool) (w : Fin k → Option Bool) :
    Fin (3 ^ (k + 1)) :=
  ⟨(h1InputRank inp).val * 3 ^ k + (h1WorkRank w).val, by
    have hi := (h1InputRank inp).isLt
    have hw := (h1WorkRank w).isLt
    have hpos : 0 < 3 ^ k := Nat.pow_pos (by omega)
    have hm := Nat.mul_le_mul_right (3 ^ k) (show (h1InputRank inp).val ≤ 2 by omega)
    rw [Nat.pow_succ]
    omega⟩

/-- States of the trusted successor-field walker. The halt tag and the
unary successor terminator lead to distinct live exits. -/
private inductive h1SuccPhase where
  | tag
  | unary
  | done (live : Bool)
deriving DecidableEq, Fintype

/-- Walk an already canonized successor field. When `copy` is true, copy
its unary state word to `dst`; when false, only advance the table head.
No catalog leaf walks a bit-terminated, non-blank-delimited word. This
leaf supplies that missing operation; it does not validate the grammar. -/
private def h1SuccTM {m : ℕ} (src dst : Fin m) (copy : Bool) :
    MultiTapeTM m Bool h1SuccPhase where
  q₀ := .tag
  tr := fun q _ w => match q with
    | .tag => tapeAction src 0 none .pos
        (if w src = some true then .unary else .done false)
    | .unary =>
        ⟨0, fun j => if j = src then (none, .pos)
          else if copy = true ∧ j = dst then (some (w src), .pos) else (none, 0),
          none, some (if w src = some true then .unary else .done true)⟩
    | .done b => inputMoveAction 0 (.done b)

/-- A framed prefix of the successor copy: the table head advances, and
only an enabled destination receives the consumed prefix. -/
private def h1UnaryCfg {m : ℕ} {x : List Bool} (src dst : Fin m) (copy : Bool)
    (d : Cfg m Bool h1SuccPhase x) (w : List Bool) (r : ℕ) (q : h1SuccPhase) :
    Cfg m Bool h1SuccPhase x :=
  { d with
    state := some q
    workTapes := fun j z =>
      if copy = true ∧ j = dst ∧ d.workTapePos dst ≤ z ∧ z < d.workTapePos dst + r
      then FinTM.bufferTape w (z - d.workTapePos dst) else d.workTapes j z
    workTapePos := fun j => d.workTapePos j +
      if j = src ∨ (copy = true ∧ j = dst) then (r : ℤ) else 0 }

/-- One unary-field transition writes precisely the next copied cell.
The public prefix-write identity handles the destination's arbitrary frame.

**Proof sketch.** The source and destination are distinct. Read the next
source bit from the framed prefix hypothesis. Expanding one machine action
advances the selected heads; on the destination, `catalog_write_take`
extends the overwritten prefix. Every other cell is unchanged. -/
private lemma h1Unary_step {m : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (w : List Bool) (r : ℕ) (hr : r < w.length)
    (hw : d.workTapes src (d.workTapePos src + r) = some w[r]) :
    (h1SuccTM src dst copy).step (h1UnaryCfg src dst copy d w r .unary) =
      h1UnaryCfg src dst copy d w (r + 1)
        (if w[r] = true then .unary else .done true) := by
  have hs : (h1UnaryCfg src dst copy d w r .unary).workTapeSymbols src = some w[r] := by
    simpa [h1UnaryCfg, Cfg.workTapeSymbols, hne] using hw
  simp only [MultiTapeTM.step, h1UnaryCfg, h1SuccTM]
  change (⟨0, _, none, some (if
      (h1UnaryCfg src dst copy d w r .unary).workTapeSymbols src = some true
      then h1SuccPhase.unary else .done true)⟩ : Action m Bool h1SuccPhase).apply _ = _
  rw [hs]
  apply Cfg.ext
  · simp
  · simp
  · funext j
    by_cases hj : j = src
    · subst j
      simp [hne]
    · by_cases hc : copy = true ∧ j = dst
      · obtain ⟨hc, he⟩ := hc
        subst j
        subst copy
        simpa [h1UnaryCfg, hj, Action.apply, Cfg.workTapeSymbols, hne, hw] using
          catalog_write_take (d.workTapes dst) (d.workTapePos dst) w r hr
      · simp [hj, hc, ← and_assoc, Action.apply]
  · funext j
    by_cases hj : j = src
    · subst j
      simp [hne, Nat.cast_add, add_assoc]
    · by_cases hc : copy = true ∧ j = dst
      · simp [hc, Ne.symm hne, Nat.cast_add, add_assoc]
      · simp [hj, hc]
  · simp

/-- Every prefix of a trusted unary state field has its literal physical
trace, including the terminating false bit. The native input and output
are fixed, and every unrelated head is fixed.

**Proof sketch.** Induct over the consumed cells. Before the last cell the
replicated bit is true; the final false bit takes the live-successor exit.
Use the single prefix-write step for both the copying and skipping modes. -/
private lemma h1Unary_run {m : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (s : ℕ) (hq : d.state = some .unary)
    (hw : ∀ (r : ℕ) (hr : r < s + 1), d.workTapes src (d.workTapePos src + r) =
      some ((List.replicate s true ++ [false])[r]'(by simpa using hr)))
    (r : ℕ) (hr : r ≤ s + 1) :
    (h1SuccTM src dst copy).runFrom d r =
      h1UnaryCfg src dst copy d (List.replicate s true ++ [false]) r
        (if r ≤ s then .unary else .done true) := by
  induction r with
  | zero =>
    apply Cfg.ext <;> simp [h1UnaryCfg, hq]
    funext j z
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), if_pos (by omega)]
    rw [h1Unary_step src dst hne copy d _ r (by simp; omega) (hw r (by omega))]
    congr 1
    by_cases hlt : r < s
    · rw [List.getElem_append_left (by simpa using hlt)]
      simp [show r + 1 ≤ s by omega]
    · have he : r = s := by omega
      subst r
      simp

/-- Configuration after the successor tag has been consumed. It is a
one-cell table move and changes no other head, cell, input or output. -/
private def h1AfterTag {m : ℕ} {x : List Bool} (src : Fin m)
    (d : Cfg m Bool h1SuccPhase x) : Cfg m Bool h1SuccPhase x :=
  { d with state := some .unary
           workTapePos := Function.update d.workTapePos src (d.workTapePos src + 1) }

/-- The trusted successor walker consumes its entire variable-width field,
optionally installing the unary successor in a blank destination. Its exit
is live in both cases: `done false` means simulated halt, `done true` means
a next state. This is a record leaf, not a grammar validator.

**Proof sketch.** The first transition reads the tag. A halt tag finishes
immediately. A live tag enters the shared unary-prefix trace for the
successor word, including its terminating false. -/
private lemma h1Succ_trace {m n : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (s : Option (Fin n)) (hq : d.state = some .tag)
    (hw : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
      d.workTapes src (d.workTapePos src + r) = some ((optStateBits s)[r]'hr))
    (t : ℕ) (ht : t ≤ (optStateBits s).length) :
    let word := (s.map unaryFin).getD []
    (h1SuccTM src dst copy).runFrom d t =
      if t = 0 then d else h1UnaryCfg src dst copy (h1AfterTag src d) word (t - 1)
        (if t < (optStateBits s).length then .unary else .done s.isSome) := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    cases s with
    | none =>
      have ht0 : t = 0 := by simpa [optStateBits] using ht
      subst t
      have hs : d.workTapeSymbols src = some false := by
        simpa [Cfg.workTapeSymbols, optStateBits] using hw 0 (by simp [optStateBits])
      change (h1SuccTM src dst copy).step d = _
      rw [step_of_tapeAction_move (h1SuccTM src dst copy) d
        (q' := h1SuccPhase.done false) src 0 .pos hq (by simp [h1SuccTM, hs])]
      apply Cfg.ext <;> simp [h1UnaryCfg, h1AfterTag, optStateBits]
      · funext j z
        split_ifs <;> first | rfl | omega
    | some s =>
      have hs : d.workTapeSymbols src = some true := by
        simpa [Cfg.workTapeSymbols, optStateBits] using hw 0 (by simp [optStateBits])
      have first : (h1SuccTM src dst copy).step d = h1AfterTag src d := by
        simpa [h1AfterTag] using step_of_tapeAction_move (h1SuccTM src dst copy) d
          (q' := h1SuccPhase.unary) src 0 .pos hq (by simp [h1SuccTM, hs])
      have reads : ∀ (r : ℕ) (hr : r < s.val + 1),
          (h1AfterTag src d).workTapes src ((h1AfterTag src d).workTapePos src + r) =
            some ((List.replicate s.val true ++ [false])[r]'(by simpa using hr)) := by
        intro r hr
        simpa [optStateBits, unaryFin, h1AfterTag, Nat.cast_add, add_assoc, add_comm] using
          hw (r + 1) (by simp [optStateBits, unaryFin]; omega)
      have run := h1Unary_run src dst hne copy (h1AfterTag src d) s.val rfl reads
        t (by simpa [optStateBits, unaryFin] using ht)
      rw [MultiTapeTM.runFrom_succ_eq_step, first]
      have phase : (t ≤ s.val) ↔ (t + 1 < (optStateBits (some s)).length) := by
        simp [optStateBits, unaryFin]; omega
      simpa [unaryFin, phase] using run

/-- Endpoint of the successor-field trace, at exactly the field's bit length. -/
private lemma h1Succ_run {m n : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (s : Option (Fin n)) (hq : d.state = some .tag)
    (hw : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
      d.workTapes src (d.workTapePos src + r) = some ((optStateBits s)[r]'hr)) :
    let word := (s.map unaryFin).getD []
    (h1SuccTM src dst copy).runFrom d (optStateBits s).length =
      h1UnaryCfg src dst copy (h1AfterTag src d) word word.length (.done s.isSome) := by
  have trace := h1Succ_trace src dst hne copy d s hq hw _ le_rfl
  cases s <;> simpa [optStateBits, unaryFin] using trace

/-- Neither successor exit is visited before the field has been consumed. -/
private lemma h1Succ_cut {m n : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (s : Option (Fin n)) (hq : d.state = some .tag)
    (hw : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
      d.workTapes src (d.workTapePos src + r) = some ((optStateBits s)[r]'hr)) :
    ∀ t < (optStateBits s).length, ∀ b,
      ((h1SuccTM src dst copy).runFrom d t).state ≠ some (.done b) := by
  intro t ht b
  rw [h1Succ_trace src dst hne copy d s hq hw t (by omega)]
  by_cases hz : t = 0
  · simp [hz, hq]
  · simp [hz, ht, h1UnaryCfg]

/-- During a successor walk only the table head and an enabled destination
head advance. Every input position and the physical output prefix are fixed.
The exact formulas include both the halt tag and the last unary bit. -/
private lemma h1Succ_heads {m n : ℕ} {x : List Bool} (src dst : Fin m)
    (hne : src ≠ dst) (copy : Bool) (d : Cfg m Bool h1SuccPhase x)
    (s : Option (Fin n)) (hq : d.state = some .tag)
    (hw : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
      d.workTapes src (d.workTapePos src + r) = some ((optStateBits s)[r]'hr)) :
    ∀ t ≤ (optStateBits s).length,
      let e := (h1SuccTM src dst copy).runFrom d t
      e.inputPos = d.inputPos ∧ e.output = d.output ∧
      ∀ j, e.workTapePos j = d.workTapePos j +
        if j = src then (t : ℤ) else if copy = true ∧ j = dst then (t - 1 : ℕ) else 0 := by
  intro t ht
  rw [h1Succ_trace src dst hne copy d s hq hw t ht]
  by_cases hz : t = 0
  · simp [hz]
  · simp only [if_neg hz]
    refine ⟨rfl, rfl, ?_⟩
    intro j
    by_cases hj : j = src
    · subst j
      simp [h1UnaryCfg, h1AfterTag, hne]
      omega
    · simp [h1UnaryCfg, h1AfterTag, hj]

/-- Phase family for a complete record skip. The fixed reader is stopped
before its payload step; the successor walker then consumes the variable tail. -/
private def h1SkipPh (k : ℕ) : Bool → Type
  | false => h1RecordState k
  | true => h1SuccPhase

/-- The skipper reuses the inherited fixed reader and the trusted tail leaf. -/
private def h1SkipPart (k : ℕ) : (b : Bool) → MultiTapeTM (k + 2) Bool (h1SkipPh k b)
  | false => h1RecordTM k
  | true => h1SuccTM (h1TableTape k) (h1SummaryTape k) false

/-- Dispatch at the fixed-width boundary, without executing the action. -/
private def h1SkipRed (k : ℕ) : (b : Bool) → h1SkipPh k b → Option (Σ b, h1SkipPh k b)
  | false, some (p, _) => if p.val = h1RecordWidth k then some ⟨true, .tag⟩ else none
  | false, none => none
  | true, _ => none

/-- One whole-record skipper, including its variable successor field.
**Promotion candidate (host H2, record skipper; machine-library-design.md §14).**
Its one stationary dispatch step is explicit in the cost. -/
private def h1SkipTM (k : ℕ) : MultiTapeTM (k + 2) Bool (Σ b, h1SkipPh k b) :=
  phaseHostTM (h1SkipPart k) ⟨false, (h1RecordTM k).q₀⟩ (h1SkipRed k)

/-- The public phase-host theorem transfers the inherited prefix trace and
then takes its sole dispatch. The payload transition is never executed. -/
private lemma h1Skip_fixed {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (bits : Fin (h1RecordWidth k) → Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i)) :
    (∀ (u : ℕ) (hu : u ≤ h1RecordWidth k),
      (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) u =
        (h1ReadCfg d bits u hu).mapState (Sigma.mk false)) ∧
    (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) (h1RecordWidth k + 1) =
      (h1ReadCfg d bits (h1RecordWidth k) le_rfl).mapState
        (fun _ => (⟨true, h1SuccPhase.tag⟩ : Σ b, h1SkipPh k b)) := by
  have step := phaseHostTM_run (h1SkipPart k) ⟨false, (h1RecordTM k).q₀⟩ (h1SkipRed k)
    false d (h1ReadCfg d bits (h1RecordWidth k) le_rfl) (h1RecordWidth k)
    (h1Record_read d bits hq hw _ le_rfl)
    (some (⟨h1RecordWidth k, by omega⟩, fun i => if i.val < h1RecordWidth k then bits i else false))
    rfl ⟨true, .tag⟩ (by simp [h1SkipRed]) (by
      intro u hu s hs
      change ((h1RecordTM k).runFrom d u).state = some s at hs
      rw [h1Record_read d bits hq hw u (by omega)] at hs
      have he : s = some (⟨u, by omega⟩, fun i => if i.val < u then bits i else false) :=
        (Option.some.inj hs).symm
      subst s
      simp [h1SkipRed, show u ≠ h1RecordWidth k by omega])
  refine ⟨?_, step.2⟩
  intro u hu
  rw [step.1 u hu]
  exact congrArg (Cfg.mapState (Sigma.mk false)) (h1Record_read d bits hq hw u hu)

/-- Once dispatched, the host follows the successor walker literally.
This is an application of public state transport, not another host trace. -/
private lemma h1Skip_tail {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool h1SuccPhase x) (t : ℕ) :
    (h1SkipTM k).runFrom (d.mapState (Sigma.mk true)) t =
      ((h1SuccTM (h1TableTape k) (h1SummaryTape k) false).runFrom d t).mapState
        (Sigma.mk true) := by
  exact MultiTapeTM.runFrom_mapState_of_agreeOn
    (h1SuccTM (h1TableTape k) (h1SummaryTape k) false) (h1SkipTM k)
    ⟨(fun q => (⟨true, q⟩ : Σ b, h1SkipPh k b)), by
      intro a b h; cases h; rfl⟩ (fun _ => True)
    (fun _ _ _ _ => rfl) d t (fun _ _ _ _ => trivial)

/-- A trusted action record splits at exactly the inherited fixed width.
Only this elementary serialization identity is missing from the public
reader's lower-bound contract; it also fixes the skipper's exact cost. -/
private lemma h1Action_split {k n : ℕ} (a : Action k Bool (Fin (n + 1))) :
    ∃ bits : Fin (h1RecordWidth k) → Bool,
      actionBitsK a = List.ofFn bits ++ optStateBits a.state := by
  let p := signBits a.inputTape ++ (List.finRange k).flatMap
    (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) ++ optBoolBits
      a.output
  have hl : p.length = h1RecordWidth k := by
    have moveLen : ∀ s : SignType, (signBits s).length = 2 := by decide
    have writeLen : ∀ w : Option (Option Bool), (optOptBoolBits w).length = 2 := by decide
    have outputLen : ∀ w : Option Bool, (optBoolBits w).length = 2 := by decide
    simp [p, List.length_flatMap, moveLen, writeLen, outputLen, h1RecordWidth]
    omega
  refine ⟨fun i => p[i.val]'(by rw [hl]; exact i.isLt), ?_⟩
  change p ++ _ = _
  congr 1
  apply List.ext_getElem
  · simpa using hl
  · intro i hi hi'
    simp only [List.getElem_ofFn]

/-- Split a literal, undelimited word read at an arbitrary physical origin.
This small indexing fact is shared by fixed fields, record lists and state groups. -/
private lemma h1Reads_append (cells : ℤ → Option Bool) (p : ℤ) (a b : List Bool)
    (h : ∀ (r : ℕ) (hr : r < (a ++ b).length), cells (p + r) = some ((a ++ b)[r]'hr)) :
    (∀ (r : ℕ) (hr : r < a.length), cells (p + r) = some (a[r]'hr)) ∧
    (∀ (r : ℕ) (hr : r < b.length), cells (p + a.length + r) = some (b[r]'hr)) := by
  constructor
  · intro r hr
    have left := h r (by simp; omega)
    rw [List.getElem_append_left hr] at left
    exact left
  · intro r hr
    have right := h (a.length + r) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at right
    simpa only [Nat.add_sub_cancel_left, Nat.cast_add, add_assoc] using right

/-- Expose the fixed and variable reads of one trusted record at an arbitrary
physical table position. The tape outside the record is unrestricted. -/
private lemma h1Action_reads {k n : ℕ} {S : Type} {x : List Bool}
    (d : Cfg (k + 2) Bool S x) (a : Action k Bool (Fin (n + 1)))
    (hw : ∀ (r : ℕ) (hr : r < (actionBitsK a).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((actionBitsK a)[r]'hr)) :
    ∃ bits : Fin (h1RecordWidth k) → Bool,
      actionBitsK a = List.ofFn bits ++ optStateBits a.state ∧
      (actionBitsK a).length = h1RecordWidth k + (optStateBits a.state).length ∧
      (∀ i : Fin (h1RecordWidth k),
        d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i)) ∧
      (∀ (r : ℕ) (hr : r < (optStateBits a.state).length),
        d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + h1RecordWidth k + r) =
          some ((optStateBits a.state)[r]'hr)) := by
  obtain ⟨bits, hb⟩ := h1Action_split a
  have hlen : (actionBitsK a).length = h1RecordWidth k + (optStateBits a.state).length := by
    rw [hb, List.length_append, List.length_ofFn]
  have parts := h1Reads_append (d.workTapes (h1TableTape k)) (d.workTapePos (h1TableTape k))
    (List.ofFn bits) (optStateBits a.state) (by simpa only [hb] using hw)
  refine ⟨bits, hb, hlen, ?_, ?_⟩
  · intro i
    have cell := parts.1 i.val (by simpa only [List.length_ofFn] using i.isLt)
    rw [List.getElem_ofFn] at cell
    exact cell
  · simpa only [List.length_ofFn] using parts.2

/-- A complete record is skipped silently. The exact elapsed time is its
bit length plus the single phase dispatch. All tape cells are framed, and
only the table head changes; the successor is not copied in skipping mode.

**Proof sketch.** Use the inherited prefix read and public phase dispatch,
then the successor-field endpoint. The two head advances add to the full
record length, including its variable unary tail. -/
private lemma h1Skip_run {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (a : Action k Bool (Fin (n + 1)))
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ (r : ℕ) (hr : r < (actionBitsK a).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((actionBitsK a)[r]'hr)) :
    (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) ((actionBitsK a).length + 1) =
      { d.mapState (fun _ => (⟨true, h1SuccPhase.done a.state.isSome⟩ : Σ b, h1SkipPh k b)) with
        workTapePos := Function.update d.workTapePos (h1TableTape k)
          (d.workTapePos (h1TableTape k) + (actionBitsK a).length) } := by
  obtain ⟨bits, hb, hlen, hread, hfield⟩ := h1Action_reads d a hw
  let tail : Cfg (k + 2) Bool h1SuccPhase x :=
    (h1ReadCfg d bits (h1RecordWidth k) le_rfl).mapState (fun _ => .tag)
  have htail : ∀ (r : ℕ) (hr : r < (optStateBits a.state).length),
      tail.workTapes (h1TableTape k) (tail.workTapePos (h1TableTape k) + r) =
        some ((optStateBits a.state)[r]'hr) := by
    intro r hr
    simpa only [tail, Cfg.mapState, h1ReadCfg, Function.update_self] using hfield r hr
  have dispatch := (h1Skip_fixed d bits hq hread).2
  have he : (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) (h1RecordWidth k + 1) =
      tail.mapState (Sigma.mk true) := by
    exact dispatch
  rw [show (actionBitsK a).length + 1 = h1RecordWidth k + 1 + (optStateBits a.state).length by
    omega,
    MultiTapeTM.runFrom_add, he, h1Skip_tail,
    h1Succ_run _ _ (Ne.symm (h1Summary_ne_table k)) false tail a.state (by rfl) htail]
  apply Cfg.ext
  · simp [h1UnaryCfg, tail, Cfg.mapState, h1ReadCfg, hq]
  · rfl
  · simp [h1UnaryCfg, tail, Cfg.mapState, h1AfterTag, h1ReadCfg]
  · funext j
    by_cases hj : j = h1TableTape k
    · subst j
      rw [hlen]
      cases a.state <;>
        simp [h1UnaryCfg, h1AfterTag, tail, Cfg.mapState, h1ReadCfg, optStateBits,
          unaryFin, Nat.cast_add, add_assoc] ; omega
    · simp [h1UnaryCfg, h1AfterTag, tail, Cfg.mapState, h1ReadCfg, hj]
  · rfl

/-- Every prefix of a whole-record skip preserves the complete data frame.
At the sole dispatch the table head pauses; on every other transition it
advances one cell. Neither successor exit can occur before the full field.

**Proof sketch.** Split the horizon at the fixed reader's dispatch. The
first interval is `h1Record_read` transported by the public phase host;
the second is the trusted successor trace transported by public agreement. -/
private lemma h1Skip_path {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (bits : Fin (h1RecordWidth k) → Bool) (s : Option (Fin n))
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ i : Fin (h1RecordWidth k),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + i.val) = some (bits i))
    (hs : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + h1RecordWidth k + r) =
        some ((optStateBits s)[r]'hr)) :
    ∀ u ≤ h1RecordWidth k + 1 + (optStateBits s).length,
      let f := (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      (∀ j, f.workTapePos j = d.workTapePos j +
        if j = h1TableTape k then ((min u (h1RecordWidth k) + (u - (h1RecordWidth k + 1)) : ℕ) : ℤ)
        else (0 : ℤ)) ∧
      (u < h1RecordWidth k + 1 + (optStateBits s).length →
        ∀ b, f.state ≠ some ⟨true, .done b⟩) := by
  intro u hu
  dsimp only
  obtain ⟨hprefix, dispatch⟩ := h1Skip_fixed d bits hq hw
  by_cases hpre : u ≤ h1RecordWidth k
  · rw [hprefix u hpre]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [Cfg.mapState, h1ReadCfg]
      by_cases hj : j = h1TableTape k
      · subst j
        simp [min_eq_left hpre, Nat.sub_eq_zero_of_le (by omega : u ≤ h1RecordWidth k + 1)]
      · simp [hj]
    · intro _ b
      simp [Cfg.mapState, h1ReadCfg]
  · let tail : Cfg (k + 2) Bool h1SuccPhase x :=
      (h1ReadCfg d bits (h1RecordWidth k) le_rfl).mapState (fun _ => .tag)
    have htail : ∀ (r : ℕ) (hr : r < (optStateBits s).length),
        tail.workTapes (h1TableTape k) (tail.workTapePos (h1TableTape k) + r) =
          some ((optStateBits s)[r]'hr) := by
      intro r hr
      simpa only [tail, Cfg.mapState, h1ReadCfg, Function.update_self] using hs r hr
    have ht : u - (h1RecordWidth k + 1) ≤ (optStateBits s).length := by omega
    have he : (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) u =
        ((h1SuccTM (h1TableTape k) (h1SummaryTape k) false).runFrom
          tail (u - (h1RecordWidth k + 1))).mapState (Sigma.mk true) := by
      conv_lhs => rw [show u = (h1RecordWidth k + 1) + (u - (h1RecordWidth k + 1)) by omega]
      rw [MultiTapeTM.runFrom_add, dispatch]
      exact h1Skip_tail tail _
    rw [he]
    have hhead := h1Succ_heads _ _ (Ne.symm (h1Summary_ne_table k)) false tail s rfl htail _ ht
    refine ⟨hhead.1, ?_, hhead.2.1, ?_, ?_⟩
    · rw [h1Succ_trace _ _ (Ne.symm (h1Summary_ne_table k)) false tail s rfl htail _ ht]
      split_ifs <;> rfl
    · intro j
      change ((h1SuccTM _ _ false).runFrom tail _).workTapePos j = _
      rw [hhead.2.2 j]
      by_cases hj : j = h1TableTape k
      · subst j
        simp [tail, Cfg.mapState, h1ReadCfg, min_eq_right (by omega : h1RecordWidth k ≤ u),
          Nat.cast_add, add_assoc]
      · simp [tail, Cfg.mapState, h1ReadCfg, hj]
    · intro hlt b
      have hc := h1Succ_cut _ _ (Ne.symm (h1Summary_ne_table k)) false tail s rfl htail
        (u - (h1RecordWidth k + 1)) (by omega) b
      intro bad
      apply hc
      exact Option.map_injective (f := fun q : h1SuccPhase => (⟨true, q⟩ : Σ b, h1SkipPh k b))
        (by intro a b h; cases h; rfl) bad

/-- The whole-record skipper's composition contract: a first live exit,
complete framing, exact head trace, and a linear cost in the whole record.
Both the prefix width and the finite controller depend on `k` alone. -/
private lemma h1Skip_spec {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (a : Action k Bool (Fin (n + 1)))
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ (r : ℕ) (hr : r < (actionBitsK a).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((actionBitsK a)[r]'hr)) :
    (∀ u < (actionBitsK a).length + 1, ∀ b,
      ((h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) u).state ≠ some ⟨true, .done b⟩) ∧
    (∀ u ≤ (actionBitsK a).length + 1,
      let f := (h1SkipTM k).runFrom (d.mapState (Sigma.mk false)) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      (∀ j, f.workTapePos j = d.workTapePos j +
        if j = h1TableTape k then ((min u (h1RecordWidth k) + (u - (h1RecordWidth k + 1)) : ℕ) : ℤ)
        else 0)) := by
  obtain ⟨bits, _, hlen, hp, ht⟩ := h1Action_reads d a hw
  have run := h1Skip_path d bits a.state hq hp ht
  constructor
  · intro u hu b
    exact (run u (by omega)).2.2.2.2 (by omega) b
  · intro u hu
    exact ⟨(run u (by omega)).1, (run u (by omega)).2.1,
      (run u (by omega)).2.2.1, (run u (by omega)).2.2.2.1⟩

/-- Each skipper phase is finite, uniformly in the coded state count. -/
private instance h1SkipPh_finite (k : ℕ) (b : Bool) : Fintype (h1SkipPh k b) := by
  cases b <;> dsimp [h1SkipPh] <;> infer_instance

/-- Equality of the two skipper phase carriers is decidable. -/
private instance h1SkipPh_decidable (k : ℕ) (b : Bool) : DecidableEq (h1SkipPh k b) := by
  cases b <;> dsimp [h1SkipPh] <;> infer_instance

/-- The selector's finite router retains the current read rank and a
within-group record countdown. The coded state itself stays on tape. -/
private inductive h1SeekCtrl (k : ℕ) where
  | observe
  | advance (rank : Fin (3 ^ (k + 1)))
  | state (rank : Fin (3 ^ (k + 1)))
  | request (rank rest : Fin (3 ^ (k + 1))) (last : Bool)
  | done
  deriving DecidableEq, Fintype

/-- Selector routing. The unary state begins at cell two of the summary
auxiliary tape: cell zero is the summary and cell one its blank separator.
Observation and one additional move enter that state word; each true skips
one whole state block, and its false terminator selects the read rank. -/
private def h1SeekRouter (k : ℕ) : MultiTapeTM (k + 2) Bool (h1SeekCtrl k) where
  q₀ := .observe
  tr := fun q inp w => match q with
    | .observe => tapeAction (h1SummaryTape k) 0 none .pos
        (.advance (h1ReadRank inp (fun i => w (Fin.castAdd 2 i))))
    | .advance rank => tapeAction (h1SummaryTape k) 0 none .pos (.state rank)
    | .state rank =>
        if w (h1SummaryTape k) = some true then
          tapeAction (h1SummaryTape k) 0 none .pos
            (.request rank ⟨3 ^ (k + 1) - 1, by have hp : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega); omega⟩ false)
        else inputMoveAction 0 (if hr : rank.val = 0 then .done
          else .request rank ⟨rank.val - 1, by have := rank.isLt; omega⟩ true)
    | .request rank rest last => inputMoveAction 0 (.request rank rest last)
    | .done => inputMoveAction 0 .done

/-- The continuation after one skipped record. `rest` counts records still
to skip after the current one, and `last` distinguishes the rank suffix
from an entire state group. -/
private def h1SeekNext {k : ℕ} (rank rest : Fin (3 ^ (k + 1))) (last : Bool) : h1SeekCtrl k :=
  if hz : rest.val = 0 then (if last then .done else .state rank)
  else .request rank ⟨rest.val - 1, by have := rest.isLt; omega⟩ last

/-- Phase keys for the selector. `none` is its router; each finite countdown
key tags a call of the same one-record skipper. -/
private abbrev h1SeekKey (k : ℕ) := Option (Fin (3 ^ (k + 1)) × Fin (3 ^ (k + 1)) × Bool)

/-- Finite state carriers of the selector's public phase host. -/
private def h1SeekPh (k : ℕ) : h1SeekKey k → Type
  | none => h1SeekCtrl k
  | some _ => Σ b, h1SkipPh k b

/-- Selector phase machines: one router and the shared record skipper. -/
private def h1SeekPart (k : ℕ) : (key : h1SeekKey k) → MultiTapeTM (k + 2) Bool (h1SeekPh k key)
  | none => h1SeekRouter k
  | some _ => h1SkipTM k

/-- Only a requested call or a completed whole record dispatches. -/
private def h1SeekRed (k : ℕ) : (key : h1SeekKey k) → h1SeekPh k key → Option (Σ key, h1SeekPh k key)
  | none, .request rank rest last => some ⟨some (rank, rest, last), (h1SkipTM k).q₀⟩
  | some (rank, rest, last), ⟨true, .done _⟩ => some ⟨none, h1SeekNext rank rest last⟩
  | _, _ => none

/-- The selector is one finite physical machine, independent of the number
of coded states. The only loop is through the public phase host and the
proved whole-record skipper. -/
private def h1SeekTM (k : ℕ) : MultiTapeTM (k + 2) Bool (Σ key, h1SeekPh k key) :=
  phaseHostTM (h1SeekPart k) ⟨none, .observe⟩ (h1SeekRed k)

/-- Reuse the reader's framed configuration as the selector's data, with
only the finite router control renamed. -/
private def h1SeekCfg {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x) (q : h1SeekCtrl k) :
    Cfg (k + 2) Bool (Σ key, h1SeekPh k key) x :=
  d.mapState (fun _ => ⟨none, q⟩)

/-- One requested whole-record call, with its two public-host dispatches.
No intermediate point has the selector's final control. All data are framed,
and every non-table head stays fixed throughout this call.

**Proof sketch.** The first dispatch enters the shared skipper. Its first-exit
contract discharges the public phase-host guard, and the host theorem provides
both the complete inner prefix and the final dispatch. -/
private lemma h1Seek_request {k n : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (a : Action k Bool (Fin (n + 1))) (rank rest : Fin (3 ^ (k + 1))) (last : Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ (r : ℕ) (hr : r < (actionBitsK a).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((actionBitsK a)[r]'hr)) :
    (h1SeekTM k).runFrom (h1SeekCfg d (.request rank rest last)) ((actionBitsK a).length + 3) =
      h1SeekCfg ({ d with
          workTapePos := Function.update d.workTapePos (h1TableTape k)
            (d.workTapePos (h1TableTape k) + (actionBitsK a).length) }) (h1SeekNext rank rest last) ∧
    (∀ u < (actionBitsK a).length + 3,
      ((h1SeekTM k).runFrom (h1SeekCfg d (.request rank rest last)) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ (actionBitsK a).length + 3,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d (.request rank rest last)) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1TableTape k → f.workTapePos j = d.workTapePos j) := by
  let key : h1SeekKey k := some (rank, rest, last)
  let start := d.mapState (@Sigma.mk Bool (h1SkipPh k) false)
  let finish : Cfg (k + 2) Bool (Σ b, h1SkipPh k b) x :=
    { d.mapState (fun _ => ⟨true, h1SuccPhase.done a.state.isSome⟩) with
      workTapePos := Function.update d.workTapePos (h1TableTape k)
        (d.workTapePos (h1TableTape k) + (actionBitsK a).length) }
  have hrun : (h1SeekPart k key).runFrom start ((actionBitsK a).length + 1) = finish :=
    h1Skip_run d a hq hw
  have hfirst : (h1SeekTM k).step (h1SeekCfg d (.request rank rest last)) =
      start.mapState (Sigma.mk key) := by
    rw [step_of_inputMoveAction (h1SeekTM k) (h1SeekCfg d (.request rank rest last))
      (q := ⟨none, .request rank rest last⟩) (q' := ⟨key, (h1SkipTM k).q₀⟩) 0
      (by simp [h1SeekCfg, Cfg.mapState, hq]) rfl]
    apply Cfg.ext <;> simp [h1SeekCfg, Cfg.mapState, hq, start, key, h1SkipTM, phaseHostTM]
  have advance (u : ℕ) := MultiTapeTM.runFrom_succ_eq_step (tm := h1SeekTM k)
    (cfg := h1SeekCfg d (.request rank rest last)) (t := u)
  rw [hfirst] at advance
  have hosted := phaseHostTM_run (h1SeekPart k) ⟨none, .observe⟩ (h1SeekRed k)
    key start finish ((actionBitsK a).length + 1) hrun ⟨true, .done a.state.isSome⟩
    (by simp [finish, Cfg.mapState, hq]) ⟨none, h1SeekNext rank rest last⟩ rfl (by
      intro u hu s hs
      have hc := (h1Skip_spec d a hq hw).1 u hu
      change ((h1SkipTM k).runFrom start u).state = some s at hs
      obtain ⟨b, q⟩ := s
      cases b with
      | false => rfl
      | true =>
        cases q with
        | tag => rfl
        | unary => rfl
        | done b => exact False.elim (hc b hs))
  have hpre (u : ℕ) (hu : u ≤ (actionBitsK a).length + 1) :
      (h1SeekTM k).runFrom (h1SeekCfg d (.request rank rest last)) (u + 1) =
        ((h1SkipTM k).runFrom start u).mapState (Sigma.mk key) := by
    rw [advance u]
    exact hosted.1 u hu
  have hend : (h1SeekTM k).runFrom (h1SeekCfg d (.request rank rest last))
      ((actionBitsK a).length + 3) =
      h1SeekCfg ({ d with
          workTapePos := Function.update d.workTapePos (h1TableTape k)
            (d.workTapePos (h1TableTape k) + (actionBitsK a).length) }) (h1SeekNext rank rest
              last) := by
    rw [show (actionBitsK a).length + 3 = ((actionBitsK a).length + 1 + 1) + 1 by omega,
      advance, hosted.2]
    apply Cfg.ext <;> simp [finish, h1SeekCfg, Cfg.mapState, hq]
  refine ⟨hend, ?_, ?_⟩
  · intro u hu
    cases u with
    | zero => simp [h1SeekCfg, Cfg.mapState, hq]
    | succ u =>
      rw [hpre u (by omega)]
      cases ((h1SkipTM k).runFrom start u).state <;> simp [Cfg.mapState, key]
  · intro u hu
    by_cases he : u = (actionBitsK a).length + 3
    · subst u
      rw [hend]
      exact ⟨rfl, rfl, rfl, fun j hj => by simp [h1SeekCfg, Cfg.mapState, hj]⟩
    · cases u with
      | zero => exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
      | succ u =>
        rw [hpre u (by omega)]
        have hf := (h1Skip_spec d a hq hw).2 u (by omega)
        refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
        intro j hj
        simpa [Cfg.mapState, hj] using hf.2.2.2 j

/-- Cost of skipping a sequence of whole records through the selector:
one skipper dispatch and two selector dispatches per record. -/
private def h1SeekCost {k n : ℕ} (records : List (Action k Bool (Fin (n + 1)))) : ℕ :=
  (records.flatMap actionBitsK).length + 3 * records.length

/-- A finite within-group countdown traverses exactly its list of whole
records. The table contents and the entire non-table data frame are preserved,
and the final router control is first reached only after the last record.

**Proof sketch.** Induct over the nonempty record list. The one-record public
host composition advances by that record's full bit length. The suffix reads
are the right-hand part of the same flat-map word. Add the exact costs; split
any intermediate horizon at the first completed call for the cut and frame. -/
private lemma h1Seek_many {k n : ℕ} {x : List Bool}
    (records : List (Action k Bool (Fin (n + 1)))) (hne : records ≠ [])
    (hlen : records.length ≤ 3 ^ (k + 1))
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (rank : Fin (3 ^ (k + 1))) (last : Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hw : ∀ (r : ℕ) (hr : r < (records.flatMap actionBitsK).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((records.flatMap actionBitsK)[r]'hr)) :
    let entry := h1SeekCtrl.request rank ⟨records.length - 1, by
      have := List.length_pos_iff.mpr hne; omega⟩ last
    let final := if last then h1SeekCtrl.done else .state rank
    (h1SeekTM k).runFrom (h1SeekCfg d entry) (h1SeekCost records) =
      h1SeekCfg ({d with
        workTapePos := Function.update d.workTapePos (h1TableTape k)
          (d.workTapePos (h1TableTape k) + (records.flatMap actionBitsK).length)}) final ∧
    (∀ u < h1SeekCost records,
      ((h1SeekTM k).runFrom (h1SeekCfg d entry) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ h1SeekCost records,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d entry) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1TableTape k → f.workTapePos j = d.workTapePos j) := by
  induction records generalizing d with
  | nil => exact False.elim (hne rfl)
  | cons a as ih =>
    dsimp only
    have parts := h1Reads_append (d.workTapes (h1TableTape k)) (d.workTapePos (h1TableTape k))
      (actionBitsK a) (as.flatMap actionBitsK) (by simpa only [List.flatMap_cons] using hw)
    have hfirstReads := parts.1
    have one := h1Seek_request d a rank
      ⟨(a :: as).length - 1, by simp only [List.length_cons] at *; omega⟩ last hq hfirstReads
    cases as with
    | nil =>
      simpa only [h1SeekCost, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.mul_one,
        h1SeekNext, Nat.add_sub_cancel, ↓reduceDIte, Nat.sub_zero] using one
    | cons b bs =>
      have bound : bs.length + 2 ≤ 3 ^ (k + 1) := by
        simpa only [List.length_cons, Nat.add_assoc] using hlen
      let ds : Cfg (k + 2) Bool (h1RecordState k) x :=
        {d with
          workTapePos := Function.update d.workTapePos (h1TableTape k)
            (d.workTapePos (h1TableTape k) + (actionBitsK a).length)}
      have htailReads : ∀ (r : ℕ) (hr : r < ((b :: bs).flatMap actionBitsK).length),
          ds.workTapes (h1TableTape k) (ds.workTapePos (h1TableTape k) + r) =
            some (((b :: bs).flatMap actionBitsK)[r]'hr) := by
        simpa only [ds, Function.update_self] using parts.2
      have recur := ih (by simp) (by simp only [List.length_cons] at *; omega)
        ds hq htailReads
      have hnext : h1SeekNext rank ⟨(a :: b :: bs).length - 1, by
          simp only [List.length_cons] at *; omega⟩ last =
          .request rank ⟨(b :: bs).length - 1, by simp only [List.length_cons] at *; omega⟩ last
            := by
        simp only [h1SeekNext, List.length_cons, Nat.add_sub_cancel, Nat.add_eq_zero_iff,
          Nat.one_ne_zero, and_false, ↓reduceDIte]
      rw [hnext] at one
      have hcost : h1SeekCost (a :: b :: bs) = (actionBitsK a).length + 3 + h1SeekCost (b :: bs)
        := by
        simp only [h1SeekCost, List.flatMap_cons, List.length_append, List.length_cons]
        omega
      have hend : (h1SeekTM k).runFrom (h1SeekCfg d (.request rank
          ⟨(a :: b :: bs).length - 1, by simp only [List.length_cons] at *; omega⟩ last))
          (h1SeekCost (a :: b :: bs)) =
          h1SeekCfg ({d with
            workTapePos := Function.update d.workTapePos (h1TableTape k)
              (d.workTapePos (h1TableTape k) + ((a :: b :: bs).flatMap actionBitsK).length)})
            (if last then .done else .state rank) := by
        rw [hcost, MultiTapeTM.runFrom_add, one.1]
        change (h1SeekTM k).runFrom (h1SeekCfg ds _) _ = _
        rw [recur.1]
        apply Cfg.ext <;> try rfl
        funext j
        by_cases hj : j = h1TableTape k
        · subst j
          simp [h1SeekCfg, Cfg.mapState, ds, List.length_flatMap, List.flatMap_cons,
            List.length_append, Nat.cast_add, add_assoc]
        · simp [h1SeekCfg, Cfg.mapState, ds, hj]
      refine ⟨hend, ?_, ?_⟩
      · intro u hu
        by_cases hl : u < (actionBitsK a).length + 3
        · exact one.2.1 u hl
        · have he : u = ((actionBitsK a).length + 3) + (u - ((actionBitsK a).length + 3)) := by
            omega
          rw [he, MultiTapeTM.runFrom_add, one.1]
          exact recur.2.1 _ (by omega)
      · intro u hu
        by_cases hl : u ≤ (actionBitsK a).length + 3
        · exact one.2.2 u hl
        · have he : u = ((actionBitsK a).length + 3) + (u - ((actionBitsK a).length + 3)) := by
            omega
          rw [he, MultiTapeTM.runFrom_add, one.1]
          have hf := recur.2.2 (u - ((actionBitsK a).length + 3)) (by omega)
          refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
          intro j hj
          simpa only [ds, Function.update_of_ne hj] using hf.2.2.2 j hj

/-- A unary-state router step either requests one complete state group and
advances the state head, or requests the finite read-rank suffix. -/
private lemma h1Seek_stateStep {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x) (rank : Fin (3 ^ (k + 1))) (b : Bool)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hs : d.workTapeSymbols (h1SummaryTape k) = some b) :
    (h1SeekTM k).step (h1SeekCfg d (.state rank)) =
      if b then
        h1SeekCfg ({d with
          workTapePos := Function.update d.workTapePos (h1SummaryTape k)
            (d.workTapePos (h1SummaryTape k) + 1)})
          (.request rank ⟨3 ^ (k + 1) - 1, by
            have hp : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega); omega⟩ false)
      else h1SeekCfg d (if hr : rank.val = 0 then .done
        else .request rank ⟨rank.val - 1, by have := rank.isLt; omega⟩ true) := by
  simp only [Cfg.workTapeSymbols] at hs
  cases b <;>
    apply Cfg.ext <;>
    simp [MultiTapeTM.step, h1SeekTM, h1SeekCfg, Cfg.mapState, phaseHostTM,
      h1SeekRed, h1SeekPart, h1SeekRouter, hq, Cfg.workTapeSymbols, hs, tapeAction,
        inputMoveAction, Action.mapState]
  all_goals
    funext j
    by_cases hj : j = h1SummaryTape k
    · subst j; simp
    · simp [hj]

/-- At the unary terminator, the selector skips exactly the read rank.
This includes rank zero: the router's single silent step exits immediately. -/
private lemma h1Seek_rank {k n : ℕ} {x : List Bool}
    (records : List (Action k Bool (Fin (n + 1))))
    (d : Cfg (k + 2) Bool (h1RecordState k) x) (rank : Fin (3 ^ (k + 1)))
    (hlen : records.length = rank.val)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hs : d.workTapeSymbols (h1SummaryTape k) = some false)
    (hw : ∀ (r : ℕ) (hr : r < (records.flatMap actionBitsK).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((records.flatMap actionBitsK)[r]'hr)) :
    (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) (1 + h1SeekCost records) =
      h1SeekCfg ({d with
        workTapePos := Function.update d.workTapePos (h1TableTape k)
          (d.workTapePos (h1TableTape k) + (records.flatMap actionBitsK).length)}) .done ∧
    (∀ u < 1 + h1SeekCost records,
      ((h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ 1 + h1SeekCost records,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1TableTape k → f.workTapePos j = d.workTapePos j) := by
  have step := h1Seek_stateStep d rank false hq hs
  simp only [Bool.false_eq_true, ↓reduceIte] at step
  by_cases hn : records = []
  · subst records
    have hz : rank.val = 0 := hlen.symm
    simp only [hz, ↓reduceDIte] at step
    have he : (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) 1 = h1SeekCfg d .done := step
    simp only [h1SeekCost, List.flatMap_nil, List.length_nil, Nat.mul_zero,
      Nat.cast_zero, add_zero, Function.update_eq_self]
    refine ⟨he, ?_, ?_⟩
    · intro u hu
      have hu0 : u = 0 := by omega
      simp [hu0, h1SeekCfg, Cfg.mapState, hq]
    · intro u hu
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
      · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
      · rw [he]
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  · have hp : 0 < rank.val := by rw [← hlen]; exact List.length_pos_iff.mpr hn
    simp only [show rank.val ≠ 0 by omega, ↓reduceDIte] at step
    have spec := h1Seek_many records hn (by rw [hlen]; exact Nat.le_of_lt rank.isLt)
      d rank true hq hw
    dsimp only at spec
    simp only [↓reduceIte] at spec
    have hm : (⟨rank.val - 1, by have := rank.isLt; omega⟩ : Fin (3 ^ (k + 1))) =
        ⟨records.length - 1, by have := rank.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
    rw [hm] at step
    have advance (u : ℕ) := MultiTapeTM.runFrom_succ_eq_step (tm := h1SeekTM k)
      (cfg := h1SeekCfg d (.state rank)) (t := u)
    rw [step] at advance
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.add_comm 1, advance]
      exact spec.1
    · intro u hu
      cases u with
      | zero => simp [h1SeekCfg, Cfg.mapState, hq]
      | succ u =>
        rw [advance u]
        exact spec.2.1 u (by omega)
    · intro u hu
      cases u with
      | zero => exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
      | succ u =>
        rw [advance u]
        exact spec.2.2 u (by omega)

/-- The two auxiliary head advances accumulated by lookup. All mirrored
heads and every tape cell remain in the original arbitrary frame. -/
private def h1SeekShift {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x) (table state : ℕ) :
    Cfg (k + 2) Bool (h1RecordState k) x :=
  {d with workTapePos := fun j => d.workTapePos j +
    if j = h1TableTape k then (table : ℤ) else if j = h1SummaryTape k then (state : ℤ) else 0}

/-- Unary-state lookup traverses one complete group per true and then the
read-rank suffix. The result is the selected record boundary, with the state
head on its false terminator. This is a single physical selector for all
state counts and arbitrary source data frames.

**Proof sketch.** Induct on the list of complete state groups. A true takes
one state-head step and invokes the proved finite countdown over that group.
Its returning exit continues the induction. At the false terminator use the
rank contract, including rank zero. Costs are the exact sum of these calls. -/
private lemma h1Seek_groups {k n : ℕ} {x : List Bool}
    (groups : List (List (Action k Bool (Fin (n + 1)))))
    (rest : List (Action k Bool (Fin (n + 1))))
    (rank : Fin (3 ^ (k + 1)))
    (hg : ∀ g ∈ groups, g.length = 3 ^ (k + 1)) (hrank : rest.length = rank.val)
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hs : ∀ r ≤ groups.length,
      d.workTapes (h1SummaryTape k) (d.workTapePos (h1SummaryTape k) + r) =
        some (decide (r < groups.length)))
    (hw : ∀ (r : ℕ) (hr : r < ((groups.flatten ++ rest).flatMap actionBitsK).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some (((groups.flatten ++ rest).flatMap actionBitsK)[r]'hr)) :
    let records := groups.flatten ++ rest
    let T := groups.length + 1 + h1SeekCost records
    (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) T =
      h1SeekCfg (h1SeekShift d (records.flatMap actionBitsK).length groups.length) .done ∧
    (∀ u < T, ((h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ T,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1TableTape k → j ≠ h1SummaryTape k → f.workTapePos j = d.workTapePos j) := by
  induction groups generalizing d with
  | nil =>
    have hs0 : d.workTapeSymbols (h1SummaryTape k) = some false := by
      simpa [Cfg.workTapeSymbols] using hs 0 (by simp)
    have run := h1Seek_rank rest d rank hrank hq hs0 (by simpa using hw)
    dsimp only
    simp only [List.flatten_nil, List.nil_append, List.length_nil, Nat.zero_add]
    refine ⟨run.1.trans ?_, run.2.1, ?_⟩
    · apply Cfg.ext <;> try rfl
      funext j
      by_cases hj : j = h1TableTape k <;> simp [h1SeekCfg, Cfg.mapState, h1SeekShift, hj]
    · intro u hu
      have frame := run.2.2 u hu
      exact ⟨frame.1, frame.2.1, frame.2.2.1, fun j hj _ => frame.2.2.2 j hj⟩
  | cons g gs ih =>
    have glen := hg g (by simp)
    have gp : g ≠ [] := by
      have pos : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega)
      intro bad; simp [bad] at glen; omega
    have parts := h1Reads_append (d.workTapes (h1TableTape k)) (d.workTapePos (h1TableTape k))
      (g.flatMap actionBitsK) ((gs.flatten ++ rest).flatMap actionBitsK)
      (by simpa only [List.flatten_cons, List.flatMap_append, List.append_assoc] using hw)
    let next : Cfg (k + 2) Bool (h1RecordState k) x :=
      {d with
        workTapePos := Function.update d.workTapePos (h1SummaryTape k)
          (d.workTapePos (h1SummaryTape k) + 1)}
    have hs0 : d.workTapeSymbols (h1SummaryTape k) = some true := by
      simpa [Cfg.workTapeSymbols] using hs 0 (by simp)
    have step := h1Seek_stateStep d rank true hq hs0
    simp only [↓reduceIte] at step
    have calls := h1Seek_many g gp (by omega) next rank false hq (by
      simpa [next, Function.update_of_ne (Ne.symm (h1Summary_ne_table k))] using parts.1)
    dsimp only at calls
    simp only [Bool.false_eq_true, ↓reduceIte] at calls
    have count : (⟨3 ^ (k + 1) - 1, by
        have p : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega); omega⟩ : Fin (3 ^ (k + 1))) =
        ⟨g.length - 1, by have p := List.length_pos_iff.mpr gp; omega⟩ := by
      apply Fin.ext; dsimp only; omega
    rw [count] at step
    have advance (u : ℕ) := MultiTapeTM.runFrom_succ_eq_step (tm := h1SeekTM k)
      (cfg := h1SeekCfg d (.state rank)) (t := u)
    rw [step] at advance
    let later := h1SeekShift d (g.flatMap actionBitsK).length 1
    have seam : (h1SeekTM k).runFrom (h1SeekCfg d (.state rank)) (1 + h1SeekCost g) =
        h1SeekCfg later (.state rank) := by
      rw [Nat.add_comm 1, advance, calls.1]
      apply Cfg.ext <;> try rfl
      funext j
      by_cases ht : j = h1TableTape k
      · subst j
        simp [h1SeekCfg, Cfg.mapState, next, later, h1SeekShift, Ne.symm (h1Summary_ne_table k)]
      · by_cases hs : j = h1SummaryTape k
        · subst j
          simp [h1SeekCfg, Cfg.mapState, next, later, h1SeekShift, h1Summary_ne_table k]
        · simp [h1SeekCfg, Cfg.mapState, next, later, h1SeekShift, ht, hs]
    have laterState : ∀ r ≤ gs.length,
        later.workTapes (h1SummaryTape k) (later.workTapePos (h1SummaryTape k) + r) =
          some (decide (r < gs.length)) := by
      intro r hr
      have h := hs (r + 1) (by simp; omega)
      simpa only [later, h1SeekShift, h1Summary_ne_table k, ↓reduceIte,
        List.length_cons, Nat.add_lt_add_iff_right, Nat.cast_add, Nat.cast_one, add_assoc,
        add_comm (r : ℤ) 1] using h
    have laterReads : ∀ (r : ℕ) (hr : r < ((gs.flatten ++ rest).flatMap actionBitsK).length),
        later.workTapes (h1TableTape k) (later.workTapePos (h1TableTape k) + r) =
          some (((gs.flatten ++ rest).flatMap actionBitsK)[r]'hr) := by
      simpa only [later, h1SeekShift, ↓reduceIte] using parts.2
    have recur := ih (fun h hh => hg h (by simp [hh])) later hq laterState laterReads
    dsimp only at recur ⊢
    have cost : (g :: gs).length + 1 + h1SeekCost (((g :: gs).flatten ++ rest)) =
        (1 + h1SeekCost g) + (gs.length + 1 + h1SeekCost (gs.flatten ++ rest)) := by
      simp only [h1SeekCost, List.length_cons, List.flatten_cons, List.flatMap_append,
        List.length_append]
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [cost, MultiTapeTM.runFrom_add, seam, recur.1]
      apply Cfg.ext <;> try rfl
      funext j
      by_cases ht : j = h1TableTape k
      · subst j
        simp [h1SeekCfg, Cfg.mapState, h1SeekShift, later, List.flatten_cons,
          List.flatMap_append, List.length_append, Nat.cast_add, add_assoc]
      · by_cases hj : j = h1SummaryTape k
        · subst j
          simp [h1SeekCfg, Cfg.mapState, h1SeekShift, later, h1Summary_ne_table k,
            Nat.cast_add, add_assoc, add_comm, List.length_cons]
        · simp [h1SeekCfg, Cfg.mapState, h1SeekShift, later, ht, hj]
    · intro u hu
      by_cases first : u < 1 + h1SeekCost g
      · cases u with
        | zero => simp [h1SeekCfg, Cfg.mapState, hq]
        | succ u =>
          rw [advance u]
          exact calls.2.1 u (by omega)
      · rw [show u = (1 + h1SeekCost g) + (u - (1 + h1SeekCost g)) by omega,
          MultiTapeTM.runFrom_add, seam]
        exact recur.2.1 _ (by omega)
    · intro u hu
      by_cases first : u ≤ 1 + h1SeekCost g
      · cases u with
        | zero => exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
        | succ u =>
          rw [advance u]
          have frame := calls.2.2 u (by omega)
          refine ⟨frame.1, frame.2.1, frame.2.2.1, ?_⟩
          intro j ht hs
          simpa only [next, Function.update_of_ne hs] using frame.2.2.2 j ht
      · rw [show u = (1 + h1SeekCost g) + (u - (1 + h1SeekCost g)) by omega,
          MultiTapeTM.runFrom_add, seam]
        have frame := recur.2.2 (u - (1 + h1SeekCost g)) (by omega)
        refine ⟨frame.1, frame.2.1, frame.2.2.1, ?_⟩
        intro j ht hs
        simpa only [later, h1SeekShift, if_neg ht, if_neg hs, add_zero] using frame.2.2.2 j ht hs

/-- Capture the finite read rank and enter the unary state word in two
silent moves of the auxiliary head. All mirrored heads stay fixed. -/
private lemma h1Seek_observe {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (hq : d.state = some (h1RecordTM k).q₀) :
    let rank := h1ReadRank d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))
    (h1SeekTM k).runFrom (h1SeekCfg d .observe) 2 =
      h1SeekCfg (h1SeekShift d 0 2) (.state rank) ∧
    (∀ u < 2, ((h1SeekTM k).runFrom (h1SeekCfg d .observe) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ 2,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d .observe) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1SummaryTape k → f.workTapePos j = d.workTapePos j) := by
  let rank := h1ReadRank d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))
  let next : Cfg (k + 2) Bool (h1RecordState k) x :=
    {d with
      workTapePos := Function.update d.workTapePos (h1SummaryTape k)
        (d.workTapePos (h1SummaryTape k) + 1)}
  have first : (h1SeekTM k).step (h1SeekCfg d .observe) = h1SeekCfg next (.advance rank) := by
    rw [step_of_tapeAction_move (h1SeekTM k) (h1SeekCfg d .observe)
      (q := ⟨none, .observe⟩) (q' := ⟨none, .advance rank⟩) (h1SummaryTape k) 0 .pos
      (by simp [h1SeekCfg, Cfg.mapState, hq]) (by rfl)]
    apply Cfg.ext <;> simp [h1SeekCfg, Cfg.mapState, next, hq]
  have second : (h1SeekTM k).step (h1SeekCfg next (.advance rank)) =
      h1SeekCfg (h1SeekShift d 0 2) (.state rank) := by
    rw [step_of_tapeAction_move (h1SeekTM k) (h1SeekCfg next (.advance rank))
      (q := ⟨none, .advance rank⟩) (q' := ⟨none, .state rank⟩) (h1SummaryTape k) 0 .pos
      (by simp [h1SeekCfg, Cfg.mapState, next, hq]) (by rfl)]
    apply Cfg.ext <;> try simp [h1SeekCfg, Cfg.mapState, next, hq, h1SeekShift]
    funext j
    by_cases hj : j = h1SummaryTape k
    · subst j
      simp [h1Summary_ne_table k, add_assoc]
    · by_cases ht : j = h1TableTape k
      · subst j
        simp [Ne.symm (h1Summary_ne_table k)]
      · simp [hj, ht]
  have run : (h1SeekTM k).runFrom (h1SeekCfg d .observe) 2 =
      h1SeekCfg (h1SeekShift d 0 2) (.state rank) := by
    change (h1SeekTM k).step ((h1SeekTM k).step _) = _
    rw [first, second]
  refine ⟨run, ?_, ?_⟩
  · intro u hu
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · simp [h1SeekCfg, Cfg.mapState, hq]
    · change ((h1SeekTM k).step _).state ≠ _
      rw [first]
      simp [h1SeekCfg, Cfg.mapState, next, hq]
  · intro u hu
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 by omega) with rfl | rfl | rfl
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    · rw [show (h1SeekTM k).runFrom (h1SeekCfg d .observe) 1 = h1SeekCfg next (.advance rank)
      from first]
      exact ⟨rfl, rfl, rfl, fun j hj => by simp [h1SeekCfg, Cfg.mapState, next, hj]⟩
    · rw [run]
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro j hj
      simp [h1SeekCfg, Cfg.mapState, h1SeekShift, hj]

/-- One state's ordered action list, before serialization. -/
private def h1ReadActions {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) : List (Action k Bool (Fin (n + 1))) :=
  (workReadsK k).map (tr q none) ++
    ((workReadsK k).map (tr q (some false)) ++ (workReadsK k).map (tr q (some true)))

/-- Every state group has the same finite number of read vectors. -/
private lemma h1ReadActions_length {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) : (h1ReadActions tr q).length = 3 ^ (k + 1) := by
  simp [h1ReadActions, h1WorkReads_length, Nat.pow_succ]
  omega

/-- The finite rank used by the physical router selects the serializer's
actual input/work-read record, including the tape-zero-first work ordering. -/
private lemma h1ReadActions_at {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) (inp : Option Bool) (w : Fin k → Option Bool) :
    (h1ReadActions tr q)[(h1ReadRank inp w).val]'(by
      rw [h1ReadActions_length]; exact (h1ReadRank inp w).isLt) = tr q inp w := by
  have hidx : (workReadsK k).idxOf w < (workReadsK k).length :=
    List.idxOf_lt_length_iff.mpr (h1WorkReads_mem k w)
  have hmap (a : Option Bool) :
      ((workReadsK k).map (tr q a))[(workReadsK k).idxOf w]'(by simpa using hidx) = tr q a w := by
    rw [List.getElem_map, List.getElem_idxOf hidx]
  have lens (a : Option Bool) : ((workReadsK k).map (tr q a)).length = 3 ^ k := by
    simp only [List.length_map, h1WorkReads_length]
  cases inp with
  | none =>
    simp only [h1ReadActions,
      h1ReadRank, h1InputRank, h1WorkRank, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
    rw [List.getElem_append_left (by simpa only [List.length_map] using hidx)]
    exact hmap none
  | some b =>
    cases b with
    | false =>
      simp only [h1ReadActions,
        h1ReadRank, h1InputRank, h1WorkRank, Fin.val_one, Nat.one_mul]
      rw [List.getElem_append_right (by rw [lens]; omega)]
      simp only [lens, Nat.add_sub_cancel_left]
      rw [List.getElem_append_left (by simpa only [List.length_map] using hidx)]
      exact hmap (some false)
    | true =>
      simp only [h1ReadActions,
        h1ReadRank, h1InputRank, h1WorkRank]
      rw [List.getElem_append_right (by rw [lens]; omega)]
      simp only [lens]
      rw [List.getElem_append_right (by rw [lens]; omega)]
      have hi : (2 * 3 ^ k + (workReadsK k).idxOf w - 3 ^ k - 3 ^ k) = (workReadsK k).idxOf w :=
        by omega
      simpa only [lens, show ((2 : Fin 3) : ℕ) = 2 from rfl, hi] using hmap (some true)

/-- The public table writer is the serialization of these state groups. -/
private lemma h1Table_groups {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1))) :
    tableBitsK tr = ((List.finRange (n + 1)).flatMap (h1ReadActions tr)).flatMap actionBitsK := by
  simp only [tableBitsK, h1ReadActions, List.flatMap_assoc, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append]

/-- Exact decomposition of the public table around a source transition.
The selector skips `q` complete state groups followed by the captured read
rank. This identifies the next record without any assumption about constant
successor widths. -/
private lemma h1Table_cut {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) (inp : Option Bool) (w : Fin k → Option Bool) :
    ∃ (groups : List (List (Action k Bool (Fin (n + 1)))))
        (rest : List (Action k Bool (Fin (n + 1)))) (tail : List Bool),
      groups.length = q.val ∧
      (∀ g ∈ groups, g.length = 3 ^ (k + 1)) ∧
      rest.length = (h1ReadRank inp w).val ∧
      tableBitsK tr = ((groups.flatten ++ rest).flatMap actionBitsK) ++ actionBitsK (tr q inp w) ++ tail := by
  let states := List.finRange (n + 1)
  let r := (h1ReadRank inp w).val
  let reads := h1ReadActions tr q
  have qs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons (by simp [states])] at h
    simpa only [states, List.getElem_finRange, Fin.eta] using h.symm
  have rlt : r < reads.length := by
    dsimp [r, reads]
    rw [h1ReadActions_length]
    exact (h1ReadRank inp w).isLt
  have rs : reads = reads.take r ++ tr q inp w :: reads.drop (r + 1) := by
    have h := List.take_append_drop r reads
    rw [List.drop_eq_getElem_cons rlt] at h
    simpa only [reads, r, h1ReadActions_at] using h.symm
  refine ⟨(states.take q.val).map (h1ReadActions tr), reads.take r,
    (reads.drop (r + 1) ++ (states.drop (q.val + 1)).flatMap (h1ReadActions tr)).flatMap
      actionBitsK,
    ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, states, List.length_finRange]
    exact min_eq_left (by omega)
  · intro g hg
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
    exact h1ReadActions_length tr a
  · simp only [List.length_take, min_eq_left (Nat.le_of_lt rlt)]
    rfl
  · rw [h1Table_groups]
    change (states.flatMap (h1ReadActions tr)).flatMap actionBitsK = _
    conv_lhs => rw [qs]
    simp only [List.flatMap_append, List.flatMap_cons]
    change _ ++ (reads.flatMap actionBitsK ++ _) = _
    conv_lhs => rw [rs]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc, ← List.flatMap_def]

/-- A literal record list has at least as many bits as records. This is a
consequence of the public action-length bound, with no table re-encoding. -/
private lemma h1Records_length {k n : ℕ} (records : List (Action k Bool (Fin (n + 1)))) :
    records.length ≤ (records.flatMap actionBitsK).length := by
  induction records with
  | nil => simp
  | cons a as ih =>
    have hp := codeActionK_length a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- A unit work-head bound summed over a run. This is the only general
head-bound argument needed for the auxiliary round envelope; mirrored and
input heads have the stronger exact phase equations.
**Promotion candidate:** a run form of `workTapePos_step_le`. -/
private lemma h1Run_headBound {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (d : Cfg m Bool S x) (t : ℕ) (j : Fin m) :
    |(M.runFrom d t).workTapePos j - d.workTapePos j| ≤ (t : ℤ) := by
  let height (u : ℕ) := (M.runFrom d u).workTapePos j
  have unit (u : ℕ) : |height (u + 1) - height u| ≤ 1 := by
    simpa only [height, MultiTapeTM.runFrom_succ_eq_step'] using
      MultiTapeTM.workTapePos_step_le (tm := M) (M.runFrom d u) j
  calc
    |(M.runFrom d t).workTapePos j - d.workTapePos j| =
        |∑ u ∈ Finset.range t, (height (u + 1) - height u)| := by
      rw [Finset.sum_range_sub]; rfl
    _ ≤ ∑ u ∈ Finset.range t, |height (u + 1) - height u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ Finset.range t, (1 : ℤ) := Finset.sum_le_sum (fun u _ => unit u)
    _ = (t : ℤ) := by simp

/-- Any machine whose actions keep the native input fixed preserves its
position at every horizon. Public iteration transport supplies the run law. -/
private lemma h1Run_input {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (h : ∀ q inp work, (M.tr q inp work).inputTape = 0)
    (d : Cfg m Bool S x) (t : ℕ) : (M.runFrom d t).inputPos = d.inputPos := by
  have commute : Function.Semiconj (fun e : Cfg m Bool S x => e.inputPos) M.step id := by
    intro e
    cases hs : e.state with
    | none => simp [MultiTapeTM.step, hs]
    | some q => simp [MultiTapeTM.step, hs, h]
  simpa only [MultiTapeTM.runFrom, Function.iterate_id, id_eq] using commute.iterate_right t d

/-- Exact number of records in a prefix of complete state groups and one
partial read group. This is only a list-length ledger. -/
private lemma h1Groups_length {k n : ℕ}
    (groups : List (List (Action k Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 3 ^ (k + 1)) :
    groups.flatten.length = groups.length * 3 ^ (k + 1) := by
  induction groups with
  | nil => simp
  | cons g gs ih =>
    have h := ih (fun a ha => hg a (by simp [ha]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul,
      Nat.one_mul, hg g (by simp), h]
    omega

/-- Whole physical lookup, including finite observation and the unary-state
loop. Its exit is first reached at the selected record boundary. The native
input, all tape cells, physical output, and mirrored heads are unchanged. -/
private lemma h1Seek_lookup {k n : ℕ} {x : List Bool}
    (groups : List (List (Action k Bool (Fin (n + 1)))))
    (rest : List (Action k Bool (Fin (n + 1))))
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (hg : ∀ g ∈ groups, g.length = 3 ^ (k + 1))
    (hrank : rest.length = (h1ReadRank d.inputSymbol
      (fun i => d.workTapeSymbols (Fin.castAdd 2 i))).val)
    (hq : d.state = some (h1RecordTM k).q₀)
    (hs : ∀ r ≤ groups.length,
      d.workTapes (h1SummaryTape k) (d.workTapePos (h1SummaryTape k) + 2 + r) =
        some (decide (r < groups.length)))
    (hw : ∀ (r : ℕ) (hr : r < ((groups.flatten ++ rest).flatMap actionBitsK).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some (((groups.flatten ++ rest).flatMap actionBitsK)[r]'hr)) :
    let records := groups.flatten ++ rest
    let T := groups.length + 3 + h1SeekCost records
    (h1SeekTM k).runFrom (h1SeekCfg d .observe) T =
      h1SeekCfg (h1SeekShift d (records.flatMap actionBitsK).length (groups.length + 2)) .done ∧
    (∀ u < T, ((h1SeekTM k).runFrom (h1SeekCfg d .observe) u).state ≠ some ⟨none, .done⟩) ∧
    (∀ u ≤ T,
      let f := (h1SeekTM k).runFrom (h1SeekCfg d .observe) u
      f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
      ∀ j, j ≠ h1TableTape k → j ≠ h1SummaryTape k → f.workTapePos j = d.workTapePos j) ∧
    T ≤ 5 * (records.flatMap actionBitsK).length + 3 := by
  let rank := h1ReadRank d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))
  have introRun := h1Seek_observe d hq
  have bodyRun := h1Seek_groups groups rest rank hg hrank (h1SeekShift d 0 2) hq
    (by simpa [h1SeekShift, h1Summary_ne_table k] using hs)
    (by simpa [h1SeekShift] using hw)
  dsimp only at introRun bodyRun ⊢
  have cost : groups.length + 3 + h1SeekCost (groups.flatten ++ rest) =
      2 + (groups.length + 1 + h1SeekCost (groups.flatten ++ rest)) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cost, MultiTapeTM.runFrom_add, introRun.1, bodyRun.1]
    apply Cfg.ext <;> try rfl
    funext j
    by_cases ht : j = h1TableTape k
    · subst j
      simp [h1SeekCfg, Cfg.mapState, h1SeekShift]
    · by_cases hj : j = h1SummaryTape k
      · subst j
        simp [h1SeekCfg, Cfg.mapState, h1SeekShift, h1Summary_ne_table k, Nat.cast_add,
          add_assoc, add_comm]
      · simp [h1SeekCfg, Cfg.mapState, h1SeekShift, ht, hj]
  · intro u hu
    by_cases hi : u < 2
    · exact introRun.2.1 u hi
    · rw [show u = 2 + (u - 2) by omega, MultiTapeTM.runFrom_add, introRun.1]
      exact bodyRun.2.1 _ (by omega)
  · intro u hu
    by_cases hi : u ≤ 2
    · have frame := introRun.2.2 u hi
      exact ⟨frame.1, frame.2.1, frame.2.2.1, fun j _ hj => frame.2.2.2 j hj⟩
    · rw [show u = 2 + (u - 2) by omega, MultiTapeTM.runFrom_add, introRun.1]
      have frame := bodyRun.2.2 (u - 2) (by omega)
      refine ⟨frame.1, frame.2.1, frame.2.2.1, ?_⟩
      intro j ht hj
      simpa only [h1SeekShift, if_neg ht, if_neg hj, add_zero] using frame.2.2.2 j ht hj
  · have hrecord := h1Records_length (groups.flatten ++ rest)
    have hgroup : groups.length ≤ (groups.flatten ++ rest).length := by
      have ht := h1Groups_length groups hg
      have hp : 1 ≤ 3 ^ (k + 1) := by have : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega); omega
      have hm := Nat.mul_le_mul_left groups.length hp
      simp only [Nat.mul_one] at hm
      simp only [List.length_append]
      omega
    unfold h1SeekCost
    omega

/-- Read a unary state word at any valid cell, including its terminating
false. This uses the canonical buffer convention directly. -/
private lemma h1Unary_read (q r : ℕ) (hr : r ≤ q) :
    FinTM.bufferTape (List.replicate q true ++ [false]) r = some (decide (r < q)) := by
  by_cases hlt : r < q
  · rw [FinTM.bufferTape_nat, List.getElem?_append_left (by simpa only [List.length_replicate]
    using hlt)]
    simp [hlt]
  · have he : r = q := by omega
    subst r
    simp [FinTM.bufferTape_nat]

/-- The summary auxiliary stores its stationary summary at zero, a blank
at one, and the current unary state word starting at two. -/
private def h1SummaryState (summary : Option Bool) (word : List Bool) (z : ℤ) : Option Bool :=
  if z = 0 then summary else FinTM.bufferTape word (z - 2)

/-- The state word and its left delimiter are a framed ordinary buffer,
separated from the summary cell. -/
private lemma h1SummaryState_cell (summary : Option Bool) (word : List Bool) (z : ℤ) (hz : -1 ≤ z) :
    h1SummaryState summary word (2 + z) = FinTM.bufferTape word z := by
  have hne : 2 + z ≠ 0 := by omega
  simp [h1SummaryState, hne]

/-- Updating the summary does not disturb the state word. -/
private lemma h1SummaryState_update (summary next : Option Bool) (word : List Bool) :
    Function.update (h1SummaryState summary word) 0 next = h1SummaryState next word := by
  funext z
  by_cases hz : z = 0
  · subst z; simp [h1SummaryState]
  · simp [h1SummaryState, hz]

/-- The canonical buffer is blank off its finite support. -/
private lemma h1Buffer_outside (word : List Bool) (z : ℤ)
    (hz : ¬(0 ≤ z ∧ z < word.length)) : FinTM.bufferTape word z = none := by
  by_cases hn : 0 ≤ z
  · simp only [FinTM.bufferTape, if_pos hn]
    exact List.getElem?_eq_none_iff.mpr (by omega)
  · simp [FinTM.bufferTape, hn]

/-- Copying a complete new state word into the cleared state region yields
exactly the next summary/state layout. -/
private lemma h1SummaryState_copy (summary : Option Bool) (word : List Bool) :
    (fun z : ℤ => if 2 ≤ z ∧ z < 2 + word.length then FinTM.bufferTape word (z - 2)
      else h1SummaryState summary [] z) = h1SummaryState summary word := by
  funext z
  by_cases hz : z = 0
  · subst z; simp [h1SummaryState]
  · by_cases hinside : 2 ≤ z ∧ z < 2 + word.length
    · simp [hinside, h1SummaryState, hz]
    · have off := h1Buffer_outside word (z - 2) (by omega)
      simp [hinside, h1SummaryState, hz, off]

/-- The catalog's framed clear erases only the state word, preserving the
stationary summary and its blank separator. -/
private lemma h1SummaryState_clear (summary : Option Bool) (word : List Bool) :
    (fun z : ℤ => if 2 ≤ z ∧ z < 2 + word.length then none else h1SummaryState summary word z) =
      h1SummaryState summary [] := by
  funext z
  rw [← h1SummaryState_copy summary word]
  by_cases hi : 2 ≤ z ∧ z < 2 + word.length
  · have hz : z ≠ 0 := by omega
    simp [hi, h1SummaryState, hz]
  · simp [hi]

/-- Lookup selects the actual source transition in the public table.
The physical input/work reads determine the finite rank. The returned table
prefix contains at least `q` bits, a useful state-head and clearing ledger.

**Proof sketch.** Cut the serializer at the ranked source transition. Feed
its literal prefix and unary state word to the proved physical selector.
The fixed group-size identity and the public action-length bound pay for the
unary state scan, and the exact table cut bounds the whole lookup. -/
private lemma h1Seek_select {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) (summary : Option Bool)
    (d : Cfg (k + 2) Bool (h1RecordState k) x)
    (hq : d.state = some (h1RecordTM k).q₀)
    (ht : d.workTapes (h1TableTape k) = FinTM.bufferTape (tableBitsK tr))
    (hp : d.workTapePos (h1TableTape k) = 0)
    (hs : d.workTapes (h1SummaryTape k) = h1SummaryState summary (unaryFin q))
    (hsp : d.workTapePos (h1SummaryTape k) = 0) :
    let a := tr q d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))
    ∃ (pre tail : List Bool) (T : ℕ),
      tableBitsK tr = pre ++ actionBitsK a ++ tail ∧ q.val ≤ pre.length ∧
      0 < T ∧ T ≤ 5 * (tableBitsK tr).length + 3 ∧
      (h1SeekTM k).runFrom (h1SeekCfg d .observe) T =
        h1SeekCfg (h1SeekShift d pre.length (q.val + 2)) .done ∧
      (∀ u < T, ((h1SeekTM k).runFrom (h1SeekCfg d .observe) u).state ≠ some ⟨none, .done⟩) ∧
      (∀ u ≤ T,
        let f := (h1SeekTM k).runFrom (h1SeekCfg d .observe) u
        f.inputPos = d.inputPos ∧ f.workTapes = d.workTapes ∧ f.output = d.output ∧
        ∀ j, j ≠ h1TableTape k → j ≠ h1SummaryTape k → f.workTapePos j = d.workTapePos j) := by
  dsimp only
  obtain ⟨groups, rest, tail, hglen, hgroup, hrank, split⟩ :=
    h1Table_cut tr q d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))
  let records := groups.flatten ++ rest
  let pre := records.flatMap actionBitsK
  have full : ∀ (r : ℕ) (hr : r < (tableBitsK tr).length),
      d.workTapes (h1TableTape k) (d.workTapePos (h1TableTape k) + r) =
        some ((tableBitsK tr)[r]'hr) := by
    intro r hr
    simp [ht, hp, FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
  have words := h1Reads_append (d.workTapes (h1TableTape k)) (d.workTapePos (h1TableTape k))
    pre (actionBitsK (tr q d.inputSymbol (fun i => d.workTapeSymbols (Fin.castAdd 2 i))) ++ tail)
    (by simpa only [split, List.append_assoc] using full)
  have stateReads : ∀ r ≤ groups.length,
      d.workTapes (h1SummaryTape k) (d.workTapePos (h1SummaryTape k) + 2 + r) =
        some (decide (r < groups.length)) := by
    intro r hr
    rw [hs, hsp, zero_add, h1SummaryState_cell _ _ _ (by omega)]
    simpa only [unaryFin, hglen] using h1Unary_read q.val r (by omega)
  have run := h1Seek_lookup groups rest d hgroup hrank hq stateReads words.1
  dsimp only at run
  have gl := h1Groups_length groups hgroup
  have recordsBound := h1Records_length records
  have groupBound : groups.length ≤ records.length := by
    have p : 1 ≤ 3 ^ (k + 1) := by have : 0 < 3 ^ (k + 1) := Nat.pow_pos (by omega); omega
    have h := Nat.mul_le_mul_left groups.length p
    simp only [Nat.mul_one] at h
    dsimp [records]
    simp only [List.length_append]
    omega
  have preBound : pre.length ≤ (tableBitsK tr).length := by
    rw [split]
    simp only [List.length_append]
    dsimp [pre, records]
    omega
  dsimp only [pre, records] at preBound
  refine ⟨pre, tail, groups.length + 3 + h1SeekCost records, split, ?_, by omega,
    run.2.2.2.trans (by omega), ?_, run.2.1, run.2.2.1⟩
  · rw [← hglen]
    exact groupBound.trans recordsBound
  · simpa only [hglen] using run.1

/-- Fixed two-cell routing between the summary cell and its state word.
No parser or variable scan is involved. -/
private def h1TwoMoveTM {m : ℕ} (i : Fin m) (move : SignType) : MultiTapeTM m Bool (Fin 3) where
  q₀ := 0
  tr := fun q _ _ => if h : q.val < 2 then
    tapeAction i 0 none move ⟨q.val + 1, by omega⟩ else inputMoveAction 0 q

/-- Every prefix of the fixed two-cell routing move. The public one-action
movement law is sufficient; all cells, input and output are framed. -/
private lemma h1TwoMove_run {m : ℕ} {x : List Bool} (i : Fin m) (move : SignType)
    (d : Cfg m Bool (Fin 3) x) (hq : d.state = some 0) :
    ∀ (u : ℕ) (hu : u ≤ 2), (h1TwoMoveTM i move).runFrom d u =
      {d with
        state := some ⟨u, by omega⟩
        workTapePos := Function.update d.workTapePos i (d.workTapePos i + (u : ℤ) * move)} := by
  intro u hu
  induction u with
  | zero =>
    apply Cfg.ext <;> simp [hq]
  | succ u ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [step_of_tapeAction_move (h1TwoMoveTM i move) _ (q := ⟨u, by omega⟩)
      (q' := ⟨u + 1, by omega⟩) i 0 move rfl (by simp [h1TwoMoveTM, show u < 2 by omega])]
    apply Cfg.ext <;> simp [Function.update_idem, Nat.cast_add, add_mul, add_assoc]

/-- The selector's phase carriers are finite and have decidable equality. -/
private instance h1SeekPh_finite (k : ℕ) (key : h1SeekKey k) : Fintype (h1SeekPh k key) := by
  cases key <;> dsimp [h1SeekPh] <;> infer_instance

/-- Equality of selector phase states uses their finite carrier instances. -/
private instance h1SeekPh_decidable (k : ℕ) (key : h1SeekKey k) : DecidableEq (h1SeekPh k key) := by
  cases key <;> dsimp [h1SeekPh] <;> infer_instance

/-- The finite schedule of one generic simulated transition. The live bit
is retained only while restoring the heads after the successor was read. -/
private inductive h1RoundKey where
  | entry | lookup | stateTail | stateHome | clearState | toSummary | record | toState | successor
  | tableTail (live : Bool) | tableHome (live : Bool)
  | stateGap (live : Bool) | stateRestore (live : Bool) | finish (live : Bool)
  | halt
  deriving DecidableEq, Fintype

/-- The round's phase carriers, all independent of the coded state count. -/
private abbrev h1RoundPh (k : ℕ) : h1RoundKey → Type
  | .entry | .halt => Unit
  | .lookup => Σ key, h1SeekPh k key
  | .stateTail | .stateHome | .tableTail _ | .tableHome _ | .stateGap _ | .stateRestore _ => SeekPhase
  | .clearState => SweepPhase
  | .toSummary | .toState | .finish _ => Fin 3
  | .record => h1RecordState k
  | .successor => h1SuccPhase

/-- All variable scans use their landed catalog machines. A table rewind
first walks to the right delimiter, then uses `skipBackTM` on the whole word;
this avoids requiring blank separators between encoded records. -/
private def h1RoundPart (k : ℕ) : (key : h1RoundKey) → MultiTapeTM (k + 2) Bool (h1RoundPh k key)
  | .entry | .halt => ⟨(), fun _ _ _ => inputMoveAction 0 ()⟩
  | .lookup => h1SeekTM k
  | .stateTail | .stateGap _ => skipTM (k + 2) (h1SummaryTape k)
  | .stateHome | .stateRestore _ => skipBackTM (k + 2) (h1SummaryTape k)
  | .clearState => clearTM (k + 2) (h1SummaryTape k)
  | .toSummary | .finish _ => h1TwoMoveTM (h1SummaryTape k) .neg
  | .toState => h1TwoMoveTM (h1SummaryTape k) .pos
  | .record => h1RecordTM k
  | .successor => h1SuccTM (h1TableTape k) (h1SummaryTape k) true
  | .tableTail _ => skipTM (k + 2) (h1TableTape k)
  | .tableHome _ => skipBackTM (k + 2) (h1TableTape k)

/-- A completed live successor returns to the round anchor; a simulated
halt returns through a separate live exit. -/
private def h1RoundExit (k : ℕ) (live : Bool) : Σ key, h1RoundPh k key :=
  if live then ⟨.entry, ()⟩ else ⟨.halt, ()⟩

/-- The round's stationary, silent phase dispatches. A simulated halt goes
to a live physical exit only after the action and all restoration have run. -/
private def h1RoundRed (k : ℕ) : (key : h1RoundKey) → h1RoundPh k key → Option (Σ key, h1RoundPh k key)
  | .entry, _ => some ⟨.lookup, (h1SeekTM k).q₀⟩
  | .lookup, q => if q = ⟨none, .done⟩ then some ⟨.stateTail, .run⟩ else none
  | .stateTail, q => if q = .done then some ⟨.stateHome, .run⟩ else none
  | .stateHome, q => if q = .done then some ⟨.clearState, .sweep⟩ else none
  | .clearState, q => if q = .done then some ⟨.toSummary, 0⟩ else none
  | .toSummary, p => if p = 2 then some ⟨.record, (h1RecordTM k).q₀⟩ else none
  | .record, q => if q = none then some ⟨.toState, 0⟩ else none
  | .toState, p => if p = 2 then some ⟨.successor, .tag⟩ else none
  | .successor, .done live => some ⟨.tableTail live, .run⟩
  | .tableTail live, q => if q = .done then some ⟨.tableHome live, .run⟩ else none
  | .tableHome live, q => if q = .done then some ⟨.stateGap live, .run⟩ else none
  | .stateGap live, q => if q = .done then some ⟨.stateRestore live, .run⟩ else none
  | .stateRestore live, q => if q = .done then some ⟨.finish live, 0⟩ else none
  | .finish live, p => if p = 2 then some (h1RoundExit k live) else none
  | _, _ => none

/-- One generic step block: lookup, clear the old state, execute the fixed
payload, install its successor, and restore both auxiliary heads home.
**Promotion candidate (host H2, step block; machine-library-design.md §14).** -/
private def h1RoundTM (k : ℕ) : MultiTapeTM (k + 2) Bool (Σ key, h1RoundPh k key) :=
  phaseHostTM (h1RoundPart k) ⟨.entry, ()⟩ (h1RoundRed k)

/-- Finiteness of the round's physical control depends only on `k`. -/
private instance h1RoundPh_finite (k : ℕ) (key : h1RoundKey) : Fintype (h1RoundPh k key) := by
  cases key <;> dsimp [h1RoundPh] <;> infer_instance

/-- The round's entry and live halt exit have decidable equality. -/
private instance h1RoundPh_decidable (k : ℕ) (key : h1RoundKey) : DecidableEq (h1RoundPh k key) := by
  cases key <;> dsimp [h1RoundPh] <;> infer_instance

/-- The generic step block as a finite binary machine. -/
private def h1RoundFinTM (k : ℕ) : FinTM Bool where
  k := k + 2
  State := Σ key, h1RoundPh k key
  tm := h1RoundTM k

/-- Canonical data frame for a round phase. The mirrored bank may contain
arbitrary source tapes and positions, while the two auxiliary words and heads
are explicit. The physical output prefix is independent of simulated output. -/
private def h1Data {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (table : List Bool) (summary : Option Bool) (word : List Bool)
    (tablePos statePos : ℤ) (pre : List Bool) : Cfg (k + 2) Bool (h1RecordState k) x where
  state := some (h1RecordTM k).q₀
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes
    (fun i : Fin 2 => if i = 0 then FinTM.bufferTape table else h1SummaryState summary word)
  workTapePos := Fin.addCases c.workTapePos (fun i : Fin 2 => if i = 0 then tablePos else statePos)
  output := pre

/-- A mirrored tape is distinct from the summary/state auxiliary. -/
private lemma h1Mirror_ne_summary (k : ℕ) (i : Fin k) : Fin.castAdd 2 i ≠ h1SummaryTape k := by
  have hi := i.isLt
  apply Fin.ne_of_val_ne
  change i.val ≠ k + 1
  omega

/-- Lookup's two head advances preserve the canonical data frame. -/
private lemma h1Data_shift {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (table : List Bool) (summary : Option Bool) (word : List Bool)
    (tablePos statePos : ℤ) (pre : List Bool) (a b : ℕ) :
    h1SeekShift (h1Data c table summary word tablePos statePos pre) a b =
      h1Data c table summary word (tablePos + a) (statePos + b) pre := by
  apply Cfg.ext <;> try rfl
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [h1SeekShift, h1Data, h1Mirror_ne_table k i, h1Mirror_ne_summary k i]
  · fin_cases i <;> simp [h1SeekShift, h1Data, h1TableTape, h1SummaryTape]

/-- During a round every simulated head is at its start or its single
source-action endpoint. State renaming does not affect this predicate. -/
private def h1RoundWindow {k n : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool S x) : Prop :=
  (d.inputPos = c.inputPos ∨ d.inputPos = (a.apply c).inputPos) ∧
    ∀ i : Fin k, d.workTapePos (Fin.castAdd 2 i) = c.workTapePos i ∨
      d.workTapePos (Fin.castAdd 2 i) = (a.apply c).workTapePos i

/-- A canonical phase frame has the round's start heads or its end heads,
independently of both auxiliary positions and words. -/
private lemma h1Data_window {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (table : List Bool) (summary : Option Bool) (word : List Bool)
    (tablePos statePos : ℤ) (pre : List Bool) (after : Bool) :
    h1RoundWindow c a (h1Data (if after then a.apply c else c) table summary word tablePos statePos pre) := by
  cases after <;>
    simp [h1RoundWindow, h1Data]

/-- A segment of the already defined round host. Its strict prefix is live,
excludes both round anchors, and satisfies the simulated-head envelope. -/
private def h1RoundSpan {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (d e : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x) (T : ℕ) : Prop :=
  (h1RoundTM k).runFrom d T = e ∧
    ∀ u < T, ∃ s, ((h1RoundTM k).runFrom d u).state = some s ∧
      s ≠ ⟨.entry, ()⟩ ∧ s ≠ ⟨.halt, ()⟩ ∧
      h1RoundWindow c a ((h1RoundTM k).runFrom d u)

/-- Concatenate two proved segments by the public run-addition identity.
This lemma only joins their strict-prefix predicates; it defines no host,
loop, or alternative machine trace. -/
private lemma h1RoundSpan_add {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    {d e f : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x} {T U : ℕ}
    (left : h1RoundSpan c a d e T) (right : h1RoundSpan c a e f U) :
    h1RoundSpan c a d f (T + U) := by
  refine ⟨?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, left.1, right.1]
  · intro u hu
    by_cases hl : u < T
    · exact left.2 u hl
    · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add, left.1]
      exact right.2 _ (by omega)

/-- Lift one callee contract through the landed phase-host theorem. The
endpoint is one silent dispatch after the callee's first selected exit.
Liveness of every earlier callee state follows from halt absorption and its
proved live endpoint. No machine trace is re-established here. -/
private lemma h1Round_phase {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (key : h1RoundKey) (hentry : key ≠ .entry) (hhalt : key ≠ .halt)
    (d e : Cfg (k + 2) Bool (h1RoundPh k key) x) (T : ℕ)
    (run : (h1RoundPart k key).runFrom d T = e)
    (s : h1RoundPh k key) (hs : e.state = some s)
    (next : Σ key, h1RoundPh k key) (redirect : h1RoundRed k key s = some next)
    (guard : ∀ u < T, ∀ q, ((h1RoundPart k key).runFrom d u).state = some q → h1RoundRed k key q = none)
    (window : ∀ u ≤ T, h1RoundWindow c a ((h1RoundPart k key).runFrom d u)) :
    h1RoundSpan c a (d.mapState (Sigma.mk key)) (e.mapState (fun _ => next)) (T + 1) := by
  have transfer := phaseHostTM_run (h1RoundPart k) ⟨.entry, ()⟩ (h1RoundRed k)
    key d e T run s hs next redirect guard
  refine ⟨transfer.2, ?_⟩
  intro u hu
  rw [transfer.1 u (by omega)]
  have live : ((h1RoundPart k key).runFrom d u).state ≠ none := by
    intro stopped
    have freeze : (h1RoundPart k key).runFrom d T = (h1RoundPart k key).runFrom d u := by
      rw [show T = u + (T - u) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ stopped]
    have contradiction : e.state = none := by rw [← run, freeze]; exact stopped
    rw [hs] at contradiction
    contradiction
  cases reached : ((h1RoundPart k key).runFrom d u).state with
  | none => exact False.elim (live reached)
  | some q =>
    refine ⟨⟨key, q⟩, by simp [Cfg.mapState, reached], ?_, ?_, window u (by omega)⟩
    · intro bad; exact hentry (congrArg Sigma.fst bad)
    · intro bad; exact hhalt (congrArg Sigma.fst bad)

/-- Enter a round phase with the data frame unchanged. -/
private def h1At {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (h1RecordState k) x) (key : h1RoundKey) (q : h1RoundPh k key) :
    Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x :=
  d.mapState (fun _ => ⟨key, q⟩)

/-- Transfer the simulated-head predicate across any data frame equality.
Control types and auxiliary head positions may differ. -/
private lemma h1Window_frame {k n : ℕ} {S R : Type} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    {d : Cfg (k + 2) Bool S x} {e : Cfg (k + 2) Bool R x}
    (window : h1RoundWindow c a d) (input : e.inputPos = d.inputPos)
    (heads : ∀ i : Fin k, e.workTapePos (Fin.castAdd 2 i) = d.workTapePos (Fin.castAdd 2 i)) :
    h1RoundWindow c a e := by
  obtain ⟨hi, hw⟩ := window
  refine ⟨by simpa only [input] using hi, ?_⟩
  intro i
  simpa only [heads i] using hw i

/-- State-word cells of a canonical phase frame, with the left blank included. -/
private lemma h1Data_stateCell {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (table : List Bool) (summary : Option Bool) (word : List Bool)
    (tablePos statePos : ℤ) (pre : List Bool) (z : ℤ) (hz : -1 ≤ z) :
    (h1Data c table summary word tablePos statePos pre).workTapes (h1SummaryTape k) (2 + z) =
      FinTM.bufferTape word z := by
  simpa only [h1Data, h1SummaryTape, Fin.addCases_right, show (1 : Fin 2) ≠ 0 from by decide,
    ↓reduceIte] using
    h1SummaryState_cell summary word z hz

/-- Clearing preparation restores the old unary-state head, erases its word,
and returns to the summary cell before invoking the selected-record reader.
All mirrored heads remain at their round-start positions throughout.

**Proof sketch.** Apply the public framed skip, reverse skip and clear contracts
in order, followed by the fixed two-cell move. Each is lifted by the public
phase host, and their proved strict prefixes are joined by run addition. -/
private lemma h1Round_prepare {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (q : Fin (n + 1)) (table : List Bool) (summary : Option Bool) (pos : ℤ) (pre : List Bool) :
    h1RoundSpan c a
      (h1At (h1Data c table summary (unaryFin q) pos (q.val + 2) pre) .stateTail .run)
      (h1At (h1Data c table summary [] pos 0 pre) .record (h1RecordTM k).q₀)
      (3 * q.val + 16) := by
  let d0 := h1Data c table summary (unaryFin q) pos (q.val + 2) pre
  let d1 := h1Data c table summary (unaryFin q) pos (q.val + 4) pre
  let d2 := h1Data c table summary (unaryFin q) pos 2 pre
  let d3 := h1Data c table summary [] pos 2 pre
  let d4 := h1Data c table summary [] pos 0 pre
  let s0 := d0.mapState (fun _ => SeekPhase.run)
  let s1 := d1.mapState (fun _ => SeekPhase.run)
  let s2 := d2.mapState (fun _ => SweepPhase.sweep)
  let s3 := d3.mapState (fun _ => (0 : Fin 3))
  have skip := skipTM_run_ofCfg (h1SummaryTape k) [false] s0 rfl (by
    intro z hz hz'
    have cases : z = 0 ∨ z = 1 := by simp only [List.length_cons, List.length_nil] at hz'; omega
    rcases cases with rfl | rfl
    · simp [s0, d0, Cfg.mapState, h1Data, h1SummaryTape, h1SummaryState, unaryFin,
        show (q.val : ℤ) + 2 ≠ 0 by omega, FinTM.bufferTape]
    · have cell := h1Data_stateCell c table summary (unaryFin q) pos (q.val + 2) pre
        ((q.val + 1 : ℕ) : ℤ) (by omega)
      have blank : FinTM.bufferTape (unaryFin q) ((q.val + 1 : ℕ) : ℤ) = none := by
        rw [FinTM.bufferTape_nat]
        simp [unaryFin]
      rw [blank] at cell
      convert cell using 1; simp [s0, d0, Cfg.mapState, h1Data, h1SummaryTape]; congr 1; omega)
  have skipEnd : (skipTM (k + 2) (h1SummaryTape k)).runFrom s0 2 = d1.mapState (fun _ =>
    SeekPhase.done) := by
    have he := skip.1
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at he
    rw [he]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s0, d0, d1, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s0, d0, d1, h1Data, Cfg.mapState, h1SummaryTape, add_assoc]
  have p0 := h1Round_phase c a .stateTail (by decide) (by decide) s0
    (d1.mapState (fun _ => SeekPhase.done)) 2 skipEnd .done rfl ⟨.stateHome, .run⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (skip.2.1 u (by simpa using hu)) (hr.trans (congrArg some
        eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table summary (unaryFin q) pos (q.val + 2) pre
        false)
      · exact h1Run_input (skipTM (k + 2) (h1SummaryTape k))
          (by intro r inp work; cases r <;> cases h : work (h1SummaryTape k) <;>
            simp [skipTM, h, tapeAction, inputMoveAction]) s0 u
      · intro i
        simpa only [h1Mirror_ne_summary k i, ↓reduceIte, s0, Cfg.mapState] using skip.2.2
          (Fin.castAdd 2 i) u (by simpa using hu))
  have back := skipBackTM_run_ofCfg (h1SummaryTape k) (unaryFin q) s1 rfl (by
    intro z hz hz'
    have cell := h1Data_stateCell c table summary (unaryFin q) pos (q.val + 4) pre z hz
    convert cell using 1; simp [s1, d1, Cfg.mapState, h1Data, h1SummaryTape, unaryFin])
  have backEnd : (skipBackTM (k + 2) (h1SummaryTape k)).runFrom s1 ((unaryFin q).length + 3) =
      d2.mapState (fun _ => SeekPhase.done) := by
    rw [back.1]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s1, d1, d2, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s1, d1, d2, h1Data, Cfg.mapState, h1SummaryTape, unaryFin]
  have p1 := h1Round_phase c a .stateHome (by decide) (by decide) s1
    (d2.mapState (fun _ => SeekPhase.done)) _ backEnd .done rfl ⟨.clearState, .sweep⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (back.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table summary (unaryFin q) pos (q.val + 4) pre
        false)
      · exact h1Run_input (skipBackTM (k + 2) (h1SummaryTape k))
          (by intro r inp work; cases r <;> cases h : work (h1SummaryTape k) <;>
            simp [skipBackTM, h, tapeAction, inputMoveAction]) s1 u
      · intro i
        simpa only [h1Mirror_ne_summary k i, ↓reduceIte, s1, Cfg.mapState] using back.2.2
          (Fin.castAdd 2 i) u hu)
  have clear := clearTM_run_ofCfg (h1SummaryTape k) (unaryFin q) s2 rfl (by
    intro z hz _
    simpa [s2, d2, Cfg.mapState, h1Data, h1SummaryTape] using
      h1Data_stateCell c table summary (unaryFin q) pos 2 pre z hz)
  have clearEnd : (clearTM (k + 2) (h1SummaryTape k)).runFrom s2 (2 * (unaryFin q).length + 2) =
      d3.mapState (fun _ => SweepPhase.done) := by
    rw [clear.1]
    apply Cfg.ext <;> try rfl
    funext j z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s2, d2, d3, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i
      · simp [s2, d2, d3, h1Data, Cfg.mapState, h1SummaryTape]
      · simpa [s2, d2, d3, h1Data, Cfg.mapState, h1SummaryTape] using
          congrFun (h1SummaryState_clear summary (unaryFin q)) z
  have p2 := h1Round_phase c a .clearState (by decide) (by decide) s2
    (d3.mapState (fun _ => SweepPhase.done)) _ clearEnd .done rfl ⟨.toSummary, (0 : Fin 3)⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (clear.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table summary (unaryFin q) pos 2 pre false)
      · exact h1Run_input (clearTM (k + 2) (h1SummaryTape k))
          (by intro r inp work; cases r <;> cases h : work (h1SummaryTape k) <;>
            simp [clearTM, h]) s2 u
      · intro i
        simpa only [h1Mirror_ne_summary k i, ↓reduceIte, s2, Cfg.mapState] using clear.2.2
          (Fin.castAdd 2 i) u hu)
  have moveEnd : (h1TwoMoveTM (h1SummaryTape k) .neg).runFrom s3 2 = d4.mapState (fun _ => (2 :
    Fin 3)) := by
    rw [h1TwoMove_run _ _ s3 rfl 2 le_rfl]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s3, d3, d4, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s3, d3, d4, h1Data, Cfg.mapState, h1SummaryTape]
  have p3 := h1Round_phase c a .toSummary (by decide) (by decide) s3
    (d4.mapState (fun _ => (2 : Fin 3))) 2 moveEnd 2 rfl ⟨.record, (h1RecordTM k).q₀⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      rw [h1TwoMove_run _ _ s3 rfl u (by omega)] at hr
      have vr : r.val = u := congrArg Fin.val (Option.some.inj hr).symm
      have ne : r ≠ 2 := by intro bad; subst r; omega
      simp [h1RoundRed, ne]) (by
      intro u hu
      rw [h1TwoMove_run _ _ s3 rfl u hu]
      refine ⟨Or.inl rfl, fun i => Or.inl ?_⟩
      simp [s3, d3, h1Data, Cfg.mapState, h1Mirror_ne_summary k i])
  have joined := h1RoundSpan_add c a (h1RoundSpan_add c a (h1RoundSpan_add c a p0 p1) p2) p3
  have cost : ((2 + 1) + ((unaryFin q).length + 3 + 1) + (2 * (unaryFin q).length + 2 + 1)) + (2
    + 1) =
      3 * q.val + 16 := by simp [unaryFin]; omega
  simpa only [h1At, s0, d0, d4, Cfg.mapState, h1Data, cost] using joined

/-- Literal cells of the middle word of a canonical concatenated buffer.
Both cuts use the same framed append-read lemma. -/
private lemma h1Buffer_reads (before word after : List Bool) :
    ∀ (r : ℕ) (hr : r < word.length),
      FinTM.bufferTape (before ++ word ++ after) (before.length + r) = some (word[r]'hr) := by
  have whole : ∀ (r : ℕ) (hr : r < (before ++ word ++ after).length),
      FinTM.bufferTape (before ++ word ++ after) ((r : ℕ) : ℤ) =
        some ((before ++ word ++ after)[r]'hr) := by
    intro r hr
    rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
  have first := h1Reads_append (FinTM.bufferTape (before ++ word ++ after)) 0 before (word ++ after)
    (by simpa only [zero_add, List.append_assoc] using whole)
  have second := h1Reads_append (FinTM.bufferTape (before ++ word ++ after)) before.length word
    after
    (by simpa only [zero_add] using first.2)
  exact second.1

/-- Execute the inherited fixed payload, return to the cleared state word,
then install the complete successor. The exit still precedes head restoration.
The halting case consumes its false tag and keeps a live physical exit.

**Proof sketch.** Cite `h1Record_effect` for all simulated fields and its head
envelope. Use the exact inherited reader execution only to frame the two
auxiliary tapes. The two-cell move enters the cleared state region, and the
proved successor copier installs its new unary word. Join the three public
phase-host segments; their total is the full record length plus six. -/
private lemma h1Round_payload {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (table before after pre : List Bool) (ht : table = before ++ actionBitsK a ++ after) :
    let word := (a.state.map unaryFin).getD []
    h1RoundSpan c a
      (h1At (h1Data c table (outputSummary c.output) [] before.length 0 pre) .record (h1RecordTM k).q₀)
      (h1At (h1Data (a.apply c) table (outputSummary (a.apply c).output) word
        (before.length + (actionBitsK a).length) (2 + word.length) pre) (.tableTail a.state.isSome) .run)
      ((actionBitsK a).length + 6) := by
  let word := (a.state.map unaryFin).getD []
  let d0 := h1Data c table (outputSummary c.output) [] before.length 0 pre
  let d1 := h1Data (a.apply c) table (outputSummary (a.apply c).output) []
    (before.length + h1RecordWidth k) 0 pre
  let d2 := h1Data (a.apply c) table (outputSummary (a.apply c).output) []
    (before.length + h1RecordWidth k) 2 pre
  let d3 := h1Data (a.apply c) table (outputSummary (a.apply c).output) word
    (before.length + (actionBitsK a).length) (2 + word.length) pre
  have reads : ∀ (r : ℕ) (hr : r < (actionBitsK a).length),
      d0.workTapes (h1TableTape k) (d0.workTapePos (h1TableTape k) + r) = some ((actionBitsK
        a)[r]'hr) := by
    simpa [d0, h1Data, h1TableTape, ht] using h1Buffer_reads before (actionBitsK a) after
  obtain ⟨bits, split, length, fixedReads, fieldReads⟩ := h1Action_reads d0 a reads
  have hbits : List.ofFn bits = (actionBitsK a).take (h1RecordWidth k) := by
    rw [split]
    exact (List.take_left' (List.length_ofFn (f := bits))).symm
  have effect := h1Record_effect d0 c a bits rfl fixedReads hbits rfl
    (by intro i; simp [d0, h1Data]) (by intro i; simp [d0, h1Data])
    (by simp [d0, h1Data, Cfg.workTapeSymbols, h1SummaryTape, h1SummaryState])
  dsimp only at effect
  obtain ⟨recordState, recordInput, recordBank, recordSum, recordOutput, recordCut, _,
    recordHeads⟩ := effect
  have literal := h1Record_execute d0 a bits rfl fixedReads hbits
  have sumStep : summaryEmit (outputSummary c.output) a.output = outputSummary (a.apply c).output :=
    (outputSummary_append c.output a.output).symm
  have recordEnd : (h1RecordTM k).runFrom d0 (h1RecordWidth k + 1) = d1.mapState (fun _ => (none
    : h1RecordState k)) := by
    apply Cfg.ext
    · exact recordState
    · exact recordInput
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [d1, h1Data, Cfg.mapState] using (recordBank i).1
      · fin_cases i
        · rw [literal]
          simp [h1ApplyPayload, h1ReadCfg, d0, d1, h1Data, Cfg.mapState, h1TableTape]
        · rw [literal]
          simp [h1ApplyPayload, h1ReadCfg, d0, d1, h1Data, Cfg.mapState, h1TableTape,
            h1SummaryTape, Cfg.workTapeSymbols,
            show h1SummaryState (outputSummary c.output) [] 0 = outputSummary c.output from rfl,
            h1SummaryState_update, sumStep]
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [d1, h1Data, Cfg.mapState] using (recordBank i).2
      · fin_cases i <;> rw [literal] <;>
          simp [h1ApplyPayload, h1ReadCfg, d0, d1, h1Data, Cfg.mapState, h1TableTape]
    · exact recordOutput
  have p0 := h1Round_phase c a .record (by decide) (by decide) d0
    (d1.mapState (fun _ => (none : h1RecordState k))) _ recordEnd none rfl ⟨.toState, (0 : Fin 3)⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ none := fun eq => recordCut u hu (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      have envelope := recordHeads u hu
      by_cases last : u = h1RecordWidth k + 1
      · refine ⟨Or.inr ?_, fun i => Or.inr ?_⟩
        · simpa [last, d0, h1Data] using envelope.2.1
        · simpa [last, d0, h1Data] using envelope.1 i
      · refine ⟨Or.inl ?_, fun i => Or.inl ?_⟩
        · simpa [last, d0, h1Data] using envelope.2.1
        · simpa [last, d0, h1Data] using envelope.1 i)
  let moving := d1.mapState (fun _ => (0 : Fin 3))
  have moveEnd : (h1TwoMoveTM (h1SummaryTape k) .pos).runFrom moving 2 = d2.mapState (fun _ => (2
    : Fin 3)) := by
    rw [h1TwoMove_run _ _ moving rfl 2 le_rfl]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [moving, d1, d2, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [moving, d1, d2, h1Data, Cfg.mapState, h1SummaryTape]
  have p1 := h1Round_phase c a .toState (by decide) (by decide) moving
    (d2.mapState (fun _ => (2 : Fin 3))) 2 moveEnd 2 rfl ⟨.successor, .tag⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      rw [h1TwoMove_run _ _ moving rfl u (by omega)] at hr
      have vr : r.val = u := congrArg Fin.val (Option.some.inj hr).symm
      have ne : r ≠ 2 := by intro bad; subst r; omega
      simp [h1RoundRed, ne]) (by
      intro u hu
      rw [h1TwoMove_run _ _ moving rfl u hu]
      refine ⟨Or.inr rfl, fun i => Or.inr ?_⟩
      simp [moving, d1, h1Data, Cfg.mapState, h1Mirror_ne_summary k i])
  let copying := d2.mapState (fun _ => h1SuccPhase.tag)
  have sourceField : ∀ (r : ℕ) (hr : r < (optStateBits a.state).length),
      copying.workTapes (h1TableTape k) (copying.workTapePos (h1TableTape k) + r) =
        some ((optStateBits a.state)[r]'hr) := by
    simpa only [copying, d2, d0, h1Data, Cfg.mapState, h1TableTape, Fin.addCases_right,
      ↓reduceIte] using fieldReads
  have tailLength : (optStateBits a.state).length = word.length + 1 := by
    dsimp only [word]
    cases a.state <;> simp [optStateBits, unaryFin]
  have successorEnd : (h1SuccTM (h1TableTape k) (h1SummaryTape k) true).runFrom copying
    (optStateBits a.state).length =
      d3.mapState (fun _ => h1SuccPhase.done a.state.isSome) := by
    rw [h1Succ_run _ _ (Ne.symm (h1Summary_ne_table k)) true copying a.state rfl sourceField]
    apply Cfg.ext <;> try rfl
    · funext j z
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
          h1Mirror_ne_summary k i]
      · fin_cases i
        · simp [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
            h1TableTape, h1SummaryTape]
        · simpa [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
            h1TableTape, h1SummaryTape, word] using
            congrFun (h1SummaryState_copy (outputSummary (a.apply c).output) word) z
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
          h1Mirror_ne_summary k i, h1Mirror_ne_table k i]
      · fin_cases i
        · simp [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
            h1TableTape, h1SummaryTape]
          change _ + _ + 1 + (word.length : ℤ) = _
          rw [length, tailLength]
          push_cast
          ring
        · simp [h1UnaryCfg, h1AfterTag, copying, d2, d3, h1Data, Cfg.mapState,
            h1TableTape, h1SummaryTape, word]
  have p2 := h1Round_phase c a .successor (by decide) (by decide) copying
    (d3.mapState (fun _ => h1SuccPhase.done a.state.isSome)) _ successorEnd (.done
      a.state.isSome) rfl
    ⟨.tableTail a.state.isSome, .run⟩ rfl (by
      intro u hu r hr
      cases r with
      | tag => rfl
      | unary => rfl
      | done b => exact False.elim (h1Succ_cut _ _ (Ne.symm (h1Summary_ne_table k)) true copying
        a.state rfl sourceField u hu b hr)) (by
      intro u hu
      have heads := h1Succ_heads _ _ (Ne.symm (h1Summary_ne_table k)) true copying a.state rfl
        sourceField u hu
      refine ⟨Or.inr heads.1, fun i => Or.inr ?_⟩
      simpa [copying, d2, h1Data, Cfg.mapState, h1Mirror_ne_summary k i, h1Mirror_ne_table k i]
        using heads.2.2 (Fin.castAdd 2 i))
  have combined := h1RoundSpan_add c a (h1RoundSpan_add c a p0 p1) p2
  have cost : (h1RecordWidth k + 1 + 1) + (2 + 1) + ((optStateBits a.state).length + 1) =
      (actionBitsK a).length + 6 := by omega
  simpa only [h1At, d0, d3, moving, copying, d1, d2, Cfg.mapState, h1Data, cost] using combined

/-- A canonical buffer's suffix, including its right blank and all cells
beyond it. This is the optional-list lookup law at a nonnegative offset. -/
private lemma h1Buffer_suffix (before word : List Bool) (z : ℤ) (hz : 0 ≤ z) :
    FinTM.bufferTape (before ++ word) (before.length + z) = FinTM.bufferTape word z := by
  have hp : (before.length : ℤ) + z = ((before.length + z.toNat : ℕ) : ℤ) := by omega
  rw [hp, FinTM.bufferTape_nat, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  simp [FinTM.bufferTape, hz]

/-- Restore the table and successor-state heads after payload execution.
The table scan reaches its right blank and the catalog reverse scan returns
it to zero. The copied state word is then rewound to two, and the final fixed
move returns the summary head to zero. The live/halt distinction is retained.

**Proof sketch.** Compose the four landed framed seek contracts and the
fixed two-cell move through the public phase host. All five segments preserve
the source action's final simulated heads and exclude both round anchors until
the last dispatch. The exact cost counts every delimiter and dispatch. -/
private lemma h1Round_restore {k n : ℕ} {x : List Bool}
    (c : Cfg k Bool (Fin (n + 1)) x) (a : Action k Bool (Fin (n + 1)))
    (table before tail word pre : List Bool) (live : Bool) (ht : table = before ++ tail) :
    h1RoundSpan c a
      (h1At (h1Data (a.apply c) table (outputSummary (a.apply c).output) word
        before.length (2 + word.length) pre) (.tableTail live) .run)
      ((h1Data (a.apply c) table (outputSummary (a.apply c).output) word 0 0 pre).mapState
        (fun _ => h1RoundExit k live))
      (tail.length + table.length + word.length + 15) := by
  let data := fun tp sp => h1Data (a.apply c) table (outputSummary (a.apply c).output) word tp sp
    pre
  let d0 := data before.length (2 + word.length)
  let d1 := data (table.length + 1) (2 + word.length)
  let d2 := data 0 (2 + word.length)
  let d3 := data 0 (word.length + 3)
  let d4 := data 0 2
  let d5 := data 0 0
  let s0 := d0.mapState (fun _ => SeekPhase.run)
  let s1 := d1.mapState (fun _ => SeekPhase.run)
  let s2 := d2.mapState (fun _ => SeekPhase.run)
  let s3 := d3.mapState (fun _ => SeekPhase.run)
  let s4 := d4.mapState (fun _ => (0 : Fin 3))
  have tableLength : table.length = before.length + tail.length := by rw [ht, List.length_append]
  have tableSkip := skipTM_run_ofCfg (h1TableTape k) tail s0 rfl (by
    intro z hz _
    simpa [s0, d0, data, h1Data, Cfg.mapState, h1TableTape, ht] using h1Buffer_suffix before tail
      z hz)
  have tableSkipEnd : (skipTM (k + 2) (h1TableTape k)).runFrom s0 (tail.length + 1) =
      d1.mapState (fun _ => SeekPhase.done) := by
    rw [tableSkip.1]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s0, d0, d1, data, h1Data, Cfg.mapState, h1Mirror_ne_table k i]
    · fin_cases i <;> simp [s0, d0, d1, data, h1Data, Cfg.mapState, h1TableTape, tableLength,
      Nat.cast_add, add_assoc]
  have p0 := h1Round_phase c a (.tableTail live) (by intro h; cases h) (by intro h; cases h) s0
    (d1.mapState (fun _ => SeekPhase.done)) _ tableSkipEnd .done rfl ⟨.tableHome live, .run⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (tableSkip.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table _ word before.length (2 + word.length)
        pre true)
      · exact h1Run_input (skipTM (k + 2) (h1TableTape k))
          (by intro r inp work; cases r <;> cases h : work (h1TableTape k) <;> simp [skipTM, h,
            tapeAction, inputMoveAction]) s0 u
      · intro i
        simpa only [h1Mirror_ne_table k i, ↓reduceIte, s0, Cfg.mapState] using tableSkip.2.2
          (Fin.castAdd 2 i) u hu)
  have tableBack := skipBackTM_run_ofCfg (h1TableTape k) table s1 rfl (by
    intro z _ _
    simp [s1, d1, data, h1Data, Cfg.mapState, h1TableTape])
  have tableBackEnd : (skipBackTM (k + 2) (h1TableTape k)).runFrom s1 (table.length + 3) =
      d2.mapState (fun _ => SeekPhase.done) := by
    rw [tableBack.1]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s1, d1, d2, data, h1Data, Cfg.mapState, h1Mirror_ne_table k i]
    · fin_cases i <;> simp [s1, d1, d2, data, h1Data, Cfg.mapState, h1TableTape]
  have p1 := h1Round_phase c a (.tableHome live) (by intro h; cases h) (by intro h; cases h) s1
    (d2.mapState (fun _ => SeekPhase.done)) _ tableBackEnd .done rfl ⟨.stateGap live, .run⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (tableBack.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table _ word (table.length + 1) (2 +
        word.length) pre true)
      · exact h1Run_input (skipBackTM (k + 2) (h1TableTape k))
          (by intro r inp work; cases r <;> cases h : work (h1TableTape k) <;> simp [skipBackTM,
            h, tapeAction, inputMoveAction]) s1 u
      · intro i
        simpa only [h1Mirror_ne_table k i, ↓reduceIte, s1, Cfg.mapState] using tableBack.2.2
          (Fin.castAdd 2 i) u hu)
  have stateGap := skipTM_run_ofCfg (h1SummaryTape k) [] s2 rfl (by
    intro z hz hz'
    have hz0 : z = 0 := by simp only [List.length_nil, Nat.cast_zero] at hz'; omega
    subst z
    have cell := h1Data_stateCell (a.apply c) table (outputSummary (a.apply c).output) word 0 (2
      + word.length) pre
      word.length (by omega)
    simpa [s2, d2, data, h1Data, Cfg.mapState, h1SummaryTape, FinTM.bufferTape_nat] using cell)
  have stateGapEnd : (skipTM (k + 2) (h1SummaryTape k)).runFrom s2 (([] : List Bool).length + 1) =
      d3.mapState (fun _ => SeekPhase.done) := by
    rw [stateGap.1]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s2, d2, d3, data, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s2, d2, d3, data, h1Data, Cfg.mapState, h1SummaryTape]; omega
  have p2 := h1Round_phase c a (.stateGap live) (by intro h; cases h) (by intro h; cases h) s2
    (d3.mapState (fun _ => SeekPhase.done)) _ stateGapEnd .done rfl ⟨.stateRestore live, .run⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (stateGap.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table _ word 0 (2 + word.length) pre true)
      · exact h1Run_input (skipTM (k + 2) (h1SummaryTape k))
          (by intro r inp work; cases r <;> cases h : work (h1SummaryTape k) <;> simp [skipTM, h,
            tapeAction, inputMoveAction]) s2 u
      · intro i
        simpa only [h1Mirror_ne_summary k i, ↓reduceIte, s2, Cfg.mapState] using stateGap.2.2
          (Fin.castAdd 2 i) u hu)
  have stateBack := skipBackTM_run_ofCfg (h1SummaryTape k) word s3 rfl (by
    intro z hz _
    have cell := h1Data_stateCell (a.apply c) table (outputSummary (a.apply c).output) word 0
      (word.length + 3) pre z hz
    convert cell using 1; simp [s3, d3, data, Cfg.mapState, h1Data, h1SummaryTape])
  have stateBackEnd : (skipBackTM (k + 2) (h1SummaryTape k)).runFrom s3 (word.length + 3) =
      d4.mapState (fun _ => SeekPhase.done) := by
    rw [stateBack.1]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s3, d3, d4, data, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s3, d3, d4, data, h1Data, Cfg.mapState, h1SummaryTape]
  have p3 := h1Round_phase c a (.stateRestore live) (by intro h; cases h) (by intro h; cases h) s3
    (d4.mapState (fun _ => SeekPhase.done)) _ stateBackEnd .done rfl ⟨.finish live, (0 : Fin 3)⟩
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      have ne : r ≠ .done := fun eq => (stateBack.2.1 u hu) (hr.trans (congrArg some eq))
      simp [h1RoundRed, ne]) (by
      intro u hu
      apply h1Window_frame c a (h1Data_window c a table _ word 0 (word.length + 3) pre true)
      · exact h1Run_input (skipBackTM (k + 2) (h1SummaryTape k))
          (by intro r inp work; cases r <;> cases h : work (h1SummaryTape k) <;> simp
            [skipBackTM, h, tapeAction, inputMoveAction]) s3 u
      · intro i
        simpa only [h1Mirror_ne_summary k i, ↓reduceIte, s3, Cfg.mapState] using stateBack.2.2
          (Fin.castAdd 2 i) u hu)
  have moveEnd : (h1TwoMoveTM (h1SummaryTape k) .neg).runFrom s4 2 = d5.mapState (fun _ => (2 :
    Fin 3)) := by
    rw [h1TwoMove_run _ _ s4 rfl 2 le_rfl]
    apply Cfg.ext <;> try rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [s4, d4, d5, data, h1Data, Cfg.mapState, h1Mirror_ne_summary k i]
    · fin_cases i <;> simp [s4, d4, d5, data, h1Data, Cfg.mapState, h1SummaryTape]
  have p4 := h1Round_phase c a (.finish live) (by intro h; cases h) (by intro h; cases h) s4
    (d5.mapState (fun _ => (2 : Fin 3))) 2 moveEnd 2 rfl (h1RoundExit k live)
    (by simp [h1RoundRed]) (by
      intro u hu r hr
      rw [h1TwoMove_run _ _ s4 rfl u (by omega)] at hr
      have vr : r.val = u := congrArg Fin.val (Option.some.inj hr).symm
      have ne : r ≠ 2 := by intro bad; subst r; omega
      simp [h1RoundRed, ne]) (by
      intro u hu
      rw [h1TwoMove_run _ _ s4 rfl u hu]
      refine ⟨Or.inr rfl, fun i => Or.inr ?_⟩
      simp [s4, d4, data, h1Data, Cfg.mapState, h1Mirror_ne_summary k i])
  have combined := h1RoundSpan_add c a (h1RoundSpan_add c a (h1RoundSpan_add c a (h1RoundSpan_add
    c a p0 p1) p2) p3) p4
  have cost : (((tail.length + 1 + 1) + (table.length + 3 + 1) + (([] : List Bool).length + 1 +
    1)) +
      (word.length + 3 + 1)) + (2 + 1) = tail.length + table.length + word.length + 15 := by
        simp; omega
  simpa only [h1At, s0, d0, s1, s2, s3, s4, d1, d2, d3, d4, d5, data, Cfg.mapState, h1Data, cost]
    using combined

/-- Lift the proved physical selector into the full round. The result names
its exact table cut, retaining both the state-size ledger and first-exit cut. -/
private lemma h1Round_lookup {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) (q : Fin (n + 1)) (pre : List Bool) :
    let a := tr q c.inputSymbol c.workTapeSymbols
    ∃ (before tail : List Bool) (T : ℕ),
      tableBitsK tr = before ++ actionBitsK a ++ tail ∧ q.val ≤ before.length ∧
      T ≤ 5 * (tableBitsK tr).length + 4 ∧
      h1RoundSpan c a
        (h1At (h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre)
          .lookup (h1SeekTM k).q₀)
        (h1At (h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q)
          before.length (q.val + 2) pre) .stateTail .run) T := by
  let a := tr q c.inputSymbol c.workTapeSymbols
  let d := h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre
  obtain ⟨before, tail, T, split, size, _, bound, run, cut, frame⟩ :=
    h1Seek_select tr q (outputSummary c.output) d rfl
      (by simp [d, h1Data, h1TableTape]) (by simp [d, h1Data, h1TableTape])
      (by simp [d, h1Data, h1SummaryTape]) (by simp [d, h1Data, h1SummaryTape])
  refine ⟨before, tail, T + 1, ?_, size, by omega, ?_⟩
  · simpa only [d, h1Data, Cfg.inputSymbol, Cfg.workTapeSymbols, Fin.addCases_left] using split
  · have lifted := h1Round_phase c a .lookup (by decide) (by decide)
      (h1SeekCfg d .observe) (h1SeekCfg (h1SeekShift d before.length (q.val + 2)) .done)
      T run ⟨none, .done⟩ rfl ⟨.stateTail, .run⟩ (by simp [h1RoundRed]) (by
        intro u hu r hr
        have ne : r ≠ ⟨none, .done⟩ := fun eq => cut u hu (hr.trans (congrArg some eq))
        simp [h1RoundRed, ne]) (by
        intro u hu
        have hf := frame u hu
        exact h1Window_frame c a (h1Data_window c a (tableBitsK tr)
          (outputSummary c.output) (unaryFin q) 0 0 pre false) hf.1
          (fun i => hf.2.2.2 _ (h1Mirror_ne_table k i) (h1Mirror_ne_summary k i)))
    have shifted : h1SeekShift d before.length (q.val + 2) =
        h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) before.length (q.val + 2)
          pre := by
      simpa only [d, zero_add, Nat.cast_add, Nat.cast_ofNat] using
        h1Data_shift c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre
          before.length (q.val + 2)
    rw [shifted] at lifted
    simpa only [h1At, h1SeekCfg, d, Cfg.mapState, h1Data] using lifted

/-- Exact complete-round execution from a canonical data frame. The cost
is bounded by fifty times the table length plus one, uniformly in the state
count, input, and simulated time. Both continuation and halt use live exits.

**Proof sketch.** Join lookup, preparation, inherited payload execution,
successor copy, and restoration. The one entry dispatch is separate so the
strict interior excludes both round anchors. The serializer cut pays for the
old unary state, selected record, suffix scan, and new unary state; the
remaining constants count dispatches and delimiter cells. -/
private lemma h1Round_canonical {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) (q : Fin (n + 1)) (pre : List Bool) :
    let a := tr q c.inputSymbol c.workTapeSymbols
    let start := h1At (h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre) .entry ()
    let finish := (h1Data (a.apply c) (tableBitsK tr) (outputSummary (a.apply c).output)
      ((a.state.map unaryFin).getD []) 0 0 pre).mapState (fun _ => h1RoundExit k a.state.isSome)
    ∃ T, 0 < T ∧ T ≤ 50 * ((tableBitsK tr).length + 1) ∧
      (h1RoundTM k).runFrom start T = finish ∧
      (∀ u, 0 < u → u < T → ∃ s, ((h1RoundTM k).runFrom start u).state = some s ∧
        s ≠ ⟨.entry, ()⟩ ∧ s ≠ ⟨.halt, ()⟩) ∧
      ∀ u ≤ T, h1RoundWindow c a ((h1RoundTM k).runFrom start u) := by
  let a := tr q c.inputSymbol c.workTapeSymbols
  let d := h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre
  let word := (a.state.map unaryFin).getD []
  obtain ⟨before, tail, L, split, stateSize, lookupBound, lookup⟩ := h1Round_lookup tr c q pre
  change tableBitsK tr = before ++ actionBitsK a ++ tail at split
  have prepare := h1Round_prepare c a q (tableBitsK tr) (outputSummary c.output) before.length pre
  have payload := h1Round_payload c a (tableBitsK tr) before tail pre split
  have restore := h1Round_restore c a (tableBitsK tr) (before ++ actionBitsK a) tail word pre
    a.state.isSome (by simpa only [List.append_assoc] using split)
  simp only [List.length_append, Nat.cast_add] at restore
  have joined := h1RoundSpan_add c a (h1RoundSpan_add c a (h1RoundSpan_add c a lookup prepare)
    payload) restore
  let U := L + (3 * q.val + 16) + ((actionBitsK a).length + 6) +
    (tail.length + (tableBitsK tr).length + word.length + 15)
  have entry : (h1RoundTM k).step (h1At d .entry ()) = h1At d .lookup (h1SeekTM k).q₀ := by
    have one := step_of_inputMoveAction (h1RoundTM k) (h1At d .entry ())
      (q := ⟨.entry, ()⟩) (q' := ⟨.lookup, (h1SeekTM k).q₀⟩) 0 rfl rfl
    simpa only [moveInputPos_zero, h1At, d, h1Data, Cfg.mapState] using one
  have advance (u : ℕ) := MultiTapeTM.runFrom_succ_eq_step (tm := h1RoundTM k) (cfg := h1At d
    .entry ()) (t := u)
  simp only [entry] at advance
  have run : (h1RoundTM k).runFrom (h1At d .entry ()) (U + 1) =
      (h1Data (a.apply c) (tableBitsK tr) (outputSummary (a.apply c).output) word 0 0 pre).mapState
        (fun _ => h1RoundExit k a.state.isSome) := by
    rw [advance]
    exact joined.1
  refine ⟨U + 1, by omega, ?_, run, ?_, ?_⟩
  · have recordSize : (actionBitsK a).length ≤ (tableBitsK tr).length := by
      have hs := congrArg List.length split
      simp only [List.length_append] at hs
      omega
    have prefixSize : before.length ≤ (tableBitsK tr).length := by
      have hs := congrArg List.length split
      simp only [List.length_append] at hs
      omega
    have suffixSize : tail.length ≤ (tableBitsK tr).length := by
      have hs := congrArg List.length split
      simp only [List.length_append] at hs
      omega
    have wordSize : word.length ≤ (actionBitsK a).length := by
      obtain ⟨bits, hs⟩ := h1Action_split a
      have hl := congrArg List.length hs
      simp only [List.length_append, List.length_ofFn] at hl
      have tailLen : (optStateBits a.state).length = word.length + 1 := by
        dsimp only [word]
        cases a.state <;> simp [optStateBits, unaryFin]
      omega
    dsimp only [U]
    omega
  · intro u hu ht
    rw [show u = (u - 1) + 1 by omega, advance]
    obtain ⟨s, hs, he, hh, _⟩ := joined.2 (u - 1) (by dsimp only [U] at ht; omega)
    exact ⟨s, hs, he, hh⟩
  · intro u hu
    by_cases hz : u = 0
    · subst u
      exact h1Data_window c a (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 pre false
    · by_cases hend : u = U + 1
      · rw [hend, run]
        exact h1Data_window c a (tableBitsK tr) (outputSummary (a.apply c).output) word 0 0 pre true
      · rw [show u = (u - 1) + 1 by omega, advance]
        exact (joined.2 (u - 1) (by dsimp only [U] at hu; omega)).choose_spec.2.2.2

/-- Relation at the generic step block's seam. The first `k` work tapes
mirror the source, and the native input position is its simulated input head.
Auxiliary tape `k` holds the immutable public table; tape `k + 1` holds the
output summary at zero, a blank at one, and the unary state at two. Both
auxiliary heads are home at zero. Simulated halt has an empty state word.
Physical control and the physical output prefix are deliberately independent. -/
private def h1RoundRep {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x)
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x) : Prop :=
  d.inputPos = c.inputPos ∧
  (∀ i : Fin k, d.workTapes (Fin.castAdd 2 i) = c.workTapes i ∧
    d.workTapePos (Fin.castAdd 2 i) = c.workTapePos i) ∧
  d.workTapes (h1TableTape k) = FinTM.bufferTape (tableBitsK tr) ∧
  d.workTapes (h1SummaryTape k) =
    h1SummaryState (outputSummary c.output) ((c.state.map unaryFin).getD []) ∧
  d.workTapePos (h1TableTape k) = 0 ∧ d.workTapePos (h1SummaryTape k) = 0

/-- A related entry configuration is exactly the canonical round frame,
with its arbitrary physical output prefix retained. This only unpacks the
seam relation; it makes no assumption about the mirrored source tapes. -/
private lemma h1RoundRep_entry {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) (q : Fin (n + 1)) (hq : c.state = some q)
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some ⟨.entry, ()⟩) (rel : h1RoundRep tr c d) :
    d = h1At (h1Data c (tableBitsK tr) (outputSummary c.output) (unaryFin q) 0 0 d.output) .entry () := by
  obtain ⟨input, bank, table, summary, tableHome, stateHome⟩ := rel
  simp only [hq, Option.map_some, Option.getD_some] at summary
  apply Cfg.ext
  · exact entry
  · exact input
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [h1At, Cfg.mapState, h1Data, Fin.addCases_left] using (bank i).1
    · fin_cases i
      · simpa [h1At, Cfg.mapState, h1Data, h1TableTape] using table
      · simpa [h1At, Cfg.mapState, h1Data, h1SummaryTape] using summary
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [h1At, Cfg.mapState, h1Data, Fin.addCases_left] using (bank i).2
    · fin_cases i
      · simpa [h1At, Cfg.mapState, h1Data, h1TableTape] using tableHome
      · simpa [h1At, Cfg.mapState, h1Data, h1SummaryTape] using stateHome
  · rfl

/-- **Promotion candidate (host H2, step block; machine-library-design.md §14).**
One finite physical machine `h1RoundFinTM k`, whose control depends only on
`k`, realizes one transition of any canonized `k`-tape table. `h1RoundRep`
fully specifies the seam. The table and unary state are data, never control.
The source action is applied even when its successor is `none`; the block
then reaches the separate live halt exit, after restoring both auxiliaries.

The bound is `50 * (|table| + 1)`. Every simulated head stays at either its
start or its action endpoint, at distance at most one. Every auxiliary head
stays within the same linear bound and returns home. Physical output is
silent at every intermediate time; simulated emission updates the summary.
The strict interior visits neither the continuation anchor nor the halt exit.

**Proof sketch.** Unpack the representation and invoke the complete canonical
round. Output-prefix monotonicity gives silence throughout. The phase window
and the public action head bound give the mirrored envelope. Summing the
public unit step bound gives the auxiliary envelope. The input clamp handles
both boundary blanks. No space ledger or alternative trace is constructed. -/
private theorem h1Round_effect {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) (q : Fin (n + 1)) (hq : c.state = some q)
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some ⟨.entry, ()⟩) (rel : h1RoundRep tr c d) :
    let a := tr q c.inputSymbol c.workTapeSymbols
    ∃ T, 0 < T ∧ T ≤ 50 * ((tableBitsK tr).length + 1) ∧
      let e := (h1RoundTM k).runFrom d T
      e.state = some (h1RoundExit k a.state.isSome) ∧ h1RoundRep tr (a.apply c) e ∧
      e.workTapeSymbols (h1SummaryTape k) = summaryEmit (d.workTapeSymbols (h1SummaryTape k)) a.output ∧
      (∀ u, 0 < u → u < T → ∃ s, ((h1RoundTM k).runFrom d u).state = some s ∧
        s ≠ ⟨.entry, ()⟩ ∧ s ≠ ⟨.halt, ()⟩) ∧
      (∀ u ≤ T, ((h1RoundTM k).runFrom d u).output = d.output) ∧
      (∀ u ≤ T,
        let f := (h1RoundTM k).runFrom d u
        (f.inputPos = d.inputPos ∨ f.inputPos = e.inputPos) ∧
        |(f.inputPos.val : ℤ) - d.inputPos.val| ≤ 1 ∧
        (∀ i : Fin k, f.workTapePos (Fin.castAdd 2 i) = d.workTapePos (Fin.castAdd 2 i) ∨
          f.workTapePos (Fin.castAdd 2 i) = e.workTapePos (Fin.castAdd 2 i)) ∧
        ∀ j : Fin (k + 2), |f.workTapePos j - d.workTapePos j| ≤
          if j.val < k then 1 else (50 * ((tableBitsK tr).length + 1) : ℕ)) ∧
      ∀ j : Fin (k + 2), k ≤ j.val → d.workTapePos j = 0 ∧ e.workTapePos j = 0 := by
  let a := tr q c.inputSymbol c.workTapeSymbols
  have canonical := h1RoundRep_entry tr c q hq d entry rel
  obtain ⟨T, positive, bound, run, cut, window⟩ := h1Round_canonical tr c q d.output
  rw [← canonical] at run cut window
  refine ⟨T, positive, bound, ?_, ?_, ?_, cut, ?_, ?_, ?_⟩
  · rw [run]
    rfl
  · rw [run]
    simp [h1RoundRep, h1Data, Cfg.mapState, Action.apply, h1TableTape, h1SummaryTape]
  · have old : d.workTapeSymbols (h1SummaryTape k) = outputSummary c.output := by
      rw [canonical]
      simp [h1At, h1Data, Cfg.mapState, Cfg.workTapeSymbols, h1SummaryTape, h1SummaryState]
    rw [run, old]
    simpa only [h1Data, Cfg.mapState, Cfg.workTapeSymbols, h1SummaryTape,
      Fin.addCases_right, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte, h1SummaryState] using
      (outputSummary_append c.output a.output)
  · intro u hu
    have lo := (h1RoundTM k).output_prefix d (Nat.zero_le u)
    have hi := (h1RoundTM k).output_prefix d hu
    rw [run] at hi
    exact hi.eq_of_length_le lo.length_le
  · intro u hu
    have frame := window u hu
    have finalInput : ((h1RoundTM k).runFrom d T).inputPos = (a.apply c).inputPos := by
      rw [run]
      rfl
    have finalHead (i : Fin k) : ((h1RoundTM k).runFrom d T).workTapePos (Fin.castAdd 2 i) =
        (a.apply c).workTapePos i := by
      rw [run]
      simp only [h1Data, Cfg.mapState, Fin.addCases_left]
      rfl
    have inputStep : |((a.apply c).inputPos.val : ℤ) - c.inputPos.val| ≤ 1 := by
      change |((moveInputPos c.inputPos a.inputTape).val : ℤ) - c.inputPos.val| ≤ 1
      apply abs_le.mpr
      have hp := c.inputPos.isLt
      cases h : a.inputTape <;> simp only [moveInputPos, SignType.cast] <;>
        split <;> simp <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [rel.1, finalInput] using frame.1
    · rw [rel.1]
      rcases frame.1 with start | finish
      · rw [start]; simp
      · rw [finish]; exact inputStep
    · intro i
      simpa only [(rel.2.1 i).2, finalHead i] using frame.2 i
    · intro j
      by_cases hj : j.val < k
      · let i : Fin k := ⟨j.val, hj⟩
        have ji : j = Fin.castAdd 2 i := Fin.ext rfl
        rw [if_pos hj, ji, (rel.2.1 i).2]
        rcases frame.2 i with start | finish
        · rw [start]; simp
        · rw [finish]; exact workTapePos_apply_le a c i
      · rw [if_neg hj]
        exact (h1Run_headBound (h1RoundTM k) d u j).trans (by omega)
  · intro j hj
    have home (e : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
        (ht : e.workTapePos (h1TableTape k) = 0) (hs : e.workTapePos (h1SummaryTape k) = 0) :
          e.workTapePos j = 0 := by
      have casesAux : j = h1TableTape k ∨ j = h1SummaryTape k := by
        have limit := j.isLt
        have indices : j.val = k ∨ j.val = k + 1 := by omega
        rcases indices with h | h
        · left; apply Fin.ext; simpa [h1TableTape] using h
        · right; apply Fin.ext; simpa [h1SummaryTape] using h
      rcases casesAux with rfl | rfl
      · exact ht
      · exact hs
    refine ⟨home d rel.2.2.2.2.1 rel.2.2.2.2.2, ?_⟩
    apply home
    · rw [run]; simp [h1Data, Cfg.mapState, h1TableTape]
    · rw [run]; simp [h1Data, Cfg.mapState, h1SummaryTape]

/-- The sanctioned binary clock around the frozen step block. The virtual
input host is applied outside this clock, so its changing boundary tag is
never mistaken for part of the counter loop's fixed return anchor. -/
private def h1ClockTM (k : ℕ) :=
  counterLoopTM (h1RoundTM k) (h1RoundExit k true) (some (h1RoundExit k false))

/-- The physical buffered clock uses exactly the public forwarding host.
Its buffer carries the simulated input; the last payload tape is the clock. -/
private def h1HostedClockTM (k : ℕ) := vhostEmitTM (h1ClockTM k)

/-- The first positive return to either frozen round exit. This is a proof
index for the public clock contract, not a machine that computes a time. -/
private noncomputable def h1RoundTime {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x) : ℕ := by
  classical
  exact if h : ∃ t, 0 < t ∧ ∃ b, ((h1RoundTM k).runFrom d t).state =
      some (h1RoundExit k b) then Nat.find h else 0

/-- The first-return index inherits the frozen block's endpoint, strict cut,
silence and linear time bound. No second interpreter trace is proved.

**Proof sketch.** The frozen contract supplies a positive exit time. Its
strict interior excludes both exits, so that time is the least positive
exit time used by the public counter loop. -/
private lemma h1RoundTime_spec {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (live : c.state ≠ none) (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true)) (rel : h1RoundRep M.tr c d) :
    0 < h1RoundTime d ∧ h1RoundTime d ≤ 50 * ((tableBitsK M.tr).length + 1) ∧
      let e := (h1RoundTM k).runFrom d (h1RoundTime d)
      e.state = some (h1RoundExit k (M.step c).state.isSome) ∧
      h1RoundRep M.tr (M.step c) e ∧ e.output = d.output ∧
      (∀ u, 0 < u → u < h1RoundTime d → ∃ s,
        ((h1RoundTM k).runFrom d u).state = some s ∧
          s ≠ h1RoundExit k true ∧ s ≠ h1RoundExit k false) := by
  classical
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp live
  obtain ⟨T, positive, bound, state, related, _, cut, silent, _⟩ :=
    h1Round_effect M.tr c q hq d entry rel
  have step : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    simp only [MultiTapeTM.step, hq]
  have existsExit : ∃ t, 0 < t ∧ ∃ b,
      ((h1RoundTM k).runFrom d t).state = some (h1RoundExit k b) :=
    ⟨T, positive, _, state⟩
  have least : Nat.find existsExit = T := by
    apply (Nat.find_eq_iff existsExit).mpr
    refine ⟨⟨positive, _, state⟩, ?_⟩
    intro u hu earlier
    obtain ⟨s, hs, he, hh⟩ := cut u earlier.1 hu
    obtain ⟨b, hb⟩ := earlier.2
    have equal : s = h1RoundExit k b := Option.some.inj (hs.symm.trans hb)
    cases b
    · exact hh equal
    · exact he equal
  have duration : h1RoundTime d = T := by
    simp only [h1RoundTime, dif_pos existsExit, least]
  rw [duration]
  exact ⟨positive, bound, by simpa only [step] using state,
    by simpa only [step] using related, silent T le_rfl, cut⟩

/-- The public body orbit represents the corresponding source run up to
and including its first halting transition. This is the representation
invariant for the existing counter loop, not another physical runner.

**Proof sketch.** Induct on the number of completed source transitions.
Each live source configuration uses the frozen round contract at its
first-return index. The source's run-addition law identifies the successor.
The output prefix is preserved by each cited round. -/
private lemma h1Clock_orbit {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true))
    (rel : h1RoundRep M.tr (M.initCfg x) d)
    (r : ℕ) (live : ∀ u < r, (M.runFrom (M.initCfg x) u).state ≠ none) :
    let e := counterLoopOrbit (h1RoundTM k) h1RoundTime d r
    e.state = some (h1RoundExit k (M.runFrom (M.initCfg x) r).state.isSome) ∧
      h1RoundRep M.tr (M.runFrom (M.initCfg x) r) e ∧ e.output = d.output := by
  induction r with
  | zero => exact ⟨entry, rel, rfl⟩
  | succ r ih =>
    obtain ⟨state, related, output⟩ := ih (fun u hu => live u (by omega))
    have alive := live r (by omega)
    have anchor :
        (counterLoopOrbit (h1RoundTM k) h1RoundTime d r).state =
          some (h1RoundExit k true) := by
      simpa only [Option.isSome_iff_ne_none.mpr alive] using state
    obtain ⟨_, _, hs, hr, ho, _⟩ := h1RoundTime_spec M (M.runFrom (M.initCfg x) r) alive
      (counterLoopOrbit (h1RoundTM k) h1RoundTime d r) anchor related
    change _ ∧ _ ∧ _
    simp only [counterLoopOrbit, Function.iterate_succ_apply']
    simpa only [MultiTapeTM.runFrom_succ_eq_step'] using
      And.intro hs (And.intro hr (ho.trans output))

/-- The clock's round hypotheses and budget follow from the source liveness
invariant and the already proved step-block contract. -/
private lemma h1Clock_round {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true))
    (rel : h1RoundRep M.tr (M.initCfg x) d)
    (r : ℕ) (live : ∀ u ≤ r, (M.runFrom (M.initCfg x) u).state ≠ none) :
    let e := counterLoopOrbit (h1RoundTM k) h1RoundTime d r
    e.state = some (h1RoundExit k true) ∧
      0 < h1RoundTime e ∧ h1RoundTime e ≤ 50 * ((tableBitsK M.tr).length + 1) ∧
      (∀ u, 0 < u → u < h1RoundTime e → ∃ s,
        ((h1RoundTM k).runFrom e u).state = some s ∧
          s ≠ h1RoundExit k true ∧ s ≠ h1RoundExit k false) := by
  obtain ⟨state, related, _⟩ := h1Clock_orbit M d entry rel r
    (fun u hu => live u (Nat.le_of_lt hu))
  have alive := live r le_rfl
  have anchor :
      (counterLoopOrbit (h1RoundTM k) h1RoundTime d r).state =
        some (h1RoundExit k true) := by
    simpa only [Option.isSome_iff_ne_none.mpr alive] using state
  obtain ⟨positive, bound, _, _, _, cut⟩ := h1RoundTime_spec M (M.runFrom (M.initCfg x) r) alive
    (counterLoopOrbit (h1RoundTM k) h1RoundTime d r) anchor related
  exact ⟨anchor, positive, bound, cut⟩

/-- The physical binary clock reaches timeout or simulated halt, with the
source represented at the inclusive deadline and with the exact physical
output prefix preserved. Both exit cuts and every decrement are included.

**Proof sketch.** If the source is still live at the deadline, all previous
configurations are live: apply the public returning loop theorem and its
amortized bound. Otherwise take the public first-halt witness and apply the
escaping theorem to its last transition. Its index is strictly below the
deadline, even for a halt exactly at that deadline. Halt absorption identifies
the represented source endpoint with the deadline configuration. -/
private lemma h1Clock_effect {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true))
    (rel : h1RoundRep M.tr (M.initCfg x) d) (t : ℕ) :
    ∃ T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * t.bits.length + 2,
      ∃ e ct, h1RoundRep M.tr (M.runFrom (M.initCfg x) t) e ∧ e.output = d.output ∧
        (h1ClockTM k).runFrom
          (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) T =
          counterLoopCfg
            (some (if (M.runFrom (M.initCfg x) t).state.isSome then .done else .escape)) e ct 0 ∧
        (∀ u < T,
          ((h1ClockTM k).runFrom
            (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) u).state ≠
              some .done ∧
          ((h1ClockTM k).runFrom
            (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) u).state ≠
              some .escape) := by
  have digits : Nat.ofDigits 2 (t.bits.map Bool.toNat) = t := by
    rw [← canonBits_value]
    exact codeBitsNat_bits t
  by_cases halted : (M.runFrom (M.initCfg x) t).state = none
  · obtain ⟨u, deadline, before, same⟩ := M.exists_first_halt (M.initCfg x) halted
    have positive : 0 < u := by
      by_contra h
      have zero : u = 0 := by omega
      have bad := congrArg Cfg.state same
      rw [zero, halted] at bad
      cases bad
    let r := u - 1
    have count : r + 1 = u := by dsimp [r]; omega
    have live (j : ℕ) (hj : j ≤ r) : (M.runFrom (M.initCfg x) j).state ≠ none :=
      before j (by omega)
    have round (j : ℕ) (hj : j ≤ r) :=
      h1Clock_round M d entry rel j (fun i hi => live i (hi.trans hj))
    obtain ⟨lastState, lastRep, lastOutput⟩ := h1Clock_orbit M d entry rel u before
    rw [same, halted, Option.isSome_none] at lastState
    rw [same] at lastRep
    let T := (∑ j ∈ Finset.range u,
      h1RoundTime (counterLoopOrbit (h1RoundTM k) h1RoundTime d j)) +
        counterOverhead t.bits u
    have run := counterLoopTM_run_escape (h1RoundTM k)
      (h1RoundExit k true) (h1RoundExit k false) (by simp [h1RoundExit])
      h1RoundTime d t.bits (FinTM.bufferTape t.bits) 0
      (by intro p _ _; simp) r (by rw [digits]; omega)
      (fun j hj => ⟨(round j hj).1, (round j hj).2.1, (round j hj).2.2.2⟩)
      (by simpa only [count] using lastState) T (by simp only [T, count])
    have sumBound : (∑ j ∈ Finset.range u,
        h1RoundTime (counterLoopOrbit (h1RoundTM k) h1RoundTime d j)) ≤
        u * (50 * ((tableBitsK M.tr).length + 1)) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range u, (50 * ((tableBitsK M.tr).length + 1)) :=
          Finset.sum_le_sum (fun j hj => (round j (by
            have := Finset.mem_range.mp hj; omega)).2.2.1)
        _ = _ := by simp
    have overhead := counterOverhead_le_of_le t.bits u (by rw [digits]; omega)
    refine ⟨T, ?_, counterLoopOrbit (h1RoundTM k) h1RoundTime d u,
      (fun q => if 0 ≤ q ∧ q < (t.bits.length : ℤ) then
        FinTM.bufferTape (counterWord t.bits u) q else FinTM.bufferTape t.bits q),
      lastRep, lastOutput, ?_, run.2.1⟩
    · have bounded := Nat.mul_le_mul_right (50 * ((tableBitsK M.tr).length + 1)) deadline
      dsimp [T]
      omega
    · simpa only [h1ClockTM, count, halted, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, zero_add, sub_zero] using run.1
  · have live (j : ℕ) (hj : j ≤ t) : (M.runFrom (M.initCfg x) j).state ≠ none :=
      M.runFrom_state_ne_none_of_le (M.initCfg x) t halted j hj
    have round (j : ℕ) (hj : j < t) :=
      h1Clock_round M d entry rel j (fun i hi => live i (by omega))
    let T := (∑ j ∈ Finset.range t,
      h1RoundTime (counterLoopOrbit (h1RoundTM k) h1RoundTime d j)) +
        counterOverhead t.bits (t + 1)
    have run := counterLoopTM_run_done (h1RoundTM k) (h1RoundExit k true)
      (some (h1RoundExit k false)) h1RoundTime d t.bits (FinTM.bufferTape t.bits) 0
      (by intro p _ _; simp) t digits (by
        intro j hj
        obtain ⟨anchor, positive, _, interior⟩ := round j hj
        obtain ⟨next, _, _⟩ := h1Clock_orbit M d entry rel (j + 1)
          (fun i hi => live i (by omega))
        refine ⟨anchor, positive, ?_, ?_⟩
        · intro v hv ht
          obtain ⟨s, hs, ha, he⟩ := interior v hv ht
          exact ⟨s, hs, ha, fun eq => he (Option.some.inj eq).symm⟩
        · simpa only [Option.isSome_iff_ne_none.mpr (live (j + 1) (by omega))] using next)
      T rfl
    obtain ⟨_, finalRep, finalOutput⟩ := h1Clock_orbit M d entry rel t
      (fun j hj => live j (Nat.le_of_lt hj))
    refine ⟨T, counterLoop_time_le (h1RoundTM k) h1RoundTime d t.bits t digits
      (50 * ((tableBitsK M.tr).length + 1)) (fun j hj => (round j hj).2.2.1),
      counterLoopOrbit (h1RoundTM k) h1RoundTime d t,
      (fun q => if 0 ≤ q ∧ q < (t.bits.length : ℤ) then some true
        else FinTM.bufferTape t.bits q), finalRep, finalOutput, ?_,
      run.2.1⟩
    simpa only [h1ClockTM, Option.isSome_iff_ne_none.mpr halted, ↓reduceIte, zero_add]
      using run.1

/-- The completed clock hosted on a buffered input, with a valid boundary
tag at its final seam and strict cuts at both exits for either tag.
The native input is arbitrary and its head is fixed by the public host.

**Proof sketch.** Apply the native clock contract, then the public virtual
input run theorem to its entire execution. Apply that same theorem at each
strict prefix to transfer the two exit cuts; the arrival tag is existential,
never assumed to be the initial tag. -/
private lemma h1HostedClock_effect {k n : ℕ} {x z : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1)))
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true))
    (rel : h1RoundRep M.tr (M.initCfg x) d) (t : ℕ)
    (p : Fin (z.length + 2)) :
    ∃ T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * t.bits.length + 2,
      ∃ e ct b, h1RoundRep M.tr (M.runFrom (M.initCfg x) t) e ∧ e.output = d.output ∧
        FinTM.VirtualTag e.inputPos b ∧
        (h1HostedClockTM k).runFrom
          (vhostCfg (counterLoopCfg (some (.dec .run)) d
            (FinTM.bufferTape t.bits) 0) true p []) T =
          vhostCfg (counterLoopCfg
            (some (if (M.runFrom (M.initCfg x) t).state.isSome then .done else .escape))
            e ct 0) b p [] ∧
        (∀ u < T, ∀ tag,
          ((h1HostedClockTM k).runFrom
            (vhostCfg (counterLoopCfg (some (.dec .run)) d
              (FinTM.bufferTape t.bits) 0) true p []) u).state ≠ some (.done, tag) ∧
          ((h1HostedClockTM k).runFrom
            (vhostCfg (counterLoopCfg (some (.dec .run)) d
              (FinTM.bufferTape t.bits) 0) true p []) u).state ≠ some (.escape, tag)) := by
  obtain ⟨T, bound, e, ct, related, output, run, cut⟩ := h1Clock_effect M d entry rel t
  let start := counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0
  have valid : FinTM.VirtualTag start.inputPos true := by
    change FinTM.VirtualTag d.inputPos true
    rw [rel.1]
    simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨b, tag, hosted⟩ := vhostEmitTM_runFrom (h1ClockTM k) start true valid p [] T
  rw [run] at tag hosted
  refine ⟨T, bound, e, ct, b, related, output, tag, hosted, ?_⟩
  intro u hu tag'
  obtain ⟨b', _, hostedPrefix⟩ := vhostEmitTM_runFrom (h1ClockTM k) start true valid p [] u
  change ((vhostEmitTM (h1ClockTM k)).runFrom (vhostCfg start true p []) u).state ≠ _ ∧ _
  rw [hostedPrefix]
  constructor
  all_goals
    intro bad
    have projected := congrArg (Option.map Prod.fst) bad
    simp only [vhostCfg, Option.map_map, Function.comp_def, Option.map_id_fun',
      Option.map_some] at projected
    first
    | exact (cut u hu).1 projected
    | exact (cut u hu).2 projected

/-- The hosted clock with its two live exits replaced by the one-step
verdict. Timeout emits false; simulated halt tests the restored summary
cell. Every other transition is the existing hosted clock transition. -/
private def h1HostedVerdictTM (k : ℕ) :
    MultiTapeTM (1 + (k + 2 + 1)) Bool (CounterLoopState (Σ key, h1RoundPh k key) × Bool) :=
  { h1HostedClockTM k with tr := fun q inp work =>
      if q.1 = .done ∨ q.1 = .escape then
        ⟨0, fun _ => (none, 0),
          some (if q.1 = .escape then
            work (vhostBank (h1SummaryTape k).castSucc) == some true else false), none⟩
      else (h1HostedClockTM k).tr q inp work }

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
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some (h1RoundExit k true))
    (rel : h1RoundRep M.tr (M.initCfg x) d) (t : ℕ)
    (p : Fin (z.length + 2)) :
    ∃ T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * t.bits.length + 3,
      let e := (h1HostedVerdictTM k).runFrom
        (vhostCfg (counterLoopCfg (some (.dec .run)) d
          (FinTM.bufferTape t.bits) 0) true p []) T
      e.state = none ∧ e.inputPos = p ∧
        e.output = d.output ++ [summaryClock M t (M.initCfg x) none] := by
  obtain ⟨T, bound, e, ct, b, related, output, _, run, cut⟩ :=
    h1HostedClock_effect M d entry rel t p
  let start := vhostCfg (counterLoopCfg (some (.dec .run)) d
    (FinTM.bufferTape t.bits) 0) true p []
  have agree : (h1HostedClockTM k).AgreeOn (h1HostedVerdictTM k)
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
  have cell : e.workTapeSymbols (h1SummaryTape k) =
      outputSummary (M.runFrom (M.initCfg x) t).output := by
    simp only [Cfg.workTapeSymbols, related.2.2.2.2.2, related.2.2.2.1,
      h1SummaryState, ↓reduceIte]
  have semantic : summaryClock M t (M.initCfg x) none =
      ((M.runFrom (M.initCfg x) t).state.isNone &&
        (outputSummary (M.runFrom (M.initCfg x) t).output == some true)) :=
    summaryClock_correct M (M.initCfg x) t
  refine ⟨T + 1, by omega, ?_⟩
  change ((h1HostedVerdictTM k).runFrom start (T + 1)).state = none ∧ _
  rw [MultiTapeTM.runFrom_succ_eq_step', transfer, run]
  rw [semantic]
  have projected :
      (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).workTapeSymbols
        (h1SummaryTape k).castSucc =
        outputSummary (M.runFrom (M.initCfg x) t).output := by
    change (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).workTapes
      (Fin.castSuccEmb (h1SummaryTape k))
      ((embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).workTapePos
        (Fin.castSuccEmb (h1SummaryTape k))) = _
    rw [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
    exact cell
  have projectedOutput :
      (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).output =
        d.output := output
  cases state : (M.runFrom (M.initCfg x) t).state <;>
    simp [MultiTapeTM.step, h1HostedVerdictTM, vhostCfg, counterLoopCfg,
      Cfg.workTapeSymbols, vhostBank, Action.apply, Cfg.mapState,
      projectedOutput, show
        (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).workTapes
            (h1SummaryTape k).castSucc
            ((embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] e).workTapePos
              (h1SummaryTape k).castSucc) =
          outputSummary (M.runFrom (M.initCfg x) t).output from projected]

/-- The hosted verdict's bit is bounded acceptance, by the inherited
semantic bridge. This specializes only the prepared-seam contract: parsing
and canonizer installation are separate startup obligations. -/
private theorem h1HostedVerdict_accepts (F : MachineFormat) (α x z : List Bool)
    (d : Cfg (F.k + 2) Bool (Σ key, h1RoundPh F.k key) x)
    (entry : d.state = some (h1RoundExit F.k true))
    (rel : h1RoundRep (F.machine (F.decode α)).tr
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

**Fill appendix (B5a H1, selected-record partial).** The private `h1RecordTM`
reads the fixed action fields into finite control and executes them on the
mirrored bank and native input, recording the emission by `summaryEmit`.
`h1Record_read`, `h1Record_execute`, and `h1Record_effect`
prove its framed physical trace, source-action relation, silence, first live
exit, and exact `4k + 5` time bound. Its control depends only on `k`; the
public `codeReadActionK_append` supplies the decoding proof. The table head
is left at the actual successor field. Record lookup, successor installation,
restoration of the round seam, nested-input setup, canonizer installation,
and the complete hosted counter loop remain open. This target keeps its
original admission; these new private components contain no admissions.
Addendum 1 is proved for this component by `h1Record_envelope` and is included
in `h1Record_effect`: only the final payload step moves a mirrored or native
input head, each by at most one; the summary head stays fixed and the table
head advances by at most `4k + 4`. The full round's auxiliary-home restoration
and head envelope remain part of the open step-block construction.

**Fill appendix (H1 continuation, partial; complete generic step block).**
The inherited frontier's items 1–3 are now proved in `h1Round_effect` for the
single finite machine `h1RoundFinTM k`. Its control is independent of the coded
state count. Whole-record lookup follows `tableBitsK`'s exact read order,
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
The frozen `h1Round_effect` now feeds the public binary counter loop through
`h1RoundTime_spec`, `h1Clock_orbit`, and `h1Clock_effect`. The counter loop is
inside the public virtual-input host: its round anchor is fixed while the
host's boundary tag may change. `h1HostedClock_effect` proves the valid arrival
tag and strict cuts at both exits, including an escape on the last permitted
round. `h1HostedVerdict_effect` adds one stationary halting emission and gives
the inherited `summaryClock` answer in at most
`t * (50 * (|table| + 1)) + 4 * t + 2 * |bits t| + 3` physical steps.
`h1HostedVerdict_accepts` cites `summaryClock_accepts` for bounded acceptance.
These contracts start at the prepared round seam and introduce no admissions.
Nested-input startup, installation of the frozen canonizer, the joint
polynomial startup ledger, and the end-to-end raw-code note-50 checks remain
open. The headline retains its original admission and pending tag.

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
