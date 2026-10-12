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
* **Status update (B5a continuation): partial.** The two headline contracts
  retain their original admissions. The native-input binary-header loader and
  the physical fail-fast binary length guard are proved; the remaining parser
  phases, complete canonizer, and generic interpreter are still open.

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
reported separately in the delivery evidence. -/
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
host assembly, and its ledger remain open; this target retains its admission. **Fill appendix
(B5a H1, selected-record partial).** The private
`h1RecordTM` reads the fixed action fields into finite control and executes
them on the mirrored bank and native input, recording the emission by
`summaryEmit`. `h1Record_read`, `h1Record_execute`, and `h1Record_effect`
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
