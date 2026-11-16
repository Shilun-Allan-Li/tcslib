/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.TuringMachine.Build.ModuleHost
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite scanners with word-valued emissions

This construction extends the existing one-bit transducer to a bounded word per input bit.
It uses the verified emitting loop, with a three-bit control and a shrinking input suffix.
The circuit-description decoder uses its seven control phases.

## Main definitions

* `ChunkScanner.Phase`: three bits of finite control.
* `ChunkScanner.scan`: concatenate the emitted words while advancing the control.

## Main results

* `ChunkScanner.scan_poly`: every such scanner is polynomial-time.

## References

Generic parsing infrastructure for [AB09, §6.2], circuit descriptions. The machine assembly
uses the emitting-loop host of `Complexity.polyTimeComputable_emitIter`.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner

open Complexity Turing

/-- The scanner has three bits of finite control: `Phase = Bool × Bool × Bool`. -/
abbrev Phase := Bool × Bool × Bool

/-- The phase code is the three-bit word `[q.1, q.2.1, q.2.2]`. -/
def phaseCode (q : Phase) : List Bool := [q.1, q.2.1, q.2.2]

/-- `phaseCode q = [q.1, q.2.1, q.2.2]`. -/
theorem phaseCode_eq (q : Phase) : phaseCode q = [q.1, q.2.1, q.2.2] := rfl

/-- Every phase code has length three: `|phaseCode q| = 3`. -/
theorem length_phaseCode (q : Phase) : (phaseCode q).length = 3 := rfl

/-- Read the first three bits, defaulting each missing bit to false. -/
def readPhase (w : List Bool) : Phase :=
  (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false)

/-- `readPhase w = (head w, head (drop 1 w), head (drop 2 w))`, with false defaults. -/
theorem readPhase_eq (w : List Bool) :
    readPhase w = (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false) := rfl

/-- Reading the phase code recovers the phase: `readPhase (phaseCode q) = q`. -/
theorem readPhase_code (q : Phase) : readPhase (phaseCode q) = q := rfl

/-- Concatenate the word `o q b` emitted at each input bit, changing control by `δ q b`. -/
def scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) :
    Phase → List Bool → List Bool
  | _, [] => []
  | q, b :: w => o q b ++ scan δ o (δ q b) w

/-- `scan δ o q [] = []`. -/
theorem scan_nil (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    scan δ o q [] = [] := rfl

/-- `scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w`. -/
theorem scan_cons (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase)
    (b : Bool) (w : List Bool) :
    scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w := rfl

/-- A scanner round stores the next three-bit control and removes one input bit. -/
def step (δ : Phase → Bool → Phase) (w : List Bool) : List Bool :=
  pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
    ((pairSndD w).drop 1)

/-- `step δ w` pairs the next phase code with `(pairSndD w).drop 1`. -/
theorem step_eq (δ : Phase → Bool → Phase) (w : List Bool) :
    step δ w =
      pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
        ((pairSndD w).drop 1) := rfl

/-- A scanner emits nothing on an empty suffix, and otherwise emits `o q (head suffix)`. -/
def emit (o : Phase → Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then [] else o (readPhase (pairFstD w)) ((pairSndD w).headD false)

/-- `emit o w` is empty on an empty second component and otherwise is the table entry. -/
theorem emit_eq (o : Phase → Bool → List Bool) (w : List Bool) :
    emit o w =
      if pairSndD w = [] then []
      else o (readPhase (pairFstD w)) ((pairSndD w).headD false) := rfl

/-- A fixed table of four polynomial-time Boolean tests is polynomial-time.

**Proof sketch.** Branch on the four bits in turn using the existing polynomial-time
conditional combinator. Each of the sixteen leaves is the corresponding constant word;
case analysis on the four bits identifies the resulting decision tree with the table. -/
private theorem table4_poly (F : Bool → Bool → Bool → Bool → List Bool)
    {a b c d : List Bool → Bool}
    (ha : PolyTimeComputable fun w => [a w])
    (hb : PolyTimeComputable fun w => [b w])
    (hc : PolyTimeComputable fun w => [c w])
    (hd : PolyTimeComputable fun w => [d w]) :
    PolyTimeComputable fun w => F (a w) (b w) (c w) (d w) := by
  convert (polyTimeComputable_ite ha
    (polyTimeComputable_ite hb
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true true true true))
    (polyTimeComputable_const (F true true true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true true false true))
    (polyTimeComputable_const (F true true false false))))
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true false true true))
    (polyTimeComputable_const (F true false true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true false false true))
    (polyTimeComputable_const (F true false false false)))))
    (polyTimeComputable_ite hb
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false true true true))
    (polyTimeComputable_const (F false true true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false true false true))
    (polyTimeComputable_const (F false true false false))))
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false false true true))
    (polyTimeComputable_const (F false false true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false false false true))
    (polyTimeComputable_const (F false false false false)))))) using 1
  funext w
  cases a w <;> cases b w <;> cases c w <;> cases d w <;> rfl

/-- The three-bit phase type is the Boolean triple: `Phase = Bool × Bool × Bool`. -/
theorem phase_eq : Phase = (Bool × Bool × Bool) := rfl

/-- Each scanner round is polynomial-time: `PolyTimeComputable (step δ)`. -/
theorem step_poly (δ : Phase → Bool → Phase) : PolyTimeComputable (step δ) := by
  exact (table4_poly (fun a b c d => phaseCode (δ (a, b, c) d))
    (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_headD.comp
      ((BinArith.polyTimeComputable_drop 1).comp polyTimeComputable_pairFstD))
    (polyTimeComputable_headD.comp
      ((BinArith.polyTimeComputable_drop 2).comp polyTimeComputable_pairFstD))
    (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

/-- Every finite emission table is polynomial-time: `PolyTimeComputable (emit o)`. -/
theorem emit_poly (o : Phase → Bool → List Bool) : PolyTimeComputable (emit o) := by
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const [])
    (table4_poly (fun a b c d => o (a, b, c) d)
      (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_headD.comp
        ((BinArith.polyTimeComputable_drop 1).comp polyTimeComputable_pairFstD))
      (polyTimeComputable_headD.comp
        ((BinArith.polyTimeComputable_drop 2).comp polyTimeComputable_pairFstD))
      (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)) using 1
  funext w
  simp only [emit_eq, readPhase_eq, decide_eq_true_eq, Function.comp_apply]

/-- On a phase/suffix pair the round advances its phase and drops one suffix bit. -/
theorem step_pair (δ : Phase → Bool → Phase) (q : Phase) (w : List Bool) :
    step δ (pairEncode (phaseCode q) w) =
      pairEncode (phaseCode (δ q (w.headD false))) (w.drop 1) := by
  rw [step_eq, pairFstD_pairEncode, pairSndD_pairEncode, readPhase_code]

/-- On a phase/suffix pair emission is empty exactly for the exhausted suffix. -/
theorem emit_pair (o : Phase → Bool → List Bool) (q : Phase) (w : List Bool) :
    emit o (pairEncode (phaseCode q) w) =
      if w = [] then [] else o q (w.headD false) := by
  rw [emit_eq, pairFstD_pairEncode, pairSndD_pairEncode, readPhase_code]

/-- The input suffix does not grow in one round:
`|pairSndD (step δ w)| ≤ |pairSndD w|`. -/
theorem length_snd_step (δ : Phase → Bool → Phase) (w : List Bool) :
    (pairSndD (step δ w)).length ≤ (pairSndD w).length := by
  rw [step_eq, pairSndD_pairEncode, List.length_drop]
  omega

/-- Every iterated suffix stays within the original word:
`|pairSndD ((step δ)^[i] w)| ≤ |w|`. -/
theorem length_snd_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    (pairSndD ((step δ)^[i] w)).length ≤ w.length := by
  induction i with
  | zero => exact length_pairSndD_le w
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_snd_step δ _).trans ih

/-- Every scanner state has a linear envelope:
`|((step δ)^[i]) w| ≤ 9 · (|w| + 1)`. -/
theorem length_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    ((step δ)^[i] w).length ≤ 9 * (w.length + 1) := by
  cases i with
  | zero => simp only [Function.iterate_zero_apply]; omega
  | succ i =>
    rw [Function.iterate_succ_apply', step_eq, length_pairEncode, length_phaseCode,
      List.length_drop]
    have h := length_snd_iterate δ w i
    omega

/-- Emitting along at least `|w|` rounds of the encoded scanner yields `scan δ o q w`.

**Proof sketch.** Induct on the round budget. The first round emits the head's table entry,
then the next state holds the remaining input. Once the suffix is empty all later emissions
are empty, so any budget at least the input length gives the same result. -/
theorem flatMap_scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool)
    (N : ℕ) (q : Phase) (w : List Bool) (hN : w.length ≤ N) :
    (List.range N).flatMap
        (fun i => emit o ((step δ)^[i] (pairEncode (phaseCode q) w))) =
      scan δ o q w := by
  induction N generalizing q w with
  | zero =>
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw
    rfl
  | succ N ih =>
    -- Peel the first round and run the remaining budget from the next state.
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
    rw [emit_pair, step_pair]
    cases w with
    | nil =>
      simp only [List.headD_nil, List.drop_nil, scan_nil]
      exact ih (δ q false) [] (by simp)
    | cons b w =>
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero,
        List.cons_ne_nil, if_false, scan_cons]
      rw [ih (δ q b) w (by simpa using hN)]

/-- A finite word-emitting scanner is polynomial-time:
`PolyTimeComputable (scan δ o q)`.

**Proof sketch.** Use the public emitting-loop host on the encoded phase and suffix.
The round and emission tables are polynomial-time finite Boolean tables; every round's
state length is bounded by `9 · (|input| + 1)`. The initial pair supplies more rounds than
there are input bits, and `flatMap_scan` identifies the emitted word exactly. -/
theorem scan_poly (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    PolyTimeComputable (scan δ o q) := by
  have h := polyTimeComputable_emitIter (step_poly δ) (emit_poly o) 1 1 9 1
    (fun w i => by simpa only [Nat.pow_one] using length_iterate δ w i)
  have hpre : PolyTimeComputable fun w => pairEncode (phaseCode q) w :=
    (polyTimeComputable_const (phaseCode q)).pairEncode polyTimeComputable_id
  convert h.comp hpre using 1
  funext w
  simp only [Function.comp_apply, Nat.one_mul, Nat.pow_one]
  symm
  apply flatMap_scan
  rw [length_pairEncode]
  omega

/-- One clean finite machine installs the scanner's value and emits nothing within
`A · (|arg| + 1)^d` steps. Every work head of that same machine remains within that bound
at every time. The machine is the public H14 clean-install module for `scan δ o q`. -/
theorem scan_host (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (scan δ o q) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
      ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(M.tm.runFrom
          (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
            (A * (arg.length + 1) ^ d : ℕ) := by
  obtain ⟨M, A, d, hM⟩ := ModuleHost.clean_install (scan_poly δ o q)
  exact ⟨M, A, d, hM, fun x arg v j => hM.envelope x arg v j⟩

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner
