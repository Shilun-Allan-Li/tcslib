/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines: the candidate simulator

This file assembles the oblivious candidate machine: the data payload alphabet,
the source decider's virtual-tape transduction `obliviousVisit`, and the machine
`obliviousCandidate` obtained by decorating the length-only schedule with it and
coding the result transversely, whose obliviousness is inherited layer by layer.
It also proves the run identities that the later cost and correctness analysis
consumes: the binary budget counter and its borrow sweeps, the one-lane
transduction lemma `lane_run`, the source payload correspondence for virtual
heads, the captured-clock stage `clockStageCfg_captures`, and the guide-tape
macrostep cycle for `macroCfg`. It was split out mechanically from
`Robustness/Oblivious.lean` at the epoch-3→4 merge; provenance: epoch-3 fill,
batch C.

## Main definitions

* `Complexity.obliviousCandidate` — the oblivious simulator produced for the
  final theorem.
* `Complexity.macroCfg`, `Complexity.clockStageCfg` — explicit configurations
  for the schedule's macrostep cycle and clock stage.

## Main results

* `Complexity.obliviousCandidate_oblivious` — the candidate is oblivious, with
  no computation or halting hypothesis.
* `Complexity.clockStageCfg_captures` — the clock stage captures the budget word.
* `Complexity.macroCfg_finish` — the schedule ends after exactly the budgeted
  macrosteps plus a final counter test.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, Exercise 1.5.)
-/

namespace Complexity

open Turing

/-- Payload tags distinguish ordinary cells from the two virtual input
boundaries. A logical head is at the guide's marked origin; moving a virtual
head shifts its represented tape while the physical schedule stays fixed. -/
abbrev OblPayload := Option Bool × Fin 3

/-- Blank payload, used also for the neighbor just outside a sweep. -/
def blankPayload : OblPayload := (none, 0)

/-- Untouched physical blanks decode to a blank payload and blank neighbor. -/
def dataCell : Option OblSymbol → OblPayload × OblPayload
  | some (.cell current left) => (current, left)
  | _ => (blankPayload, blankPayload)

/-- The source state, saved answer, source reads at macrostep entry, and sweep
neighbor registers form a finite data state. Coordinates stay on tapes. -/
abbrev OblData (M : FinTM Bool) :=
  Option M.State × Bool × (Fin (M.k + 1) → OblPayload) × (Fin (M.k + 1) → OblPayload)

/-- The source action is the identity after halting. It never halts or shortens
the physical schedule, whose state is maintained separately. -/
def obliviousSourceAction (M : FinTM Bool) (q : Option M.State)
    (read : Fin (M.k + 1) → OblPayload) : Action M.k Bool M.State :=
  match q with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => M.tm.tr q (read (Fin.natAdd M.k (0 : Fin 1))).1
      (fun i => (read (i.castAdd 1)).1)

/-- Directions of virtual work heads and the clamped virtual input head.
These directions select shifted payloads, never physical head moves. -/
def obliviousSourceMove (M : FinTM Bool) (q : Option M.State)
    (read : Fin (M.k + 1) → OblPayload) : Fin (M.k + 1) → SignType :=
  let a := obliviousSourceAction M q read
  Fin.addCases (fun i => (a.workTapes i).2) (fun _ =>
    let tag := (read (Fin.natAdd M.k (0 : Fin 1))).2
    if (tag = 1 ∧ a.inputTape = .neg) ∨ (tag = 2 ∧ a.inputTape = .pos)
    then 0 else a.inputTape)

/-- The initial data state has a live source state, no answer emission, and
blank sweep registers. -/
def obliviousDataInit (M : FinTM Bool) : OblData M :=
  (some M.tm.q₀, false, fun _ => blankPayload, fun _ => blankPayload)

/-- Data updates along the prescribed schedule. The input is copied with
explicit boundary payloads. At each marked origin the source transition is
selected and its writes are performed. The forward sweep caches left neighbors;
the backward sweep shifts each tape according to its virtual move. The return
to the origin installs the source successor state, including the idle `none`.
Only the final failed unary-counter test emits the stored answer. -/
def obliviousVisit (W M : FinTM Bool) (a : ℕ)
    (phase : OblPhase W.State a) (d : OblData M) (inp : Option OblSymbol)
    (schedule : Fin (W.k + 3) → Option OblSymbol)
    (data : Fin (M.k + 1) → Option OblSymbol) :
    OblData M × (Fin (M.k + 1) → Option (Option OblSymbol)) × Option OblSymbol :=
  let unary := schedule (Fin.natAdd W.k (1 : Fin 3))
  let guide := schedule (Fin.natAdd W.k (2 : Fin 3))
  let noWrites := fun (_ : Fin (M.k + 1)) => (none : Option (Option OblSymbol))
  let keep := (d, noWrites, (none : Option OblSymbol))
  let current := fun i => (dataCell (data i)).1
  let copy (payload : OblPayload) :=
    (d, Fin.addCases (fun _ => none) (fun (_ : Fin 1) =>
      some (some (.cell payload blankPayload))), (none : Option OblSymbol))
  match phase with
  | .copyLeftWrite => copy (none, 1)
  | .copyFirst | .copyMore =>
    copy (clockBit inp, if inp.isNone then 2 else 0)
  | .macroCheck =>
    if unary = some .unit then
      let action := obliviousSourceAction M d.1 current
      ((d.1, action.output.getD d.2.1, current, fun _ => blankPayload),
        Fin.addCases (fun i => (action.workTapes i).1.map (fun p =>
          some (.cell (p, 0) blankPayload))) (fun _ => none), none)
    else (d, noWrites, some (.bit d.2.1))
  | .seekLeft =>
    if guide = some (.edge false) then
      ((d.1, d.2.1, d.2.2.1, fun _ => blankPayload), noWrites, none)
    else keep
  | .forward =>
    if guide = some (.edge true) then
      ((d.1, d.2.1, d.2.2.1, fun _ => blankPayload), noWrites, none)
    else
      ((d.1, d.2.1, d.2.2.1, current),
        fun i => some (some (.cell (current i) (d.2.2.2 i))), none)
  | .backward =>
    if guide = some (.edge false) then keep
    else
      ((d.1, d.2.1, d.2.2.1, current),
        fun i => some (some (.cell
          (match obliviousSourceMove M d.1 d.2.2.1 i with
            | .neg => (dataCell (data i)).2
            | .zero => current i
            | .pos => d.2.2.2 i) blankPayload)), none)
  | .returnCenter =>
    if guide = some .origin then
      (((obliviousSourceAction M d.1 d.2.2.1).state, d.2.1, d.2.2.1, d.2.2.2), noWrites, none)
    else keep
  | _ => keep

/-- The concrete binary simulator candidate. The finite alphabet is realized
by simultaneous transverse binary blocks, retaining the exact schedule. -/
noncomputable def obliviousCandidate (W M : FinTM Bool) (a : ℕ) : FinTM Bool := by
  classical
  exact parallelTM
    (decorateTM (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
      (obliviousDataInit M) (obliviousVisit W M a)) oblEmbed

/-- The concrete simulator is oblivious on all binary inputs of every length,
including empty input and inputs with different simulated answers. No source
computation assumption is used in this trajectory theorem. -/
lemma obliviousCandidate_oblivious (W M : FinTM Bool) (a : ℕ) :
    (obliviousCandidate W M a).Oblivious := by
  classical
  unfold obliviousCandidate
  apply parallelTM_oblivious
  exact decorateTM_oblivious _ _ _ _ _ (obliviousSchedule_output W a)
    (obliviousSchedule_oblivious W a)

/-- An already halted source contributes no further writes, no output, and no
virtual movement. The surrounding physical schedule nevertheless continues. -/
private lemma obliviousSourceAction_idle (M : FinTM Bool)
    (read : Fin (M.k + 1) → OblPayload) :
    obliviousSourceAction M none read = ⟨0, fun _ => (none, 0), none, none⟩ := rfl

/-- Every virtual head is stationary during an idle macrostep. -/
private lemma obliviousSourceMove_idle (M : FinTM Bool)
    (read : Fin (M.k + 1) → OblPayload) :
    obliviousSourceMove M none read = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [obliviousSourceMove, obliviousSourceAction]
  · simp [obliviousSourceMove, obliviousSourceAction]

/-- The little-endian value of a possibly zero-padded budget word. -/
def budgetValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (budgetValue bs)

/-- The clock's canonical bit representation has the prescribed numeric value. -/
lemma budgetValue_bits (n : ℕ) : budgetValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [budgetValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simp only [budgetValue, ih]

/-- The fixed-width borrow pass of the budget controller. It always processes
the whole word, retaining its width even when leading high bits become zero. -/
def budgetBorrow : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: bs =>
    let rest := budgetBorrow (carry && !b) bs
    (rest.1, Bool.xor b carry :: rest.2)

/-- A cleared borrow leaves every remaining bit unchanged. -/
private lemma budgetBorrow_false (bs : List Bool) : budgetBorrow false bs = (false, bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [budgetBorrow, ih]

/-- Every borrow pass has exactly the original word width. -/
lemma budgetBorrow_length (carry : Bool) (bs : List Bool) :
    (budgetBorrow carry bs).2.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [budgetBorrow, List.length_cons, ih]

/-- Borrow underflow occurs exactly at numeric zero, even for padded words. -/
lemma budgetBorrow_underflow (bs : List Bool) :
    (budgetBorrow true bs).1 = true ↔ budgetValue bs = 0 := by
  induction bs with
  | nil => simp [budgetBorrow, budgetValue]
  | cons b bs ih =>
    cases b <;> simp [budgetBorrow, budgetBorrow_false, budgetValue, Nat.bit_val, ih]

/-- A successful full-width borrow subtracts exactly one.
**Proof sketch.** For a low one, clear it and leave the tail unchanged. For a
low zero, the positive input has a positive high part; recursively decrement
that part and write a low one. Underflow is excluded by positivity. -/
lemma budgetBorrow_value (bs : List Bool) (h : 0 < budgetValue bs) :
    budgetValue (budgetBorrow true bs).2 + 1 = budgetValue bs := by
  induction bs with
  | nil => simp [budgetValue] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have ht : 0 < budgetValue bs := by simpa [budgetValue, Nat.bit_val] using h
      have hb := ih ht
      change Nat.bit true (budgetValue (budgetBorrow true bs).2) + 1 = Nat.bit false (budgetValue bs)
      simp only [Nat.bit_val]
      change (2 * budgetValue (budgetBorrow true bs).2 + 1) + 1 = 2 * budgetValue bs + 0
      omega
    | true => simp [budgetBorrow, budgetBorrow_false, budgetValue, Nat.bit_val]

/-- A single active tape lane, with every inactive tape taken from a base
configuration. This supports exact setup transductions in a multi-tape machine. -/
def laneCfg {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) : Cfg k A S x :=
  ⟨q, base.inputPos, Function.update base.workTapes lane (FinTM.sweepTape z l r),
    Function.update base.workTapePos lane z, base.output⟩

/-- An action that writes and moves just one lane, leaving input and output
stationary. -/
private def laneAction {A S : Type} {k : ℕ} (lane : Fin k) (q : S)
    (s : Option A) (d : SignType) : Action k A S :=
  ⟨0, Function.update (fun _ => (none, 0)) lane (some s, d), none, some q⟩

/-- The active lane reads the first unprocessed zipper entry. -/
private lemma laneCfg_read {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) :
    (laneCfg base lane q z l r).workTapeSymbols lane = r.head?.join := by
  simp only [laneCfg, Cfg.workTapeSymbols, Function.update_self, FinTM.sweepTape_read]

/-- The right-moving zipper identity lifts to one lane of any machine. -/
private lemma laneCfg_right {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S) (q' : S)
    (z : ℤ) (l r : List (Option A)) (a b : Option A) :
    (laneAction lane q' b .pos).apply (laneCfg base lane q z l (a :: r)) =
      laneCfg base lane (some q') (z + 1) (b :: l) r := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    by_cases hi : i = lane
    · subst i
      simp only [laneAction, laneCfg, Action.apply, Function.update_self]
      exact FinTM.sweepTape_right z l r a b
    · simp only [laneAction, laneCfg, Action.apply, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = lane
    · subst i
      simp [laneAction, laneCfg]
    · simp [laneAction, laneCfg, hi]
  · exact List.append_nil _

/-- A finite forward transduction on one lane has exact cost equal to its word
length, without changing inactive tapes.
**Proof sketch.** The first entry supplies the local transition hypothesis.
One write-and-right step moves it into the left zipper stack, and induction
processes the remaining word. The full resulting configuration is retained. -/
private lemma lane_run {A S R C : Type} {k : ℕ} {x : List A}
    (tm : MultiTapeTM k A S) (lane : Fin k)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s c inp ws, ws lane = some (symbol c) →
      tm.tr (state s) inp ws = laneAction lane (state (visit s c).1)
        (some (symbol (visit s c).2)) .pos)
    (base : Cfg k A S x) (as : List C) (s : R)
    (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (laneCfg base lane (some (state s)) z l
      (as.map (fun c => some (symbol c)) ++ r)) as.length =
    laneCfg base lane (some (state (FinTM.sweepFold visit s as).1)) (z + as.length)
      (((FinTM.sweepFold visit s as).2.map (fun c => some (symbol c))).reverse ++ l) r := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, MultiTapeTM.runFrom_zero,
      FinTM.sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (laneCfg base lane (some (state s)) z l
        (some (symbol a) :: (as.map (fun c => some (symbol c)) ++ r))).workTapeSymbols lane =
        some (symbol a) := laneCfg_read _ _ _ _ _ _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [htr s a _ _ hr, laneCfg_right, ih]
    simp only [FinTM.sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Local finite transducer for a full-width binary borrow. -/
private def budgetVisit (carry b : Bool) : Bool × Bool := (carry && !b, Bool.xor b carry)

/-- The sweep fold is precisely the fixed-width borrow operation. -/
private lemma budgetFold (carry : Bool) (bs : List Bool) :
    FinTM.sweepFold budgetVisit carry bs = budgetBorrow carry bs := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [FinTM.sweepFold, budgetVisit, budgetBorrow, ih]

/-- Updating the budget lane of the three-tape schedule is a focused action. -/
private lemma oblAction_budget {S : Type} {k : ℕ} (q : S)
    (b : Option OblSymbol) (d : SignType) :
    oblAction (k := k) (some q) 0 (some b, d) (none, 0) (none, 0) =
      laneAction (Fin.natAdd k (0 : Fin 3)) q b d := by
  unfold oblAction laneAction
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hn : j.castAdd 3 ≠ Fin.natAdd k (0 : Fin 3) := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = k + 0 at hv
      have := j.isLt
      omega
    simp [hn]
  · by_cases hj : j = 0
    · subst j
      simp
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hn : Fin.natAdd k j ≠ Fin.natAdd k (0 : Fin 3) := by
        intro he
        apply hj
        apply Fin.ext
        have hh := congrArg Fin.val he
        simpa using hh
      simp [hj, hn]

/-- The concrete controller's borrow transition realizes the local bit rule. -/
private lemma obliviousSchedule_borrow (W : FinTM Bool) (a : ℕ)
    (carry b : Bool) (inp : Option OblSymbol) (ws : Fin (W.k + 3) → Option OblSymbol)
    (hw : ws (Fin.natAdd W.k (0 : Fin 3)) = some (.bit b)) :
    (obliviousSchedule W a).tm.tr (.borrow carry) inp ws =
      laneAction (Fin.natAdd W.k (0 : Fin 3))
        (OblPhase.borrow (S := W.State) (a := a) (carry && !b))
        (some (.bit (Bool.xor b carry))) .pos := by
  simp only [obliviousSchedule, hw]
  exact oblAction_budget _ _ _

/-- The implemented borrow pass has exact cost equal to the captured word's
width and exactly the abstract numeric result. Other tape contents and head
positions, including copied input data in later decorations, are unchanged. -/
lemma obliviousSchedule_borrow_run (W : FinTM Bool) (a : ℕ)
    {x : List OblSymbol} (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (carry : Bool) (bs : List Bool) (z : ℤ) (l r : List (Option OblSymbol)) :
    (obliviousSchedule W a).tm.runFrom
      (laneCfg base (Fin.natAdd W.k (0 : Fin 3)) (some (.borrow carry)) z l
        (bs.map (fun b => some (.bit b)) ++ r)) bs.length =
      laneCfg base (Fin.natAdd W.k (0 : Fin 3))
        (some (.borrow (budgetBorrow carry bs).1)) (z + bs.length)
        (((budgetBorrow carry bs).2.map (fun b => some (.bit b))).reverse ++ l) r := by
  have h := lane_run (obliviousSchedule W a).tm (Fin.natAdd W.k (0 : Fin 3))
    OblPhase.borrow OblSymbol.bit budgetVisit (obliviousSchedule_borrow W a) base bs carry z l r
  simpa only [budgetFold] using h

/-- The virtual input word has separate left and right boundary payloads. -/
def inputPayload (x : List Bool) (z : ℤ) : OblPayload :=
  (FinTM.bufferTape x z, if z = -1 then 1 else if z = x.length then 2 else 0)

/-- The boundary tag at a native source input position. -/
private def inputTag {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Fin 3 :=
  if c.inputPos.val = 0 then 1 else if c.inputPos.val = x.length + 1 then 2 else 0

/-- The virtual input payload at its head gives precisely the native read and
boundary tag, including both boundaries on empty input. -/
private lemma inputPayload_head {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) :
    inputPayload x ((c.inputPos.val : ℤ) - 1) = (c.inputSymbol, inputTag c) := by
  unfold inputPayload inputTag
  rw [FinTM.bufferTape_inputSymbol]
  have hleft : (c.inputPos.val : ℤ) - 1 = -1 ↔ c.inputPos.val = 0 := by omega
  have hright : (c.inputPos.val : ℤ) - 1 = x.length ↔ c.inputPos.val = x.length + 1 := by omega
  simp only [hleft, hright]

/-- Native input clamping, expressed as a virtual tape-shift direction. -/
private def clippedMove {n : ℕ} (p : Fin (n + 2)) (d : SignType) : SignType :=
  if (p.val = 0 ∧ d = .neg) ∨ (p.val = n + 1 ∧ d = .pos) then 0 else d

/-- The clipped virtual displacement equals the native input-head displacement. -/
private lemma clippedMove_correct {n : ℕ} (p : Fin (n + 2)) (d : SignType) :
    ((moveInputPos p d).val : ℤ) - 1 = (p.val : ℤ) - 1 + (clippedMove p d : ℤ) := by
  cases d with
  | zero => simp [clippedMove]
  | neg =>
    rw [FinTM.moveInputPos_neg_val]
    by_cases h : p.val = 0
    · simp [clippedMove, h]
    · have hm : clippedMove p .neg = .neg := by simp [clippedMove, h]
      rw [hm]
      change ((p.val - 1 : ℕ) : ℤ) - 1 = (p.val : ℤ) - 1 + (-1)
      omega
  | pos =>
    by_cases h : p.val = n + 1
    · have hp : p = ⟨n + 1, by omega⟩ := Fin.ext h
      rw [hp]
      simp [clippedMove, SignType.pos_eq_one]
    · rw [moveInputPos_pos_of_ne_right p h]
      simp [clippedMove, h]

/-- Head-centered source tape payloads. The last tape is the copied virtual
input; the earlier tapes are the source work tapes. -/
def sourcePayload {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (z : ℤ) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i => (c.workTapes i (c.workTapePos i + z), 0))
    (fun _ => inputPayload x ((c.inputPos.val : ℤ) - 1 + z))

/-- Source reads at a macrostep origin. -/
private def sourceReads {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i => (c.workTapeSymbols i, 0)) (fun _ => (c.inputSymbol, inputTag c))

/-- Reading the marked origin obtains all source reads simultaneously. -/
private lemma sourcePayload_origin {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : sourcePayload c 0 = sourceReads c := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [sourcePayload, sourceReads, Cfg.workTapeSymbols]
  · simp [sourcePayload, sourceReads, inputPayload_head]

/-- Interpret halting as an identity action for an idle macrostep. -/
def sourceTotalAction (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Action M.k Bool M.State :=
  match c.state with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => M.tm.tr q c.inputSymbol c.workTapeSymbols

/-- The data controller selects the exact source transition at the origin. -/
lemma obliviousSourceAction_correct (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    obliviousSourceAction M c.state (sourcePayload c 0) = sourceTotalAction M c := by
  rw [sourcePayload_origin]
  cases hs : c.state <;> simp [obliviousSourceAction, sourceTotalAction, hs, sourceReads]

/-- Applying the totalized action is exactly one source step, including idle
steps after source halting. -/
lemma sourceTotalAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : (sourceTotalAction M c).apply c = M.tm.step c := by
  cases hs : c.state with
  | none =>
    apply Cfg.ext
    · simpa only [sourceTotalAction, hs, Action.apply, MultiTapeTM.step] using hs.symm
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
    · funext i
      simp [sourceTotalAction, hs, MultiTapeTM.step]
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
  | some q => simp [sourceTotalAction, MultiTapeTM.step, hs]

/-- The shifts prescribed by a supplied source action. -/
private def sourceShift {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) : Fin (k + 1) → SignType :=
  Fin.addCases (fun i => (a.workTapes i).2) (fun _ => clippedMove c.inputPos a.inputTape)

/-- The controller's virtual shift agrees with native clamping and source work
head movement. -/
lemma obliviousSourceMove_correct (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    obliviousSourceMove M c.state (sourcePayload c 0) = sourceShift c (sourceTotalAction M c) := by
  unfold obliviousSourceMove
  rw [obliviousSourceAction_correct, sourcePayload_origin]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [sourceShift]
  · simp only [Fin.addCases_right, sourceReads, sourceShift]
    have hp := c.inputPos.isLt
    by_cases hl : c.inputPos.val = 0
    · simp [inputTag, clippedMove, hl]
    · by_cases hr : c.inputPos.val = x.length + 1
      · simp [inputTag, clippedMove, hl, hr]
      · simp [inputTag, clippedMove, hl, hr]

/-- The origin write precedes tape shifting. Input payloads are read-only. -/
def sourceWrittenPayload {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i =>
    (if z = 0 then (a.workTapes i).1.getD (c.workTapeSymbols i)
      else c.workTapes i (c.workTapePos i + z), 0))
    (fun _ => inputPayload x ((c.inputPos.val : ℤ) - 1 + z))

/-- **Head-centered simulation identity.** Write at the old origin, then shift
each virtual tape by its source displacement. The resulting payloads are those
of the next source configuration.

**Proof sketch.** For a work tape, the updated cell is at old relative coordinate
zero and the new head offset is exactly its movement. For the input tape the
word is unchanged and the clamped-displacement identity changes only its origin.
This includes stationary moves, boundary attempts, and writes of blank. -/
lemma sourcePayload_apply {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) (i : Fin (k + 1)) :
    sourcePayload (a.apply c) z i =
      sourceWrittenPayload c a (z + (sourceShift c a i : ℤ)) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sourcePayload, sourceShift, sourceWrittenPayload, Fin.addCases_left]
    have he : c.workTapePos j + ((a.workTapes j).2 : ℤ) + z =
        c.workTapePos j + (z + ((a.workTapes j).2 : ℤ)) := by omega
    dsimp only [Action.apply]
    rw [he]
    by_cases hz : z + ((a.workTapes j).2 : ℤ) = 0
    · rw [hz]
      simp only [add_zero, if_true]
      cases hw : (a.workTapes j).1 <;> simp [hw, Cfg.workTapeSymbols]
    · have hn : c.workTapePos j + (z + ((a.workTapes j).2 : ℤ)) ≠ c.workTapePos j := by omega
      cases hw : (a.workTapes j).1 <;> simp [hz, hw, Function.update_of_ne hn]
  · simp only [sourcePayload, sourceShift, sourceWrittenPayload, Fin.addCases_right, Action.apply]
    rw [clippedMove_correct]
    congr 1
    omega

/-- One parallel row of a head-centered tape layout. -/
private def payloadRow {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) (cached : Bool) :
    I → OblPayload × OblPayload :=
  fun i => (f z i, if cached then f (z - 1) i else blankPayload)

/-- The forward row transducer records its incoming left neighbor. -/
private def payloadForward {I : Type} (left : I → OblPayload)
    (row : I → OblPayload × OblPayload) :
    (I → OblPayload) × (I → OblPayload × OblPayload) :=
  (fun i => (row i).1, fun i => ((row i).1, left i))

/-- The return row transducer chooses the neighbor selected by each virtual
head movement while all physical heads move left. -/
private def payloadBackward {I : Type} (d : I → SignType) (right : I → OblPayload)
    (row : I → OblPayload × OblPayload) :
    (I → OblPayload) × (I → OblPayload × OblPayload) :=
  (fun i => (row i).1, fun i =>
    ((match d i with | .neg => (row i).2 | .zero => (row i).1 | .pos => right i), blankPayload))

/-- A forward row preserves the payload and records exactly its left neighbor. -/
private lemma payloadForward_row {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) :
    payloadForward (f (z - 1)) (payloadRow f z false) = (f z, payloadRow f z true) := rfl

/-- A backward row implements the chosen shifts exactly. -/
private lemma payloadBackward_row {I : Type} (f : ℤ → I → OblPayload)
    (d : I → SignType) (z : ℤ) :
    payloadBackward d (f (z + 1)) (payloadRow f z true) =
      (f z, payloadRow (fun z i => f (z + (d i : ℤ)) i) z false) := by
  apply Prod.ext
  · rfl
  · funext i
    cases hd : d i <;> simp [payloadBackward, payloadRow, hd, SignType.cast, sub_eq_add_neg]

/-- Consecutive parallel rows of the fixed layout. -/
private def payloadZone {I : Type} (f : ℤ → I → OblPayload) (z : ℤ)
    (cached : Bool) : ℕ → List (I → OblPayload × OblPayload)
  | 0 => []
  | n + 1 => payloadRow f z cached :: payloadZone f (z + 1) cached n

/-- Every guide cell contributes exactly one parallel data row. -/
private lemma payloadZone_length {I : Type} (f : ℤ → I → OblPayload) (z : ℤ)
    (cached : Bool) (n : ℕ) : (payloadZone f z cached n).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [payloadZone, List.length_cons, ih]

/-- The full forward transduction installs all left-neighbor caches.
**Proof sketch.** The first row supplies the next carry register, and induction
handles the remaining consecutive rows. The visited interval is fixed throughout. -/
private lemma payloadForward_zone {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold payloadForward (f (z - 1)) (payloadZone f z false n) =
      (f (z + n - 1), payloadZone f z true n) := by
  induction n generalizing z with
  | zero => simp [payloadZone, FinTM.sweepFold]
  | succ n ih =>
    simp only [payloadZone, FinTM.sweepFold, payloadForward_row]
    rw [show f z = f (z + 1 - 1) from congrArg f (by omega)]
    rw [ih]
    rw [show z + 1 + (n : ℤ) - 1 = z + (n + 1 : ℕ) - 1 by omega]

/-- The full return transduction shifts every row as prescribed.
**Proof sketch.** Scan the reversed interval with the right-neighbor register.
The induction hypothesis processes all but its original first row, and the
one-row identity finishes that row with the correct right neighbor. -/
private lemma payloadBackward_zone {I : Type} (f : ℤ → I → OblPayload)
    (d : I → SignType) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold (payloadBackward d) (f (z + n)) (payloadZone f z true n).reverse =
      (f z, (payloadZone (fun z i => f (z + (d i : ℤ)) i) z false n).reverse) := by
  induction n generalizing z with
  | zero => simp [payloadZone, FinTM.sweepFold]
  | succ n ih =>
    have he : z + (n + 1 : ℕ) = z + 1 + n := by omega
    simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih,
      FinTM.sweepFold, payloadBackward_row, List.append_nil]

/-- The two finite transductions realize one source action on the whole fixed
layout. This is the data-content invariant paired with the trajectory certificate. -/
private lemma payload_sweeps_source {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold (payloadBackward (sourceShift c a))
      (sourceWrittenPayload c a (z + n))
      (payloadZone (sourceWrittenPayload c a) z true n).reverse =
      (sourceWrittenPayload c a z, (payloadZone (sourcePayload (a.apply c)) z false n).reverse) := by
  have h := payloadBackward_zone (sourceWrittenPayload c a) (sourceShift c a) z n
  have he : (fun z i => sourceWrittenPayload c a (z + (sourceShift c a i : ℤ)) i) =
      sourcePayload (a.apply c) := by
    funext z i
    exact (sourcePayload_apply c a z i).symm
  rw [he] at h
  exact h

/-- Outside both virtual input boundaries, the head-centered payload is blank. -/
lemma inputPayload_outside (x : List Bool) (z : ℤ)
    (hz : z < -1 ∨ (x.length : ℤ) < z) : inputPayload x z = blankPayload := by
  rcases hz with hz | hz
  · have hn : ¬0 ≤ z := by omega
    have hl : z ≠ -1 := by omega
    have hr : z ≠ x.length := by omega
    simp [inputPayload, FinTM.bufferTape, hn, hl, hr, blankPayload]
  · have hn : 0 ≤ z := by omega
    have hl : z ≠ -1 := by omega
    have hr : z ≠ x.length := by omega
    have hv : x.length ≤ z.toNat := by omega
    simp [inputPayload, FinTM.bufferTape, hn, hl, hr, List.getElem?_eq_none hv, blankPayload]

/-- The head-centered layout fits in the prescribed radius throughout the
entire padded source run. This uses initialized source bounds, rather than a
claim about arbitrary starting configurations.

**Proof sketch.** Both a source work head and every nonblank source cell lie
within distance `t` of the original origin, so their relative displacement has
magnitude at most `2t`. The copied input and both boundaries lie within its
length plus one of the virtual input head. Radius `3B` therefore contains every
payload whenever `t ≤ B` and input length plus one is at most `B`. -/
lemma sourcePayload_support (M : FinTM Bool) (x : List Bool) (t B : ℕ)
    (ht : t ≤ B) (hn : x.length + 1 ≤ B) (z : ℤ)
    (hz : z < -3 * (B : ℤ) ∨ 3 * (B : ℤ) < z) (i : Fin (M.k + 1)) :
    sourcePayload (M.tm.runFrom (M.tm.initCfg x) t) z i = blankPayload := by
  let c := M.tm.runFrom (M.tm.initCfg x) t
  obtain ⟨hp, hc⟩ := FinTM.source_bounds M x t
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sourcePayload, Fin.addCases_left]
    have hpos := hp j
    have hout : c.workTapePos j + z < -(t : ℤ) ∨ (t : ℤ) < c.workTapePos j + z := by
      dsimp only [c] at *
      omega
    have hblank := hc j _ hout
    exact congrArg (fun v => (v, (0 : Fin 3))) hblank
  · simp only [sourcePayload, Fin.addCases_right]
    apply inputPayload_outside
    have hpos := c.inputPos.isLt
    dsimp only [c] at *
    omega

/-- Appending at most one source symbol updates a one-bit last-output register
by exactly `Option.getD`. This permits storing the answer in finite control. -/
lemma lastOutput_append (w : List Bool) (b : Option Bool) :
    (w ++ b.toList).getLast?.getD false = b.getD (w.getLast?.getD false) := by
  cases b <;> simp

/-- At the padded source budget, the last-output register is the decision bit. -/
lemma sourceAnswer_at_budget (M : FinTM Bool) (L : Language Bool)
    (T : ℕ → ℕ) (a : ℕ) (hM : M.DecidesInTime L (fun n => a * T n)) (x : List Bool) :
    (M.tm.runFrom (M.tm.initCfg x) ((a + 1) * (T x.length + 1))).output.getLast?.getD false =
      MultiTapeTM.indicator (L : Set (List Bool)) x := by
  have hle : a * T x.length ≤ (a + 1) * (T x.length + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have h := (FinTM.computesInTime_iff M _ _ _).mp ((hM x).mono hle)
  rw [h.2]
  rfl

/-- Captured clock bits begin at cell one, with a permanent origin sentinel. -/
def clockTape (w : List Bool) (z : ℤ) : Option OblSymbol :=
  if z = 0 then some .origin else (FinTM.bufferTape w (z - 1)).map OblSymbol.bit

/-- The initial captured word contains only its sentinel. -/
private lemma clockTape_nil : clockTape [] = Function.update (fun _ : ℤ => none) 0 (some .origin) := by
  funext z
  simp [clockTape, Function.update_apply]

/-- Capturing one clock emission writes precisely the next buffer cell. -/
private lemma clockTape_append (w : List Bool) (b : Bool) :
    clockTape (w ++ [b]) = Function.update (clockTape w) (w.length + 1 : ℤ) (some (.bit b)) := by
  funext z
  by_cases hz : z = (w.length + 1 : ℤ)
  · subst z
    have hn : (w.length + 1 : ℤ) ≠ 0 := by omega
    simp [clockTape, hn]
  · rw [Function.update_of_ne hz]
    by_cases h0 : z = 0
    · simp [clockTape, h0]
    · have hne : z - 1 ≠ (w.length : ℤ) := by omega
      simp only [clockTape, if_neg h0, FinTM.bufferTape_append, Function.update_of_ne hne]

/-- A clock-stage configuration embeds the masked witness work block and
captures its entire append-only output on the budget tape. -/
def clockStageCfg (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed) :=
  ⟨some ((c.state.map OblPhase.clock).getD .resetStart),
    ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩,
    Fin.addCases (fun i z => (c.workTapes i z).map OblSymbol.bit) (fun j =>
      if j.val = 0 then clockTape c.output else if j.val = 1 then clockTape [] else fun _ => none),
    Fin.addCases c.workTapePos (fun j => if j.val = 0 then c.output.length + 1 else if j.val = 1 then 1 else 0),
    []⟩

/-- The clock-stage input read agrees with the masked native read. -/
private lemma clockStageCfg_input (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) :
    (clockStageCfg W a c).inputSymbol.map (fun _ => false) = c.inputSymbol.map (fun _ => false) := by
  unfold Cfg.inputSymbol
  simp only [clockStageCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- The captured clock block reads the witness's work symbols exactly. -/
private lemma clockStageCfg_work (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) :
    (fun i => clockBit ((clockStageCfg W a c).workTapeSymbols (i.castAdd 3))) = c.workTapeSymbols := by
  funext i
  simp only [clockStageCfg, Cfg.workTapeSymbols, Fin.addCases_left]
  cases c.workTapes i (c.workTapePos i) <;> rfl

/-- One live witness transition, including its possible final emission, is one
captured clock transition. Administrative work begins only after that transition. -/
private lemma clockStageCfg_step (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) (q : W.State) (hs : c.state = some q) :
    (obliviousSchedule W a).tm.step (clockStageCfg W a c) =
      clockStageCfg W a ((maskedClock W false).tm.step c) := by
  have hstate : (clockStageCfg W a c).state = some (.clock q) := by
    simp only [clockStageCfg, hs, Option.map_some, Option.getD_some]
  unfold MultiTapeTM.step
  rw [hstate, hs]
  dsimp only [obliviousSchedule, maskedClock]
  rw [clockStageCfg_input, clockStageCfg_work]
  let act := W.tm.tr q (c.inputSymbol.map (fun _ => false)) c.workTapeSymbols
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp only [Action.apply, clockStageCfg, moveInputPos, List.length_map]
    split <;> rfl
  · funext i z
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Action.apply, clockStageCfg, Fin.addCases_left]
      cases hw : (act.workTapes j).1 with
      | none => simp only [act, Option.map_none]
      | some b =>
        by_cases hz : z = c.workTapePos j
        · subst z
          simp only [act, Option.map_some, Function.update_self]
        · simp only [act, Option.map_some, Function.update_of_ne hz]
    · simp only [Action.apply, clockStageCfg, Fin.addCases_right]
      by_cases h0 : j.val = 0
      · simp only [if_pos h0]
        cases ho : act.output with
        | none => simp only [act, Option.toList_none, List.append_nil]
        | some b =>
          simp only [act, Option.toList_some, clockTape_append]
      · by_cases h1 : j.val = 1 <;> simp [h0, h1]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Action.apply, clockStageCfg, Fin.addCases_left]
    · simp only [Action.apply, clockStageCfg, Fin.addCases_right]
      by_cases h0 : j.val = 0
      · simp only [if_pos h0]
        cases ho : act.output <;> simp [act, List.length_append, ho] <;> omega
      · by_cases h1 : j.val = 1 <;> simp [h0, h1]
  · rfl

/-- Exhaust the three administrative tape indices. -/
lemma finThree_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  have hj := j.isLt
  have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- The first schedule transition initializes both sentinels and starts the
clock in its source initial configuration. -/
private lemma clockStageCfg_init (W : FinTM Bool) (a : ℕ) (x : List Bool) :
    (obliviousSchedule W a).tm.step ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) =
      clockStageCfg W a ((maskedClock W false).tm.initCfg x) := by
  change (oblAction (k := W.k) (some (OblPhase.clock (a := a) W.tm.q₀)) 0
    (some (some .origin), .pos) (some (some .origin), .pos) (none, 0)).apply _ = _
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp [oblAction, clockStageCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, clockStageCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;>
        simp [oblAction, clockStageCfg, clockTape_nil]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, clockStageCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, clockStageCfg]
  · rfl

/-- Up to the clock's first halt, its entire initialized computation and every
emitted budget bit are represented by the concrete schedule.
**Proof sketch.** Sentinel initialization costs one transition. Every live
source step is exactly one captured clock step; induction stops at the source
halt before administrative rewinding starts. -/
private lemma clockStageCfg_run (W : FinTM Bool) (a : ℕ) (x : List Bool) (τ : ℕ)
    (hlive : ∀ t < τ, ((maskedClock W false).tm.runFrom
      ((maskedClock W false).tm.initCfg x) t).state ≠ none) :
    ∀ t ≤ τ, (obliviousSchedule W a).tm.runFrom
      ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) (t + 1) =
      clockStageCfg W a ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) t) := by
  intro t
  induction t with
  | zero => intro _; exact clockStageCfg_init W a x
  | succ t ih =>
    intro ht
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), clockStageCfg_step W a _ q hs,
      ← MultiTapeTM.runFrom_succ_eq_step']

/-- The actual schedule captures the prescribed budget and reaches its rewind
phase within the clock bound plus one. No assumption that the original witness
is oblivious is used. -/
lemma clockStageCfg_captures (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1))) (x : List Bool) :
    ∃ τ ≤ b * (T x.length + 1), ∃ c : Cfg W.k Bool W.State x,
      c.state = none ∧ c.output = (T x.length).bits ∧
      (obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) (τ + 1) = clockStageCfg W a c := by
  classical
  have hm := maskedClock_computes W T b hW x
  have hhalt := ((FinTM.computesInTime_iff _ _ _ _).mp hm).1
  have hex : ∃ t, ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) t).state = none :=
    ⟨_, hhalt⟩
  let τ := Nat.find hex
  have hs : ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) τ).state = none :=
    Nat.find_spec hex
  have ht : τ ≤ b * (T x.length + 1) := Nat.find_min' hex hhalt
  have hlive : ∀ t < τ, ((maskedClock W false).tm.runFrom
      ((maskedClock W false).tm.initCfg x) t).state ≠ none := fun _ h => Nat.find_min hex h
  let c := (maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) τ
  have hc : (maskedClock W false).ComputesInTime x c.output τ :=
    (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  exact ⟨τ, ht, c, hs, hc.output_unique hm, clockStageCfg_run W a x τ hlive τ (le_refl _)⟩

/-- The fixed sweep guide has one marked origin and two structural boundaries. -/
def guideTape (R : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = -(R : ℤ) - 1 then some (.edge false)
  else if z = (R : ℤ) + 1 then some (.edge true)
  else if z = 0 then some .origin
  else if -(R : ℤ) ≤ z ∧ z ≤ R then some .inside else none

/-- The guide's left tag occurs exactly at its left boundary. -/
lemma guideTape_left (R : ℕ) (z : ℤ) :
    guideTape R z = some (.edge false) ↔ z = -(R : ℤ) - 1 := by
  unfold guideTape
  split_ifs <;> simp_all

/-- The guide's right tag occurs exactly at its right boundary. -/
lemma guideTape_right (R : ℕ) (z : ℤ) :
    guideTape R z = some (.edge true) ↔ z = (R : ℤ) + 1 := by
  unfold guideTape
  split_ifs <;> simp_all <;> omega

/-- The guide's origin tag occurs exactly at coordinate zero. -/
lemma guideTape_origin (R : ℕ) (z : ℤ) :
    guideTape R z = some .origin ↔ z = 0 := by
  unfold guideTape
  split_ifs <;> simp_all <;> omega

/-- A macrostep configuration keeps every tape and the native input fixed;
only its phase and the unary/guide head positions vary. -/
def macroCfg (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x :=
  ⟨q, base.inputPos, base.workTapes,
    Fin.addCases (fun i => base.workTapePos (i.castAdd 3)) (fun j =>
      if j.val = 0 then base.workTapePos (Fin.natAdd W.k (0 : Fin 3))
      else if j.val = 1 then u else g), base.output⟩

/-- Read the unary counter from a macrostep configuration. -/
lemma macroCfg_unary (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) :
    (macroCfg W a base q u g).workTapeSymbols (Fin.natAdd W.k (1 : Fin 3)) =
      base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u := by
  simp [macroCfg, Cfg.workTapeSymbols]

/-- Read the guide from a macrostep configuration. -/
lemma macroCfg_guide (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) :
    (macroCfg W a base q u g).workTapeSymbols (Fin.natAdd W.k (2 : Fin 3)) =
      base.workTapes (Fin.natAdd W.k (2 : Fin 3)) g := by
  simp [macroCfg, Cfg.workTapeSymbols]

/-- A read-only schedule action updates exactly the two macrostep heads. -/
private lemma macroCfg_apply (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (u g : ℤ) (du dg : SignType) :
    (oblAction (k := W.k) q' 0 (none, 0) (none, du) (none, dg)).apply
      (macroCfg W a base q u g) = macroCfg W a base q' (u + du) (g + dg) := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, macroCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, macroCfg]
  · exact List.append_nil _

/-- One counter test starts a full macrostep or finishes the fixed schedule. -/
lemma macroCfg_check (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .macroCheck) u g) =
      macroCfg W a base
        (if base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit then some .seekLeft else none) u g := by
  change ((obliviousSchedule W a).tm.tr .macroCheck _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_unary]
  split <;> rw [macroCfg_apply] <;> simp

/-- The outward scan turns only at the guide's left boundary. -/
lemma macroCfg_seek (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .seekLeft) u g) =
      if g = -(R : ℤ) - 1 then macroCfg W a base (some .forward) u (g + 1)
      else macroCfg W a base (some .seekLeft) u (g - 1) := by
  change ((obliviousSchedule W a).tm.tr .seekLeft _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_left]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The forward scan turns only at the guide's right boundary. -/
lemma macroCfg_forward (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .forward) u g) =
      if g = (R : ℤ) + 1 then macroCfg W a base (some .backward) u (g - 1)
      else macroCfg W a base (some .forward) u (g + 1) := by
  change ((obliviousSchedule W a).tm.tr .forward _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_right]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The return data scan turns only at the guide's left boundary. -/
lemma macroCfg_backward (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .backward) u g) =
      if g = -(R : ℤ) - 1 then macroCfg W a base (some .returnCenter) u (g + 1)
      else macroCfg W a base (some .backward) u (g - 1) := by
  change ((obliviousSchedule W a).tm.tr .backward _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_left]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The final scan commits at the origin and advances exactly one unary cell. -/
lemma macroCfg_center (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .returnCenter) u g) =
      if g = 0 then macroCfg W a base (some .macroCheck) (u + 1) g
      else macroCfg W a base (some .returnCenter) u (g + 1) := by
  change ((obliviousSchedule W a).tm.tr .returnCenter _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_origin]
  split <;> rw [macroCfg_apply] <;> simp

/-- Exact prefix of the scan from the origin to the left boundary. -/
private lemma macroCfg_seek_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .seekLeft) u 0) n =
      macroCfg W a base (some .seekLeft) u (-(n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_seek W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of a full forward scan. -/
private lemma macroCfg_forward_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ 2 * R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .forward) u (-(R : ℤ))) n =
      macroCfg W a base (some .forward) u (-(R : ℤ) + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_forward W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of a full backward scan. -/
private lemma macroCfg_backward_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ 2 * R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .backward) u R) n =
      macroCfg W a base (some .backward) u ((R : ℤ) - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_backward W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of the scan returning to the origin. -/
private lemma macroCfg_center_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ R) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .returnCenter) u (-(R : ℤ))) n =
      macroCfg W a base (some .returnCenter) u (-(R : ℤ) + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_center W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- **Exact macrostep duration.** A positive counter cell executes the entire
fixed path in exactly `6R+8` transitions and advances the counter by one.

**Proof sketch.** The initial counter test costs one transition. The outward
scan and turn cost `R+2`, each full data scan and turn costs `2R+2`, and the
return-to-origin scan and counter advance cost `R+1`. The exact scan-prefix
lemmas compose to give the complete final configuration. -/
private lemma macroCfg_cycle (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .macroCheck) u 0) (6 * R + 8) =
      macroCfg W a base (some .macroCheck) (u + 1) 0 := by
  have hcheck : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) u 0) 1 = macroCfg W a base (some .seekLeft) u 0 := by
    simpa only [hu, ↓reduceIte] using macroCfg_check W a base u 0
  have hseek : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .seekLeft) u 0) (R + 2) =
      macroCfg W a base (some .forward) u (-(R : ℤ)) := by
    rw [show R + 2 = (R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_seek_run W a base u R _ hg (le_refl _), macroCfg_seek W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hfwd : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .forward) u (-(R : ℤ))) (2 * R + 2) =
      macroCfg W a base (some .backward) u R := by
    rw [show 2 * R + 2 = (2 * R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_forward_run W a base u R _ hg (le_refl _), macroCfg_forward W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hback : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .backward) u R) (2 * R + 2) =
      macroCfg W a base (some .returnCenter) u (-(R : ℤ)) := by
    rw [show 2 * R + 2 = (2 * R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_backward_run W a base u R _ hg (le_refl _), macroCfg_backward W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hcenter : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .returnCenter) u (-(R : ℤ))) (R + 1) =
      macroCfg W a base (some .macroCheck) (u + 1) 0 := by
    rw [MultiTapeTM.runFrom_succ_eq_step', macroCfg_center_run W a base u R _ hg (le_refl _),
      macroCfg_center W a base u _ R hg, if_pos (by omega)]
    congr 1
    omega
  rw [show 6 * R + 8 = 1 + ((R + 2) + ((2 * R + 2) + ((2 * R + 2) + (R + 1)))) by omega,
    MultiTapeTM.runFrom_add, hcheck, MultiTapeTM.runFrom_add, hseek,
    MultiTapeTM.runFrom_add, hfwd, MultiTapeTM.runFrom_add, hback, hcenter]

/-- Any initialized unary segment executes its exact number of macrosteps,
regardless of all simulated data and source halting behavior. -/
private lemma macroCfg_repeat (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (R B : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : ∀ j < B, base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit) :
    ∀ j ≤ B, (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) 1 0) (j * (6 * R + 8)) =
      macroCfg W a base (some .macroCheck) ((j : ℤ) + 1) 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Nat.succ_mul, MultiTapeTM.runFrom_add, ih (by omega),
      macroCfg_cycle W a base _ R hg (hu j (by omega))]
    congr 1

/-- The empty cell immediately following the unary budget ends the schedule
after exactly the budgeted macrosteps plus its final test. -/
lemma macroCfg_finish (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (R B : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : ∀ j < B, base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit)
    (hend : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((B : ℤ) + 1) = none) :
    (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) 1 0) (B * (6 * R + 8) + 1) =
      macroCfg W a base none ((B : ℤ) + 1) 0 := by
  rw [MultiTapeTM.runFrom_succ_eq_step', macroCfg_repeat W a base R B hg hu B (le_refl _),
    macroCfg_check, hend]
  rfl

end Complexity
