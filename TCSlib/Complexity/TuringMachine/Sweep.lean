/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sweep gadgets

The generic zipper/transduction layer for sweep-based tape simulations,
promoted out of the one-work-tape construction at the epoch-2/epoch-3
boundary per the epoch-2 audit's promotion recommendations 2-4 (statements
preserved verbatim; only the `private` modifiers were removed). The
controller-specific representations of that construction (its cell type,
alphabet, and finite control) deliberately stay private in
`TCSlib.Complexity.TuringMachine.Robustness.SingleTape`.

## Contents

* **Tape zippers** (`Turing.FinTM.sweepTape`, `sweepCfg`, `sweepRevCfg`, with
  their read/write/turn identities and the beyond-the-zone variants): a finite
  window of a work tape as two stacks around a frontier, scanned in either
  direction, with arbitrary inactive native input and output.
* **Finite transductions** (`Turing.FinTM.sweepFold`, `sweep_run`,
  `sweep_run_reverse`, `sweepFold_append`, `sweep_generate`): a local
  transition-table hypothesis realizes a complete sweep at exact cost, in
  either direction, returning the full resulting configuration.
* **Indexed transducers** (`Turing.FinTM.indexedVisit`, `indexedFold`, and the
  forward/reverse complete-block specializations): a table-valued control that
  changes only the entry named by each cell. The `Nodup` hypothesis of
  `indexedFold` is load-bearing (epoch-2 audit, recommendation 4): two visits
  to the same index could change the control twice.
* **Source bounds** (`Turing.FinTM.source_bounds`): on an initialized run,
  every work head lies in `[-t, t]` at time `t` and every cell outside that
  interval is blank. Initialized runs only — not asserted for arbitrary
  starting configurations (epoch-2 audit, recommendation 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, Claim 1.6 — the simulation these
  gadgets were built for; the module itself is internal infrastructure.)
-/

namespace Turing.FinTM

/-- A finite tape zipper; the left list is stored nearest-cell first. -/
def sweepTape {A : Type} (z : ℤ) (l r : List (Option A))
    (p : ℤ) : Option A :=
  if p < z then (l[(z - 1 - p).toNat]?).join else (r[(p - z).toNat]?).join

/-- Read the current cell of a zipper. -/
lemma sweepTape_read {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r z = r.head?.join := by
  simp only [sweepTape, lt_self_iff_false, ↓reduceIte, sub_self, Int.toNat_zero]
  cases r <;> rfl

/-- A write followed by a right move transfers one cell to the left stack.
**Proof sketch.** At the written coordinate both sides read the new symbol.
Strictly to its left or right, the old and new list indices differ by one,
exactly compensating for the cons or tail operation. -/
lemma sweepTape_right {A : Type} (z : ℤ) (l r : List (Option A))
    (a b : Option A) :
    Function.update (sweepTape z l (a :: r)) z b =
      sweepTape (z + 1) (b :: l) r := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · have h' : p < z + 1 := by omega
      have he : (z + 1 - 1 - p).toNat = (z - 1 - p).toNat + 1 := by omega
      simp only [sweepTape, if_pos h, if_pos h', he, List.getElem?_cons_succ]
    · have h' : ¬p < z + 1 := by omega
      have he : (p - z).toNat = (p - (z + 1)).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, if_neg h', he, List.getElem?_cons_succ]

/-- A configuration at a sweep frontier, with arbitrary native input and output. -/
def sweepCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x := ⟨q, p, fun _ => sweepTape z l r, fun _ => z, out⟩

/-- A sweep's local write, with the native input and output left stationary. -/
def sweepAct {A S : Type} (q : S) (a : Option A) (d : SignType) :
    Action 1 A S := ⟨0, fun _ => (some a, d), none, some q⟩

/-- The one-cell tape identity lifts to configurations. -/
lemma sweepCfg_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l (a :: r) out) =
      sweepCfg (some q') p (z + 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    exact sweepTape_right z l r a b
  · funext i
    rfl
  · exact List.append_nil _

/-- A finite-state left-to-right transduction, recording both its final state
and its rewritten word. -/
def sweepFold {R C : Type} (visit : R → C → R × C) (s : R) :
    List C → R × List C
  | [] => (s, [])
  | a :: as =>
    let v := visit s a
    let rest := sweepFold visit v.1 as
    (rest.1, v.2 :: rest.2)

/-- A local transition rule realizes a complete finite forward sweep.
**Proof sketch.** Induct on the unprocessed word. One machine step writes the
transduced first cell and moves it to the reversed left stack; the induction
hypothesis processes the tail. Input position and output are preserved at every
step, and the number of transitions is exactly the word length. -/
lemma sweep_run {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .pos)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepCfg (some (state (sweepFold visit s as).1)) p (z + as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read z l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr]
    rw [sweepCfg_right, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- The same zipper viewed while scanning toward decreasing coordinates. -/
def sweepRevCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x :=
  ⟨q, p, fun _ w => sweepTape (-z) l r (-w), fun _ => z, out⟩

/-- Reflection converts the forward zipper identity into a left-moving step. -/
lemma sweepRevCfg_left {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l (a :: r) out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i w
    have h := congrFun (sweepTape_right (-z) l r a b) (-w)
    have he : -(z - 1) = -z + 1 := by omega
    change Function.update (fun w => sweepTape (-z) l (a :: r) (-w)) z b w =
      sweepTape (-(z - 1)) (b :: l) r (-w)
    simpa only [Function.update_apply, neg_inj, he] using h
  · funext i
    rfl
  · exact List.append_nil _

/-- The finite transduction lemma for the return sweep, with the exact cost. -/
lemma sweep_run_reverse {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .neg)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepRevCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepRevCfg (some (state (sweepFold visit s as).1)) p (z - as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, sub_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepRevCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read (-z) l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr, sweepRevCfg_left, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Turning round exchanges the two finite stacks. -/
lemma sweepTape_turn {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r = fun w => sweepTape (-(z - 1)) r l (-w) := by
  funext w
  by_cases h : w < z
  · have h' : ¬ -w < -(z - 1) := by omega
    have he : -w - -(z - 1) = z - 1 - w := by omega
    simp only [sweepTape, if_pos h, if_neg h', he]
  · have h' : -w < -(z - 1) := by omega
    have he : -(z - 1) - 1 - -w = w - z := by omega
    simp only [sweepTape, if_neg h, if_pos h', he]

/-- Concatenating two scans threads the finite control between them. -/
lemma sweepFold_append {R C : Type} (visit : R → C → R × C)
    (s : R) (as bs : List C) :
    sweepFold visit s (as ++ bs) =
      let first := sweepFold visit s as
      let second := sweepFold visit first.1 bs
      (second.1, first.2 ++ second.2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, sweepFold, ih]

/-- A transducer whose state is a table, changing only the entry named by a cell. -/
def indexedVisit {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (s : I → V) (a : I × C) :
    (I → V) × (I × C) :=
  let v := visit a.1 (s a.1) a.2
  (Function.update s a.1 v.1, (a.1, v.2))

/-- On a block with distinct tape indices, each local rule sees the original
table entry. This is the block invariant for both sweeps.
**Proof sketch.** Induct on the index list. The first update does not affect
any remaining index because the list has no duplicates. For the final table,
split an arbitrary queried index into the first index, a tail member, or neither. -/
lemma indexedFold {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (cell : I → C) (is : List I) (hi : is.Nodup)
    (s : I → V) :
    sweepFold (indexedVisit visit) s (is.map (fun i => (i, cell i))) =
      (fun i => if i ∈ is then (visit i (s i) (cell i)).1 else s i,
        is.map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  induction is generalizing s with
  | nil => simp [sweepFold]
  | cons i is ih =>
    obtain ⟨hin, ht⟩ := List.nodup_cons.mp hi
    simp only [List.map_cons, sweepFold, indexedVisit]
    rw [ih ht]
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j
        simp [hin]
      · simp only [Function.update_of_ne hj, List.mem_cons]
        by_cases hm : j ∈ is <;> simp [hj, hm]
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hin hj
      simp only [Function.update_of_ne hji]

/-- Each simulated tape contributes exactly one cell to an interleaved block. -/
lemma indexedFold_block {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s ((List.finRange k).map (fun i => (i, cell i))) =
      (fun i => (visit i (s i) (cell i)).1,
        (List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  simpa only [List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k) (List.nodup_finRange k) s


/-- The return sweep's block rule is valid in reverse tape-index order too. -/
lemma indexedFold_block_reverse {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s (((List.finRange k).map (fun i => (i, cell i))).reverse) =
      (fun i => (visit i (s i) (cell i)).1,
        ((List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))).reverse) := by
  rw [← List.map_reverse, ← List.map_reverse]
  simpa only [List.mem_reverse, List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k).reverse
      (by simpa using List.nodup_finRange k) s


/-- One blank cell can be made explicit at the end of the zipper. -/
lemma sweepTape_nil {A : Type} (z : ℤ) (l : List (Option A)) :
    sweepTape z l [] = sweepTape z l [none] := by
  funext p
  unfold sweepTape
  split
  · rfl
  · cases (p - z).toNat <;> rfl

/-- The forward write identity also applies beyond the stored zone. -/
lemma sweepCfg_right_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepCfg_right q q' p z l r out a b
  | nil =>
    have hc : sweepCfg q p z l ([] : List (Option A)) out =
        sweepCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i
      exact sweepTape_nil z l
    rw [hc]
    exact sweepCfg_right q q' p z l [] out none b

/-- The backward write identity also applies beyond the stored zone. -/
lemma sweepRevCfg_left_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepRevCfg_left q q' p z l r out a b
  | nil =>
    have hc : sweepRevCfg q p z l ([] : List (Option A)) out =
        sweepRevCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i w
      exact congrFun (sweepTape_nil (-z) l) (-w)
    rw [hc]
    exact sweepRevCfg_left q q' p z l [] out none b

/-- A fixed finite sequence of writes, in either direction, takes its exact
length. The hypothesis is the local controller rule, and has no global-run premise. -/
lemma sweep_generate {A S : Type} {x : List A}
    (tm : MultiTapeTM 1 A S) (w : List A)
    (cfg : Fin (w.length + 1) → ℤ → List (Option A) → List (Option A) → Cfg 1 A S x)
    (d : ℤ)
    (hstep : ∀ (i : ℕ) (hi : i < w.length) z l r,
      tm.step (cfg ⟨i, by omega⟩ z l r) =
        cfg ⟨i + 1, by omega⟩ (z + d) (some w[i] :: l) r.tail)
    (z : ℤ) (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    tm.runFrom (cfg 0 z l r) n =
      cfg ⟨n, by omega⟩ (z + d * n) ((w.take n).map some |>.reverse |>.append l)
        (r.drop n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep n (by omega)]
    have hz : z + d * n + d = z + d * (n + 1 : ℕ) := by push_cast; ring
    rw [hz, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, ← List.drop_one, List.drop_drop]
    rfl


/-- Source heads and nonblank cells stay within the elapsed-time interval.
**Proof sketch.** Heads start at zero and move by at most one per step.
A write can only change the cell under an old head, so it cannot create a
nonblank cell outside the larger interval at the next time. -/
lemma source_bounds {Γ : Type} (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ t) ∧
    (∀ i z, z < -(t : ℤ) ∨ (t : ℤ) < z →
      (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none) := by
  induction t with
  | zero => simp [MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    constructor
    · intro i
      have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
      rw [abs_le] at hp
      have := ih.1 i
      push_cast
      omega
    · intro i z hz
      have hz' : z < -(t : ℤ) ∨ (t : ℤ) < z := by omega
      have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by
        have := ih.1 i
        omega
      unfold MultiTapeTM.step
      cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => exact ih.2 i z hz'
      | some q =>
        dsimp only [Action.apply]
        cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
          (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
        · exact ih.2 i z hz'
        · dsimp only
          rw [Function.update_of_ne hne]
          exact ih.2 i z hz'

end Turing.FinTM
