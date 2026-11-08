/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cleaning up after a computation

A subroutine that is called again and again must leave its work tapes as it found them.
[AB09, §4.1.1] remarks that a space-bounded machine can be modified "to erase all its work
tapes before halting". This file carries that out for the machine model of the campaign:
`Complexity.LogProg.cleanTM M` simulates `M` while marking, on one extra *mark tape* per work
tape, every cell the work head visits (the origin with a distinguished mark); when `M` halts,
each work tape is swept: right to the end of the marked interval, left erasing it (the
visited cells form an interval around the origin, so this erases every nonblank cell), and
right again to the origin mark. The cleaned machine has the same output, twice as many work
tapes, and its heads stay within one cell of `M`'s visited cells
(`Complexity.LogProg.cleanTM_run`).

The definition of `Complexity.LogProg.cleanTM` and the sweeps of one tape are in
`TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep`, which this file re-exports.

## Main definitions

* `Complexity.LogProg.cleanTM` — the cleaned machine.

## Main results

* `Complexity.LogProg.cleanTM_run` — from `init q`, the cleaned machine halts with `M`'s
  output, blank work tapes and heads at the origin, its heads staying within `[-s, s]` when
  `M` (started in `q`) visits at most `s` cells per tape.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.LogProg

open Turing

variable {k : ℕ} {S : Type}

/-! ## The simulation phase and the whole run -/

/-- The mark tape of a set of visited cells (the origin always carries the origin mark). -/
def markSet (F : Finset ℤ) (z : ℤ) : Option Bool :=
  if z = 0 then some true else if z ∈ F then some false else none

/-- The state of the cleaned machine simulating a configuration of `M`. -/
def simSt {x : List Bool} (c : Cfg k Bool S x) : Option (CleanSt S k) :=
  match c.state with
  | some q' => some (.sim q')
  | none => if h : 0 < k then some (.cl ⟨0, h⟩ .mark) else none

section Run

variable (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool)

/-- The positions of work head `i` before time `t`. -/
def visB (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range t).image fun t' => (M.runFrom (Cfg.init q V) t').workTapePos i

/-- The cleaned machine's configuration simulating `M` at time `t`. -/
def simCfg (t : ℕ) : Cfg (k + k) Bool (CleanSt S k) V :=
  ccfg (simSt (M.runFrom (Cfg.init q V) t)) (M.runFrom (Cfg.init q V) t).inputPos
    (M.runFrom (Cfg.init q V) t).workTapes (M.runFrom (Cfg.init q V) t).workTapePos
    (fun i => markSet (visB M q V t i)) (M.runFrom (Cfg.init q V) t).workTapePos
    (M.runFrom (Cfg.init q V) t).output

/-- The first step writes the origin marks.

**Proof sketch.** Unfold the first step from the initial state `init q`. It writes the origin
mark on every mark tape and enters the simulation state `sim q` without moving, which is `simCfg
M q V 0` (no cell visited yet besides the origin). Compare componentwise. -/
lemma init_step : (cleanTM M q₁).step (Cfg.init (.init q) V) = simCfg M q V 0 := by
  have e : simCfg M q V 0 = ccfg (some (.sim q)) 1 (fun _ _ => none) (fun _ => 0)
      (fun _ => markSet ∅) (fun _ => 0) [] := by
    simp only [simCfg, MultiTapeTM.runFrom_zero, visB, Finset.range_zero, Finset.image_empty]
    try rfl
  rw [e]
  unfold MultiTapeTM.step
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp only [Cfg.init, cleanTM, Action.apply, moveInputPos_zero]; rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_left, idleK]
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_right, markSet,
        Finset.notMem_empty, if_false, Function.update_apply]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_left, idleK,
        SignType.coe_zero, add_zero]
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_right,
        SignType.coe_zero, add_zero]

/-- The cells visited by tape `i` in `t + 1` steps are those visited in `t` steps and the head
position after `t` steps. -/
lemma visB_succ (t : ℕ) (i : Fin k) :
    visB M q V (t + 1) i = insert ((M.runFrom (Cfg.init q V) t).workTapePos i) (visB M q V t i) := by
  simp only [visB, Finset.range_add_one, Finset.image_insert]

/-- Writing the mark of the current cell adds it to the marked set. -/
lemma wr_markSet (F : Finset ℤ) (p : ℤ) :
    wr (if markSet F p = some true then none else some (some false)) (markSet F) p =
      markSet (insert p F) := by
  funext z
  by_cases hp : p = 0
  · subst hp
    have h0 : markSet F 0 = some true := by simp [markSet]
    simp only [↓reduceIte, wr, markSet, Finset.mem_insert]
    by_cases hz : z = 0 <;> simp [hz]
  · have hm : markSet F p ≠ some true := by
      unfold markSet; rw [if_neg hp]; split_ifs <;> simp
    simp only [hm, ↓reduceIte, wr]
    by_cases hz : z = p
    · subst hz; simp [markSet, hp]
    · rw [Function.update_of_ne hz]; simp [markSet, Finset.mem_insert, hz]

end Run

/-- One simulated step, for an arbitrary live configuration of `M` and arbitrary marks.

**Proof sketch.** Unfold one step of the cleaned machine in a simulation state: it applies `M`'s
action to the decider block, writes a mark under each decider head (keeping the origin mark),
and moves the mark heads with the decider heads. Compare the configurations componentwise. -/
lemma step_sim {x : List Bool} (M : MultiTapeTM k Bool S) (q₁ : S) (c : Cfg k Bool S x)
    (q' : S) (hq' : c.state = some q') (Mt : Fin k → ℤ → Option Bool) :
    (cleanTM M q₁).step (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt
        c.workTapePos c.output) =
      ccfg (simSt (M.step c)) (M.step c).inputPos (M.step c).workTapes (M.step c).workTapePos
        (fun i => wr (if Mt i (c.workTapePos i) = some true then none else some (some false))
          (Mt i) (c.workTapePos i)) (M.step c).workTapePos (M.step c).output := by
  have hMstep : M.step c = (M.tr q' c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step; rw [hq']
  rw [hMstep]
  unfold MultiTapeTM.step
  simp only [ccfg_state]
  have hin : (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt c.workTapePos
      c.output : Cfg (k + k) Bool (CleanSt S k) x).inputSymbol = c.inputSymbol := rfl
  have hw : (fun i => (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt
      c.workTapePos c.output : Cfg (k + k) Bool (CleanSt S k) x).workTapeSymbols
        (Fin.castAdd k i)) = c.workTapeSymbols := by
    funext i; rw [ccfg_work]; rfl
  simp only [cleanTM, hin, hw, ccfg_mark]
  refine Cfg.ext ?_ rfl ?_ ?_ ?_
  · simp only [Action.apply, ccfg, simSt]
    cases (M.tr q' c.inputSymbol c.workTapeSymbols).state <;> rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Action.apply, ccfg, Fin.append_left]
    · simp only [Action.apply, ccfg, Fin.append_right, wr]
      try (split_ifs <;> rfl)
  · funext i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Action.apply, ccfg, Fin.append_left]
    · simp only [Action.apply, ccfg, Fin.append_right]
  · simp only [Action.apply, ccfg]

/-- **The simulation phase**: one step of the cleaned machine is one step of `M`, the mark
tapes recording the cell each head leaves. -/
lemma sim_step_clean (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool) (t : ℕ)
    (hlive : (M.runFrom (Cfg.init q V) t).state ≠ none) :
    (cleanTM M q₁).step (simCfg M q V t) = simCfg M q V (t + 1) := by
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hlive
  have e0 : simCfg M q V t = ccfg (some (.sim q')) (M.runFrom (Cfg.init q V) t).inputPos
      (M.runFrom (Cfg.init q V) t).workTapes (M.runFrom (Cfg.init q V) t).workTapePos
      (fun i => markSet (visB M q V t i)) (M.runFrom (Cfg.init q V) t).workTapePos
      (M.runFrom (Cfg.init q V) t).output := by
    simp only [simCfg, simSt, hq']
  rw [e0, step_sim M q₁ _ q' hq']
  simp only [simCfg, MultiTapeTM.runFrom_succ_eq_step', visB_succ, wr_markSet]



/-- The visited cells of a tape form an interval around the origin.

**Proof sketch.** The visited set is finite and contains `0`. Take `a` its minimum and `b` its
maximum. By `abs_pos_lt_card_visited`'s intermediate-value argument, every integer between `0`
and a visited cell is visited, so the set is exactly `[a, b]`. -/
lemma visited_interval (M : MultiTapeTM k Bool S) (q : S) (V : List Bool) (T : ℕ) (j : Fin k) :
    ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ a ∈ M.visitedByTapeHead (Cfg.init q V) T j ∧
      b ∈ M.visitedByTapeHead (Cfg.init q V) T j ∧
      ∀ z, z ∈ M.visitedByTapeHead (Cfg.init q V) T j ↔ a ≤ z ∧ z ≤ b := by
  set U := M.visitedByTapeHead (Cfg.init q V) T j with hU
  have h0 : (0 : ℤ) ∈ U := by
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, by simp [Cfg.init]⟩
  have hne : U.Nonempty := ⟨0, h0⟩
  refine ⟨U.min' hne, U.max' hne, U.min'_le 0 h0, U.le_max' 0 h0, U.min'_mem hne,
    U.max'_mem hne, fun z => ⟨fun hz => ⟨U.min'_le z hz, U.le_max' z hz⟩, fun ⟨h1, h2⟩ => ?_⟩⟩
  set p : ℕ → ℤ := fun t => (M.runFrom (Cfg.init q V) t).workTapePos j with hp
  have hp0 : p 0 = 0 := by simp [hp, Cfg.init]
  have hstep : ∀ t, |p (t + 1) - p t| ≤ 1 := by
    intro t; simp only [hp, MultiTapeTM.runFrom_succ_eq_step']
    exact M.workTapePos_step_le _ j
  have hmem : ∀ y ∈ U, ∃ t ≤ T, p t = y := by
    intro y hy
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨t, ht, h⟩ := hy
    exact ⟨t, by omega, h⟩
  rcases le_total 0 z with hz | hz
  · obtain ⟨t, ht, hpt⟩ := hmem _ (U.max'_mem hne)
    obtain ⟨t', ht', hpt'⟩ := MultiTapeTM.ConfigCount.exists_eq_of_between p hp0 hstep t z (Or.inl ⟨hz, by rw [hpt]; exact h2⟩)
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨t', by omega, hpt'⟩
  · obtain ⟨t, ht, hpt⟩ := hmem _ (U.min'_mem hne)
    obtain ⟨t', ht', hpt'⟩ := MultiTapeTM.ConfigCount.exists_eq_of_between p hp0 hstep t z (Or.inr ⟨by rw [hpt]; exact h1, hz⟩)
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨t', by omega, hpt'⟩

/-- The state at cleanup stage `i`. -/
def stSt (i : ℕ) : Option (CleanSt S k) := if h : i < k then some (.cl ⟨i, h⟩ .mark) else none

/-- The configuration after cleaning tapes `0, …, i - 1`. -/
def stg {x : List Bool} (i : ℕ) (ip : Fin (x.length + 2)) (Dt Mt : Fin k → ℤ → Option Bool)
    (Dp : Fin k → ℤ) (out : List Bool) : Cfg (k + k) Bool (CleanSt S k) x :=
  ccfg (stSt i) ip (fun j => if j.val < i then (fun _ => none) else Dt j)
    (fun j => if j.val < i then 0 else Dp j) (fun j => if j.val < i then (fun _ => none) else Mt j)
    (fun j => if j.val < i then 0 else Dp j) out

/-- **The cleanup of all tapes**, tape after tape.

**Proof sketch.** Induction on the number `n` of tapes left. Tape `i` is cleaned by the walk
right (`goR_run`), the erasing walk left (`erase_run`) and the walk back (`back_run`), whose
hypotheses come from `htape`. The cleaned tape is blank with heads at `0`, which is the stage
configuration `stg (i + 1)`. -/
lemma stages_run (M : MultiTapeTM k Bool S) (q₁ : S) {x : List Bool} (ip : Fin (x.length + 2))
    (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (out : List Bool) (B : ℤ)
    (htape : ∀ j : Fin k, ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ -B ≤ a - 1 ∧ b + 1 ≤ B ∧
      a ≤ Dp j ∧ Dp j ≤ b ∧
      wr (if Mt j (Dp j) = some true then none else some (some false)) (Mt j) (Dp j) =
        markI a b ∧ ∀ z, Dt j z ≠ none → a ≤ z ∧ z ≤ b)
    (hB0 : 0 ≤ B) :
    ∀ n i, i + n = k →
      ∃ T, (∀ t ≤ T, PB B ((cleanTM M q₁).runFrom (stg i ip Dt Mt Dp out) t)) ∧
        (cleanTM M q₁).runFrom (stg i ip Dt Mt Dp out) T = stg k ip Dt Mt Dp out := by
  have hBs : ∀ i, ∀ j : Fin k, |(fun j : Fin k => if j.val < i then (0 : ℤ) else Dp j) j| ≤ B := by
    intro i j
    simp only
    split_ifs
    · simpa using hB0
    · obtain ⟨a, b, -, -, h1, h2, h3, h4, -⟩ := htape j
      rw [abs_le]; constructor <;> omega
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [show i = k by omega]
    refine ⟨0, fun t ht => ?_, rfl⟩
    obtain rfl : t = 0 := by omega
    exact PB_ccfg _ _ _ _ _ _ _ _ (hBs k) (hBs k)
  | succ n ih =>
    intro i hi
    have hik : i < k := by omega
    obtain ⟨a, b, ha, hb, haB, hbB, hh1, hh2, hmk, hsupp⟩ := htape ⟨i, hik⟩
    obtain ⟨T₁, hb₁, hr₁⟩ := clean_tape M q₁ ⟨i, hik⟩ ip out B a b
      (fun j => if j.val < i then (fun _ => none) else Dt j)
      (fun j => if j.val < i then (fun _ => none) else Mt j)
      (fun j => if j.val < i then 0 else Dp j) ha hb haB hbB
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact ⟨hh1, hh2⟩)
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact hmk)
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact hsupp) (hBs i)
    have hstg : (ccfg (clNext ⟨i, hik⟩) ip
        (Function.update (fun j : Fin k => if j.val < i then (fun _ => none) else Dt j) ⟨i, hik⟩
          fun _ => none)
        (Function.update (fun j : Fin k => if j.val < i then 0 else Dp j) ⟨i, hik⟩ 0)
        (Function.update (fun j : Fin k => if j.val < i then (fun _ => none) else Mt j) ⟨i, hik⟩
          fun _ => none)
        (Function.update (fun j : Fin k => if j.val < i then 0 else Dp j) ⟨i, hik⟩ 0) out :
          Cfg (k + k) Bool (CleanSt S k) x) =
        stg (i + 1) ip Dt Mt Dp out := by
      have e : ∀ {α : Type} (f : Fin k → α) (v : α),
          Function.update (fun j : Fin k => if j.val < i then v else f j) ⟨i, hik⟩ v =
            fun j => if j.val < i + 1 then v else f j := by
        intro α f v
        funext j
        by_cases hj : j = ⟨i, hik⟩
        · subst hj; simp
        · rw [Function.update_of_ne hj]
          have : j.val ≠ i := fun h => hj (Fin.ext h)
          split_ifs <;> first | rfl | omega
      simp only [stg, e]
      congr 1
    obtain ⟨T₂, hb₂, hr₂⟩ := ih (i + 1) (by omega)
    have hstgi : (stg i ip Dt Mt Dp out : Cfg (k + k) Bool (CleanSt S k) x) =
        ccfg (some (.cl ⟨i, hik⟩ .mark))
          ip (fun j => if j.val < i then (fun _ => none) else Dt j)
          (fun j => if j.val < i then 0 else Dp j) (fun j => if j.val < i then (fun _ => none) else Mt j)
          (fun j => if j.val < i then 0 else Dp j) out := by simp [stg, stSt, hik]
    rw [hstgi]
    refine ⟨T₁ + T₂, ?_, ?_⟩
    · apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb₁
      rw [hr₁, hstg]; exact hb₂
    · rw [MultiTapeTM.runFrom_add, hr₁, hstg, hr₂]

/-- **The cleaned machine** started in `init q` on `V`: if `M` started in `q` has halted by
time `T`, visiting at most `s` cells of each tape, then the cleaned machine halts with `M`'s
output, blank work tapes and heads at the origin, every head staying in `[-s, s]`.

**Proof sketch.** One step writes the origin marks; `sim_step_clean` simulates `M` up to its
first halting time `T₀ ≤ T`, the mark tapes recording the cells visited. The visited cells
of each tape form an interval `[a, b] ∋ 0` (`visited_interval`) that contains every
nonblank cell (`Turing.MultiTapeTM.mem_visited_of_ne_none`), and every position in it has
absolute value below the number of visited cells, at most `s`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`); `stages_run` then cleans the tapes. -/
theorem cleanTM_run (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool) (T : ℕ)
    (hT : (M.runFrom (Cfg.init q V) T).state = none) (s : ℕ)
    (hs : ∀ i, (M.visitedByTapeHead (Cfg.init q V) T i).card ≤ s) :
    ∃ T', ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').state = none ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').output =
        (M.runFrom (Cfg.init q V) T).output ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').workTapes = (fun _ _ => none) ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').workTapePos = (fun _ => 0) ∧
      ∀ t ≤ T', ∀ j, |((cleanTM M q₁).runFrom (Cfg.init (.init q) V) t).workTapePos j| ≤ s := by
  classical
  -- the machine `M` with start state `q`, to use the results stated for `initCfg`
  set M' : MultiTapeTM k Bool S := { M with q₀ := q } with hM'
  have hinit : M'.initCfg V = Cfg.init q V := rfl
  have hrun : ∀ t, M'.runFrom (Cfg.init q V) t = M.runFrom (Cfg.init q V) t := fun _ => rfl
  have hex : ∃ t, (M.runFrom (Cfg.init q V) t).state = none := ⟨T, hT⟩
  set T0 := Nat.find hex with hT0def
  have hT0 : (M.runFrom (Cfg.init q V) T0).state = none := Nat.find_spec hex
  have hT0le : T0 ≤ T := Nat.find_min' hex hT
  have hlive : ∀ t < T0, (M.runFrom (Cfg.init q V) t).state ≠ none :=
    fun t ht => Nat.find_min hex ht
  have hfinT : M.runFrom (Cfg.init q V) T = M.runFrom (Cfg.init q V) T0 := by
    rw [show T = T0 + (T - T0) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hT0]
  -- positions of `M` stay in `[-(s-1), s-1]`
  have hvis : ∀ j (z : ℤ), z ∈ M.visitedByTapeHead (Cfg.init q V) T0 j → |z| + 1 ≤ s := by
    intro j z hz
    have h1 := MultiTapeTM.abs_pos_lt_card_visited M' V T0 j (z := z) hz
    have h2 := Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (Cfg.init q V) hT0le j)
    have h3 := hs j
    change |z| < ((M.visitedByTapeHead (Cfg.init q V) T0 j).card : ℤ) at h1
    omega
  -- the simulation phase
  have hsim : ∀ t ≤ T0, (cleanTM M q₁).runFrom (simCfg M q V 0) t = simCfg M q V t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), sim_step_clean M q₁ q V t
        (hlive t (by omega))]
  have hstart : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) 1 = simCfg M q V 0 :=
    init_step M q₁ q V
  -- the interval data of every tape at the halt
  set c := M.runFrom (Cfg.init q V) T0 with hc
  have htape : ∀ j : Fin k, ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ -(s : ℤ) ≤ a - 1 ∧ b + 1 ≤ s ∧
      a ≤ c.workTapePos j ∧ c.workTapePos j ≤ b ∧
      wr (if markSet (visB M q V T0 j) (c.workTapePos j) = some true then none
        else some (some false)) (markSet (visB M q V T0 j)) (c.workTapePos j) = markI a b ∧
      ∀ z, c.workTapes j z ≠ none → a ≤ z ∧ z ≤ b := by
    intro j
    obtain ⟨a, b, ha, hb, haU, hbU, hU⟩ := visited_interval M q V T0 j
    have hva := hvis j a haU
    have hvb := hvis j b hbU
    have hpos : c.workTapePos j ∈ M.visitedByTapeHead (Cfg.init q V) T0 j := by
      simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
      exact ⟨T0, by omega, rfl⟩
    have hUeq : insert (c.workTapePos j) (visB M q V T0 j) =
        M.visitedByTapeHead (Cfg.init q V) T0 j := by
      simp only [visB, MultiTapeTM.visitedByTapeHead, Finset.range_add_one, Finset.image_insert, hc]
    have hna := neg_abs_le a
    have hnb := le_abs_self b
    refine ⟨a, b, ha, hb, by omega, by omega,
      ((hU _).mp hpos).1, ((hU _).mp hpos).2, ?_, ?_⟩
    · rw [wr_markSet, hUeq]
      funext z
      simp only [markSet, markI, hU]
    · intro z hz
      have := MultiTapeTM.mem_visited_of_ne_none M' V T0 j z hz
      exact (hU z).mp this
  have hstg0 : simCfg M q V T0 = stg 0 c.inputPos c.workTapes
      (fun j => markSet (visB M q V T0 j)) c.workTapePos c.output := by
    simp only [simCfg, stg, stSt, simSt, ← hc, hT0, Nat.not_lt_zero, ↓reduceIte]
    try rfl
  obtain ⟨T₂, hb₂, hr₂⟩ := stages_run M q₁ c.inputPos c.workTapes
    (fun j => markSet (visB M q V T0 j)) c.workTapePos c.output s htape (by omega) k 0 (by omega)
  have hfinal : (stg k c.inputPos c.workTapes (fun j => markSet (visB M q V T0 j)) c.workTapePos
      c.output : Cfg (k + k) Bool (CleanSt S k) V) = ccfg none c.inputPos (fun _ _ => none)
        (fun _ => 0) (fun _ _ => none) (fun _ => 0) c.output := by
    simp only [stg, stSt, lt_self_iff_false, ↓reduceDIte, Fin.is_lt, ↓reduceIte]
  have hrun_total : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) (1 + (T0 + T₂)) =
      ccfg none c.inputPos (fun _ _ => none) (fun _ => 0) (fun _ _ => none) (fun _ => 0)
        c.output := by
    rw [MultiTapeTM.runFrom_add, hstart, MultiTapeTM.runFrom_add, hsim T0 le_rfl, hstg0, hr₂,
      hfinal]
  refine ⟨1 + (T0 + T₂), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun_total]; rfl
  · rw [hrun_total, hfinT]; rfl
  · rw [hrun_total]; funext j z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j <;>
      simp only [ccfg, Fin.append_left, Fin.append_right]
  · rw [hrun_total]; funext j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j <;>
      simp only [ccfg, Fin.append_left, Fin.append_right]
  · apply Complexity.LogProg.runFrom_forall_append (Q := PB (s : ℤ))
    · intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        intro j; simp [Cfg.init]
      · obtain rfl : t = 1 := by omega
        rw [hstart]
        exact PB_ccfg _ _ _ _ _ _ _ _ (fun j => by simp [Cfg.init]) (fun j => by simp [Cfg.init])
    rw [hstart]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB (s : ℤ))
    · intro t ht
      rw [hsim t ht]
      have hb : ∀ j, |(M.runFrom (Cfg.init q V) t).workTapePos j| ≤ s := by
        intro j
        have : (M.runFrom (Cfg.init q V) t).workTapePos j ∈
            M.visitedByTapeHead (Cfg.init q V) T0 j := by
          simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
          exact ⟨t, by omega, rfl⟩
        have := hvis j _ this
        omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hb hb
    rw [hsim T0 le_rfl, hstg0]
    exact hb₂

/-- A clean run within a head range is a clean run within any larger range. -/
lemma CleanRun.mono {kD : ℕ} {SD : Type} {D : MultiTapeTM kD Bool SD} {q : SD}
    {V : List Bool} {b : Bool} {B B' : ℕ} (h : CleanRun D q V b B) (hB : B ≤ B') :
    CleanRun D q V b B' := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, fun t ht i => (h5 t ht i).trans (by exact_mod_cast hB)⟩

end Complexity.LogProg
