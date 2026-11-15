/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The cleaned machine and its cleanup sweeps

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Clean`: the cleaned machine
`Complexity.LogProg.cleanTM M` (simulate `M` while marking visited cells on mark tapes, then
sweep every tape) and the runs of the three sweeps of one tape: right to the end of the
marked interval, left erasing it, and back to the origin mark.

## Main definitions

* `Complexity.LogProg.cleanTM` — the cleaned machine.

## Main results

* `Complexity.LogProg.goR_run`, `Complexity.LogProg.erase_run`,
  `Complexity.LogProg.back_run` — the sweeps of one tape.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The cleanup phases for one work tape. -/
inductive CPh where
  /-- mark the current cell -/
  | mark
  /-- walk right over the marked cells -/
  | goR
  /-- walk left over the marked cells, erasing -/
  | erase
  /-- walk right back to the origin mark, and erase it -/
  | back
  deriving DecidableEq, Fintype

/-- The states of the cleaned machine. -/
inductive CleanSt (S : Type) (k : ℕ) where
  /-- write the origin marks, then simulate from state `q` -/
  | init (q : S)
  /-- simulate the original machine in state `q` -/
  | sim (q : S)
  /-- clean work tape `i`, in phase `ph` -/
  | cl (i : Fin k) (ph : CPh)
  deriving DecidableEq, Fintype

variable {k : ℕ} {S : Type}

/-- The idle action on a block of tapes. -/
def idleK : Fin k → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- The action of a cleanup phase on tape `i` and its mark tape: optional writes `wD`, `wM`,
both heads moving by `mv`. -/
def clAct (i : Fin k) (wD wM : Option (Option Bool)) (mv : SignType) (st : Option (CleanSt S k)) :
    Action (k + k) Bool (CleanSt S k) :=
  ⟨0, Fin.append (fun j => if j = i then (wD, mv) else (none, 0))
    (fun j => if j = i then (wM, mv) else (none, 0)), none, st⟩

/-- The state after cleaning tape `i`: the next tape, or halt. -/
def clNext (i : Fin k) : Option (CleanSt S k) :=
  if h : i.val + 1 < k then some (.cl ⟨i.val + 1, h⟩ .mark) else none

/-- **The cleaned machine.** Work tapes `0, …, k - 1` are `M`'s, tapes `k, …, 2k - 1` the
mark tapes. -/
def cleanTM (M : MultiTapeTM k Bool S) (q₀ : S) : MultiTapeTM (k + k) Bool (CleanSt S k) where
  q₀ := .init q₀
  tr
    | .init q, _, _ =>
      ⟨0, Fin.append idleK (fun _ => (some (some true), 0)), none, some (.sim q)⟩
    | .sim q, a, w =>
      let act := M.tr q a (fun i => w (Fin.castAdd k i))
      ⟨act.inputTape,
        Fin.append act.workTapes (fun i =>
          (if w (Fin.natAdd k i) = some true then none else some (some false),
            (act.workTapes i).2)),
        act.output,
        match act.state with
        | some q' => some (.sim q')
        | none => if h : 0 < k then some (.cl ⟨0, h⟩ .mark) else none⟩
    | .cl i .mark, _, w =>
      clAct i none (if w (Fin.natAdd k i) = some true then none else some (some false)) 0
        (some (.cl i .goR))
    | .cl i .goR, _, w =>
      if (w (Fin.natAdd k i)).isSome then clAct i none none 1 (some (.cl i .goR))
      else clAct i none none (-1) (some (.cl i .erase))
    | .cl i .erase, _, w =>
      match w (Fin.natAdd k i) with
      | some true => clAct i (some none) none (-1) (some (.cl i .erase))
      | some false => clAct i (some none) (some none) (-1) (some (.cl i .erase))
      | none => clAct i none none 1 (some (.cl i .back))
    | .cl i .back, _, w =>
      match w (Fin.natAdd k i) with
      | some true => clAct i none (some none) 0 (clNext i)
      | _ => clAct i none none 1 (some (.cl i .back))

/-- A configuration of the cleaned machine from its two blocks. -/
def ccfg {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) : Cfg (k + k) Bool (CleanSt S k) x :=
  ⟨st, ip, Fin.append Dt Mt, Fin.append Dp Mp, out⟩

/-- The configuration built by `ccfg st …` is in state `st`. -/
@[simp] lemma ccfg_state {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) : (ccfg st ip Dt Dp Mt Mp out).state = st := rfl

/-- A `ccfg` configuration reads mark tape `i` at the mark head position. -/
@[simp] lemma ccfg_mark {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (i : Fin k) :
    (ccfg st ip Dt Dp Mt Mp out).workTapeSymbols (Fin.natAdd k i) = Mt i (Mp i) := by
  simp only [ccfg, Cfg.workTapeSymbols, Fin.append_right]

/-- A `ccfg` configuration reads decider tape `i` at the decider head position. -/
@[simp] lemma ccfg_work {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (i : Fin k) :
    (ccfg st ip Dt Dp Mt Mp out).workTapeSymbols (Fin.castAdd k i) = Dt i (Dp i) := by
  simp only [ccfg, Cfg.workTapeSymbols, Fin.append_left]

/-- Apply an optional write at a position. -/
def wr (w : Option (Option Bool)) (f : ℤ → Option Bool) (p : ℤ) : ℤ → Option Bool :=
  match w with
  | none => f
  | some s => Function.update f p s

/-- The effect of a cleanup action.

**Proof sketch.** Unfold the action's application on a `ccfg` configuration: it writes the
decider and mark cells of tape `i` under their heads and moves both heads of tape `i` by `mv`.
Both updates commute with `Fin.append`, which is checked tape by tape on the two blocks. -/
lemma apply_clAct {x : List Bool} (i : Fin k) (wD wM : Option (Option Bool)) (mv : SignType)
    (st st' : Option (CleanSt S k)) (ip : Fin (x.length + 2)) (Dt : Fin k → ℤ → Option Bool)
    (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool) (Mp : Fin k → ℤ) (out : List Bool) :
    (clAct i wD wM mv st').apply (ccfg st ip Dt Dp Mt Mp out) =
      ccfg st' ip (Function.update Dt i (wr wD (Dt i) (Dp i)))
        (Function.update Dp i (Dp i + mv)) (Function.update Mt i (wr wM (Mt i) (Mp i)))
        (Function.update Mp i (Mp i + mv)) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [clAct, ccfg])
  · funext j z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j
    · simp only [clAct, ccfg, Action.apply, Fin.append_left]
      by_cases h : r = i
      · subst h; cases wD <;> simp [wr]
      · simp [h]
    · simp only [clAct, ccfg, Action.apply, Fin.append_right]
      by_cases h : r = i
      · subst h; cases wM <;> simp [wr]
      · simp [h]
  · funext j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j
    · simp only [clAct, ccfg, Action.apply, Fin.append_left]
      by_cases h : r = i
      · subst h; simp
      · simp [h]
    · simp only [clAct, ccfg, Action.apply, Fin.append_right]
      by_cases h : r = i
      · subst h; simp
      · simp [h]

/-! ## The cleanup sweeps of one tape -/

/-- The mark tape of an interval `[a, b]` around the origin: the origin mark at `0`, plain
marks on the rest of `[a, b]`. -/
def markI (a b : ℤ) (z : ℤ) : Option Bool :=
  if z = 0 then some true else if a ≤ z ∧ z ≤ b then some false else none

/-- All heads of a configuration of the cleaned machine lie in `[-B, B]`. -/
def PB {x : List Bool} (B : ℤ) (g : Cfg (k + k) Bool (CleanSt S k) x) : Prop :=
  ∀ j, |g.workTapePos j| ≤ B

/-- A `ccfg` configuration whose decider and mark heads are within `B` of the origin has all
work heads within `B`. -/
lemma PB_ccfg {x : List Bool} (B : ℤ) (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (hD : ∀ j, |Dp j| ≤ B) (hM : ∀ j, |Mp j| ≤ B) :
    PB B (ccfg st ip Dt Dp Mt Mp out) := by
  intro j
  refine Fin.addCases (fun r => ?_) (fun r => ?_) j
  · simp only [ccfg, Fin.append_left]; exact hD r
  · simp only [ccfg, Fin.append_right]; exact hM r

/-- Updating one coordinate of a family bounded by `B` with a value bounded by `B` keeps the
family bounded by `B`. -/
lemma abs_update_le (Dp : Fin k → ℤ) (i : Fin k) (v B : ℤ) (h : ∀ j, |Dp j| ≤ B)
    (hv : |v| ≤ B) : ∀ j, |Function.update Dp i v j| ≤ B := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hv
  · rw [Function.update_of_ne hj]; exact h j

section Sweeps

variable (M : MultiTapeTM k Bool S) (q₀ : S) {x : List Bool} (i : Fin k)
  (ip : Fin (x.length + 2)) (out : List Bool) (B : ℤ)

/-- The walk right over the marked interval `[a, b]`, ending on `b` in the erase phase.

**Proof sketch.** Induction on `n = b + 1 - Dp i`. Inside the marked interval the mark tape
reads a mark, so both heads of tape `i` move right; just past `b` the mark tape is blank, so
they move back onto `b` and the erase phase begins. All heads stay within `B`. -/
lemma goR_run (a b : ℤ) (Dt : Fin k → ℤ → Option Bool) (Mt : Fin k → ℤ → Option Bool)
    (hMt : Mt i = markI a b) (hb : 0 ≤ b) (hbB : b + 1 ≤ B) :
    ∀ (n : ℕ) (Dp : Fin k → ℤ), b + 1 - Dp i = n → a ≤ Dp i → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (some (.cl i .erase)) ip Dt (Function.update Dp i b) Mt (Function.update Dp i b)
          out := by
  intro n
  induction n with
  | zero =>
    intro Dp hn _ hB
    have hp : Dp i = b + 1 := by omega
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, hp]; simp only [markI]; split_ifs <;> first | omega | rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .erase)) ip Dt (Function.update Dp i b) Mt (Function.update Dp i b)
          out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte]
      rw [apply_clAct]
      simp [wr, hp]
    have hbB' : |b| ≤ B := by have := hB i; rw [hp] at this; rw [abs_le] at this ⊢; omega
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB hbB')
        (abs_update_le _ _ _ _ hB hbB')
  | succ n ih =>
    intro Dp hn ha hB
    have hin : a ≤ Dp i ∧ Dp i ≤ b := ⟨ha, by omega⟩
    have hrd : Mt i (Dp i) ≠ none := by
      rw [hMt]; unfold markI; split_ifs <;> simp_all
    set Dp' := Function.update Dp i (Dp i + 1) with hDp'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .goR)) ip Dt Dp' Mt Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, Option.isSome_iff_ne_none.mpr hrd,
        ↓reduceIte]
      rw [apply_clAct]
      simp [wr, hDp']
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dp' (by simp [hDp']; omega) (by simp [hDp']; omega) hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp']

/-- A tape erased strictly above position `p`. -/
def eraseAbove (f : ℤ → Option Bool) (p : ℤ) : ℤ → Option Bool := fun z => if z ≤ p then f z else none

/-- The walk left over the marked interval, erasing it (keeping the origin mark), ending on
`a` in the back phase.

**Proof sketch.** Induction on `n = Dp i - (a - 1)`. At each marked cell the decider cell is
erased and the mark is erased too, except at the origin mark `true`, and both heads move left.
Past `a` the mark tape is blank, so the heads move back right onto `a` and the back phase
begins. -/
lemma erase_run (a b : ℤ) (f : ℤ → Option Bool) (ha : a ≤ 0) (haB : -B ≤ a - 1) :
    ∀ (n : ℕ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ), Dp i - (a - 1) = n →
      Dp i ≤ b → Dt i = eraseAbove f (Dp i) → Mt i = markI a (Dp i) → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (some (.cl i .back)) ip (Function.update Dt i (eraseAbove f (a - 1)))
          (Function.update Dp i a) (Function.update Mt i (markI a (a - 1)))
          (Function.update Dp i a) out := by
  intro n
  induction n with
  | zero =>
    intro Dt Mt Dp hn _ hDt hMt hB
    have hp : Dp i = a - 1 := by omega
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, hp]; simp only [markI]; split_ifs <;> first | omega | rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .back)) ip (Function.update Dt i (eraseAbove f (a - 1)))
          (Function.update Dp i a) (Function.update Mt i (markI a (a - 1)))
          (Function.update Dp i a) out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      have e1 : Function.update Dt i (Dt i) = Function.update Dt i (eraseAbove f (a - 1)) := by
        rw [hDt, hp]
      have e2 : Function.update Mt i (Mt i) = Function.update Mt i (markI a (a - 1)) := by
        rw [hMt, hp]
      simp only [wr]
      rw [e1, e2, hp]
      congr 2 <;> simp
    have haB' : |a| ≤ B := by
      have := hB i; rw [hp, abs_le] at this; rw [abs_le]; omega
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB haB')
        (abs_update_le _ _ _ _ hB haB')
  | succ n ih =>
    intro Dt Mt Dp hn hpb hDt hMt hB
    set p := Dp i with hpdef
    have hpa : a ≤ p := by omega
    set Dp' := Function.update Dp i (p - 1) with hDp'
    set Dt' := Function.update Dt i (eraseAbove f (p - 1)) with hDt'
    set Mt' := Function.update Mt i (markI a (p - 1)) with hMt'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .erase)) ip Dt' Dp' Mt' Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark]
      have hEr : Function.update (Dt i) p none = eraseAbove f (p - 1) := by
        rw [hDt]; funext z; simp only [eraseAbove, Function.update_apply]
        split_ifs <;> first | rfl | omega
      by_cases hp0 : p = 0
      · have hrd : Mt i p = some true := by rw [hMt]; simp [markI, hp0]
        rw [← hpdef, hrd]
        rw [apply_clAct]
        simp only [wr, ← hpdef, hEr]
        have hM : Function.update Mt i (Mt i) = Mt' := by
          rw [hMt', hMt]; congr 1; funext z; simp only [markI]; split_ifs <;> first | rfl | omega
        rw [hM]
        congr 2
      · have hrd : Mt i p = some false := by
          rw [hMt]; simp only [markI]; split_ifs <;> first | rfl | omega
        rw [← hpdef, hrd]
        rw [apply_clAct]
        simp only [wr, ← hpdef, hEr]
        have hM : Function.update (Mt i) p none = markI a (p - 1) := by
          rw [hMt]; funext z; simp only [markI, Function.update_apply]
          split_ifs <;> first | rfl | omega
        rw [hM]
        congr 2
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dt' Mt' Dp' (by simp [hDp']; omega) (by simp [hDp']; omega)
      (by simp [hDt', hDp']) (by simp [hMt', hDp']) hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp', hDt', hMt']

/-- The origin-only mark tape is `markI a (a - 1)`. -/
lemma markI_empty (a : ℤ) (z : ℤ) : markI a (a - 1) z = if z = 0 then some true else none := by
  simp only [markI]; split_ifs <;> first | rfl | omega

/-- The walk right back to the origin mark, which is erased; tape `i` is then clean.

**Proof sketch.** Induction on `n = -Dp i`. The heads walk right over the erased cells until the
origin mark, which is erased; the machine then moves on to the next tape (`clNext i`), with tape
`i`'s heads at `0` and its mark tape blank. -/
lemma back_run (a : ℤ) :
    ∀ (n : ℕ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ), -Dp i = n → a ≤ Dp i →
      Mt i = markI a (a - 1) → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (clNext i) ip Dt (Function.update Dp i 0) (Function.update Mt i (fun _ => none))
          (Function.update Dp i 0) out := by
  intro n
  induction n with
  | zero =>
    intro Dt Mt Dp hn _ hMt hB
    have hp : Dp i = 0 := by omega
    have hrd : Mt i (Dp i) = some true := by rw [hMt, hp, markI_empty]; rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) =
        ccfg (clNext i) ip Dt (Function.update Dp i 0) (Function.update Mt i (fun _ => none))
          (Function.update Dp i 0) out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      simp only [wr]
      have e1 : Function.update (Mt i) (Dp i) none = fun _ => none := by
        rw [hMt, hp]; funext z; rw [Function.update_apply, markI_empty]
        split_ifs <;> rfl
      rw [e1, hp]
      congr 2; simp
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      have h0 : |(0 : ℤ)| ≤ B := by have := hB i; rw [hp] at this; exact this
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB h0) (abs_update_le _ _ _ _ hB h0)
  | succ n ih =>
    intro Dt Mt Dp hn hpa hMt hB
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, markI_empty]; split_ifs <;> first | rfl | omega
    set Dp' := Function.update Dp i (Dp i + 1) with hDp'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .back)) ip Dt Dp' Mt Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      simp [wr, hDp']
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dt Mt Dp' (by simp [hDp']; omega) (by simp [hDp']; omega) hMt hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp']

/-- **Cleaning one tape.** If, after marking the current cell, the mark tape of tape `i` marks
an interval `[a, b]` around the origin that contains the head and every nonblank cell of
tape `i`, then the cleanup of tape `i` blanks it and its mark tape, returns both heads to the
origin, and moves on; the heads stay in `[a - 1, b + 1]`.

**Proof sketch.** One marking step, then `goR_run`, `erase_run` (every nonblank cell lies in
`[a, b]`, so nothing survives) and `back_run`. -/
lemma clean_tape (a b : ℤ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ)
    (ha : a ≤ 0) (hb : 0 ≤ b) (haB : -B ≤ a - 1) (hbB : b + 1 ≤ B)
    (hh : a ≤ Dp i ∧ Dp i ≤ b)
    (hMt : wr (if Mt i (Dp i) = some true then none else some (some false)) (Mt i) (Dp i) =
      markI a b)
    (hsupp : ∀ z, Dt i z ≠ none → a ≤ z ∧ z ≤ b) (hB : ∀ j, |Dp j| ≤ B) :
    ∃ T, (∀ t ≤ T, PB B ((cleanTM M q₀).runFrom
        (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) T =
        ccfg (clNext i) ip (Function.update Dt i (fun _ => none)) (Function.update Dp i 0)
          (Function.update Mt i (fun _ => none)) (Function.update Dp i 0) out := by
  set Mt1 := Function.update Mt i (markI a b) with hMt1
  have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) =
      ccfg (some (.cl i .goR)) ip Dt Dp Mt1 Dp out := by
    unfold MultiTapeTM.step
    simp only [ccfg_state, cleanTM, ccfg_mark]
    rw [apply_clAct]
    simp only [wr, Function.update_eq_self, SignType.coe_zero, add_zero]
    rw [hMt1, ← hMt]
    rfl
  obtain ⟨hb1, hr1⟩ := goR_run M q₀ i ip out B a b Dt Mt1 (by simp [hMt1]) hb hbB
    (b + 1 - Dp i).toNat Dp (by omega) hh.1 hB
  set Dpb := Function.update Dp i b with hDpb
  have hBb : ∀ j, |Dpb j| ≤ B := abs_update_le _ _ _ _ hB (by rw [abs_le]; omega)
  have hDte : Dt i = eraseAbove (Dt i) (Dpb i) := by
    funext z; simp only [eraseAbove, hDpb, Function.update_self]
    split_ifs with h
    · rfl
    · by_contra hne; exact h (hsupp z (fun h0 => hne (by rw [h0]))).2
  obtain ⟨hb2, hr2⟩ := erase_run M q₀ i ip out B a b (Dt i) ha haB (b - (a - 1)).toNat Dt Mt1 Dpb
    (by simp [hDpb]; omega) (by simp [hDpb]) hDte (by simp [hMt1, hDpb]) hBb
  set Dpa := Function.update Dpb i a with hDpa
  have hBa : ∀ j, |Dpa j| ≤ B := abs_update_le _ _ _ _ hBb (by rw [abs_le]; omega)
  have hblank : eraseAbove (Dt i) (a - 1) = fun _ => none := by
    funext z; simp only [eraseAbove]
    split_ifs with h
    · by_contra hne; have := (hsupp z hne).1; omega
    · rfl
  rw [hblank] at hr2
  obtain ⟨hb3, hr3⟩ := back_run M q₀ i ip out B a (-a).toNat (Function.update Dt i fun _ => none)
    (Function.update Mt1 i (markI a (a - 1))) Dpa (by simp [hDpa]; omega) (by simp [hDpa])
    (by simp) hBa
  refine ⟨1 + ((b + 1 - Dp i).toNat + 1 + ((b - (a - 1)).toNat + 1 + ((-a).toNat + 1))),
    ?_, ?_⟩
  · apply Complexity.LogProg.runFrom_forall_append (Q := PB B)
    · intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain rfl : t = 1 := by omega
        rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
        exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb1
    rw [hr1]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb2
    rw [hr2]
    exact hb3
  · rw [MultiTapeTM.runFrom_add,
      show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep,
      MultiTapeTM.runFrom_add, hr1, MultiTapeTM.runFrom_add, hr2, hr3]
    simp [hDpa, hDpb, hMt1]

end Sweeps

end Complexity.LogProg
