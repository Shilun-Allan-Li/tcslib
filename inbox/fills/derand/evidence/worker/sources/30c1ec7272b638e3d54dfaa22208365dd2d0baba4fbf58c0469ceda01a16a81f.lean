/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The circuit-value machine: definition and step lemmas

The two-work-tape Turing machine implementing the circuit-value algorithm of
`TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec`, and its run lemmas: one
description bit (two physical steps, since the description is doubled by
`Turing.pairEncode`), the rewinds of the two work tapes, the append excursion, and the
simulation of the main pass of the algorithm, bit by bit. The machine works over the
binary tape alphabet `Option Bool` (no larger alphabet is needed), so it is a
`Turing.FinTM Bool` and decides languages in the sense of `Complexity.P` directly.

Tape `0` (the *value tape*) holds the vertex values from cell `0`; tape `1` (the *mark
tape*) holds the marks of the arguments of the current gate (during setup: the number
of inputs in unary). The two work heads always move together.

## Main definitions

* `BoolCircuit.CircuitEval.evalTM` — the machine (parametrized by `exact`: whether the
  number of inputs must equal the input length).
* `BoolCircuit.CircuitEval.cfA` — the machine configuration of an abstract state.

## Main results

* `BoolCircuit.CircuitEval.macro_step` — one abstract step of the main pass is simulated
  within `2 · |vals| + 4` machine steps.
* `BoolCircuit.CircuitEval.main_run` — the main pass halts with the abstract verdict
  `absRun`, within `(|l| + 1) · (2B + 4)` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine; §6.1–§6.2.)
-/

namespace BoolCircuit

namespace CircuitEval

open Turing

/-! ## The machine -/

/-- The machine action of a logical action, with the given input-head move. -/
def LA.toAct (im : SignType) (la : LA) : Action 2 Bool St :=
  ⟨im, fun i => (if i.val = 0 then la.vw else la.mw, la.hm), la.o, la.q⟩

/-- The logical symbol of an aligned pair of input bits: `bb` is the bit `b`, `01` is
the end of the description (the separator of `Turing.pairEncode`), `10` is malformed. -/
def pairSym (b b' : Bool) : Option (Option Bool) :=
  if b = b' then some (some b) else if b = false then some none else none

/-- The transition table. `rd1`/`rd2` read an aligned pair and apply `lact`; `rewM` and
`rewV` rewind a work tape to its left blank; `copy` copies the first `n` input bits to
the value tape while erasing the unary `n` from the mark tape; `rewI0`/`rewI` rewind the
input head; `app` walks to the end of the value list erasing marks and appends a gate
value. -/
def tr (exact : Bool) : St → Option Bool → (Fin 2 → Option Bool) → Action 2 Bool St
  | .rd1 φ, some b, _ => LA.toAct .pos (.go (.rd2 φ b))
  | .rd1 _, none, _ => LA.toAct 0 .rej
  | .rd2 φ b, some b', w => match pairSym b b' with
    | some s => LA.toAct .pos (lact φ s (w 0) (w 1))
    | none => LA.toAct 0 .rej
  | .rd2 _ _, none, _ => LA.toAct 0 .rej
  | .rewM, _, w =>
    if (w 1).isSome then LA.toAct 0 ⟨none, none, .neg, none, some .rewM⟩
    else LA.toAct 0 ⟨none, none, .pos, none, some .copy⟩
  | .copy, inp, w =>
    if (w 1).isSome then
      match inp with
      | some b => LA.toAct .pos ⟨some (some b), some none, .pos, none, some .copy⟩
      | none => LA.toAct 0 .rej
    else if exact && inp.isSome then LA.toAct 0 .rej
    else LA.toAct 0 ⟨none, none, .neg, none, some (.rewV none)⟩
  | .rewV d, _, w =>
    if (w 0).isSome then LA.toAct 0 ⟨none, none, .neg, none, some (.rewV d)⟩
    else LA.toAct 0 ⟨none, none, .pos, none, some (match d with
      | none => .rewI0
      | some φ => .rd1 φ)⟩
  | .rewI0, _, _ => FinTM.controlAction .neg (some .rewI)
  | .rewI, inp, _ => match inp with
    | some _ => FinTM.controlAction .neg (some .rewI)
    | none => FinTM.controlAction .pos (some (.rd1 .skipN))
  | .app v, _, w =>
    if (w 0).isSome then LA.toAct 0 ⟨none, some none, .pos, none, some (.app v)⟩
    else LA.toAct 0 ⟨some (some v), some none, .neg, none, some (.rewV (some .g))⟩

/-- **The circuit-value machine**: two work tapes, finite control `St`, started in the
setup phase. With `exact`, the number of inputs of the circuit must equal the length of
the input string. -/
def evalTM (exact : Bool) : FinTM Bool where
  k := 2
  State := St
  tm := { q₀ := .rd1 .n0, tr := tr exact }

/-! ## Configurations

Configuration plumbing (`tp`, `cf`, `wr`, `ip`, `tapeM`, `erase`, `cfA`, and the
invariant vocabulary `main`, `walk`, `Inv`, `LAok`) lives in the inner namespace
`BoolCircuit.CircuitEval.Internal`. -/

/-- The two work tapes. -/
def Internal.tp (vt mt : ℤ → Option Bool) : Fin 2 → ℤ → Option Bool :=
  fun i => if i.val = 0 then vt else mt

open Internal

/-- A configuration with value tape `vt`, mark tape `mt`, both heads at `j`. -/
def Internal.cf (z : List Bool) (q : Option St) (p : Fin (z.length + 2))
    (vt mt : ℤ → Option Bool)
    (j : ℤ) (out : List Bool) : Cfg 2 Bool St z :=
  ⟨q, p, tp vt mt, fun _ => j, out⟩

/-- Apply an optional write at cell `j`. -/
def Internal.wr (t : ℤ → Option Bool) (j : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => t
  | some s => Function.update t j s

/-- The input-head position reading symbol `i` (or the right blank at `i = |z|`). -/
def Internal.ip (z : List Bool) (i : ℕ) (hi : i ≤ z.length) : Fin (z.length + 2) :=
  ⟨i + 1, by omega⟩

/-- The mark tape with marks at the cells `ms`. -/
def Internal.tapeM (ms : List ℕ) : ℤ → Option Bool :=
  fun c => if 0 ≤ c ∧ c.toNat ∈ ms then some true else none

/-- One machine step from a state whose transition is a logical action.

**Proof sketch.** Unfold the step: the action applies the optional writes to the two tapes at the
common head position, moves both heads by `hm`, and appends the emitted symbol. -/
theorem step_cf (exact : Bool) {z : List Bool} (q : St) (p : Fin (z.length + 2))
    (vt mt : ℤ → Option Bool) (j : ℤ) (out : List Bool) (im : SignType) (la : LA)
    (h : tr exact q (cf z (some q) p vt mt j out).inputSymbol (fun i => tp vt mt i j) =
      la.toAct im) :
    (evalTM exact).tm.step (cf z (some q) p vt mt j out) =
      cf z la.q (moveInputPos p im) (wr vt j la.vw) (wr mt j la.mw) (j + la.hm)
        (out ++ la.o.toList) := by
  unfold MultiTapeTM.step
  change (tr exact q (cf z (some q) p vt mt j out).inputSymbol
    (fun i => tp vt mt i j)).apply _ = _
  rw [h]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val = 0
    · simp only [Action.apply, LA.toAct, hi, if_true, cf, tp]
      cases la.vw <;> rfl
    · simp only [Action.apply, LA.toAct, hi, if_false, cf, tp]
      cases la.mw <;> rfl
  · funext i
    rfl

/-- One description bit: two machine steps read an aligned pair `b b'` with logical
symbol `s` and apply the logical action.

**Proof sketch.** Two applications of `step_cf`: `rd1` reads `b` (`FinTM.inputSymbol_at`) and
moves right into `rd2 φ b`; `rd2` reads `b'`, decodes the pair with `pairSym`, and
applies `lact`. Both input moves stay inside the input. -/
theorem lstep (exact : Bool) {z : List Bool} (φ : Ph) (i : ℕ) (hi : i + 2 ≤ z.length)
    (b b' : Bool) (hb : z[i]? = some b) (hb' : z[i + 1]? = some b') (s : Option Bool)
    (hs : pairSym b b' = some s) (vt mt : ℤ → Option Bool) (j : ℤ) :
    (evalTM exact).tm.runFrom (cf z (some (.rd1 φ)) (ip z i (by omega)) vt mt j []) 2 =
      cf z (lact φ s (vt j) (mt j)).q (ip z (i + 2) hi) (wr vt j (lact φ s (vt j) (mt j)).vw)
        (wr mt j (lact φ s (vt j) (mt j)).mw) (j + (lact φ s (vt j) (mt j)).hm)
        (lact φ s (vt j) (mt j)).o.toList := by
  have h1 : (evalTM exact).tm.step (cf z (some (.rd1 φ)) (ip z i (by omega)) vt mt j []) =
      cf z (some (.rd2 φ b)) (ip z (i + 1) (by omega)) vt mt j [] := by
    have := step_cf exact (z := z) (.rd1 φ) (ip z i (by omega)) vt mt j [] .pos (.go (.rd2 φ b))
      (by
        rw [FinTM.inputSymbol_at _ i (by omega) rfl, hb]
        rfl)
    rw [this]
    simp only [LA.go, wr, SignType.coe_zero, add_zero, Option.toList_none, List.append_nil]
    congr 1
    apply Fin.ext
    simp only [ip]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  have h2 : (evalTM exact).tm.step (cf z (some (.rd2 φ b)) (ip z (i + 1) (by omega)) vt mt j []) =
      cf z (lact φ s (vt j) (mt j)).q (ip z (i + 2) hi) (wr vt j (lact φ s (vt j) (mt j)).vw)
        (wr mt j (lact φ s (vt j) (mt j)).mw) (j + (lact φ s (vt j) (mt j)).hm)
        (lact φ s (vt j) (mt j)).o.toList := by
    have := step_cf exact (z := z) (.rd2 φ b) (ip z (i + 1) (by omega)) vt mt j [] .pos
      (lact φ s (vt j) (mt j))
      (by
        rw [FinTM.inputSymbol_at _ (i + 1) (by omega) rfl, hb']
        simp only [tr, hs, tp]
        rfl)
    rw [this]
    simp only [List.nil_append]
    congr 1
    apply Fin.ext
    simp only [ip]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  change (evalTM exact).tm.step ((evalTM exact).tm.step _) = _
  rw [h1, h2]

/-- A rewind: in state `q`, keyed on tape `key`, move left while the key cell is
nonblank, then step right into `dest`. From head `h₀ - 1`, with key cells `0, …, h₀ - 1`
nonblank and cell `-1` blank, it takes `h₀ + 1` steps and ends at head `0`.

**Proof sketch.** Induction on `h₀`. At head `-1` the key cell is blank and one right move enters
`dest` at cell `0`; otherwise the key cell `h₀ - 1` is nonblank and one left move reduces
to the case `h₀ - 1`. -/
theorem rew (exact : Bool) {z : List Bool} (q : St) (key : Fin 2) (dest : St)
    (htr : ∀ inp w, tr exact q inp w = if (w key).isSome
      then LA.toAct 0 ⟨none, none, .neg, none, some q⟩
      else LA.toAct 0 ⟨none, none, .pos, none, some dest⟩)
    (p : Fin (z.length + 2)) (vt mt : ℤ → Option Bool) (out : List Bool) :
    ∀ h₀ : ℕ, (∀ c : ℕ, c < h₀ → tp vt mt key c ≠ none) →
      tp vt mt key (-1) = none →
      (evalTM exact).tm.runFrom (cf z (some q) p vt mt ((h₀ : ℤ) - 1) out) (h₀ + 1) =
        cf z (some dest) p vt mt 0 out := by
  intro h₀
  induction h₀ with
  | zero =>
    intro _ hleft
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [step_cf exact q p vt mt _ out 0 ⟨none, none, .pos, none, some dest⟩
      (by rw [htr]; simp [hleft])]
    simp [wr, moveInputPos_zero]
  | succ h ih =>
    intro hcells hleft
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hc := hcells h (by omega)
    rw [step_cf exact q p vt mt _ out 0 ⟨none, none, .neg, none, some q⟩
      (by rw [htr]; simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [if_pos (Option.isSome_iff_ne_none.mpr hc)])]
    simp only [wr, moveInputPos_zero, Option.toList_none, List.append_nil]
    have := ih (fun c hc' => hcells c (by omega)) hleft
    convert this using 2
    simp [SignType.cast, sub_eq_add_neg]

/-- Erase the cells `h, …, len` of a tape. -/
def Internal.erase (t : ℤ → Option Bool) (h len : ℕ) : ℤ → Option Bool :=
  fun c => if (h : ℤ) ≤ c ∧ c ≤ len then none else t c

/-- The append walk: from head `h` on the value list `vals`, walk right to the first
blank erasing the mark tape, write `v` there, and step left into the rewind.

**Proof sketch.** Induction on the distance `r` to the end of the value list. Over a value cell
the machine erases the mark cell and moves right; at the first blank (`h = |vals|`) it
writes `v` (`FinTM.bufferTape_append`), erases the mark cell, and moves left. -/
theorem app_walk (exact : Bool) {z : List Bool} (v : Bool) (p : Fin (z.length + 2))
    (vals : List Bool) (out : List Bool) :
    ∀ (r h : ℕ) (mt : ℤ → Option Bool), h + r = vals.length →
      (evalTM exact).tm.runFrom (cf z (some (.app v)) p (FinTM.bufferTape vals) mt h out)
        (r + 1) =
      cf z (some (.rewV (some .g))) p (FinTM.bufferTape (vals ++ [v])) (erase mt h vals.length)
        ((vals.length : ℤ) - 1) out := by
  intro r
  induction r with
  | zero =>
    intro h mt hh
    simp only [Nat.add_zero] at hh
    subst hh
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [step_cf exact (.app v) p _ mt _ out 0
      ⟨some (some v), some none, .neg, none, some (.rewV (some .g))⟩
      (by simp [tr, tp, FinTM.bufferTape_nat])]
    simp only [wr, moveInputPos_zero, Option.toList_none, List.append_nil]
    rw [FinTM.bufferTape_append]
    congr 1
    · funext c
      simp only [erase, Function.update_apply]
      split_ifs <;> first | rfl | (exfalso; omega)
  | succ r ih =>
    intro h mt hh
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hlt : h < vals.length := by omega
    rw [step_cf exact (.app v) p _ mt _ out 0 ⟨none, some none, .pos, none, some (.app v)⟩
      (by simp [tr, tp, FinTM.bufferTape_nat, List.getElem?_eq_getElem hlt])]
    simp only [wr, moveInputPos_zero, Option.toList_none, List.append_nil]
    have := ih (h + 1) (Function.update mt (h : ℤ) none) (by omega)
    rw [show (h : ℤ) + (SignType.pos : ℤ) = ((h + 1 : ℕ) : ℤ) by simp [SignType.cast], this]
    congr 1
    funext c
    simp only [erase, Function.update_apply]
    split_ifs <;> first | rfl | (exfalso; omega)

/-! ## Simulating the main pass -/

/-- The main-pass phases (everything but the setup phases `n0`, `sep`). -/
def Internal.main : Ph → Bool
  | .n0 => false
  | .sep => false
  | _ => true

/-- The phases in which the work heads may be away from cell `0`. -/
def Internal.walk : Ph → Bool
  | .u _ _ _ => true
  | .o => true
  | .fin _ => true
  | _ => false

/-- The invariant of the main pass: the heads are within the value list, every mark is
on a vertex, the phase is a main-pass phase, and outside the walking phases the heads
are at cell `0`. -/
def Internal.Inv (s : AS) : Prop :=
  s.j ≤ s.vals.length ∧ (∀ a ∈ s.ms, a < s.vals.length) ∧ main s.φ = true ∧
    (walk s.φ = false → s.j = 0)

/-- The shape of the main-pass logical actions: no write on the value tape, at most a
mark (and only on a vertex), and per successor state the head move and output. -/
def Internal.LAok (w : Bool) (vc : Option Bool) (la : LA) : Prop :=
  la.vw = none ∧ (la.mw = none ∨ (la.mw = some (some true) ∧ vc.isSome = true)) ∧
  match la.q with
  | none => la.o.isSome = true
  | some (.rd1 φ') => la.o = none ∧ main φ' = true ∧
      (la.hm = 0 ∨ (la.hm = .pos ∧ vc.isSome = true)) ∧
      (walk φ' = false → w = false ∧ la.hm = 0)
  | some (.rewV (some φ')) => la.o = none ∧ main φ' = true ∧ walk φ' = false ∧
      la.hm = .neg ∧ vc.isSome = true
  | some (.app _) => la.o = none ∧ la.hm = 0 ∧ la.mw = none ∧ w = false
  | some _ => False

/-- Every main-pass logical action has the shape `LAok`. -/
theorem lact_ok (φ : Ph) (hφ : main φ = true) (sym vc mc : Option Bool) :
    LAok (walk φ) vc (lact φ sym vc mc) := by
  cases φ <;> rcases sym with _ | _ | _ <;> rcases vc with _ | _ | _ <;>
    rcases mc with _ | _ | _ <;> simp [LAok, lact, LA.go, LA.rej, main, walk] at hφ ⊢ <;>
    split_ifs <;> simp

/-- The machine configuration of an abstract main-pass state at input position `i`. -/
def Internal.cfA (z : List Bool) (s : AS) (i : ℕ) (hi : i ≤ z.length) : Cfg 2 Bool St z :=
  cf z (some (.rd1 s.φ)) (ip z i hi) (FinTM.bufferTape s.vals) (tapeM s.ms) s.j []

/-- The mark tape read at a natural cell. -/
theorem tapeM_nat (ms : List ℕ) (j : ℕ) : tapeM ms (j : ℤ) = markCell ms j := by
  simp [tapeM, markCell]

/-- Writing a mark at cell `j`. -/
theorem wr_tapeM (ms : List ℕ) (j : ℕ) :
    wr (tapeM ms) (j : ℤ) (some (some true)) = tapeM (j :: ms) := by
  funext c
  simp only [wr, tapeM, Function.update_apply, List.mem_cons]
  by_cases hc : c = (j : ℤ)
  · subst hc; simp
  · rw [if_neg hc]
    congr 1
    apply propext
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h0, Or.inr h1⟩
    · rintro ⟨h0, h1 | h1⟩
      · exact absurd (by omega) hc
      · exact ⟨h0, h1⟩

/-- **One abstract step of the main pass is simulated by the machine**, within
`2 · |vals| + 4` steps: two steps for the description bit, plus a rewind or an append
excursion. The invariant is preserved and the value list grows by at most one.

**Proof sketch.** `lstep` performs the logical action `la = lact φ sym (value cell) (mark
cell)` in two steps, and `lact_ok` gives its shape. If `la` halts, it emits the verdict
bit. If it continues in a reading phase, the tapes are the abstract ones with possibly a
new mark (`wr_tapeM`), and the heads moved by `0` or by `+1` onto a value cell, so the
invariant holds. If it enters the value-tape rewind, `rew` returns the heads to `0` in
`j + 1` steps. If it appends, the heads are at `0` (a non-walking phase), `app_walk`
walks to the end erasing every mark (all marks are on vertices) and writes the gate
value, and `rew` returns in `|vals| + 1` steps. -/
theorem macro_step (exact : Bool) {z : List Bool} (s : AS) (hs : Inv s) (i : ℕ)
    (hi : i + 2 ≤ z.length) (b b' : Bool) (hb : z[i]? = some b) (hb' : z[i + 1]? = some b')
    (sym : Option Bool) (hsym : pairSym b b' = some sym) :
    match absStep s sym with
    | .inl s' => Inv s' ∧ s'.vals.length ≤ s.vals.length + 1 ∧
        ∃ t ≤ 2 * s.vals.length + 4,
          (evalTM exact).tm.runFrom (cfA z s i (by omega)) t = cfA z s' (i + 2) hi
    | .inr v => ∃ t ≤ 2 * s.vals.length + 4,
        ((evalTM exact).tm.runFrom (cfA z s i (by omega)) t).state = none ∧
        ((evalTM exact).tm.runFrom (cfA z s i (by omega)) t).output = [v] := by
  obtain ⟨φ, vals, ms, j⟩ := s
  obtain ⟨hj, hms, hmain, hwalk⟩ := hs
  simp only at hj hms hmain hwalk
  have hl := lstep exact (z := z) φ i hi b b' hb hb' sym hsym (FinTM.bufferTape vals)
    (tapeM ms) j
  rw [FinTM.bufferTape_nat, tapeM_nat] at hl
  have hok := lact_ok φ hmain sym vals[j]? (markCell ms j)
  simp only [cfA, absStep, absOf]
  generalize lact φ sym vals[j]? (markCell ms j) = la at hl hok ⊢
  obtain ⟨hvw, hmw, hq⟩ := hok
  rcases hq' : la.q with _ | q'
  · -- the action halts, emitting its bit
    rw [hq'] at hq
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
    refine ⟨2, by omega, ?_, ?_⟩
    · rw [hl, hq']; rfl
    · rw [hl, hv]; simp [cf]
  · cases q' with
    | rd1 φ' =>
      rw [hq'] at hq
      obtain ⟨ho, hmain', hhm, hw'⟩ := hq
      have hvc : vals[j]?.isSome = true → j < vals.length := by
        intro h; by_contra hc; simp [List.getElem?_eq_none (by omega : vals.length ≤ j)] at h
      refine ⟨⟨?_, ?_, hmain', ?_⟩, by simp, 2, by omega, ?_⟩
      · rcases hhm with h | ⟨h, hs⟩
        · simp [h]; omega
        · have := hvc hs; simp [h]; omega
      · show ∀ a ∈ (if la.mw = some (some true) then j :: ms else ms), a < vals.length
        intro a ha
        by_cases h : la.mw = some (some true)
        · rw [if_pos h] at ha
          rcases hmw with h' | ⟨h', hs⟩
          · rw [h'] at h; exact absurd h (by simp)
          · have := hvc hs
            simp at ha; rcases ha with rfl | ha; exact this; exact hms a ha
        · rw [if_neg h] at ha; exact hms a ha
      · intro hwf
        obtain ⟨h1, h2⟩ := hw' hwf
        simp [h2, hwalk h1]
      · rw [hl, hq', hvw, ho]
        simp only [cf, wr, Option.toList_none]
        congr 2
        · rcases hmw with h | ⟨h, -⟩
          · simp [h]
          · simp only [h, if_true]
            have := wr_tapeM ms j
            simp only [wr] at this
            rw [this]
        · funext _
          rcases hhm with h | ⟨h, -⟩
          · simp [h]
          · simp [h, SignType.cast]
    | rewV d =>
      cases d with
      | none => rw [hq'] at hq; exact hq.elim
      | some φ' =>
        rw [hq'] at hq
        obtain ⟨ho, hmain', hw', hhm, hvc⟩ := hq
        have hjl : j < vals.length := by
          by_contra hc; simp [List.getElem?_eq_none (by omega : vals.length ≤ j)] at hvc
        let ms' := if la.mw = some (some true) then j :: ms else ms
        have hmt : wr (tapeM ms) j la.mw = tapeM ms' := by
          rcases hmw with h | ⟨h, -⟩
          · simp [ms', h, wr]
          · simp only [ms', h, if_true]; exact wr_tapeM ms j
        have hr := rew exact (z := z) (.rewV (some φ')) 0 (.rd1 φ') (fun _ _ => rfl)
          (ip z (i + 2) hi) (FinTM.bufferTape vals) (tapeM ms') [] j
          (by
            intro c hc
            simp [tp, FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega : c < vals.length)])
          (by simp [tp])
        refine ⟨⟨by simp, ?_, hmain', fun _ => rfl⟩, by simp, 2 + (j + 1), by omega, ?_⟩
        · intro a ha
          split_ifs at ha
          · simp at ha; rcases ha with rfl | ha; exact hjl; exact hms a ha
          · exact hms a ha
        · rw [MultiTapeTM.runFrom_add, hl, hq', hvw, ho, hmt, hhm]
          simp only [wr, Option.toList_none]
          rw [show (j : ℤ) + ((SignType.neg : SignType) : ℤ) = (j : ℤ) - 1 by
            simp [SignType.cast, sub_eq_add_neg]]
          exact hr
    | app v =>
      rw [hq'] at hq
      obtain ⟨ho, hhm, hmw', hw⟩ := hq
      have hj0 : j = 0 := hwalk hw
      subst hj0
      have ha := app_walk exact (z := z) v (ip z (i + 2) hi) vals [] vals.length 0 (tapeM ms)
        (by simp)
      have hr := rew exact (z := z) (.rewV (some .g)) 0 (.rd1 .g) (fun _ _ => rfl)
        (ip z (i + 2) hi) (FinTM.bufferTape (vals ++ [v])) (erase (tapeM ms) 0 vals.length) []
        vals.length
        (by
          intro c hc
          simp [tp, FinTM.bufferTape_nat, List.getElem?_append_left hc,
            List.getElem?_eq_getElem hc])
        (by simp [tp])
      have herase : erase (tapeM ms) 0 vals.length = tapeM [] := by
        funext c
        simp only [erase, tapeM, List.not_mem_nil, and_false, if_false]
        by_cases h1 : ((0 : ℕ) : ℤ) ≤ c ∧ c ≤ vals.length
        · rw [if_pos h1]
        · rw [if_neg h1]
          split_ifs with h2
          · exfalso
            have := hms c.toNat h2.2
            omega
          · rfl
      refine ⟨⟨by simp, by simp, rfl, fun _ => rfl⟩, by simp, 2 + (vals.length + 1) +
        (vals.length + 1), by omega, ?_⟩
      rw [MultiTapeTM.runFrom_add _ (2 + (vals.length + 1)) (vals.length + 1),
        MultiTapeTM.runFrom_add _ 2 (vals.length + 1), hl, hq', hvw, ho, hmw', hhm]
      simp only [wr, Option.toList_none, Nat.cast_zero, SignType.coe_zero, add_zero]
      simp only [Nat.cast_zero] at ha
      rw [ha]
      rw [hr, herase]
    | _ => rw [hq'] at hq; exact hq.elim

/-- The end of the description always halts the abstract run. -/
theorem absStep_none (s : AS) : ∃ v, absStep s none = .inr v := by
  obtain ⟨φ, vals, ms, j⟩ := s
  cases φ <;> simp [absStep, absOf, lact, LA.rej]

/-- **The main pass.** From the machine configuration of an abstract state, reading the
doubled remaining description bits `l` and then the separator, the machine halts with
the abstract verdict `absRun s l`, within `(|l| + 1) · (2B + 4)` steps whenever
`|vals| + |l| ≤ B`.

**Proof sketch.** Induct on `l`; each bit is one `macro_step`, which either halts with
the abstract verdict or reaches the configuration of the next abstract state; the
separator halts by `absStep_none`. The value list grows by at most one per bit, so the
bound `B` is preserved. -/
theorem main_run (exact : Bool) {z : List Bool} (x : List Bool) :
    ∀ (l : List Bool) (s : AS) (pre : List Bool), z = pre ++ dbl l ++ ([false, true] ++ x) →
      ∀ (hi : pre.length ≤ z.length), Inv s → ∀ B : ℕ, s.vals.length + l.length ≤ B →
      ∃ t ≤ (l.length + 1) * (2 * B + 4),
        ((evalTM exact).tm.runFrom (cfA z s pre.length hi) t).state = none ∧
        ((evalTM exact).tm.runFrom (cfA z s pre.length hi) t).output = [absRun s l] := by
  intro l
  induction l with
  | nil =>
    intro s pre hz hi hs B hB
    have hi2 : pre.length + 2 ≤ z.length := by rw [hz]; simp
    have hm := macro_step exact s hs pre.length hi2 false true (by rw [hz]; simp)
      (by rw [hz]; simp) none rfl
    obtain ⟨v, hv⟩ := absStep_none s
    rw [hv] at hm
    obtain ⟨t, ht, h1, h2⟩ := hm
    refine ⟨t, by simp at hB ⊢; omega, h1, ?_⟩
    rw [h2]
    simp [absRun, hv]
  | cons b l ih =>
    intro s pre hz hi hs B hB
    have hi2 : pre.length + 2 ≤ z.length := by rw [hz]; simp
    have hm := macro_step exact s hs pre.length hi2 b b (by rw [hz]; simp)
      (by rw [hz]; simp) (some b) (by simp [pairSym])
    rcases hstep : absStep s (some b) with s' | v
    · rw [hstep] at hm
      obtain ⟨hs', hlen, t₁, ht₁, hrun⟩ := hm
      have hz' : z = (pre ++ [b, b]) ++ dbl l ++ ([false, true] ++ x) := by
        rw [hz]; simp
      obtain ⟨t₂, ht₂, h1, h2⟩ := ih s' (pre ++ [b, b]) hz' (by rw [hz]; simp) hs' B
        (by simp at hB; omega)
      have hcfg : cfA z s' (pre.length + 2) hi2 = cfA z s' (pre ++ [b, b]).length
          (by rw [hz]; simp) := by
        simp only [List.length_append, List.length_cons, List.length_nil]
      refine ⟨t₁ + t₂, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at hB ⊢
        have : t₁ ≤ 2 * B + 4 := by omega
        nlinarith
      · rw [MultiTapeTM.runFrom_add, hrun, hcfg, h1]
      · rw [MultiTapeTM.runFrom_add, hrun, hcfg, h2]
        simp [absRun, hstep]
    · rw [hstep] at hm
      obtain ⟨t, ht, h1, h2⟩ := hm
      refine ⟨t, ?_, h1, ?_⟩
      · simp only [List.length_cons] at hB ⊢
        nlinarith
      · rw [h2]; simp [absRun, hstep]

end CircuitEval

end BoolCircuit
