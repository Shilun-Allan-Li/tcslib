/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Steps
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The extended word RAM: input, output, coins and halving; footprints and halting

The word RAM of [AFM26] (`WordRAM.Instr`, nine instructions) is extended by a wrapper:
`WordRAM.XInstr` has the vendored instructions as `XInstr.base`, and four more:

* `rdIn i j`, the input bit at the position held in a cell, read in place;
* `emit i`, which appends the bit "`[i]` is nonzero" to an append-only output;
* `coin i`, the next coin of a read-once coin stream;
* `half i j`, an arithmetic shift right.

A configuration `WordRAM.XCfg` extends `WordRAM.Cfg` by the emitted bits and the number of
coins consumed. Input and coin streams are parameters of a run. The vendored run calculus
applies through `XProgram.proj`, as proved by `XSteps.of_steps_proj`.

The run calculus also records which memory cells a run touches and when the program halts
within given bounds on steps and cells. All run, footprint, and halting results below are proved.

## Main definitions

* `WordRAM.XInstr`, `WordRAM.XProgram`, `WordRAM.XCfg`, `WordRAM.xstep`, `WordRAM.XSteps`:
  the extended machine and its runs.
* `WordRAM.CoinFree`, `WordRAM.XProgram.proj`: coin-free programs and the vendored projection.
* `WordRAM.baseTouches`, `WordRAM.XInstr.touches`: the cells one instruction reads or writes.
* `WordRAM.StepsIn`, `WordRAM.XStepsIn`: runs within a footprint.
* `WordRAM.initMem`, `WordRAM.XCfg.init`, `WordRAM.HaltsWithin`: initialization and bounded halting.

## Main results

* `WordRAM.XSteps.trans`, `WordRAM.xstep_map_base`, `WordRAM.XSteps.of_steps`,
  `WordRAM.XSteps.of_steps_proj`: composition and conservativity over the vendored RAM.
* `WordRAM.StepsIn.agreeOutside`: intermediate memories agree outside the footprint.
* `WordRAM.stepsIn_straight`: straight-line execution with a footprint.
* `WordRAM.XSteps.exists_xStepsIn`, `WordRAM.HaltsWithin.touches_le`: a run of `n` steps
  touches at most `3 * n` cells, giving a cell bound from a time bound.
* `WordRAM.HaltsWithin.mono`, `WordRAM.HaltsWithin.unique`, `WordRAM.HaltsWithin.coin_irrel`:
  monotonicity, determinism, and independence of the coin stream for coin-free programs.
* Readers (equations of the definitions, for other files): `WordRAM.inBitWord_def`,
  `WordRAM.coinWord_def`, `WordRAM.xstep_def`, `WordRAM.XSteps.zero_iff`, `.succ_iff`,
  `WordRAM.baseTouches_def`, `WordRAM.XInstr.touches_def`, `WordRAM.XStepsIn.zero_iff`,
  `.succ_iff`, `WordRAM.initMem_def`, `WordRAM.XCfg.init_def`, `WordRAM.haltsWithin_iff`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math` (https://github.com/anthropics/formal-math),
  project `3sum-apsp`, commit `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05),
  Apache-2.0, © Anthropic, PBC. Design adaptation: the word RAM of `EndStatement.lean`
  and the run calculus of `ThreeSumApsp/Machine/Steps.lean`, vendored as
  `TCSlib/Programs/WordRAM/Basic.lean` and `Steps.lean`, which this file wraps. `xstep` restates
  the match of `WordRAM.step`, routing the six memory instructions through `WordRAM.effect`;
  `XSteps` and `StepsIn` use the same finite-run convention as `WordRAM.Steps`. The proofs cite
  the vendored equations and lemmas. The footprint notion is ours: upstream's
  `ThreeSumApsp/Machine/Footprint.lean` bounds how many cells a run changes and reads, not which.
-/

namespace WordRAM

/-! ## The machine -/

/-- **The instructions of the extended word RAM** (design §15c, §15d): the nine instructions of
the vendored `WordRAM.Instr`, as `base`, and four more. `rdIn i j` sets `[i]` to the input bit at
position `[j]`, as `0` or `1` (`0` off the input, negative positions included); `emit i` appends
the bit "`[i]` is nonzero" to the output; `coin i` sets `[i]` to the next coin, as `0` or `1`,
and consumes it; `half i j` sets `[i]` to `[j]` shifted right by one place with the sign kept,
that is `⌊[j] / 2⌋`. The extension wraps `Instr` instead of adding constructors to it (user
decision, 2026-10-12), so the vendored files and their run calculus are unchanged.
[AFM26, `EndStatement.lean`], extended per design §15c. -/
inductive XInstr : Type where
  | base (i : Instr)
  | rdIn (i j : ℤ)
  | emit (i : ℤ)
  | coin (i : ℤ)
  | half (i j : ℤ)

/-- A program of the extended word RAM: its instructions, at positions `0, 1, 2, …`. -/
abbrev XProgram : Type := List XInstr

/-- **A configuration of the extended RAM**: the vendored configuration (the position of the
next instruction and the memory), the bits emitted so far, and the number of coins consumed so
far. The input and the coin stream are not part of it: they are parameters of a run. -/
structure XCfg (W : ℕ) extends Cfg W where
  /-- The bits emitted so far, oldest first. -/
  out : List Bool
  /-- The number of coins consumed so far. -/
  rd : ℕ

/-- The word that `rdIn` writes for the position `p` of the input `x`: `1` if `0 ≤ p` and the bit
of `x` at `p` is `true`, and `0` otherwise, in particular off the input. -/
def inBitWord (W : ℕ) (x : List Bool) (p : ℤ) : BitVec W :=
  if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0

/-- The word that `coin` writes for the coin `b`: `1` for `true`, `0` for `false`. -/
def coinWord (W : ℕ) (b : Bool) : BitVec W := if b then 1 else 0

/-- **One step of the extended RAM** on the input `x` with the coin stream `ρ`: the next
configuration, or the verdict. The nine vendored instructions behave as in `WordRAM.step` (the
six that only change the memory through the vendored `WordRAM.effect`) and leave the output and
the coin count alone; past its end the program rejects. The coin is read as `ρ.getD rd false`,
so a stream that has run out reads `false`; quantifying over all lists `ρ` covers every stream. -/
def xstep {W : ℕ} (P : XProgram) (x ρ : List Bool) (c : XCfg W) : XCfg W ⊕ Bool :=
  let m := c.mem
  match P.getD c.pc (.base .reject) with
  | .base .accept => .inr true
  | .base .reject => .inr false
  | .base (.bltz i l) => .inl { c with pc := if (m i).toInt < 0 then l else c.pc + 1 }
  | .base ins => .inl { c with pc := c.pc + 1, mem := effect ins m }
  | .rdIn i j =>
    .inl { c with pc := c.pc + 1, mem := Function.update m i (inBitWord W x (m j).toInt) }
  | .emit i => .inl { c with pc := c.pc + 1, out := c.out ++ [decide (m i ≠ 0)] }
  | .coin i =>
    .inl { c with pc := c.pc + 1, mem := Function.update m i (coinWord W (ρ.getD c.rd false)),
                  rd := c.rd + 1 }
  | .half i j => .inl { c with pc := c.pc + 1, mem := Function.update m i ((m j).sshiftRight 1) }

/-- `XSteps P x ρ n c c'`: exactly `n` steps of `P` on the input `x` with the coin stream `ρ`
lead from `c` to `c'`, none of them a verdict. The extended counterpart of `WordRAM.Steps`. -/
def XSteps {W : ℕ} (P : XProgram) (x ρ : List Bool) : ℕ → XCfg W → XCfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, xstep P x ρ c = .inl c₁ ∧ XSteps P x ρ n c₁ c'

/-- A program is **coin-free** when none of its instructions is a `coin`. -/
def CoinFree (P : XProgram) : Prop := ∀ ins ∈ P, ∀ a : ℤ, ins ≠ .coin a

/-- **The vendored projection** of a program of the extended RAM: the same program with each new
instruction replaced by `reject`. A run of the projection that gives no verdict never executes a
replaced position, so it is also a run of the extended program (`XSteps.of_steps_proj`). This is
how the vendored run calculus and the compiler's segment lemmas serve code that mixes old and new
instructions. -/
def XProgram.proj (P : XProgram) : List Instr :=
  P.map fun
    | .base i => i
    | _ => .reject

/-! ## Private instruction comparison -/

/-- Mapping a fetch follows `List.getElem?_map` and `Option.getD_map`. -/
private theorem mapped_fetch {α β : Type} (l : List α) (d : α) (f : α → β) (n : ℕ) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

/-- A base instruction has the same effect in both machines. The instruction cases use
`step_def` and `effect_def`; `Function.update_apply` identifies the memory functions. -/
private theorem xstep_base_fetch {W : ℕ} {P : XProgram} {Q : List Instr}
    (x ρ : List Bool) (c : Cfg W) (o : List Bool) (r : ℕ)
    (h : P.getD c.pc (.base .reject) = .base (Q.getD c.pc .reject)) :
    xstep P x ρ ⟨c, o, r⟩ =
      Sum.map (fun d => (⟨d, o, r⟩ : XCfg W)) id (step Q c) := by
  rw [xstep, h, step_def]
  cases Q.getD c.pc .reject <;>
    simp only [effect_def, Sum.map_inl, Sum.map_inr, id_eq]
  all_goals congr 3; funext a; simp only [Function.update_apply]; try rfl

/-- A non-verdict step of the projection can only fetch a base instruction. -/
private theorem projected_fetch {W : ℕ} {P : XProgram} {c d : Cfg W}
    (hs : step P.proj c = .inl d) :
    P.getD c.pc (.base .reject) = .base (P.proj.getD c.pc .reject) := by
  have hget : P.proj.getD c.pc .reject =
      (match P.getD c.pc (.base .reject) with | .base i => i | _ => .reject) :=
    by simpa only [XProgram.proj] using
      (mapped_fetch (β := Instr) P (.base .reject)
        (fun i : XInstr => match i with | .base j => j | _ => Instr.reject) c.pc)
  cases hi : P.getD c.pc (.base .reject) <;> simp only [hi] at hget
  case base i => exact congrArg XInstr.base hget.symm
  all_goals
    have hv := step_reject hget
    rw [hs] at hv
    contradiction

/-! ## Private run lifting -/

/-- A map that preserves single steps preserves finite runs. -/
private theorem lift_run {C D : Type} {S : C → C → Prop} {T : D → D → Prop}
    {R : ℕ → C → C → Prop} {R' : ℕ → D → D → Prop}
    (hz : ∀ c d, R 0 c d ↔ c = d)
    (hs : ∀ n c d, R (n + 1) c d ↔ ∃ e, S c e ∧ R n e d)
    (hz' : ∀ c d, R' 0 c d ↔ c = d)
    (hs' : ∀ n c d, R' (n + 1) c d ↔ ∃ e, T c e ∧ R' n e d)
    (f : C → D) (hstep : ∀ c d, S c d → T (f c) (f d))
    {n : ℕ} {c d : C} (h : R n c d) : R' n (f c) (f d) := by
  induction n generalizing c with
  | zero => exact (hz' _ _).mpr (congrArg f ((hz c d).mp h))
  | succ n ih =>
    obtain ⟨e, hstep', hr⟩ := (hs n c d).mp h
    exact (hs' n _ _).mpr ⟨f e, hstep c e hstep', ih hr⟩

section RunCalculus

variable {W : ℕ} {P : XProgram} {x ρ : List Bool}

/-- One run after the other: `n` steps from `c` to `c₁`, then `k` steps from `c₁` to `c₂`, are
`n + k` steps from `c` to `c₂`. The counterpart of `WordRAM.Steps.trans`.

**Proof sketch.** Induct on the first run length, generalizing the starting configuration.
The zero case is the second run; the successor case keeps the first step and composes the
tail by induction, as in `WordRAM.Steps.trans`. -/
theorem XSteps.trans {n k : ℕ} {c c₁ c₂ : XCfg W} (h₁ : XSteps P x ρ n c c₁)
    (h₂ : XSteps P x ρ k c₁ c₂) : XSteps P x ρ (n + k) c c₂ := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h₁
    simpa only [Nat.zero_add] using h₂
  | succ n ih =>
    obtain ⟨d, hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨d, hs, ih hr⟩

/-- **Conservativity, one step.** On a program of vendored instructions, a step of the extended
RAM is the vendored step, with the output and the coin count unchanged.

**Proof sketch.** `mapped_fetch` identifies the instruction in the mapped program.
Apply `xstep_base_fetch`, whose single instruction case analysis uses `step_def` and
`effect_def`; `Function.update_apply` identifies the memory functions. -/
theorem xstep_map_base (P : List Instr) (c : Cfg W) (o : List Bool) (r : ℕ) :
    xstep (P.map .base) x ρ ⟨c, o, r⟩ =
      Sum.map (fun c' => (⟨c', o, r⟩ : XCfg W)) id (step P c) := by
  exact xstep_base_fetch x ρ c o r (mapped_fetch P .reject XInstr.base c.pc)

/-- **Conservativity, runs.** A run of a vendored program is a run of its extended copy, with
the output and the coin count unchanged.

**Proof sketch.** Apply `lift_run` with the configuration embedding that preserves
the output and coin count. `Steps.zero_iff` and `Steps.succ_iff` expose the vendored run,
and `xstep_map_base` preserves each step. -/
theorem XSteps.of_steps {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : Steps P n c c')
    (o : List Bool) (r : ℕ) : XSteps (P.map .base) x ρ n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P c = .inl d)
    (T := fun c d => xstep (P.map .base) x ρ c = .inl d)
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  change xstep (P.map .base) x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
  rw [xstep_map_base, hs, Sum.map_inl]

/-- **The vendored run calculus on mixed code.** A verdict-free run of the projection `P.proj` is
a run of `P` itself, with the output and the coin count unchanged.

**Proof sketch.** Use `lift_run` with the configuration embedding. At each step,
`projected_fetch` rules out a replacement instruction using `step_reject`.
`xstep_base_fetch` then identifies the extended transition with the projected one. -/
theorem XSteps.of_steps_proj {n : ℕ} {c c' : Cfg W} (h : Steps P.proj n c c')
    (o : List Bool) (r : ℕ) : XSteps P x ρ n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P.proj c = .inl d)
    (T := fun c d => xstep P x ρ c = .inl d)
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  change xstep P x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
  rw [xstep_base_fetch x ρ c o r (projected_fetch hs), hs, Sum.map_inl]

end RunCalculus

/-! ## The cells a run touches (backlog PROG-3, RAM level) -/

/-- The cells that a vendored instruction reads or writes in the memory `m`: the cells it names
and, for `load` and `store`, the cell whose address it reads from memory (the source of `load`,
the target of `store`). The verdicts touch nothing. -/
def baseTouches {W : ℕ} (ins : Instr) (m : ℤ → BitVec W) : Finset ℤ :=
  match ins with
  | .one i => {i}
  | .add i j k => {i, j, k}
  | .sub i j k => {i, j, k}
  | .mul i j k => {i, j, k}
  | .load i j => {i, j, (m j).toInt}
  | .store i j => {i, j, (m i).toInt}
  | .bltz i _ => {i}
  | .accept => ∅
  | .reject => ∅

/-- The cells that an instruction of the extended RAM reads or writes in the memory `m`: those of
`baseTouches` for a vendored instruction, and the cells named by a new one. The input and the
coin stream are not cells. -/
def XInstr.touches {W : ℕ} : XInstr → (ℤ → BitVec W) → Finset ℤ
  | .base ins, m => baseTouches ins m
  | .rdIn i j, _ => {i, j}
  | .emit i, _ => {i}
  | .coin i, _ => {i}
  | .half i j, _ => {i, j}

/-- Every instruction touches at most three cells.

**Proof sketch.** Case on the instruction and use `Finset.card_le_three`,
`Finset.card_le_two`, `Finset.card_singleton`, and `Finset.card_empty` for the listed cells. -/
theorem XInstr.card_touches_le {W : ℕ} (ins : XInstr) (m : ℤ → BitVec W) :
    (ins.touches m).card ≤ 3 := by
  cases ins <;> simp only [touches]
  case base i =>
    cases i <;> simp only [baseTouches] <;>
      first | exact Finset.card_le_three
            | simp only [Finset.card_singleton, Finset.card_empty]; omega
  all_goals first
    | exact Finset.card_le_two.trans (by decide)
    | simp only [Finset.card_singleton]; omega

/-- `XStepsIn P x ρ K n c c'`: an `XSteps` run in which every step reads and writes only cells of
`K`, the *footprint*. Every run is such a run for the set of the cells it touches
(`XSteps.exists_xStepsIn`). -/
def XStepsIn {W : ℕ} (P : XProgram) (x ρ : List Bool) (K : Set ℤ) :
    ℕ → XCfg W → XCfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, xstep P x ρ c = .inl c₁ ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K ∧ XStepsIn P x ρ K n c₁ c'

/-- `StepsIn P K n c c'`: a `WordRAM.Steps` run of a vendored program in which every step reads
and writes only cells of `K`. The PROG-3 strengthening of `WordRAM.Steps`, added beside it; the
vendored definition is unchanged. -/
def StepsIn {W : ℕ} (P : List Instr) (K : Set ℤ) : ℕ → Cfg W → Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, step P c = .inl c₁ ∧
      ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K ∧ StepsIn P K n c₁ c'

/-! ## Private footprint inclusion -/

/-- Footprint inclusion for any run relation with the same first-step equations. -/
private theorem footprint_mono {C : Type} {S : C → C → Prop} {F : C → Finset ℤ}
    {R : Set ℤ → ℕ → C → C → Prop}
    (hz : ∀ K c d, R K 0 c d ↔ c = d)
    (hs : ∀ K n c d, R K (n + 1) c d ↔
      ∃ e, S c e ∧ ↑(F c) ⊆ K ∧ R K n e d)
    {K L : Set ℤ} {n : ℕ} {c d : C} (h : R K n c d) (hKL : K ⊆ L) :
    R L n c d := by
  induction n generalizing c with
  | zero => exact (hz L c d).mpr ((hz K c d).mp h)
  | succ n ih =>
    obtain ⟨e, hstep, hK, hr⟩ := (hs K n c d).mp h
    exact (hs L n c d).mpr ⟨e, hstep, hK.trans hKL, ih hr⟩

/-- A run whose steps each touch at most three cells has a finite footprint.

**Proof sketch.** Induct on the run length using its zero and successor equations. In
the successor case unite the first step's footprint with the recursively obtained set.
`Finset.card_union_le` gives the cardinal bound and `footprint_mono` enlarges the tail. -/
private theorem exists_footprint {C : Type} {S : C → C → Prop} {F : C → Finset ℤ}
    {R : ℕ → C → C → Prop} {RI : Set ℤ → ℕ → C → C → Prop}
    (hz : ∀ c d, R 0 c d ↔ c = d)
    (hs : ∀ n c d, R (n + 1) c d ↔ ∃ e, S c e ∧ R n e d)
    (hIz : ∀ K c d, RI K 0 c d ↔ c = d)
    (hIs : ∀ K n c d, RI K (n + 1) c d ↔
      ∃ e, S c e ∧ ↑(F c) ⊆ K ∧ RI K n e d)
    (hcard : ∀ c, (F c).card ≤ 3) {n : ℕ} {c d : C} (h : R n c d) :
    ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ RI (↑K) n c d := by
  induction n generalizing c with
  | zero =>
    obtain rfl := (hz c d).mp h
    exact ⟨∅, by simp only [Finset.card_empty, Nat.mul_zero, le_refl], (hIz _ _ _).mpr rfl⟩
  | succ n ih =>
    obtain ⟨e, hstep, hr⟩ := (hs n c d).mp h
    obtain ⟨L, hL, hrL⟩ := ih hr
    refine ⟨F c ∪ L, ?_, (hIs _ n c d).mpr ⟨e, hstep, ?_, ?_⟩⟩
    · have hc := Finset.card_union_le (F c) L
      have hF := hcard c
      omega
    · intro a ha
      exact Finset.mem_union.mpr (Or.inl ha)
    · exact footprint_mono hIz hIs hrL
        (fun _ ha => Finset.mem_union.mpr (Or.inr ha))

section Footprints

variable {W : ℕ} {K K' : Set ℤ}

/-- A run within a footprint is a `WordRAM.Steps` run, the footprint forgotten.

**Proof sketch.** Apply `lift_run` with the identity configuration map, dropping the
footprint part of the step relation. Read the target run through `Steps.zero_iff` and
`Steps.succ_iff`. -/
theorem StepsIn.toSteps {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : StepsIn P K n c c') :
    Steps P n c c' := by
  exact lift_run (S := fun c d => step P c = .inl d ∧
      ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K)
    (T := fun c d => step P c = .inl d) (R := StepsIn P K) (R' := Steps P)
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [StepsIn, and_assoc])
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    id (fun _ _ hs => hs.1) h

/-- **Every run has a small footprint**: a run of `n` steps of a vendored program stays within a
finite set of at most `3 n` cells, the cells it touches. So `StepsIn` loses nothing.

**Proof sketch.** Apply `exists_footprint` to the vendored step and the
`baseTouches` footprint. `Steps.zero_iff` and `Steps.succ_iff` expose the run, while
`XInstr.card_touches_le` for a base instruction bounds each step by three cells. -/
theorem Steps.exists_stepsIn {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : Steps P n c c') :
    ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ StepsIn P (↑K) n c c' := by
  exact exists_footprint (S := fun c d => step P c = .inl d)
    (F := fun c => baseTouches (P.getD c.pc .reject) c.mem)
    (RI := StepsIn P) (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun c => XInstr.card_touches_le (.base _) c.mem) h

/-- A run within a footprint is a run within every larger set of cells.

**Proof sketch.** Apply `footprint_mono`: induction on the run length composes each
first-step inclusion with the larger footprint inclusion. -/
theorem StepsIn.mono {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : StepsIn P K n c c')
    (hK : K ⊆ K') : StepsIn P K' n c c' := by
  exact footprint_mono (S := fun c d => step P c = .inl d)
    (F := fun c => baseTouches (P.getD c.pc .reject) c.mem)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl) h hK

/-- One run after the other, within the union of the two footprints.

**Proof sketch.** Induct on the first run length. Enlarge the second run to the union
with `StepsIn.mono` in the zero case; in the successor case include the first footprint
in the union and compose the tail by induction. -/
theorem StepsIn.trans {P : List Instr} {n k : ℕ} {c c₁ c₂ : Cfg W}
    (h₁ : StepsIn P K n c c₁) (h₂ : StepsIn P K' k c₁ c₂) :
    StepsIn P (K ∪ K') (n + k) c c₂ := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h₁
    simpa only [Nat.zero_add] using h₂.mono Set.subset_union_right
  | succ n ih =>
    obtain ⟨d, hs, hK, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨d, hs, hK.trans Set.subset_union_left, ih hr⟩

/-! ### Private one-step framing -/

/-- A base step changes no cell outside its footprint.

**Proof sketch.** Read the transition through `step_def`. Each writing arm is an update
at a cell listed by `baseTouches`, so `AgreeOutside.update` applies to
`AgreeOutside.refl`. The branch leaves the memory unchanged, and verdicts cannot step. -/
private theorem step_agreeOutside {P : List Instr} {c d : Cfg W}
    (hs : step P c = .inl d)
    (hK : ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K) :
    AgreeOutside K c.mem d.mem := by
  have write (a : ℤ) (v : BitVec W) (ha : a ∈ K) :
      AgreeOutside K c.mem (fun z => if z = a then v else c.mem z) := by
    have he : (fun z => if z = a then v else c.mem z) = Function.update c.mem a v := by
      funext z
      exact (Function.update_apply c.mem a v z).symm
    rw [he]
    exact (AgreeOutside.refl K c.mem).update ha v
  cases hi : P.getD c.pc .reject <;>
    simp only [step_def, hi, Sum.inl.injEq, Sum.inr_ne_inl] at hs
  all_goals
    subst d
    simp only [hi, baseTouches] at hK
    first | exact AgreeOutside.refl K c.mem
          | exact write _ _ (hK (by simp))

/-- **Every intermediate memory stays inside the footprint** (design §15c, obstacle 1). Along a
run within `K`, the configuration reached after any `k ≤ n` steps splits the run into two runs
within `K`, and its memory agrees with the starting memory outside `K`. The vendored `Finished`
and `compileProgram_correct` speak of the last memory only.

**Proof sketch.** Induct on the prefix length. Split off the first step and
apply induction to the remaining run. `step_agreeOutside` frames that step by
`AgreeOutside.update`, including the indirect target of a store; `AgreeOutside.trans`
composes this frame with that of the remaining prefix. -/
theorem StepsIn.agreeOutside {P : List Instr} {n : ℕ} {c c' : Cfg W}
    (h : StepsIn P K n c c') {k : ℕ} (hk : k ≤ n) :
    ∃ d : Cfg W, StepsIn P K k c d ∧ StepsIn P K (n - k) d c' ∧ AgreeOutside K c.mem d.mem := by
  induction k generalizing n c with
  | zero => exact ⟨c, rfl, h, AgreeOutside.refl K c.mem⟩
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨d, hs, hK, hr⟩ := h
      obtain ⟨e, hp, ht, hm⟩ := ih hr (Nat.le_of_succ_le_succ hk)
      refine ⟨e, ⟨d, hs, hK, hp⟩, ?_, (step_agreeOutside hs hK).trans hm⟩
      simpa only [Nat.add_sub_add_right] using ht

/-- **Straight-line code with its footprint.** A list of straight-line instructions runs through
in its length, as in `WordRAM.steps_straight`, within any `K` that contains what each instruction
touches in every memory. For `load` and `store` the hypothesis asks `K` to contain every address
a word can hold, so in practice this row serves code without them; loads and stores take the
known-number rows `steps_load`/`steps_store`, with their address added to the footprint.

**Proof sketch.** Induct on the instruction list. Obtain the first transition by
specializing `steps_straight` to the singleton head, using `CodeAt.left` and the published
`Steps` equations. Add the footprint inclusion from `hK` and recurse on `CodeAt.tail`;
`effects_cons` identifies the final memory. -/
theorem stepsIn_straight {P : List Instr} (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W)
    (hcode : CodeAt P pc l) (hl : ∀ i ∈ l, Straight i)
    (hK : ∀ i ∈ l, ∀ m' : ℤ → BitVec W, ↑(baseTouches i m') ⊆ K) :
    StepsIn P K l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => simp only [List.length_nil, Nat.add_zero, effects_nil, StepsIn]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.mp hl
    have hfirst : Steps P 1 ⟨pc, m⟩ ⟨pc + 1, effect i m⟩ := by
      simpa only [List.length_singleton, effects_cons, effects_nil] using
        (steps_straight [i] pc m (CodeAt.left (l₂ := l) hcode)
          (by simpa only [List.forall_mem_singleton] using hi))
    obtain ⟨d, hs, he⟩ := Steps.succ_iff.mp hfirst
    obtain rfl := Steps.zero_iff.mp he
    simp only [List.length_cons, effects_cons]
    refine ⟨⟨pc + 1, effect i m⟩, hs, ?_, ?_⟩
    · rw [hcode.head]
      exact hK i (List.mem_cons_self) m
    · have ht := ih (pc + 1) (effect i m) hcode.tail hl
        (fun j hj m' => hK j (List.mem_cons_of_mem i hj) m')
      convert ht using 1; congr 1; omega

/-- An extended run within a footprint is an `XSteps` run, the footprint forgotten.

**Proof sketch.** Apply `lift_run` with the identity configuration map, dropping
only the footprint inclusion from each extended step. -/
theorem XStepsIn.toXSteps {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W}
    (h : XStepsIn P x ρ K n c c') : XSteps P x ρ n c c' := by
  exact lift_run (S := fun c d => xstep P x ρ c = .inl d ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K)
    (T := fun c d => xstep P x ρ c = .inl d) (R := XStepsIn P x ρ K)
    (R' := XSteps P x ρ) (fun _ _ => Iff.rfl)
    (fun _ _ _ => by simp only [XStepsIn, and_assoc])
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) id (fun _ _ hs => hs.1) h

/-- **Every extended run has a small footprint**: a run of `n` steps stays within a finite set of
at most `3 n` cells, the cells it touches.

**Proof sketch.** Apply the shared `exists_footprint` construction to
`xstep` and `XInstr.touches`. `XInstr.card_touches_le` bounds each step, and
`Finset.card_union_le` bounds their accumulated union. -/
theorem XSteps.exists_xStepsIn {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W}
    (h : XSteps P x ρ n c c') : ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ XStepsIn P x ρ (↑K) n c c' := by
  exact exists_footprint (S := fun c d => xstep P x ρ c = .inl d)
    (F := fun c => (P.getD c.pc (.base .reject)).touches c.mem)
    (RI := XStepsIn P x ρ) (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun c => XInstr.card_touches_le _ c.mem) h

/-- The footprint form of `XSteps.of_steps_proj`: a verdict-free run of the projection within `K`
is a run of the extended program within `K`.

**Proof sketch.** Use `lift_run` to preserve both the transition and its
footprint. `projected_fetch` identifies the fetched base instruction, and
`xstep_base_fetch` identifies its transition; its `XInstr.touches` is the projected
instruction's `baseTouches`. -/
theorem XStepsIn.of_stepsIn_proj {P : XProgram} {x ρ : List Bool} {n : ℕ}
    {c c' : Cfg W} (h : StepsIn P.proj K n c c') (o : List Bool) (r : ℕ) :
    XStepsIn P x ρ K n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P.proj c = .inl d ∧
      ↑(baseTouches (P.proj.getD c.pc .reject) c.mem) ⊆ K)
    (T := fun c d => xstep P x ρ c = .inl d ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K)
    (R := StepsIn P.proj K) (R' := XStepsIn P x ρ K)
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [StepsIn, and_assoc])
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  obtain ⟨hs, hK⟩ := hs
  have hf := projected_fetch hs
  constructor
  · change xstep P x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
    rw [xstep_base_fetch x ρ c o r hf, hs, Sum.map_inl]
  · change ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K
    rw [hf]
    exact hK

end Footprints

/-! ## Starting and halting -/

/-- **The memory in which a run starts**, on an input of length `n`: the cell `-1` holds `n`
(as a word, so modulo `2^W`) and every other cell holds `0`. The cell `-1` is the compiler's
first argument cell (`Light.Compiler.cARG1`, `Light/Compiler/StatementCode.lean:82`), so a
compiled program receives `|x|` as its first argument (design §15c: `inLen` from an argument
cell, no `len` instruction). -/
def initMem (W n : ℕ) : ℤ → BitVec W :=
  Function.update (fun _ => 0) (-1) (wd W n)

/-- The start configuration on an input of length `n`: position `0`, `initMem W n`, nothing
emitted, no coin consumed. -/
def XCfg.init (W n : ℕ) : XCfg W := { pc := 0, mem := initMem W n, out := [], rd := 0 }

/-- **Halting within steps and cells** (stage 2's hypothesis). `HaltsWithin P x ρ W t v o f`: run
on the input `x` with the coin stream `ρ` and word size `W` from `XCfg.init W |x|`, the program
`P` gives the verdict `v` within `t` steps, the verdict step counted as in `WordRAM.exec`; it has
then emitted `o`; and every step before the verdict stays within a set of at most `f` cells. -/
def HaltsWithin (P : XProgram) (x ρ : List Bool) (W t : ℕ) (v : Bool) (o : List Bool) (f : ℕ) :
    Prop :=
  ∃ (n : ℕ) (c : XCfg W) (K : Finset ℤ), n < t ∧ K.card ≤ f ∧
    XStepsIn P x ρ (↑K) n (XCfg.init W x.length) c ∧ xstep P x ρ c = .inr v ∧ c.out = o

section Halting

variable {P : XProgram} {x ρ : List Bool} {W t t' f f' : ℕ} {v v' : Bool} {o o' : List Bool}

/-- A run that halts within `t` steps and `f` cells halts within any larger bounds.

**Proof sketch.** Keep the same witnesses, composing `n < t` with `t ≤ t'` and
the footprint cardinal bound with `f ≤ f'`. -/
theorem HaltsWithin.mono (h : HaltsWithin P x ρ W t v o f) (ht : t ≤ t') (hf : f ≤ f') :
    HaltsWithin P x ρ W t' v o f' := by
  obtain ⟨n, c, K, hn, hK, hr, hv, ho⟩ := h
  exact ⟨n, c, K, hn.trans_le ht, hK.trans hf, hr, hv, ho⟩

/-- **A bound in steps gives one in cells**: a run that halts within `t` steps halts within `t`
steps touching at most `3 t` cells. So for time bounds the cell count needs no separate proof.

**Proof sketch.** Forget the footprint with `XStepsIn.toXSteps`, then use
`XSteps.exists_xStepsIn` to obtain at most `3 * n` cells. Multiply `n < t` by three
to place that footprint within the required bound. -/
theorem HaltsWithin.touches_le (h : HaltsWithin P x ρ W t v o f) :
    HaltsWithin P x ρ W t v o (3 * t) := by
  obtain ⟨n, c, _, hn, _, hr, hv, ho⟩ := h
  obtain ⟨K, hK, hrun⟩ := hr.toXSteps.exists_xStepsIn
  exact ⟨n, c, K, hn, hK.trans (Nat.mul_le_mul_left 3 hn.le), hrun, hv, ho⟩

/-! ### Private halting-run determinism -/

/-- Two runs from one configuration that end in verdicts have the same last configuration
and verdict.

**Proof sketch.** Induct on the first length and case on the second. A zero-length run
already gives a verdict, so a positive-length competitor contradicts the disjointness of
`Sum.inl` and `Sum.inr`. If both lengths are positive, injectivity of `Sum.inl` identifies
the first successors and the induction hypothesis identifies the tails. -/
private theorem xSteps_verdict_unique {n k : ℕ} {c d e : XCfg W}
    (h₁ : XSteps P x ρ n c d) (hv : xstep P x ρ d = .inr v)
    (h₂ : XSteps P x ρ k c e) (hv' : xstep P x ρ e = .inr v') :
    d = e ∧ v = v' := by
  induction n generalizing c k with
  | zero =>
    obtain rfl := h₁
    cases k with
    | zero =>
      obtain rfl := h₂
      exact ⟨rfl, Sum.inr.inj (hv.symm.trans hv')⟩
    | succ k =>
      obtain ⟨a, hs, _⟩ := h₂
      have bad := hv.symm.trans hs
      contradiction
  | succ n ih =>
    obtain ⟨a, hs, hr⟩ := h₁
    cases k with
    | zero =>
      obtain rfl := h₂
      have bad := hv'.symm.trans hs
      contradiction
    | succ k =>
      obtain ⟨b, hs', hr'⟩ := h₂
      have he : a = b := Sum.inl.inj (hs.symm.trans hs')
      subst b
      exact ih hr hr'

/-- **The run is determined** by the input, the coin stream and the word size: two halting runs
give the same verdict and the same output.

**Proof sketch.** Forget the footprints and apply `xSteps_verdict_unique`.
That helper synchronizes the two runs using injectivity of `Sum.inl` and excludes
stepping past a verdict. Equality of the last configurations identifies their outputs. -/
theorem HaltsWithin.unique (h : HaltsWithin P x ρ W t v o f)
    (h' : HaltsWithin P x ρ W t' v' o' f') : v = v' ∧ o = o' := by
  obtain ⟨_, c, _, _, _, hr, hv, ho⟩ := h
  obtain ⟨_, d, _, _, _, hr', hv', ho'⟩ := h'
  obtain ⟨he, hvv⟩ := xSteps_verdict_unique hr.toXSteps hv hr'.toXSteps hv'
  exact ⟨hvv, ho.symm.trans ((congrArg XCfg.out he).trans ho')⟩

/-! ### Private coin-free transition -/

/-- A coin-free program takes the same step for every coin stream. -/
private theorem xstep_coin_irrel (hP : CoinFree P) (ρ' : List Bool) (c : XCfg W) :
    xstep P x ρ c = xstep P x ρ' c := by
  have hnot : ∀ a, P.getD c.pc (.base .reject) ≠ .coin a := by
    intro a ha
    rw [List.getD_eq_getElem?_getD, Option.getD_eq_iff] at ha
    rcases ha with hm | ⟨_, he⟩
    · exact hP (.coin a) (List.mem_of_getElem? hm) a rfl
    · cases he
  cases hi : P.getD c.pc (.base .reject) <;> simp only [xstep, hi]
  case base i => cases i <;> rfl
  case coin i => exact (hnot i hi).elim

/-- **A coin-free program does not depend on the coin stream.**

**Proof sketch.** `xstep_coin_irrel` excludes a fetched coin instruction
using `CoinFree` and `List.mem_of_getElem?`. Apply `lift_run` with the identity map to
transport each footprint run between coin streams, preserving the final verdict and output.
The same transport proves both directions. -/
theorem HaltsWithin.coin_irrel (hP : CoinFree P) (ρ' : List Bool) :
    HaltsWithin P x ρ W t v o f ↔ HaltsWithin P x ρ' W t v o f := by
  have transport (σ τ : List Bool) (h : HaltsWithin P x σ W t v o f) :
      HaltsWithin P x τ W t v o f := by
    obtain ⟨n, c, K, hn, hK, hr, hv, ho⟩ := h
    refine ⟨n, c, K, hn, hK, ?_, (xstep_coin_irrel hP τ c).symm.trans hv, ho⟩
    exact lift_run (S := fun a b => xstep P x σ a = .inl b ∧
        ↑((P.getD a.pc (.base .reject)).touches a.mem) ⊆ (↑K : Set ℤ))
      (T := fun a b => xstep P x τ a = .inl b ∧
        ↑((P.getD a.pc (.base .reject)).touches a.mem) ⊆ (↑K : Set ℤ))
      (R := XStepsIn P x σ (↑K)) (R' := XStepsIn P x τ (↑K))
      (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
      (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
      id (fun a _ hs => ⟨(xstep_coin_irrel hP τ a).symm.trans hs.1, hs.2⟩) hr
  exact ⟨transport ρ ρ', transport ρ' ρ⟩

end Halting

/-! ## Readers

Equations for the definitions above, so that other files read them without unfolding them
(policy rule 10; Seyoon, 2026-11-18, for stage 2's simulation). Each restates its definition and
is proved by `rfl` or `Iff.rfl`. -/

section Readers

variable {W : ℕ}

/-- The word of an input bit, as an equation: `1` if `0 ≤ p` and the bit of `x` at `p` is
`true`, and `0` otherwise. -/
theorem inBitWord_def (x : List Bool) (p : ℤ) :
    inBitWord W x p = if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0 := rfl

/-- The word of a coin, as an equation: `1` for `true`, `0` for `false`. -/
theorem coinWord_def (b : Bool) : coinWord W b = if b then 1 else 0 := rfl

/-- **One step of the extended RAM, as an equation**: the match on the instruction at `c.pc`
(`WordRAM.reject` past the end). -/
theorem xstep_def (P : XProgram) (x ρ : List Bool) (c : XCfg W) :
    xstep P x ρ c =
      match P.getD c.pc (.base .reject) with
      | .base .accept => .inr true
      | .base .reject => .inr false
      | .base (.bltz i l) =>
        .inl { c with pc := if (c.mem i).toInt < 0 then l else c.pc + 1 }
      | .base ins => .inl { c with pc := c.pc + 1, mem := effect ins c.mem }
      | .rdIn i j =>
        .inl { c with pc := c.pc + 1,
                      mem := Function.update c.mem i (inBitWord W x (c.mem j).toInt) }
      | .emit i => .inl { c with pc := c.pc + 1, out := c.out ++ [decide (c.mem i ≠ 0)] }
      | .coin i =>
        .inl { c with pc := c.pc + 1,
                      mem := Function.update c.mem i (coinWord W (ρ.getD c.rd false)),
                      rd := c.rd + 1 }
      | .half i j =>
        .inl { c with pc := c.pc + 1, mem := Function.update c.mem i ((c.mem j).sshiftRight 1) }
    := rfl

/-- A run of no steps stays where it is. -/
theorem XSteps.zero_iff {P : XProgram} {x ρ : List Bool} {c c' : XCfg W} :
    XSteps P x ρ 0 c c' ↔ c = c' := Iff.rfl

/-- A run of `n + 1` steps is a first step to some `c₁`, giving no verdict, followed by a run of
`n` steps from `c₁`. -/
theorem XSteps.succ_iff {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W} :
    XSteps P x ρ (n + 1) c c' ↔ ∃ c₁, xstep P x ρ c = .inl c₁ ∧ XSteps P x ρ n c₁ c' := Iff.rfl

/-- The cells a vendored instruction touches, as an equation. -/
theorem baseTouches_def (ins : Instr) (m : ℤ → BitVec W) :
    baseTouches ins m =
      match ins with
      | .one i => {i}
      | .add i j k => {i, j, k}
      | .sub i j k => {i, j, k}
      | .mul i j k => {i, j, k}
      | .load i j => {i, j, (m j).toInt}
      | .store i j => {i, j, (m i).toInt}
      | .bltz i _ => {i}
      | .accept => ∅
      | .reject => ∅ := rfl

/-- The cells an instruction of the extended RAM touches, as an equation. -/
theorem XInstr.touches_def (ins : XInstr) (m : ℤ → BitVec W) :
    ins.touches m =
      match ins with
      | .base ins => baseTouches ins m
      | .rdIn i j => {i, j}
      | .emit i => {i}
      | .coin i => {i}
      | .half i j => {i, j} := by
  cases ins <;> rfl

/-- A run within `K` of no steps stays where it is. -/
theorem XStepsIn.zero_iff {P : XProgram} {x ρ : List Bool} {K : Set ℤ} {c c' : XCfg W} :
    XStepsIn P x ρ K 0 c c' ↔ c = c' := Iff.rfl

/-- A run within `K` of `n + 1` steps is a first step to some `c₁`, giving no verdict and
touching only cells of `K`, followed by a run within `K` of `n` steps from `c₁`. -/
theorem XStepsIn.succ_iff {P : XProgram} {x ρ : List Bool} {K : Set ℤ} {n : ℕ}
    {c c' : XCfg W} :
    XStepsIn P x ρ K (n + 1) c c' ↔ ∃ c₁, xstep P x ρ c = .inl c₁ ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K ∧ XStepsIn P x ρ K n c₁ c' := Iff.rfl

/-- The memory in which a run starts, as an equation: `n` (as a word) at the cell `-1` and `0`
everywhere else. -/
theorem initMem_def (n : ℕ) : initMem W n = Function.update (fun _ => 0) (-1) (wd W n) := rfl

/-- The start configuration, as an equation. -/
theorem XCfg.init_def (n : ℕ) :
    XCfg.init W n = { pc := 0, mem := initMem W n, out := [], rd := 0 } := rfl

/-- Halting within steps and cells, as an equivalence with its definition. -/
theorem haltsWithin_iff (P : XProgram) (x ρ : List Bool) (t : ℕ) (v : Bool) (o : List Bool)
    (f : ℕ) :
    HaltsWithin P x ρ W t v o f ↔
      ∃ (n : ℕ) (c : XCfg W) (K : Finset ℤ), n < t ∧ K.card ≤ f ∧
        XStepsIn P x ρ (↑K) n (XCfg.init W x.length) c ∧ xstep P x ρ c = .inr v ∧ c.out = o :=
  Iff.rfl

end Readers

end WordRAM
