/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTable
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRegister
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemoryMachines
import TCSlib.Complexity.RAMSimulation.Sim.PhaseEmit
import TCSlib.Complexity.TuringMachine.Build.InputBit
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: one phase per instruction

The simulating machine runs one phase for each instruction it executes. A phase is a machine on
the eight tapes of `WordRAM.Sim.Encodes`: from tapes encoding a configuration `c` whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep … c`, and its exit
tells the host where the program goes next. The host (a phase host over the program's positions)
and the induction over a run are built from these phases.

Every phase is a nondeterministic machine whose two transitions agree everywhere except at the
entry of a `coin` phase, where the choice is the coin. Fixing the choice gives a deterministic
machine (`Turing.NDTM.fixChoice`), and the phase's run is stated for each fixed choice; the
deterministic simulation fixes it to `false`, so that coins read `0`.

## Main definitions

* `WordRAM.Sim.isCoin`, `WordRAM.Sim.isVerdict`, `WordRAM.Sim.jumpTarget`.

## Main results

* `WordRAM.Sim.exists_phase`: the phase of an instruction other than `accept` and `reject`.
* `WordRAM.Sim.exists_verdictPhase`: the phase of `accept` and `reject`, which writes the output
  and halts.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2: nondeterministic machines.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- Whether an instruction is a `coin`. -/
def isCoin : XInstr → Bool
  | .coin _ => true
  | _ => false

/-- Whether an instruction is a `coin`, as an equation. -/
theorem isCoin_def (ins : XInstr) :
    isCoin ins = match ins with
      | .coin _ => true
      | _ => false := by
  cases ins <;> rfl

/-- Whether an instruction gives a verdict: `accept` or `reject`. -/
def isVerdict : XInstr → Bool
  | .base .accept => true
  | .base .reject => true
  | _ => false

/-- Whether an instruction gives a verdict, as an equation. -/
theorem isVerdict_def (ins : XInstr) :
    isVerdict ins = match ins with
      | .base .accept => true
      | .base .reject => true
      | _ => false := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- The position a taken jump goes to: the label of `bltz`, and `0` for any other instruction
(which never jumps). -/
def jumpTarget : XInstr → ℕ
  | .base (.bltz _ l) => l
  | _ => 0

/-- The position a taken jump goes to, as an equation. -/
theorem jumpTarget_def (ins : XInstr) :
    jumpTarget ins = match ins with
      | .base (.bltz _ l) => l
      | _ => 0 := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **The phase of an instruction.** For `a`, an output mode `fn` and an instruction `ins` that is
not a verdict and whose addresses are below `2^(a-1)` in absolute value, there is a
nondeterministic machine `N` on eight tapes, with an entry and two exits `next` and `jump`, and a
constant `C`, such that:
* the entry is never re-entered, and the two transitions of `N` agree at every state except the
  entry, and at the entry too unless `ins` is a `coin`;
* for each choice `b`: whenever the instruction at `c.pc` of a program `P` is `ins` (and, for a
  `coin`, the coin `ρ.getD c.rd false` is `b`), and `d`, at the entry, encodes `c` over the cells
  `T` with origins `o`, then `xstep P x ρ c` is a configuration `c'`, and the machine with the
  choice fixed to `b` reaches, within `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
  `C·((|T| + 1)·(W + 1) + log |x| + 1)`, a configuration `d'` encoding `c'` over the cells
  `T ∪ touches` with the same origins, at `next` if the program goes on to `c.pc + 1` and at
  `jump` if it jumps to `jumpTarget ins`.

[AB09, Exercise 1.9; §2.1.2]

**Proof sketch.** Choose the certified phase by cases on `ins`: `phase_oneMachine`,
`phase_binaryMachine`, the load/store/half/input machines, `phase_bltzMachine`,
`phase_emitMachine` or `phase_coinMachine`. These place the native word, keyed-memory and input
rows on the eight tapes and compose their contracts. The coin and emission continuations use
`NDTM.phaseHostND` through `Contract.inPhase`; the coin remembers its one choice at a fresh
entry. `TableOf` correctness and the address-range/layout lemmas preserve the memory encoding,
and `phaseTime`/`phaseSpace` absorb every native allowance and dispatch. Finally remove the
initial control with `PhaseFrame.ofCfg`, run the selected `PhaseMachine`, and apply its
`PhasePost` to the matching program and compatible coin stream. Reinstall the selected next or
jump control; encoding congruence preserves the tape postcondition and the frame equations give
the theorem's exact bounds. -/
theorem exists_phase (a : ℕ) (fn : Bool) (ins : XInstr) (hins : ImmBound a ins)
    (hv : isVerdict ins = false) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : NDTM 8 Bool S) (entry next jump : S)
      (C : ℕ), next ≠ jump ∧
      (∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry) ∧
      (∀ q : S, q ≠ entry ∨ isCoin ins = false → N.tr false q = N.tr true q) ∧
      ∀ (b : Bool) {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool) (T : Finset ℤ)
        (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x),
        P.getD c.pc (.base .reject) = ins → (isCoin ins = true → ρ.getD c.rd false = b) →
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ (c' : XCfg W) (d' : Turing.Cfg 8 Bool S x), xstep P x ρ c = .inl c' ∧
          Encodes a fn (T ∪ ins.touches c.mem) c' (Function.Embedding.refl _) o d' ∧
          ((d'.state = some next ∧ c'.pc = c.pc + 1) ∨
            (d'.state = some jump ∧ c'.pc = jumpTarget ins)) ∧
          ReachesWithin (N.fixChoice b) d {some next, some jump}
            (C * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1))
            (C * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1)) d' := by
  have hImm : ∀ z ∈ immediates ins, InRange a z := (immBound_iff a ins).mp hins
  have hm : ∃ flag : Bool → List Bool → PhaseData → Bool,
      Nonempty (PhaseMachine (isCoin ins) (PhaseState a fn (fun _ _ _ => none))
        (fun b x i F => PhasePost a fn ins (jumpTarget ins) (flag b x i) b x i F) flag) := by
    cases ins with
    | base op =>
      cases op with
      | one z =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_oneMachine a fn z hz
      | add z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .add
      | sub z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .sub
      | mul z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .mul
      | load z j =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_loadMachine a fn z j hz hj
      | store z j =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_storeMachine a fn z j hz hj
      | bltz z label =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ i => PhaseTestKind.sign.bit (i.cfg.mem z), ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_bltzMachine a fn z label hz
      | accept =>
        have h : (true : Bool) = false := by simpa only [isVerdict_def] using hv
        cases h
      | reject =>
        have h : (true : Bool) = false := by simpa only [isVerdict_def] using hv
        cases h
    | rdIn z j =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_inputMachine a fn z j hz hj
    | emit z =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_emitMachine a fn z hz
    | coin z =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_coinMachine a fn z hz
    | half z j =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_halfMachine a fn z j hz hj
  obtain ⟨flag, ⟨M⟩⟩ := hm
  letI := M.finite
  letI := M.decEq
  refine ⟨M.State, M.finite, M.decEq, M.machine, M.entry, M.next, M.jump, M.constant,
    M.distinct, M.fresh, M.agree, ?_⟩
  intro b x W P ρ T c o d hf hc hd he
  let i : PhaseData := ⟨W, T, c, o⟩
  let F := PhaseFrame.ofCfg d
  have hp : PhaseState a fn (fun _ _ _ => none) x i F := by
    apply (phaseState_iff a fn _ x i F).mpr
    refine ⟨phase_frame_ofCfg_encodes fn T c o d he, ?_⟩
    intro r w h
    cases h
  obtain ⟨G, hq, hr⟩ := M.run b x i F hp
  have hcoins : ∀ z : ℤ, ins = .coin z → ρ.getD c.rd false = b := by
    intro z hz
    apply hc
    simp only [hz, isCoin_def]
  obtain ⟨c', hs, he', hpc⟩ := (phasePost_iff a fn ins (jumpTarget ins) (flag b x i) b x i G).mp
    hq P ρ hf hcoins
  let d' := G.cfg (if flag b x i then M.jump else M.next)
  refine ⟨c', d', hs, ?_, ?_, ?_⟩
  · exact (phase_encodes_congr fn _ c' c' (Function.Embedding.refl _) o (G.cfg ()) d'
      (by simp only [d', PhaseFrame.cfg_eq]) (by simp only [d', PhaseFrame.cfg_eq])
      (by simp only [d', PhaseFrame.cfg_eq]) rfl rfl).mp he'
  · by_cases hflag : flag b x i = true
    · right
      exact ⟨by simp only [d', if_pos hflag, PhaseFrame.cfg_eq],
        by simpa only [if_pos hflag] using hpc⟩
    · left
      exact ⟨by simp only [d', if_neg hflag, PhaseFrame.cfg_eq],
        by simpa only [if_neg hflag] using hpc⟩
  · have hF : F.cfg M.entry = d := PhaseFrame.cfg_ofCfg d M.entry hd
    rw [hF] at hr
    simpa only [i, phaseTime_eq, phaseSpace_eq, d'] using hr

/-- **The phase of a verdict.** For an output mode `fn` and a verdict `v`, there is a deterministic
machine on eight tapes, with an entry, and a constant `C`, such that from tapes at the entry
encoding `c`, the machine halts within `C` steps with the output `c.out` in function mode and
`[v]` in verdict mode, every head fixed. [AB09, Exercise 1.9]

**Proof sketch.** A stationary action halts after one step, emitting `v` precisely in verdict
mode. `encodes_iff` supplies the initial output. `MultiTapeTM.runFrom_one`,
`MultiTapeTM.step_of_some` and the field equations of `Action.apply` give the final state,
output and unchanged heads. There is no catalog row for this stationary optional emission
followed by a halt, so the action is supplied directly. -/
theorem exists_verdictPhase (fn v : Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 8 Bool S) (entry : S)
      (C : ℕ),
      ∀ (a : ℕ) {x : List Bool} {W : ℕ} (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
        (d : Turing.Cfg 8 Bool S x),
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ t ≤ C, (M.runFrom d t).state = none ∧
          (M.runFrom d t).output = (if fn then c.out else [v]) ∧
          ∀ s ≤ t, (M.runFrom d s).workTapePos = d.workTapePos := by
  let M : MultiTapeTM 8 Bool Unit :=
    ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), if fn then none else some v, none⟩⟩
  refine ⟨Unit, inferInstance, inferInstance, M, (), 1, ?_⟩
  intro a x W T c o d hd he
  have ho := ((encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he).2.2.2.2.2.2
  have hstep : M.runFrom d 1 =
      (M.tr () d.inputSymbol d.workTapeSymbols).apply d := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (tm := M) hd]
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · rw [hstep, Action.apply_state]
  · rw [hstep, Action.apply_output, ho]
    cases fn <;> simp only [M, Bool.false_eq_true, ↓reduceIte, Option.toList_some,
      Option.toList_none, List.nil_append, List.append_nil]
  · intro s hs
    have hs' : s = 0 ∨ s = 1 := by omega
    rcases hs' with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]
      funext j
      rw [Action.apply_workTapePos]
      simp only [M, SignType.coe_zero, add_zero]

end WordRAM.Sim
