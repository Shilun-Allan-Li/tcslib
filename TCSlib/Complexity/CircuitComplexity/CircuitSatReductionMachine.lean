/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachineTapes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Tseitin emitter machine: simulation

The proof that the three-work-tape machine `BoolCircuit.CktSatReduction.Emitter.emTM`
(`CircuitSatReductionMachineTapes.lean`) computes the Tseitin emitter
`BoolCircuit.CktSatReduction.Emitter.gateClauses` of `CircuitSatReductionSpec.lean`
within `200 · (n + 1)²` steps.

Work tape `t ∈ {0, 1, 2}` holds counter `t` of the algorithm (the vertex `z`, the
arguments `a`, `b`) in unary: cells `0, …, v - 1` hold `1`, everything else is blank, and
between input symbols the head rests on cell `v`.  Incrementing a counter writes one
cell and steps right.  Printing a counter walks left over its cells emitting a `1` for
each, then walks back; resetting a counter walks left erasing.

## Main definitions

* `BoolCircuit.CktSatReduction.Emitter.cfgS` — the configuration of an abstract state.

## Main results

* `BoolCircuit.CktSatReduction.Emitter.em_main_run` — from the configuration of an abstract
  state, the machine halts with the abstract output `emRun`.
* `BoolCircuit.CktSatReduction.Emitter.emTM_computes` — the machine computes `gateClauses`
  within `200 · (n + 1)²` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§1.2: the multi-tape machine; §6.1.2, Lemma 6.11.)
-/

namespace BoolCircuit

namespace CktSatReduction

namespace Emitter

open Turing Turing.UnaryTape

/-! ## Counter configurations -/

/-- The work tapes holding the counters `v`. -/
def tapesOf (v : Fin 3 → ℕ) : Fin 3 → ℤ → Option Bool := fun i => ones (v i)

/-- The heads resting after the counters `v`. -/
def headsOf (v : Fin 3 → ℕ) : Fin 3 → ℤ := fun i => (v i : ℤ)

/-- Replacing one counter's tape by the unary tape of `m` sets that counter to `m`. -/
theorem tapesOf_update (v : Fin 3 → ℕ) (t : Fin 3) (m : ℕ) :
    Function.update (tapesOf v) t (ones m) = tapesOf (Function.update v t m) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp [tapesOf]
  · simp [tapesOf, hi]

/-- Moving one counter's head to cell `m` is the rest position of the counter `m`. -/
theorem headsOf_update (v : Fin 3 → ℕ) (t : Fin 3) (m : ℕ) :
    Function.update (headsOf v) t (m : ℤ) = headsOf (Function.update v t m) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp [headsOf]
  · simp [headsOf, hi]

/-- Moving one counter's head to cell `0` is the rest position of the counter `0`. -/
theorem headsOf_update_zero (v : Fin 3 → ℕ) (t : Fin 3) :
    Function.update (headsOf v) t 0 = headsOf (Function.update v t 0) := by
  simpa using headsOf_update v t 0

/-- The input-head position reading symbol `i`. -/
def ip (w : List Bool) (i : ℕ) (hi : i ≤ w.length) : Fin (w.length + 2) := ⟨i + 1, by omega⟩

/-- Moving the input head right from symbol `i < |w|` reads symbol `i + 1`. -/
theorem move_ip (w : List Bool) (i : ℕ) (hi : i < w.length) :
    moveInputPos (ip w i hi.le) .pos = ip w (i + 1) hi := by
  rw [moveInputPos_pos_of_ne_right _ (by simp [ip]; omega)]
  rfl

/-- **The emission loop**: from instruction `pc` of a gate's program, with counters `v`
bounded by `M`, the machine prints the rest of the program, `rest.flatMap (exec v)`, in
at most `|rest| · (2M + 3)` steps and stops at the end of the program.

**Proof sketch.** Induction on the remaining instructions: an output instruction is one
step; a print instruction is one step left onto the counter, the print walk
(`print_walk`) and the return walk (`back_walk`), `2 v t + 3` steps in all. -/
theorem em_loop {w : List Bool} (k : GateKind) (c : Fin 3) (p : Fin (w.length + 2))
    (v : Fin 3 → ℕ) (M : ℕ) (hM : ∀ t, v t ≤ M) :
    ∀ (rest : List Instr) (pc : ℕ) (hpc : pc < 64) (out : List Bool),
      (prog k c).drop pc = rest →
      ∃ T ≤ rest.length * (2 * M + 3), ∃ pe : Fin 64, (prog k c)[pe.val]? = none ∧
        emTM.tm.runFrom (⟨some (.em k c ⟨pc, hpc⟩), p, tapesOf v, headsOf v, out⟩ :
          Cfg 3 Bool St w) T =
          ⟨some (.em k c pe), p, tapesOf v, headsOf v, out ++ rest.flatMap (exec v)⟩ := by
  intro rest
  induction rest with
  | nil =>
    intro pc hpc out hr
    refine ⟨0, by simp, ⟨pc, hpc⟩, ?_, by simp⟩
    have := congrArg List.length hr
    simp only [List.length_drop, List.length_nil] at this
    exact List.getElem?_eq_none (show (prog k c).length ≤ pc by omega)
  | cons ins rest ih =>
    intro pc hpc out hr
    have hlen := length_prog_le k c
    have hlt : pc < (prog k c).length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hr
      exact List.cons_ne_nil _ _ hr.symm
    have hget : (prog k c)[pc]? = some ins := by
      have := congrArg List.head? hr
      simpa [List.head?_drop] using this
    have hr' : (prog k c).drop (pc + 1) = rest := by
      have := congrArg List.tail hr
      simpa [List.tail_drop] using this
    have hsucc : (⟨pc, hpc⟩ + 1 : Fin 64) = ⟨pc + 1, by omega⟩ := by
      apply Fin.ext; simp [Fin.val_add]; omega
    cases ins with
    | out b =>
      obtain ⟨T, hT, pe, hpe, hrun⟩ := ih (pc + 1) (by omega) (out ++ [b]) hr'
      refine ⟨1 + T, ?_, pe, hpe, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step,
          MultiTapeTM.runFrom_zero, step_some]
        simp only [tr, hget]
        rw [apply_ctl, moveInputPos_zero, hsucc]
        simp only [Option.toList_some]
        rw [hrun]
        simp [exec]
    | pr t =>
      obtain ⟨T, hT, pe, hpe, hrun⟩ := ih (pc + 1) (by omega)
        (out ++ List.replicate (v t) true) hr'
      refine ⟨1 + (v t + 1) + (v t + 1) + T, ?_, pe, hpe, ?_⟩
      · have := hM t
        simp only [List.length_cons]; nlinarith
      · have h1 : emTM.tm.runFrom (⟨some (.em k c ⟨pc, hpc⟩), p, tapesOf v, headsOf v, out⟩ :
            Cfg 3 Bool St w) 1 = ⟨some (.prW k c ⟨pc, hpc⟩ t), p, tapesOf v,
              Function.update (headsOf v) t (((v t : ℕ) : ℤ) - 1), out⟩ := by
          rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
          simp only [tr, hget]
          rw [apply_act, moveInputPos_zero]
          simp only [wrT, Function.update_eq_self, Option.toList_none, List.append_nil]
          rw [show headsOf v t + ((SignType.neg : SignType) : ℤ) = ((v t : ℕ) : ℤ) - 1 by
            simp [headsOf, SignType.cast]; omega]
        have h2 := print_walk k c ⟨pc, hpc⟩ t p (tapesOf v) (headsOf v) (v t) rfl (v t) out le_rfl
        have h3 := back_walk k c ⟨pc, hpc⟩ t p (tapesOf v) (headsOf v) (v t) rfl
          (out ++ List.replicate (v t) true) (v t) le_rfl
        rw [show (((v t - v t : ℕ) : ℤ)) = 0 by simp,
          show Function.update (headsOf v) t ((v t : ℕ) : ℤ) = headsOf v from
            Function.update_eq_self _ _, hsucc] at h3
        rw [MultiTapeTM.runFrom_add _ (1 + (v t + 1) + (v t + 1)) T,
          MultiTapeTM.runFrom_add _ (1 + (v t + 1)) (v t + 1),
          MultiTapeTM.runFrom_add _ 1 (v t + 1), h1, h2, h3, hrun]
        simp [exec]

/-- The machine configuration of an abstract state, reading input symbol `i`. -/
def cfgS (w : List Bool) (s : ES) (i : ℕ) (hi : i ≤ w.length) (out : List Bool) :
    Cfg 3 Bool St w :=
  ⟨some (.rd s.φ), ip w i hi, tapesOf s.vec, headsOf s.vec, out⟩


/-- One step from the configuration of an abstract state applies the transition of its
phase to the input symbol read. -/
theorem rd_step (w : List Bool) (s : ES) (i : ℕ) (hi : i ≤ w.length) (out : List Bool) :
    emTM.tm.runFrom (cfgS w s i hi out) 1 =
      (tr (.rd s.φ) w[i]? (fun j => tapesOf s.vec j (headsOf s.vec j))).apply
        (cfgS w s i hi out) := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  unfold cfgS
  rw [step_some, FinTM.inputSymbol_at _ i hi rfl]

/-- The gate excursion: at the end of a gate's argument list (phase `l k c`, the `0`
already consumed), the machine prints the gate's program, erases the argument counters,
increments the vertex counter and returns to phase `g`, within `200 (M + 1)` steps.

**Proof sketch.** The emission loop (`em_loop`) prints `emitBits`; one step moves onto
counter `1`, the erase walk (`clear_walk`) clears it, one step moves onto counter `2`,
the erase walk clears it, and one step increments counter `0`. -/
theorem gate_run (w : List Bool) (s : ES) (k : GateKind) (c : Fin 3) (i : ℕ)
    (hi : i ≤ w.length) (out : List Bool) (M : ℕ) (hM : ∀ t, s.vec t ≤ M) :
    ∃ T ≤ 200 * (M + 1),
      emTM.tm.runFrom (⟨some (.em k c 0), ip w i hi, tapesOf s.vec, headsOf s.vec, out⟩ :
        Cfg 3 Bool St w) T =
        cfgS w ⟨.g, s.z + 1, 0, 0⟩ i hi (out ++ emitBits k c s.vec) := by
  set v := s.vec with hv
  obtain ⟨T₁, hT₁, pe, hpe, h₁⟩ := em_loop k c (ip w i hi) v M hM (prog k c) 0 (by decide) out
    (by simp)
  have hlen := length_prog_le k c
  -- one step onto counter `1`
  have h₂ : emTM.tm.runFrom (⟨some (.em k c pe), ip w i hi, tapesOf v, headsOf v,
      out ++ (prog k c).flatMap (exec v)⟩ : Cfg 3 Bool St w) 1 =
      ⟨some (.clW 1), ip w i hi, Function.update (tapesOf v) (1 : Fin 3) (ones (v 1)),
        Function.update (headsOf v) (1 : Fin 3) (((v 1 : ℕ) : ℤ) - 1),
        out ++ emitBits k c v⟩ := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    simp only [tr, hpe]
    rw [apply_act, moveInputPos_zero]
    simp only [wrT, Option.toList_none, List.append_nil, emitBits]
    congr 2
  set v₁ := Function.update v 1 0 with hv₁
  have h₃ : emTM.tm.runFrom (⟨some (.clW 1), ip w i hi,
      Function.update (tapesOf v) (1 : Fin 3) (ones (v 1)),
      Function.update (headsOf v) (1 : Fin 3) (((v 1 : ℕ) : ℤ) - 1),
      out ++ emitBits k c v⟩ : Cfg 3 Bool St w) (v 1 + 1) =
      ⟨some .clS2, ip w i hi, tapesOf v₁, headsOf v₁, out ++ emitBits k c v⟩ := by
    rw [clear_walk, tapesOf_update, headsOf_update_zero]
    rfl
  -- one step onto counter `2`
  have h₄ : emTM.tm.runFrom (⟨some .clS2, ip w i hi, tapesOf v₁, headsOf v₁,
      out ++ emitBits k c v⟩ : Cfg 3 Bool St w) 1 =
      ⟨some (.clW 2), ip w i hi, Function.update (tapesOf v₁) (2 : Fin 3) (ones (v 2)),
        Function.update (headsOf v₁) (2 : Fin 3) (((v 2 : ℕ) : ℤ) - 1),
        out ++ emitBits k c v⟩ := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    simp only [tr]
    rw [apply_act, moveInputPos_zero]
    simp only [wrT, Option.toList_none, List.append_nil]
    have h2 : v₁ 2 = v 2 := by simp [hv₁]
    congr 2
  set v₂ := Function.update v₁ 2 0 with hv₂
  have h₅ : emTM.tm.runFrom (⟨some (.clW 2), ip w i hi,
      Function.update (tapesOf v₁) (2 : Fin 3) (ones (v 2)),
      Function.update (headsOf v₁) (2 : Fin 3) (((v 2 : ℕ) : ℤ) - 1),
      out ++ emitBits k c v⟩ : Cfg 3 Bool St w) (v 2 + 1) =
      ⟨some .inc, ip w i hi, tapesOf v₂, headsOf v₂, out ++ emitBits k c v⟩ := by
    rw [clear_walk, tapesOf_update, headsOf_update_zero]
    rfl
  -- one step incrementing counter `0`
  have h₆ : emTM.tm.runFrom (⟨some .inc, ip w i hi, tapesOf v₂, headsOf v₂,
      out ++ emitBits k c v⟩ : Cfg 3 Bool St w) 1 =
      cfgS w ⟨.g, s.z + 1, 0, 0⟩ i hi (out ++ emitBits k c v) := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    simp only [tr]
    rw [apply_act, moveInputPos_zero]
    unfold cfgS
    refine Cfg.ext rfl rfl ?_ ?_ (by simp)
    · funext t
      fin_cases t
      · simp [tapesOf, wrT, headsOf, hv₂, hv₁, hv, ES.vec, update_ones_succ]
      · simp [tapesOf, hv₂, hv₁, ES.vec, ones_zero]
      · simp [tapesOf, hv₂, hv₁, ES.vec, ones_zero]
    · funext t
      fin_cases t <;> simp [headsOf, hv₂, hv₁, hv, ES.vec, SignType.cast]
  refine ⟨T₁ + 1 + (v 1 + 1) + 1 + (v 2 + 1) + 1, ?_, ?_⟩
  · have := hM 1; have := hM 2
    have : T₁ ≤ 56 * (2 * M + 3) := le_trans hT₁ (Nat.mul_le_mul_right _ hlen)
    omega
  · rw [show T₁ + 1 + (v 1 + 1) + 1 + (v 2 + 1) + 1 =
      T₁ + (1 + ((v 1 + 1) + (1 + ((v 2 + 1) + 1)))) by omega]
    rw [MultiTapeTM.runFrom_add, show (0 : Fin 64) = ⟨0, by decide⟩ from rfl, h₁,
      MultiTapeTM.runFrom_add, h₂, MultiTapeTM.runFrom_add, h₃, MultiTapeTM.runFrom_add, h₄,
      MultiTapeTM.runFrom_add, h₅, h₆, hv]

/-- **The main run**: from the configuration of an abstract state `s` with counters at
most `i`, reading the rest `l = w.drop i` of the input, the machine halts with the
abstract output `emRun s l` within `(|l| + 1) · 200 (|w| + 1)` steps.

**Proof sketch.** Induction on `l`.  At the end of the input the machine halts in one
step.  Otherwise one step reads the symbol and performs the action `lstep`: halting
(with at most one output bit), changing phase, incrementing a counter (one cell
written), or — at the end of a gate — the gate excursion (`gate_run`).  Counters grow
by at most one per input symbol, so they stay below the input position. -/
theorem em_main_run (w : List Bool) :
    ∀ (l : List Bool) (s : ES) (i : ℕ) (hi : i ≤ w.length) (out : List Bool),
      w.drop i = l → (∀ t, s.vec t ≤ i) →
      ∃ T ≤ (l.length + 1) * (200 * (w.length + 1)),
        (emTM.tm.runFrom (cfgS w s i hi out) T).state = none ∧
        (emTM.tm.runFrom (cfgS w s i hi out) T).output = out ++ emRun s l := by
  intro l
  induction l with
  | nil =>
    intro s i hi out hl _
    have hix : w[i]? = none := by
      have := congrArg List.length hl
      simp only [List.length_drop, List.length_nil] at this
      exact List.getElem?_eq_none (by omega)
    refine ⟨1, by nlinarith, ?_, ?_⟩ <;>
    · rw [rd_step, hix]
      simp [tr, lstep, cfgS, ctl, emRun]
  | cons b l ih =>
    intro s i hi out hl hv
    have hlt : i < w.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact List.cons_ne_nil _ _ hl.symm
    have hb : w[i]? = some b := by
      have := congrArg List.head? hl
      simpa [List.head?_drop] using this
    have hl' : w.drop (i + 1) = l := by
      have := congrArg List.tail hl
      simpa [List.tail_drop] using this
    have hB : 1 ≤ 200 * (w.length + 1) := by omega
    -- continuing from the configuration of the next abstract state
    have cont : ∀ (s' : ES) (pre : List Bool) (T₀ : ℕ), T₀ ≤ 200 * (w.length + 1) →
        (∀ t, s'.vec t ≤ i + 1) →
        emTM.tm.runFrom (cfgS w s i hi out) T₀ = cfgS w s' (i + 1) hlt (out ++ pre) →
        emRun s (b :: l) = pre ++ emRun s' l →
        ∃ T ≤ ((b :: l).length + 1) * (200 * (w.length + 1)),
          (emTM.tm.runFrom (cfgS w s i hi out) T).state = none ∧
          (emTM.tm.runFrom (cfgS w s i hi out) T).output = out ++ emRun s (b :: l) := by
      intro s' pre T₀ hT₀ hv' hrun hem
      obtain ⟨T, hT, h1, h2⟩ := ih s' (i + 1) hlt (out ++ pre) hl' hv'
      refine ⟨T₀ + T, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · rw [MultiTapeTM.runFrom_add, hrun, h1]
      · rw [MultiTapeTM.runFrom_add, hrun, h2, hem, List.append_assoc]
    cases hla : lstep s.φ (some b) with
    | halt o =>
      refine ⟨1, by simp only [List.length_cons]; nlinarith, ?_, ?_⟩ <;>
      · rw [rd_step, hb]
        simp only [tr, hla]
        unfold cfgS
        rw [apply_ctl]
        try simp [emRun, hla]
    | go φ' inc =>
      cases inc with
      | none =>
        refine cont ⟨φ', s.z, s.a, s.b⟩ [] 1 hB ?_ ?_ ?_
        · intro t; have := hv t; fin_cases t <;> simp only [ES.vec] at this ⊢ <;> omega
        · rw [rd_step, hb]
          simp only [tr, hla]
          unfold cfgS
          rw [apply_ctl, move_ip w i hlt]
          simp only [List.append_nil, Option.toList_none]
          have : (⟨φ', s.z, s.a, s.b⟩ : ES).vec = s.vec := by
            funext t; fin_cases t <;> rfl
          rw [this]
        · simp [emRun, hla]
      | some t =>
        refine cont (s.incTo φ' t) [] 1 hB ?_ ?_ ?_
        · intro t'
          rw [ES.vec_incTo]
          by_cases h : t' = t
          · subst h; simp; have := hv t'; omega
          · simp [h]; have := hv t'; omega
        · rw [rd_step, hb]
          simp only [tr, hla]
          unfold cfgS
          rw [apply_act, move_ip w i hlt]
          simp only [wrT, Option.toList_none, List.append_nil]
          have hφ : (s.incTo φ' t).φ = φ' := by fin_cases t <;> rfl
          rw [hφ, ES.vec_incTo, ← tapesOf_update, ← headsOf_update]
          congr 2
          · show Function.update (ones (s.vec t)) (s.vec t : ℤ) (some true) = _
            rw [update_ones_succ]
        · simp [emRun, hla]
    | gate k c =>
      obtain ⟨T₁, hT₁, h₁⟩ := gate_run w s k c (i + 1) hlt out i hv
      refine cont ⟨.g, s.z + 1, 0, 0⟩ (emitBits k c s.vec) (1 + T₁) (by nlinarith) ?_ ?_ ?_
      · intro t; have := hv 0; fin_cases t <;> simp only [ES.vec] at this ⊢ <;> omega
      · rw [MultiTapeTM.runFrom_add, rd_step, hb]
        simp only [tr, hla]
        unfold cfgS
        rw [apply_ctl, move_ip w i hlt]
        simpa using h₁
      · simp [emRun, hla]

/-- **The emitter machine computes `gateClauses`** within `200 · (n + 1)²` steps.

**Proof sketch.** The initial configuration is the configuration of the initial
abstract state (all counters `0`: blank tapes); conclude with `em_main_run` on the
whole input, the halted configuration being absorbing. -/
theorem emTM_computes :
    emTM.ComputesFunInTime gateClauses fun n => 200 * (n + 1) ^ 2 := by
  intro w
  have hinit : emTM.tm.initCfg w = cfgS w ⟨.n, 0, 0, 0⟩ 0 (by omega) [] := by
    simp only [MultiTapeTM.initCfg, Cfg.init, cfgS]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext t; fin_cases t <;> simp [tapesOf, ES.vec, ones_zero]
    · funext t; fin_cases t <;> simp [headsOf, ES.vec]
  obtain ⟨T, hT, h1, h2⟩ := em_main_run w w ⟨.n, 0, 0, 0⟩ 0 (by omega) [] (by simp)
    (by intro t; fin_cases t <;> simp [ES.vec])
  have hT' : T ≤ 200 * (w.length + 1) ^ 2 := by nlinarith
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ?_
  have he := emTM.tm.runFrom_add (emTM.tm.initCfg w) T (200 * (w.length + 1) ^ 2 - T)
  rw [Nat.add_sub_of_le hT', hinit, MultiTapeTM.runFrom_of_halt _ h1] at he
  rw [hinit, he]
  exact ⟨h1, by rw [h2]; rfl⟩

end Emitter

end CktSatReduction

end BoolCircuit
