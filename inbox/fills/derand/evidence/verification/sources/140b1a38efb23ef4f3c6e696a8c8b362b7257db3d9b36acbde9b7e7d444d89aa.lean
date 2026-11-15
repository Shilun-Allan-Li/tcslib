/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.Randomized.BPLInPCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded PTMs through configuration codes

The register-machine form of error reduction in logarithmic space [AB09, §7.7, p. 139] keeps
the configuration of the repeated PTM `N` as a code (`Complexity.Codec.cfgCode`) in a register
and moves it along the step pairs of `Complexity.Codec.stepLang N`. This file supplies the
facts about `N` that the simulation needs: a space-bounded PTM that halts on every branch
halts within the number `2 ^ (codeK N · (S + logSpace |x| + 1))` of codes (a branch repeating a
code could be pumped forever), its reachable configurations are coded, their two successors are
exactly the step partners of their code, and the probability of acceptance after `j` coins,
`Randomized.PolyAmp.accP`, averages over the two successors.

## Main definitions

* `Randomized.PolyAmp.codeBound` — the bound `2 ^ (codeK N · (S + logSpace |x| + 1))` on codes.
* `Randomized.PolyAmp.Accepting`, `Randomized.PolyAmp.accP` — acceptance and its probability
  after `j` coins.

## Main results

* `Randomized.PolyAmp.haltsWithin_codeBound` — halting within the code bound.
* `Randomized.PolyAmp.accP_succ` — the one-step recursion of `accP`.
* `Randomized.PolyAmp.mem_stepLang_iff` — the step partners of a reachable code.
* `Randomized.PolyAmp.mem_acceptLang_iff`, `Randomized.PolyAmp.mem_initLang_iff`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.PolyAmp

open Turing Complexity Complexity.Codec

variable {N : FinNDTM Bool} {x : List Bool}

/-- The bound `2 ^ (codeK N · (S + logSpace |x| + 1))` on the codes at radius `S`. -/
def codeBound (N : FinNDTM Bool) (n S : ℕ) : ℕ := 2 ^ (codeK N * (S + logSpace n + 1))

/-- A configuration is accepting: halted with output `[true]`. -/
def Accepting (C : Cfg N.k Bool N.State x) : Prop := C.state = none ∧ C.output = [true]

instance (C : Cfg N.k Bool N.State x) : Decidable (Accepting C) := by
  unfold Accepting; infer_instance

/-- The probability that `j` coins drive `N` from `C` to an accepting configuration. -/
noncomputable def accP (C : Cfg N.k Bool N.State x) (j : ℕ) : ℚ :=
  randProb j fun w => Accepting (N.tm.runWith w C)

/-- Acceptance depends only on the configuration-graph vertex. -/
theorem accepting_congr {C D : Cfg N.k Bool N.State x} (h : NDTM.coreSum C = NDTM.coreSum D) :
    Accepting C ↔ Accepting D := by
  have hs : C.state = D.state := by
    have := congrArg (fun z => z.1.1) h
    simpa [NDTM.coreSum, MultiTapeTM.ConfigCount.core] using this
  have ho : outSummary C.output = outSummary D.output := congrArg Prod.snd h
  unfold Accepting
  rw [hs, ← outSummary_eq_accept_iff, ← outSummary_eq_accept_iff, ho]

/-- `accP` depends only on the configuration-graph vertex. -/
theorem accP_congr {C D : Cfg N.k Bool N.State x} (h : NDTM.coreSum C = NDTM.coreSum D)
    (j : ℕ) : accP C j = accP D j :=
  randProb_congr fun _ => accepting_congr (NDTM.coreSum_runWith _ _ h)

/-- With no coin left, `accP` is the indicator of acceptance. -/
theorem accP_zero (C : Cfg N.k Bool N.State x) : accP C 0 = if Accepting C then 1 else 0 := by
  unfold accP
  rw [← randProb_const 0 (Accepting C)]
  exact randProb_congr fun r => by simp [List.ofFn_zero]

/-- **One coin**: `accP` averages over the two successors. -/
theorem accP_succ (C : Cfg N.k Bool N.State x) (j : ℕ) :
    accP C (j + 1) = (accP (N.tm.stepWith true C) j + accP (N.tm.stepWith false C) j) / 2 := by
  unfold accP
  rw [randProb_succ]
  rfl

/-- After the halting time, `accP` from the start is the probability of output `[true]`. -/
theorem accP_init {T : ℕ} (hT : N.tm.HaltsWithin x T) :
    accP (N.tm.initCfg x) T = N.outputProb x T [true] :=
  randProb_congr fun r => by
    simp only [Accepting, FinNDTM.outputWith, hT _ (List.length_ofFn), true_and]

/-! ### Halting within the code bound -/

/-- **A space-bounded PTM that halts halts within the code bound** [AB09, §4.1.1]: the code
form of `Randomized.BPLInP.haltsWithin_of_codes`. -/
theorem haltsWithin_codeBound {sp : ℕ → ℕ} {S T : ℕ} (hN : N.UsesSpace sp)
    (hs : sp x.length ≤ S) (hT : N.tm.HaltsWithin x T) :
    N.tm.HaltsWithin x (codeBound N x.length S) :=
  BPLInP.haltsWithin_of_codes hN hs le_rfl hT

/-! ### The code languages on reachable configurations -/

/-- A configuration is *reachable*: its vertex is that of some branch from the start. -/
def Reach (C : Cfg N.k Bool N.State x) : Prop :=
  ∃ u : List Bool, NDTM.coreSum (N.tm.runWith u (N.tm.initCfg x)) = NDTM.coreSum C

/-- The start is reachable. -/
theorem reach_init : Reach (N.tm.initCfg x) := ⟨[], rfl⟩

/-- A successor of a reachable configuration is reachable. -/
theorem Reach.step {C : Cfg N.k Bool N.State x} (h : Reach C) (b : Bool) :
    Reach (N.tm.stepWith b C) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u ++ [b], ?_⟩
  rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
  exact NDTM.coreSum_stepWith _ b hu

/-- Reachable configurations are in the window. -/
theorem Reach.inWin {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (h : Reach C) : ∃ D, Cfg.InWindow S D ∧
      NDTM.coreSum D = NDTM.coreSum C ∧ cfgCode S D = cfgCode S C := by
  obtain ⟨u, hu⟩ := h
  exact ⟨_, BPLInP.inWin_run hN hs u, hu, by rw [cfgCode, cfgWord_congr hu]; rfl⟩

/-- **The initial code**: `c` is the initial code iff it is the code of the start. -/
theorem mem_initLang_iff (S c : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits S)) ∈ initLang N ↔
      c = cfgCode S (N.tm.initCfg x) := by
  rw [mem_initLang]; exact eq_comm

/-- **The accepting codes**: the code of a reachable configuration is accepting iff the
configuration is. -/
theorem mem_acceptLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) :
    pairEncode x (pairEncode (Nat.bits (cfgCode S C)) (Nat.bits S)) ∈ acceptLang N ↔
      Accepting C := by
  obtain ⟨D, hD, hDC, hcD⟩ := hC.inWin hN hs
  rw [mem_acceptLang]
  constructor
  · rintro ⟨E, hE, hcE, hst, hout⟩
    have h := BPLInP.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)
    exact (accepting_congr (h.trans hDC)).mp ⟨hst, hout⟩
  · intro h
    exact ⟨D, hD, hcD, (accepting_congr hDC).mpr h⟩

/-- **The step partners of a reachable code** are the codes of its two successors. -/
theorem mem_stepLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) (c' : ℕ) :
    pairEncode x (pairEncode (Nat.bits (cfgCode S C)) (pairEncode (Nat.bits c') (Nat.bits S))) ∈
        stepLang N ↔ ∃ b, c' = cfgCode S (N.tm.stepWith b C) := by
  obtain ⟨u, hDC⟩ := hC
  set D := N.tm.runWith u (N.tm.initCfg x)
  have hD : Cfg.InWindow S D := BPLInP.inWin_run hN hs u
  have hcD : cfgCode S D = cfgCode S C := by rw [cfgCode, cfgWord_congr hDC]; rfl
  rw [mem_stepLang]
  constructor
  · rintro ⟨E, hE, hcE, E', ⟨b, rfl⟩, -, rfl⟩
    have h := (BPLInP.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)).trans hDC
    refine ⟨b, ?_⟩
    rw [cfgCode, cfgWord_congr (NDTM.coreSum_stepWith _ b h)]
    rfl
  · rintro ⟨b, rfl⟩
    refine ⟨D, hD, hcD, N.tm.stepWith b D, ⟨b, rfl⟩, ?_, ?_⟩
    · have := BPLInP.inWin_run hN hs (u ++ [b])
      rwa [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil] at this
    · rw [cfgCode, cfgWord_congr (NDTM.coreSum_stepWith _ b hDC)]
      rfl

/-- The successor codes are below the code bound. -/
theorem cfgCode_lt_codeBound (S : ℕ) (C : Cfg N.k Bool N.State x) :
    cfgCode S C < codeBound N x.length S := cfgCode_lt S C

end Randomized.PolyAmp
