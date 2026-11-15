import TCSlib.Complexity.Randomized.Build.IterateFind

set_option maxHeartbeats 0
set_option autoImplicit false

open Turing Complexity.IterateFind

-- Experimental reader contracts, proved before the mask. Final readers would
-- be proved in the constructors' defining files, never in this consumer.
theorem probe_copy_raw : ∃ tm : MultiTapeTM 1 Bool (Fin 2),
    tm.q₀ = 0 ∧
    (∀ {x : List Bool} (cfg : Cfg 1 Bool (Fin 2) x), tm.step cfg = copyTM.tm.step cfg) ∧
    (∀ {x : List Bool} (cfg : Cfg 1 Bool (Fin 2) x) (t : ℕ),
      tm.runFrom cfg t = copyTM.tm.runFrom cfg t) := ⟨_, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem probe_host_raw {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M) :
    ∃ tm : MultiTapeTM K Bool (ModuleHost.State C M), tm.q₀ = q₀ ∧
      (∀ {x : List Bool} (cfg : Cfg K Bool (ModuleHost.State C M) x),
        tm.step cfg = (ModuleHost.hostTM M K hk ctrl ret q₀).tm.step cfg) ∧
      (∀ {x : List Bool} (cfg : Cfg K Bool (ModuleHost.State C M) x) (t : ℕ),
        tm.runFrom cfg t = (ModuleHost.hostTM M K hk ctrl ret q₀).tm.runFrom cfg t) :=
  ⟨_, rfl, fun _ => rfl, fun _ _ => rfl⟩

attribute [local irreducible] copyTM ModuleHost.hostTM

example (x : List Bool) : ∃ tm : MultiTapeTM 1 Bool (Fin 2),
    ∀ t < 2 * x.length + 2,
      ¬(tm.runFrom (Cfg.ofWords (input := x) 0 (stateWord 1 [])) t).Halted := by
  obtain ⟨tm, hq, hs, hr⟩ := probe_copy_raw
  refine ⟨tm, ?_⟩
  have h := (copy_clean x).1
  simp_rw [← hr] at h
  exact h

example {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M)
    (x : List Bool) (c : C) (w : Fin K → List Bool) :
    ∃ tm : MultiTapeTM K Bool (ModuleHost.State C M),
      ∀ cfg : Cfg K Bool (ModuleHost.State C M) x, cfg.state = some (.inl c) →
        tm.step cfg = (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  obtain ⟨tm, hq, hs, hr⟩ := probe_host_raw M K hk ctrl ret q₀
  refine ⟨tm, ?_⟩
  intro cfg hcfg
  rw [hs]
  exact ModuleHost.hostTM_step_inl M K hk ctrl ret q₀ cfg c hcfg
