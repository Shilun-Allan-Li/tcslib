import TCSlib.Complexity.Randomized.Build.IterateFind

set_option maxHeartbeats 0
set_option autoImplicit false

open Turing Complexity.IterateFind

-- Prototype readers. They are proved before the experimental mask and would
-- belong beside the machine constructors, not in a consumer, if used in source.
theorem probe_copy_shape : ∃ tm : MultiTapeTM 1 Bool (Fin 2),
    copyTM = { k := 1, State := Fin 2, tm := tm } := ⟨_, rfl⟩

theorem probe_host_shape {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M) :
    ∃ tm : MultiTapeTM K Bool (ModuleHost.State C M),
      ModuleHost.hostTM M K hk ctrl ret q₀ = { k := K, State := ModuleHost.State C M, tm := tm } :=
  ⟨_, rfl⟩

attribute [local irreducible] copyTM ModuleHost.hostTM

example (x : List Bool) : ∃ tm : MultiTapeTM 1 Bool (Fin 2),
    ∀ t < 2 * x.length + 2,
      (tm.runFrom (Cfg.ofWords (input := x) 0 (stateWord 1 [])) t).state ≠ some 0 := by
  obtain ⟨tm, htm⟩ := probe_copy_shape
  refine ⟨tm, ?_⟩
  have h := (copy_clean x).1
  rw [htm] at h
  exact h

example {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M)
    (x : List Bool) (c : C) (w : Fin K → List Bool) :
    ∃ tm : MultiTapeTM K Bool (ModuleHost.State C M),
      tm.step (Cfg.ofWords (input := x) (.inl c) w) =
        (ctrl c (Cfg.ofWords (input := x) (.inl c) w).inputSymbol
          (Cfg.ofWords (input := x) (.inl c) w).workTapeSymbols).apply
            (Cfg.ofWords (input := x) (.inl c) w) := by
  obtain ⟨tm, htm⟩ := probe_host_shape M K hk ctrl ret q₀
  refine ⟨tm, ?_⟩
  have h := ModuleHost.hostTM_step_inl M K hk ctrl ret q₀
    (Cfg.ofWords (input := x) (.inl c) w) c (by rw [Cfg.ofWords_state])
  rw [htm] at h
  exact h
