import TCSlib.Complexity.Randomized.Build.IterateFind

set_option maxHeartbeats 0
set_option autoImplicit false

open Turing Complexity.IterateFind

-- Experimental type-stabilized views and readers. A source contribution would
-- put each beside its constructor; this file tests the consumer after masking.
abbrev probe_copy_view : FinTM Bool where
  k := 1
  State := Fin 2
  tm := copyTM.tm

theorem probe_copy_view_eq : probe_copy_view = copyTM := rfl

theorem probe_copy_view_clean (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(probe_copy_view.tm.runFrom (Cfg.ofWords (input := x) 0 (stateWord 1 [])) v).Halted) ∧
    probe_copy_view.tm.runFrom (Cfg.ofWords (input := x) 0 (stateWord 1 []))
      (2 * x.length + 2) =
        {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} :=
  copy_clean x

abbrev probe_host_view {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M) : FinTM Bool where
  k := K
  State := ModuleHost.State C M
  tm := (ModuleHost.hostTM M K hk ctrl ret q₀).tm

theorem probe_host_view_step {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M) {x : List Bool}
    (cfg : Cfg K Bool (ModuleHost.State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (probe_host_view M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  ModuleHost.hostTM_step_inl M K hk ctrl ret q₀ cfg c hc

attribute [local irreducible] copyTM ModuleHost.hostTM

example (x : List Bool) :
    ∀ t < 2 * x.length + 2,
      ¬(probe_copy_view.tm.runFrom (Cfg.ofWords (input := x) 0 (stateWord 1 [])) t).Halted :=
  (probe_copy_view_clean x).1

example {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (ModuleHost.State C M))
    (ret : Fin n → ModuleHost.State C M) (q₀ : ModuleHost.State C M)
    {x : List Bool} (cfg : Cfg K Bool (ModuleHost.State C M) x)
    (c : C) (hc : cfg.state = some (.inl c)) :
    (probe_host_view M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  probe_host_view_step M K hk ctrl ret q₀ cfg c hc
