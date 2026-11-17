
/-- **The anchor's dispatch, for the typed view** (`host_dispatch` for
`Turing.ModuleHost.hostTMView`): from the seam at `inl 0` holding `w`, one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the seam at the
verdict module's entry holding `w`,
`H.tm.step (Cfg.ofWords (inl 0) (stateWord (K + 1) w)) =
Cfg.ofWords (entry M 2) (stateWord (K + 1) w)`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_dispatch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 0 (Cfg.ofWords_state _ _), hostCtrl_eq,
    if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero, Cfg.ofWords_def, Cfg.ofWords_def]

/-- **The branch, for the typed view** (`host_branch` for `Turing.ModuleHost.hostTMView`): the
branch state reads the first cell of tape 0, the verdict `b` of a word `w` with `w[0]? = some b`,
and one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` dispatches into the payload
module (`b` true) or the step module (`b` false) at the seam holding `w`,
`H.tm.step (Cfg.ofWords (inl 1) (stateWord (K + 1) w)) =
Cfg.ofWords (entry M (if b then 4 else 3)) (stateWord (K + 1) w)`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_branch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp only [Cfg.workTapeSymbols_eq, Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos,
      stateWord_eq, FinTM.bufferTape_eq]
    simpa using hw
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _ _ 1 (Cfg.ofWords_state _ _), hostCtrl_eq,
    if_neg (by decide), if_pos rfl, hread, FinTM.controlAction_apply, moveInputPos_zero,
    Cfg.ofWords_def, Cfg.ofWords_def]
  cases b <;> rfl

/-- **The halt, for the typed view** (`host_halt` for `Turing.ModuleHost.hostTMView`): from the
seam at `inl 2` holding `w` with output `o`, one step of the typed view
`H = hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)` reaches the same seam with
control `none` and output `o`,
`H.tm.step {Cfg.ofWords (inl 2) (stateWord (K + 1) w) with output := o} =
{Cfg.ofWords (inl 2) (stateWord (K + 1) w) with state := none, output := o}`.
Framework glue, no textbook counterpart (the host's control table). -/
theorem host_halt_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  rw [ModuleHost.hostTMView_step_inl _ _ _ _ _ _
    ({Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} :
      Cfg (K + 1) Bool (ModuleHost.State (Fin 3) M) x) 2
    (Cfg.ofWords_state (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)),
    hostCtrl_eq, if_neg (by decide), if_neg (by decide),
    FinTM.controlAction_apply, moveInputPos_zero]
