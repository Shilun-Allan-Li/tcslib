  let ι := iw_select j dst hjd
  refine ⟨CounterLoopState Bool, inferInstance, inferInstance,
    embedEmitTM ι iw_machine, .dec .run, .done, 6, ?_⟩
  intro z c p w hc hi hw
  let body : Cfg 1 Bool Bool z :=
    ⟨some false, c.inputPos, fun _ => c.workTapes dst,
      fun _ => c.workTapePos dst, c.output⟩
  let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
  have hp : p ≤ z.length := by have := c.inputPos.isLt; omega
  have hn : y.length = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p) := by
    simp only [y, List.length_take, List.length_drop]
  have hbound : p + y.length ≤ z.length := by
    have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
    omega
  have htake : (z.drop p).take y.length = y := by
    simpa only [y, List.length_take] using
      (List.take_eq_take_min (l := z.drop p) (i := Nat.ofDigits 2 (w.map Bool.toNat))).symm
  obtain ⟨T, hT, v, hv, hrun, hfirst⟩ :=
    iw_local body p rfl hi hp w (c.workTapes j) (c.workTapePos j) hw y.length hn
  let start := counterLoopCfg (some (.dec .run)) body (c.workTapes j) (c.workTapePos j)
  let finish := counterLoopCfg (some .done) (iw_prefix body p y.length hbound)
    (iw_patch (c.workTapes j) (c.workTapePos j) v) (c.workTapePos j)
  let out : Cfg k Bool (CounterLoopState Bool) z :=
    ⟨some .done, (iw_prefix body p y.length hbound).inputPos,
      Function.update (Function.update c.workTapes dst
        (iw_patch (c.workTapes dst) (c.workTapePos dst) y)) j
        (iw_patch (c.workTapes j) (c.workTapePos j) v),
      Function.update c.workTapePos dst (c.workTapePos dst + (y.length : ℤ)), c.output⟩
  have hstart : embedEmitCfg ι c.workTapes c.workTapePos [] start = c := by
    apply embedEmitCfg_eq
    · simpa only [start, counter_cfg_eq] using hc.symm
    · simp only [start, counter_cfg_eq, body]
    · simp only [start, counter_cfg_eq, body, List.nil_append]
    · intro i
      fin_cases i <;> simp [start, counter_cfg_eq, body, ι, iw_select]
    · intro i _
      exact ⟨rfl, rfl⟩
  have hend : embedEmitCfg ι c.workTapes c.workTapePos [] finish = out := by
    apply embedEmitCfg_eq
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, iw_prefix, body, out, List.nil_append]
    · intro i
      fin_cases i <;>
        simp [finish, counter_cfg_eq, out, iw_prefix, body, ι, iw_select, htake, hjd,
          Ne.symm hjd]
    · intro i hnone
      have hd : i ≠ dst := by
        intro he
        apply hnone
        exact ⟨0, by simp [ι, iw_select, he]⟩
      have hj : i ≠ j := by
        intro he
        apply hnone
        exact ⟨1, by simp [ι, iw_select, he]⟩
      simp [out, hd, hj]
  have hlift (u : ℕ) : (embedEmitTM ι iw_machine).runFrom c u =
      embedEmitCfg ι c.workTapes c.workTapePos [] (iw_machine.runFrom start u) := by
    calc
      _ = (embedEmitTM ι iw_machine).runFrom
          (embedEmitCfg ι c.workTapes c.workTapePos [] start) u :=
        congrArg (fun d => (embedEmitTM ι iw_machine).runFrom d u) hstart.symm
      _ = _ := embedEmitTM_runFrom ι iw_machine c.workTapes c.workTapePos [] start u
  have he : (embedEmitTM ι iw_machine).runFrom c T = out := by
    rw [hlift T, hrun]
    exact hend
  refine ⟨T, hT, v, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [he, out]
  · simp only [he, out, iw_prefix]
  · rw [he]
    simp only [out, iw_patch, hv]
  · simp only [he, out]
  · simp only [he, out]
  · intro u hu
    rw [hlift u, embedEmitCfg_state]
    exact hfirst u hu
