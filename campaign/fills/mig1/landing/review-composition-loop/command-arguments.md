# Inspected proof command arguments

This raw lexical index supports the source review; it is not a Lean parser. Public-reader applications, same-home definitions and local let views are distinguished during review. Core Fin index equalities in `show ... from rfl` supply equality proofs to `rw`; a Core definition is never passed directly to the rewriter. The generated rewind matcher is never named in the landing source.

## Composition.idTM_computes

```lean
rw MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_of_some hstate,
      Cfg.inputSymbol_of_end hpos
rw hrun1, Action.apply_state
rw hrun1, Action.apply_output, hout, List.take_length
```

## Composition.ifEqTM_computes

```lean
rw MultiTapeTM.initCfg_eq, Cfg.init_state
rw MultiTapeTM.initCfg_eq, Cfg.init_inputPos, Fin.val_one
rw MultiTapeTM.initCfg_eq, Cfg.init_output
```

## Composition.condTM_branch_run

```lean
rw ← branchTM_k M₁ M₂ tag, ← branchTM_State M₁ M₂ tag
rw ← branchTM_k M₁ M₂ tag, ← branchTM_State M₁ M₂ tag
change (condTM D M₁ M₂).tm.runFrom (rightCfg emb c tapes heads) t =
dsimp condTM, V, emb
simp branchTM_k, branchTM_State
```

## Composition.condTM_computes_iff

```lean
rw ← branchTM_k M₁ M₂ tag, ← branchTM_State M₁ M₂ tag
dsimp start, V
simpa branchTM_k, branchTM_State
rw MultiTapeTM.runFrom_add, hstart
rw hr t
simpa rightCfg_state, Option.map_eq_none_iff
simpa rightCfg_output
simpa start, V, branchTM_k, branchTM_State
simpa start, V, branchTM_k, branchTM_State
simpa start, V, branchTM_k, branchTM_State
simpa start, V, branchTM_k, branchTM_State
rw hr t
simpa rightCfg_state, Option.map_eq_none_iff
simpa rightCfg_output
```

## Wrappers.timedCondTM_computes

```lean
rw ← branchTM_k M₁ M₂ tag, ← branchTM_State M₁ M₂ tag
dsimp start, V
simpa branchTM_k, branchTM_State
dsimp V
simpa branchTM_k, branchTM_State
simpa start, V, branchTM_k, branchTM_State
simpa start, V, branchTM_k, branchTM_State
rw MultiTapeTM.runFrom_add, hstart', hr
simpa timedBranchCfg, leftCfg_state, rightCfg_state,
      Option.map_eq_none_iff
simpa timedBranchCfg, leftCfg_output, rightCfg_output
dsimp B
```

## Wrappers.timed_control_heads

```lean
simp timedControlCfg, captureCfg_workTapePos, leftCfg_workTapePos, timedHeads, j.isLt
simp timedControlCfg, captureCfg_workTapePos, leftCfg_output, timedHeads
```

## Wrappers.timed_branch_heads

```lean
simp timedBranchCfg, leftCfg_workTapePos, rightCfg_workTapePos, timedHeads,
      Fin.addCases_left
simp timedBranchCfg, leftCfg_workTapePos, timedHeads, Fin.addCases_right
```

## Wrappers.timedReadyCfg_workTapePos

```lean
rw ← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b
rw MultiTapeTM.initCfg_eq, Cfg.init_workTapePos
rw h0
dsimp timedReadyCfg, V
simpa branchTM_k, branchTM_State
```

## Wrappers.timedReady_dispatch

```lean
rw ← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b
simp branchTM_k, branchTM_State
simp timedBranchCfg, leftCfg_state, rightCfg_state, MultiTapeTM.initCfg_eq,
      Cfg.init_state, Option.map_some, id_eq
simp timedBranchCfg, leftCfg_inputPos, rightCfg_inputPos,
      MultiTapeTM.initCfg_eq, Cfg.init_inputPos
simp timedReadyCfg, branchTM_k, branchTM_State
simp timedReadyCfg, branchTM_k, branchTM_State
simp timedReadyCfg, branchTM_k, branchTM_State
```

## Wrappers.timed_read_heads

```lean
simpa ho
simp timedControlCfg, captureCfg_state, leftCfg_state, hs,
        Option.map_none, Option.getD_none
rw MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hstate
rw Action.apply_workTapePos, timed_control_heads
simp timedCondTM, timedHeads, j.isLt
simp timedCondTM, timedHeads, ho
rw timed_read D M₁ M₂ c b hs ho, timedReadyCfg_workTapePos
```

## Wrappers.timed_ledger

```lean
rw ← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b
rw ← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b
change ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
change (D.tm.runFrom (D.tm.initCfg x) d).state = none
rw hcfg
change (D.tm.runFrom (D.tm.initCfg x) d).output = [b]
rw hcfg
rw timed_control_init
dsimp timedCondTM, V
simp branchTM_k, branchTM_State
rw MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap d (le_refl _),
      timed_read D M₁ M₂ c b hs ho, hr
rw MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos
change (D.tm.runFrom (D.tm.initCfg x) u).output.length ≤ c.output.length at hp
rw ho
simp List.length_singleton
rw hcap u hu, timed_control_heads, h0
rw show u = d + (u - d) by omega, MultiTapeTM.runFrom_add, hcap d (le_refl _), h0
show u = d + (u - d) by omega, MultiTapeTM.runFrom_add, hcap d (le_refl _), h0]
rw show u = d + 2 + (u - (d + 2)) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_add, hcap d (le_refl _), timed_read D M₁ M₂ c b hs ho,
          hrheads _ (by omega), timedReadyCfg_workTapePos, h0
show u = d + 2 + (u - (d + 2)) by omega, MultiTapeTM.runFrom_add,
dsimp V
simpa branchTM_k, branchTM_State
rw show u = d + 2 + r + (u - (d + 2 + r)) by omega,
          MultiTapeTM.runFrom_add, hstart, hbranch, timed_branch_heads
show u = d + 2 + r + (u - (d + 2 + r)) by omega,
simp Nat.add_sub_cancel_left
```

## Wrappers.timedCondTM_spaceUsed

```lean
rw ← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b
dsimp M, V
simpa branchTM_k, branchTM_State
rw MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card
change _ = ((timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
rw he
rw show (Fin.castAdd (M₁.k + M₂.k) i).castSucc =
      Fin.castAdd 1 (Fin.castAdd (M₁.k + M₂.k) i) from rfl
show (Fin.castAdd (M₁.k + M₂.k) i).castSucc =
simp timedHeads, Fin.addCases_left
rw MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card
change _ = timedHeads D M₁ M₂ _ (V.runFrom (V.initCfg x) w).workTapePos z at he
change _ = ((timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
rw he
rw show (Fin.natAdd D.k i).castSucc = Fin.castAdd 1 (Fin.natAdd D.k i) from rfl
show (Fin.natAdd D.k i).castSucc = Fin.castAdd 1 (Fin.natAdd D.k i) from rfl]
simp timedHeads, Fin.addCases_left, Fin.addCases_right
rw MultiTapeTM.spaceUsedByTape_eq_card
change ((timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _ ∈ _
rw he
rw show Fin.last (D.k + (M₁.k + M₂.k)) =
        Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1) from rfl
show Fin.last (D.k + (M₁.k + M₂.k)) =
simpa timedHeads, Fin.addCases_right
rw MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum
change (∑ i : Fin ((D.k + (M₁.k + M₂.k)) + 1), M.tm.spaceUsedByTape (M.tm.initCfg x) t i) ≤ _
rw Fin.sum_univ_add, Fin.sum_univ_add
simp Fintype.sum_unique
```

## Loop.loop_first_halt

```lean
rw he
rw hz, MultiTapeTM.runFrom_zero
```

## Loop.loopHost_prepare

```lean
rw MultiTapeTM.initCfg_eq, Cfg.init_state
dsimp c
rw hue
rw loopHost_init, loopFuel_init
rw loopHost_fuel_capture
rw loopFuel_run
rw loopFuel_run
change (loopFuelCfg body F (F.tm.runFrom (F.tm.initCfg x) v)).state ≠ none
simpa loopFuelCfg, rightCfg_state, Option.map_id
rw loopFuelCaptured_frame body F c hc
rw ho
rw MultiTapeTM.initCfg_eq, Cfg.init_inputPos
change (F.tm.runFrom (F.tm.initCfg x) u).inputPos.val ≤ 1 + u
rw MultiTapeTM.initCfg_eq
simpa Fin.val_one, Nat.add_comm
change v ≤ c.inputPos.val + 2 at hv
rw MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew
rw MultiTapeTM.initCfg_eq, Cfg.init_workTapePos
rw h0
change -(T x.length : ℤ) ≤ (F.tm.runFrom (F.tm.initCfg x) u).workTapePos i ∧
```

## Loop.loopCall_heads

```lean
simp loopCall, captureCfg_workTapePos, loopBodyPadded, leftCfg_output, loopBodyCfg, Cfg.ofWords_workTapePos,
      Cfg.ofWords_output
simp loopCall, captureCfg_workTapePos, Fin.coe_castSucc, dif_pos j.isLt
change -(B : ℤ) ≤ (loopBodyPadded body F anchor
simp loopBodyPadded, leftCfg_workTapePos
simp Fin.addCases_left, loopBodyCfg, Cfg.ofWords_workTapePos
simp Fin.addCases_right
simp Fin.addCases_left
simpa Fin.addCases_right
```

## Loop.loopHost_contracts

```lean
dsimp words
rw loopDebit_iterate_length
rw loopDebit_success
dsimp words
rw loopDebit_iterate_value _ _ hi
change v ≤ 10 * (T x.length + 1)
simpa candidate, words, orbit, Function.iterate_succ_apply', hsuccess i hi
simpa time, dif_pos hi
dsimp terminal
simpa ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl
dsimp terminal
change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
rw hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      loopHost_start body F anchor false findMode (s0 x) btime fuel hbguard hbend
simp candidate, words, orbit, Function.iterate_zero_apply, hfo
rw hcfg i hi
simp candidate, loopCall, captureCfg_output
simpa cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)
simpa cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)
rw hcfg i hi
change (if acceptF x (orbit i) then _ else _)
simp ha, if_true
simpa orbit
simp ha, Bool.false_eq_true, ↓reduceIte
rw hcfg (i + 1) (by omega)
simpa if_pos hlt
rw show cfg (R x.length + 1) = terminal from if_neg (by omega)
show cfg (R x.length + 1) = terminal from if_neg (by omega)]
simp terminal, ha, Bool.false_eq_true, ↓reduceIte
rw hcfg i hi
rw show cfg (R x.length + 1) = terminal from if_neg (by omega)
show cfg (R x.length + 1) = terminal from if_neg (by omega)]
```

## Loop.segment_heads

```lean
rw MultiTapeTM.runFrom_of_halt _ hend
rw show t = u + (t - u) by omega, MultiTapeTM.runFrom_add
show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
rw MultiTapeTM.runFrom_of_halt _ he
rw he
```

## Loop.seamed_space

```lean
rw MultiTapeTM.initCfg_eq, Cfg.init_workTapePos
rw h0, sub_zero, abs_le
rw h0, zero_sub, zero_add
rw show u = startup + (u - startup) by omega, MultiTapeTM.runFrom_add, hinit
show u = startup + (u - startup) by omega, MultiTapeTM.runFrom_add, hinit]
```

## Loop.loopHostTM_decides

```lean
rw hinit
rw hrun
rw hrun
rw Nat.mul_comm (R x.length + 1)
simp Nat.mul_add, Nat.mul_one, Nat.mul_two
```

## Loop.loopHostTM_finds

```lean
rw hinit
rw hrun
rw hrun
rw Nat.mul_comm (R x.length + 1)
simp Nat.mul_add, Nat.mul_one, Nat.mul_two
```

## Loop.loopHostTM_spaceUsed_le_budget

```lean
rw Nat.mul_assoc, Nat.mul_left_comm
```

## Loop.emCall_pair_not_mem

```lean
change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
simp emCall_triple_inverse, emCall_triple_pair
```

## Loop.emCall_triple_not_mem

```lean
change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
simp emCall_triple_inverse, emCall_triple_other, if_neg hji
```

## Loop.emCall_bank_initial

```lean
simp emCallEmbeddedCfg, Cfg.mapState_state, embedEmitCfg_state,
      emCallClearCfg, emCallBankFrame, emCallFrame, Option.map_some
simp emCallEmbeddedCfg, Cfg.mapState_inputPos, embedEmitCfg_inputPos,
      emCallClearCfg, emCallBankFrame, emCallFrame
simp emCallEmbeddedCfg
rw Cfg.mapState_workTapes
change (embedEmitCfg _ _ _ [] _).workTapes ((emCallTripleEmbedding M i) r) = _
rw embedEmitCfg_selected_tape
simp emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg
simp emCallEmbeddedCfg, Cfg.mapState_workTapePos
change (embedEmitCfg _ _ _ [] _).workTapePos ((emCallTripleEmbedding M i) r) = _
rw embedEmitCfg_selected_pos
simp emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg
simp emCallEmbeddedCfg, Cfg.mapState_output, embedEmitCfg_output,
      emCallClearCfg, emCallBankFrame, emCallFrame, List.nil_append
```

## Loop.emCall_bank_final

```lean
simp emCallEmbeddedCfg, Cfg.mapState_state, embedEmitCfg_state,
      emCallClearCfg, emCallBankFrame, emCallFrame, Option.map_some
simp emCallEmbeddedCfg, Cfg.mapState_inputPos, embedEmitCfg_inputPos,
      emCallClearCfg, emCallBankFrame, emCallFrame
simp emCallEmbeddedCfg
rw Cfg.mapState_workTapes
simp emCallBankFrame, emCallFrame, emCall_layout_pair
simp emCallBankFrame, emCallFrame, emCall_layout_pair
change (embedEmitCfg _ _ _ [] _).workTapes ((emCallTripleEmbedding M i) r) = _
rw embedEmitCfg_selected_tape
simp emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg
simp emCallBankFrame, emCallFrame, emCall_layout_triple, hiff
simp emCallEmbeddedCfg, Cfg.mapState_workTapePos
simp emCallBankFrame, emCallFrame, emCall_layout_pair
simp emCallBankFrame, emCallFrame, emCall_layout_pair
change (embedEmitCfg _ _ _ [] _).workTapePos ((emCallTripleEmbedding M i) r) = _
rw embedEmitCfg_selected_pos
simp emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg
simp emCallBankFrame, emCallFrame, emCall_layout_triple, hiff
simp emCallEmbeddedCfg, Cfg.mapState_output, embedEmitCfg_output,
      emCallClearCfg, emCallBankFrame, emCallFrame, List.nil_append
```

## Loop.emitLoopTM_computes

```lean
dsimp words
rw loopDebit_iterate_length
rw loopDebit_success
dsimp words
rw loopDebit_iterate_value _ _ hi
simpa E, candidate, words, orbit, Function.iterate_succ_apply',
        hsuccess i (by omega), Nat.add_lt_add_iff_right
dsimp startup
rw MultiTapeTM.runFrom_add, hprepare,
      loopHost_start body F anchor true true (s0 x) btime fuel hbguard hbend
simp candidate, words, orbit, Function.iterate_zero_apply, hfo
simp candidate, loopCall, captureCfg_output
simp candidate, loopCall, captureCfg_output
rw hclean
rw hinit
rw hrun
rw hrun
simpa List.nil_append, orbit
rw Nat.mul_comm (R x.length + 1)
simp Nat.mul_add, Nat.mul_one, Nat.mul_two
```
