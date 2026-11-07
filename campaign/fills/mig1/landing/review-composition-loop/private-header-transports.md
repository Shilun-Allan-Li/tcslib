# Private header transport re-expressions

Both private results retain their mathematical content. The explicit let-view transports the branch machine by the approved `branchTM_k` and `branchTM_State` equations before using it in the fixed sum carrier. The old headers required implicit reduction of `branchTM` to type-check. Public headers and every executable definition are byte-preserved.

## Wrappers.timedReady_dispatch

Old complete header:

```lean
private lemma timedReady_dispatch (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    ({timedReadyCfg D M₁ M₂ c b with
        state := some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))), inputPos := 1} :
      Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x) =
      timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b
```

New complete header:

```lean
private lemma timedReady_dispatch (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    let V : MultiTapeTM (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) := by
      rw [← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b]
      exact (branchTM M₁ M₂ b).tm
    ({timedReadyCfg D M₁ M₂ c b with
        state := some (.inr (.inr (.inr V.q₀))), inputPos := 1} :
      Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x) =
      timedBranchCfg D M₁ M₂ (V.initCfg x) c.workTapes c.workTapePos b
```

## Wrappers.timed_ledger

Old complete header:

```lean
private lemma timed_ledger (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) u).workTapePos =
        timedHeads D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) v).workTapePos
          ((branchTM M₁ M₂ b).tm.runFrom ((branchTM M₁ M₂ b).tm.initCfg x) w).workTapePos z
```

New complete header:

```lean
private lemma timed_ledger (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    let V : MultiTapeTM (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) := by
      rw [← branchTM_k M₁ M₂ b, ← branchTM_State M₁ M₂ b]
      exact (branchTM M₁ M₂ b).tm
    ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) u).workTapePos =
        timedHeads D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) v).workTapePos
          (V.runFrom (V.initCfg x) w).workTapePos z
```

The actual fixed-false host table obligations were checked separately in `FixedFalse-v3` and `TimedFixedFalse-v1`; the full repaired conditional consumers and ledger also pass their strict source-region seals. No table-agreement hypothesis was added to a public theorem. Unchanged legacy helpers above remain opaque same-home dependencies; their bodies are not globally sealed.
