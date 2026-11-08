# Exact private-header transport proposal

Pending user approval. These are literal private header changes, with both full opaque-header/body seals and transparent complete-type equality probes passing. Mathematical statements are preserved by kernel-checked equality of their complete forall types.

`TCSlib/Complexity/TuringMachine/Build/Wrappers.lean` — `timed_start`

Original:

```lean
private lemma timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) a =
        timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
```

Proposed:

```lean
private lemma timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) a =
        timedBranchCfg D M₁ M₂ (show Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x from by
          simpa only [branchTM_k, branchTM_State] using ((branchTM M₁ M₂ b).tm.initCfg x)) tapes heads b := by
```

Equality input: `evidence/project/HeaderEquivalence_Wrappers_v4.lean.txt`; complete raw result: `evidence/runs/HeaderEquivalence-Wrappers-v4.out`.

`TCSlib/Complexity/TuringMachine/Composition.lean` — `condTM_start`

Original:

```lean
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
```

Proposed:

```lean
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) (show Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x from by
          simpa only [branchTM_k, branchTM_State] using ((branchTM M₁ M₂ b).tm.initCfg x)) tapes heads := by
```

Equality input: `evidence/project/HeaderEquivalence_Composition_v4.lean.txt`; complete raw result: `evidence/runs/HeaderEquivalence-Composition-v4.out`.

