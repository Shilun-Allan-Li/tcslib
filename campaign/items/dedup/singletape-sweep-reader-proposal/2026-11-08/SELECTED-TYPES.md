`Turing.FinTM.sweepRevCfg_state`

```lean
∀ {A S : Type} {x : List A} (q : Option S) (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A),
  (Turing.FinTM.sweepRevCfg q p z l r out).state = q
```

Universes: []. Axioms: [].

`Turing.FinTM.sweepRevCfg_output`

```lean
∀ {A S : Type} {x : List A} (q : Option S) (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A),
  (Turing.FinTM.sweepRevCfg q p z l r out).output = out
```

Universes: []. Axioms: [].

`Turing.FinTM.one_work_tape`

```lean
∀ {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : Turing.FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ),
  M.ComputesFunInTime f T → ∃ Γ' x x e M' c, M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2
```

Universes: []. Axioms: ["propext", "Quot.sound", "Classical.choice"].

`_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.dg_all_inputs`

```lean
∀ {Γ : Type} [inst : Fintype Γ] [inst_1 : DecidableEq Γ] (M : Turing.FinTM Γ),
  0 < M.k →
    ∀ (a₀ : Γ) (f : List Γ → List Γ) (T S : ℕ → ℕ),
      M.ComputesFunInTime f T →
        (∀ (y : List Γ) (t : ℕ), Turing.MultiTapeTM.spaceUsed (Turing.MultiTapeTM.initCfg y) t ≤ S y.length) →
          ∀ (x : List (Turing.FinTM.SweepAlphabet✝ Γ M.k)),
            (Turing.FinTM.dgTM✝ M a₀).ComputesInTime x
                (List.map (⇑(Turing.FinTM.sweepEmbed✝ Γ M.k)) (f (List.map (Turing.FinTM.dgRetract✝ a₀) x)))
                ((9 * M.k + 6) * (T x.length + 1) ^ 2) ∧
              ∀ (t : ℕ),
                Turing.MultiTapeTM.spaceUsed (Turing.MultiTapeTM.initCfg x) t ≤ (9 * M.k + 6) * (S x.length + 1)
```

Universes: []. Axioms: ["propext", "Quot.sound", "Classical.choice"].

