`Turing.MultiTapeTM.ConfigCount.core_eq`

```lean
∀ {k : ℕ} {S : Type} {x : List Bool} (c : Turing.Cfg k Bool S x),
  Turing.MultiTapeTM.ConfigCount.core c = (c.state, c.inputPos, c.workTapes, c.workTapePos)
```

Universes: []. Axioms: [].

`Complexity.LogProg.runFrom_count_eq`

```lean
∀ {K : ℕ} {St : Type} {x : List Bool} [inst : Fintype St] (tm : Turing.MultiTapeTM (K + 1) Bool St) (B P T : ℕ),
  (∀ (q : St) (a : Option Bool) (w : Fin (K + 1) → Option Bool),
      ((tm.tr q a w).workTapes (Fin.last K)).1 = none ∨ ((tm.tr q a w).workTapes (Fin.last K)).1 = some (some true)) →
    (Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) T).state = none →
      (∀ t ≤ T,
          (∀ (i : Fin K), |(Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) t).workTapePos i.castSucc| ≤ ↑B) ∧
            |(Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) t).workTapePos (Fin.last K)| ≤ ↑P) →
        Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x)
            ((Fintype.card St + 1) * (x.length + 2) * 3 ^ (K * (2 * B + 1)) * (2 * B + 1) ^ K *
              ((2 * P + 1) * (2 * P + 2))) =
          Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) T
```

Universes: []. Axioms: ["propext", "Quot.sound", "Classical.choice"].

