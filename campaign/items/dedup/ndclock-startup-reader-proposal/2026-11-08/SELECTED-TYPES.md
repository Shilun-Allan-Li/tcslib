`Turing.ClockHost.bootCfg_of_halt`

```lean
∀ {S : Turing.FinTM Bool} {A : Turing.FinNDTM Bool} {x : List Bool} (c : Turing.Cfg S.k Bool S.State x),
  c.state = none →
    Turing.ClockHost.bootCfg c =
      Turing.ClockHost.hostCfg (some Turing.ClockPhase.rew) c.inputPos c.workTapes c.workTapePos (fun x x_1 => none)
        (fun x => 0) (Turing.FinTM.bufferTape c.output) ↑c.output.length []
```

Universes: []. Axioms: ["propext", "Quot.sound"].

`Turing.ClockHost.runCfg_initCfg`

```lean
∀ {S : Turing.FinTM Bool} {A : Turing.FinNDTM Bool} {x : List Bool} (m : ℕ) (j : ℤ) (sT : Fin S.k → ℤ → Option Bool)
  (sP : Fin S.k → ℤ),
  Turing.ClockHost.runCfg m (Turing.NDTM.initCfg x) j sT sP =
    Turing.ClockHost.hostCfg (some (Turing.ClockPhase.run (some A.tm.q₀) none)) 1 sT sP (fun x x_1 => none) (fun x => 0)
      (Turing.ClockHost.yard m) j []
```

Universes: []. Axioms: ["propext", "Quot.sound"].

`Turing.ClockHost.startup`

```lean
∀ {S : Turing.FinTM Bool} {A : Turing.FinNDTM Bool} {loop : Bool} {x : List Bool} (m : ℕ) {T : ℕ},
  S.ComputesInTime x (List.replicate m true) T →
    x.length ≤ m →
      ∃ s₀ ≤ T + m + 2,
        ∃ sT sP,
          ∀ (w : List Bool),
            w.length = s₀ →
              Turing.NDTM.runWith w (Turing.NDTM.initCfg x) = Turing.ClockHost.runCfg m (Turing.NDTM.initCfg x) 0 sT sP
```

Universes: []. Axioms: ["propext", "Quot.sound", "Classical.choice"].

