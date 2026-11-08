<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanTrues_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a Run of Ones

**Claim.** If the first $j$ entries of $x$ are all true, then after $j$ steps the machine is in state $q$ at position $j$, with $j$ false outputs when `emit` is true and empty output otherwise.

**Proof.** Induct on $j$. The claim at zero steps holds because the initial output is empty. For the successor case, the hypothesis that the first $j+1$ entries are true implies both that the first $j$ entries are true and that the next scanned symbol is true. The induction hypothesis identifies the configuration after $j$ steps. Its next transition therefore uses the assumed transition on `true`: it moves right, returns to $q$, and emits false exactly when `emit` is true. The scan-reading identity (`scanCfg_read`) identifies the symbol, and the right-move fact (`moveInputPos_pos_of_ne_right`) advances the position. When a false symbol is emitted, it is appended to the previous list of false outputs, making a list of $j+1$ false entries; otherwise the output remains empty. Equality of the resulting state, position, and output gives equality of configurations (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
