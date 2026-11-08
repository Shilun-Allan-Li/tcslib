<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanCopy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output During a Partial Input Scan

**Claim.** Under the stated copying and halting transition rules, for every Boolean word $x$, output word $o$, and $j\le|x|$, after $j$ steps from the scan configuration at position zero with state $q$, the machine is at position $j$ in state $q$ with output $o++x.take j$.

**Proof.** Induct on $j$. At zero steps, the configuration has its prescribed initial state, position, and output, and the prefix of length zero is empty. For the successor step, the bound $j+1\le|x|$ ensures that the $j$th input bit exists. By the successor run law (`Turing.MultiTapeTM.runFrom_succ_eq_step'`), the next configuration is one transition from the inductive configuration. The input-symbol scan fact (`Turing.FinTM.f2_scanCfg_read`) says this transition reads $x[j]$, and the assumed rule copies that bit to the output, moves right, and remains in state $q$. The head-position fact (`Turing.moveInputPos_pos_of_ne_right`) gives the new scan position $j+1$, since this step is before the right boundary. The output becomes $(o++x.take j)++[x[j]]=o++x.take(j+1)$, using the list-prefix successor identity. With no work tapes, equality of state, input position, and output determines equality of configurations (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
