<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanCopy_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of a Full Input Scan

**Claim.** Under the stated copying and halting transition rules, after $|x|+1$ steps from the scan configuration at position zero with state $q$ and output $o$, the machine is halted at position $|x|$ with output $o++x$.

**Proof.** First run the machine through the $|x|$ actual input bits. The partial-scan result (`Turing.FinTM.f2_scanCopy_run`) gives state $q$, scan position $|x|$, and output $o++x.take |x|$, which is $o++x$. The run successor law (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) expresses the additional step as one transition from this configuration. At position $|x|$, the scan-symbol result (`Turing.FinTM.f2_scanCfg_read`) identifies the input reading as the blank option. The assumed transition rule on a blank emits nothing and halts without moving the input head or changing the output. Hence the resulting configuration is the halted scan configuration at position $|x|$ with output $o++x$. Finally, configurations with zero work tapes are equal once their state, input position, and output agree (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.FinTM.f2_scanCopy_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_scanCfg_read`, `Turing.Cfg.ext_zero_tapes`.
