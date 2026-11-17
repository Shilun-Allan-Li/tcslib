<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanCopy_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of a Copy State

**Claim.** From the scan configuration at position $0$ in state $q$, the copy machine halts after $|x|+1$ steps at position $|x|$, with output $o$ followed by $x$.

**Proof.** The copy-run result (`scanCopy_run`) gives the configuration after the first $|x|$ steps: the machine is still in state $q$, its head is at position $|x|$, and its output is $o$ followed by the first $|x|$ symbols of $x$, namely all of $x$. Decompose the run of $|x|+1$ steps as those $|x|$ steps followed by one more step (`runFrom_succ_eq_step'`). At position $|x|$, the scanned symbol is blank (`scanCfg_read`), so the transition rule halts, makes no input-head movement, and emits nothing. The resulting state, position, and output are therefore those of the claimed halted scan configuration. Since there are no work tapes, agreement of those components gives equality of configurations (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.scanCopy_run`, `Turing.FinTM.scanCfg_read`, `Turing.Cfg.ext_zero_tapes`.
