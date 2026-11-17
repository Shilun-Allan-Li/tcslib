<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairDup_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Time for Pair Duplication

**Claim.** The duplicator halts after exactly $4(|x|+1)$ steps on input $x$ and outputs the encoding formed by writing every bit of $x$ twice, then the separator $01$, then $x$.

**Proof.** Let $p$ be the list obtained by writing each bit of $x$ twice. After $2|x|+1$ steps, the machine is at the end of its doubling pass, in the configuration with output $p$ followed by $0$ (`Turing.FinTM.pairDup_double`, together with the one-step transition analyzed using `Turing.FinTM.scanCfg_read`). It then rewinds across the input in $|x|+1$ steps, reaching the start in its emission state (`Turing.FinTM.rewind_scan`). One more step emits the separator's $1$ and enters the copying state. The copying phase takes another $|x|+1$ steps and appends $x$ (`Turing.FinTM.scanCopy_finish`). Composing these phases with the run-addition and successor-step identities gives total time $(2|x|+1)+(|x|+1)+1+(|x|+1)=4(|x|+1)$. The configuration comparisons are justified by extensionality for machines with zero work tapes (`Turing.Cfg.ext_zero_tapes`); the computation characterization then gives the exact halting and output claims (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Turing.FinTM.pairDup_double`, `Turing.FinTM.scanCfg_read`, `Turing.FinTM.rewind_scan`, `Turing.FinTM.scanCopy_finish`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`.
