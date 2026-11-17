<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonCountTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Canonical Count

**Claim.** For every machine format $F$, a finite Boolean-alphabet Turing machine computes the canonical count of each Boolean word $w$ in time bounded by a constant times $|w|+1$.

**Proof.** First use the linear-time append-bit construction with bit false, then follow it by the linear-time fixed-width increment machine. The increment machine's time bound is monotone, so the composition theorem applies: it gives a machine for the composite function, namely the canonical count, with a bound of the form $c(a(|w|+1)+b(a(|w|+1)+1)+1)$. The stated canonical count is exactly this composite, since it increments $w$ with a false bit appended and uses the empty word if incrementing fails. Finally, the displayed polynomial is bounded by a constant multiple of $|w|+1$; increasing the time allowance is valid by the monotonicity of computation time.

**Key facts.** `Turing.FinTM.computesFunInTime_appendBit`, `Turing.FinTM.computesFunInTime_incFixed`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.ComputesInTime.mono`.
