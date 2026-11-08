<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_const_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-Word Computation with Bounded Space

**Claim.** For every fixed Boolean word $w$, a finite Turing machine outputs $w$ on every input within $c(|x|+1)$ steps and uses at most $c$ space at every time, for some constant $c$.

**Proof.** Take the constant-word emitter and set $c=|w|+1$. As in the emission argument, after $|w|+1$ steps it has halted with output $w$ ( `emit_halts`); monotonicity in the time bound ( `ComputesInTime.mono`) gives the bound $c(|x|+1)$. This emitter has zero work tapes, so its space use is zero at every time ( `spaceUsed_zero_tapes_eq_zero`), which is in particular at most $c$.

**Key facts.** `Turing.FinTM.emit_halts`, `Turing.FinTM.ComputesInTime.mono`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
