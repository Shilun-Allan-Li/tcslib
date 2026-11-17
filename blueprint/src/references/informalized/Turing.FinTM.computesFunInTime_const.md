<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.computesFunInTime_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Words in Linear Time

**Claim.** For every fixed Boolean word $w$, there is a finite Turing machine that outputs $w$ on every input and halts within $c(|x|+1)$ steps for some constant $c$.

**Proof.** Use the machine whose states successively emit the symbols of the fixed word $w$ and then halt, and take $c=|w|+1$. The emission lemma ( `emit_halts`) shows that after $|w|+1$ steps, starting from the initial configuration with empty output, the machine has halted and its output is $w$. This gives computation in time $|w|+1$ on every input. Since $|x|+1\ge 1$, this time is at most $(|w|+1)(|x|+1)$; the time monotonicity lemma ( `ComputesInTime.mono`) transfers the computation to the claimed bound.

**Key facts.** `Turing.FinTM.emit_halts`, `Turing.FinTM.ComputesInTime.mono`.
