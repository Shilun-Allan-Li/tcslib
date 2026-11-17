<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_fill -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Constant Fill

**Claim.** For each fixed bit $b$, the function mapping a binary word $x$ to the word of $|x|$ copies of $b$ is polynomial-time computable.

**Proof.** Use the machine that writes the fixed bit $b$ once for each input position. Its run characterization (`Complexity.clFill_run`) says that, starting at position $i+1$ with output $out$, after $|x|-i+1$ steps it halts at the right boundary with output $out$ followed by $|x|-i$ copies of $b$. Take $i=0$ and the empty output: the initial configuration is the machine's standard initial configuration, and the resulting output is exactly $|x|$ copies of $b$. The run takes $|x|+1$ steps. The equivalence between computation in time and having halted with the specified output (`Turing.FinTM.computesInTime_iff`) therefore establishes computation of the desired function. Since $|x|+1$ is the polynomial bound with both coefficients and exponent equal to one, the function is polynomial-time computable.

**Key facts.** `Complexity.clFill_run`, `Turing.FinTM.computesInTime_iff`.
