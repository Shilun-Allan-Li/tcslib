<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.diagLangOf_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Language Time Bound

**Claim.** For a time-constructible function $g$, the language of words on which $W$ does not halt at time $g(|x|)$ with output $1$ is decidable in time $c(g(n)+1)$ for some constant $c$.

**Proof.** Choose a machine $K$ witnessing that $g$ is time-constructible, with constant $c_K$: on input $x$, it outputs the binary representation of $g(|x|)$ in time $c_K(g(|x|)+1)$. The clocked simulation of $K$ and $W$ then decides whether $W$ halts at that prescribed time with output $1$. Indeed, `clockTM_spec` gives the simulation’s output as the negation of that event, and `ctrVal_bits` identifies the value of the binary clock supplied by $K$ with $g(|x|)$. Thus the output bit is precisely the indicator of the diagonal language. Its running time is $c_K(g(|x|)+1)+4| (g(|x|)) .bits|+|x|+4g(|x|)+6$. The binary representation has length at most its value (`length_bits_le_self`), and time-constructibility gives $|x|\le g(|x|)$. These inequalities bound the displayed time by $(c_K+15)(g(|x|)+1)$. Finally, monotonicity of computation time lets the machine run for this larger bound, so it witnesses membership in the stated time class.

**Key facts.** `Complexity.TimeHierarchy.clockTM_spec`, `Complexity.TimeHierarchy.ctrVal_bits`, `Turing.length_bits_le_self`, `Turing.FinTM.ComputesInTime.mono`.
