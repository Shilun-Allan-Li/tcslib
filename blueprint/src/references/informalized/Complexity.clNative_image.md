<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computation on an Image

**Claim.** If $f$ is polynomial-time computable and a finite Boolean machine computes $g(x)$ from input $f(x)$ within $b(|f(x)|+1)^r$ steps for every $x$, then $g$ is polynomial-time computable.

**Proof.** Take a machine $A$ computing $f$ in time $a(|x|+1)^d$. Run $A$ and then the given machine $B$ on its output. The buffered-composition construction computes the composite in time equal to the first run time, the intermediate word length, a fixed overhead, and the second run time (`Turing.FinTM.bufferedCompTM_computesInTime`); computation is preserved when the time bound is increased (`Turing.FinTM.ComputesInTime.mono`). The output-length bound (`Turing.MultiTapeTM.output_length_le`), applied to $A$, gives $|f(x)|\le a(|x|+1)^d$. Since $(|x|+1)^d\ge1$, it follows that $|f(x)|+1\le(a+1)(|x|+1)^d$. Raising this inequality to the power $r$ bounds $B$'s time by $b(a+1)^r(|x|+1)^{dr}$. The first run time is bounded by $a(|x|+1)^{d(r+1)}$, and the intermediate length and fixed overhead are absorbed using $|f(x)|\le a(|x|+1)^d$ and $(|x|+1)^{d(r+1)}\ge1$. Together these terms are bounded by $(2a+b(a+1)^r+2)(|x|+1)^{d(r+1)}$, a polynomial in $|x|$.

**Key facts.** `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
