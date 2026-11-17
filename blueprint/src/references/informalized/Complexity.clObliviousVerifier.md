<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clObliviousVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oblivious Polynomial-Time Verifier

**Claim.** If $V$ is a language in $\mathrm{P}$, then there are a finite Turing machine $M$ and positive natural numbers $c,A,d$ such that $M$ is oblivious and decides $V$ within $c\bigl(A(n+1)^d+1\bigr)^2$ steps on inputs of length $n$.

**Proof.** By the characterization of $\mathrm{P}$, choose constants $A,d$ and a machine deciding $V$ in time $A(n+1)^d$. Increase the bound to $(A+1)(n+1)^{d+1}$: both the coefficient and the power have been increased, so this bound dominates the original one for every input length. The polynomial time bound with coefficient $A+1$ and exponent $d$ is time-constructible. The theorem converting a time-constructible time bound into an oblivious computation therefore gives an oblivious machine $M$ and a constant $c$ that decides $V$ within $c((A+1)(n+1)^{d+1}+1)^2$ steps. Set the new parameters to $A+1$ and $d+1$. These are positive. The constant $c$ must also be positive: if it were zero, the bound would be zero on the empty input, contradicting the fact that no machine computes an output in zero steps. Thus all requested positivity conditions hold.

**Key facts.** `Complexity.mem_P_iff`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.timeConstructible_poly`, `Complexity.oblivious_of_mem_DTIME`, `Turing.FinTM.not_computesInTime_zero`.
