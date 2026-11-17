<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Complexity.LOGSPACE_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log Space in Polynomial Time

**Claim.** Every language decidable by a finite Turing machine using space bounded by a constant multiple of $\log_2(n)+1$ is decidable in polynomial time.

**Proof.** Take a language in $\mathsf{LOGSPACE}$, witnessed by a machine whose space is bounded by a constant multiple of $\mathrm{logSpace}(n)$. The configuration-counting theorem for space-bounded machines supplies a polynomial running-time bound for computing the decision output: the bound has the form $K(n+1)^d$ for constants $K,d$ depending on the machine and its space constant. The characterization of $\mathsf{P}$ by bounds of this form then places the language in $\mathsf{P}$.

**Key facts.** `Turing.FinTM.ComputesInSpace.computesFunInTime`, `Complexity.mem_P_iff`.
