<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.code_bound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Code Bound

**Claim.** For a Boolean-alphabet nondeterministic machine and natural numbers $n,s$, the exponential bound using $s+\logSpace(n)+1$ is at most the bound using $s+\operatorname{lgv}(n)+1$.

**Proof.** The exponent on the left is no larger than the exponent defining $\mathrm{kb}(N,n,s)$: first, $\logSpace(n)\leq\operatorname{lgv}(n)$ by the logarithmic comparison lemma (`logSpace_le_lgv`); multiplying this inequality by the nonnegative code-size parameter preserves it, and adding the common terms preserves the comparison. Since raising $2$ to a natural-number exponent is monotone, the claimed inequality follows.

**Key facts.** `Complexity.LogProg.ExpBFS.logSpace_le_lgv`.
