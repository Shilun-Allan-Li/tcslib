<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.lambda_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Nontrivial Operator Norm

**Claim.** For a symmetric stochastic matrix $A$, the supremum $\lambda(A)$ of $\|Av\|$ over unit vectors orthogonal to the uniform vector is at most $1$.

**Proof.** Every vector in the set defining the supremum has norm $1$. A symmetric stochastic matrix is a contraction on the whole space (`norm_toCLM_apply_le`), so each corresponding value $\|Av\|$ is at most $1$. Hence their supremum is at most $1$.

**Key facts.** `Expander.norm_toCLM_apply_le`.
