<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.kb_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the exponential code bound

**Claim.** For every finite-state nondeterministic Turing machine $N$, every $n\in\mathbb{N}$, and $s\le s'$, the bound $kb(N,n,s)$ is at most $kb(N,n,s')$.

**Proof.** The exponent defining $kb(N,n,s)$ is $codeK(N)(s+lgv(n)+1)$. Since $s\le s'$, multiplying by the natural number $codeK(N)$ preserves the inequality, so this exponent is at most $codeK(N)(s'+lgv(n)+1)$. Raising the base $2$ to these ordered natural-number exponents preserves order, giving the result.
