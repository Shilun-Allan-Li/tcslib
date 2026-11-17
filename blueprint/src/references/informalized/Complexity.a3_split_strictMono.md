<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_strictMono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict monotonicity of exponential padding

**Claim.** For natural numbers $C,c$, the function $n\mapsto n+C\cdot 2^{(n+1)^c}$ is strictly increasing.

**Proof.** Let $n<m$. Then $n+1\le m+1$, so raising these positive bases to the power $c$ preserves the weak inequality, and raising $2$ to those resulting exponents does as well. Multiplication by the nonnegative number $C$ preserves that inequality. Adding the strict inequality $n<m$ to this weak inequality shows $n+C\cdot 2^{(n+1)^c}<m+C\cdot 2^{(m+1)^c}$, as required.
