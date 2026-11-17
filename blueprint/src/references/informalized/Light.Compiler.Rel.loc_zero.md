<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.loc_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Local Variable Address

**Claim.** If $F>0$, then the memory value at stack address $q$ is the encoding of the first local variable, $\sigma_{\mathrm{loc}}(0)$.

**Proof.** The storage relation states that for every local-variable index $x<F$, the memory at stack address $q+x$ contains the encoding of $\sigma_{\mathrm{loc}}(x)$. Since $F>0$, the index $0$ is in range. Substituting $x=0$ gives the claim because $q+0=q$.
