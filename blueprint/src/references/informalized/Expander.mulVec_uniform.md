<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.mulVec_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Vector is Fixed

**Claim.** A symmetric stochastic matrix $A$ fixes the constant vector whose coordinates are $1/n$.

**Proof.** At coordinate $i$, applying $A$ to the uniform vector gives $\sum_j A_{ij}(1/n)$. Factor out the constant $1/n$; the row sum is $1$, so this coordinate equals $1/n$. This holds in every coordinate, proving that the vector is fixed.
