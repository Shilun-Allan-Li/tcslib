<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.iteratedPmfLpNorm_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor formula for iterated $L^p$ norms

**Claim.** At length $n+1$, the iterated $L^p$ norm is the one-coordinate $L^p$ norm, with respect to $\lambda$, of the function assigning to each $a$ the length-$n$ iterated norm of $x\mapsto f(x,a)$.

**Proof.** This is the successor clause of the recursive definition: first fix the last coordinate $a$ and take the iterated norm over the preceding $n$ coordinates of the function obtained by appending $a$; then take the one-coordinate $L^p$ norm of those values with respect to $\lambda$.
