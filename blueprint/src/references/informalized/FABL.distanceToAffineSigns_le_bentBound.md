<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.distanceToAffineSigns_le_bentBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bent Bound for Affine-Sign Distance

**Claim.** When $n$ is even, every sign-valued function on the Boolean cube has distance to the affine sign functions at most $\frac12-\frac{1}{2\cdot 2^{n/2}}$.

**Proof.** The bent-coefficient bound supplies an index $\gamma$ with $2^{-n/2}\le |\widehat f(\gamma)|$ (`exists_bent_extremal_coefficient`). This coefficient's magnitude is at most the maximum Fourier magnitude. By the distance formula (`distanceToAffineSigns_eq`), the distance is $\frac12-\frac12\|\widehat f\|_\infty$. Substituting the lower bound on the maximum gives the asserted upper bound.

**Key facts.** `FABL.exists_bent_extremal_coefficient`, `FABL.distanceToAffineSigns_eq`.
