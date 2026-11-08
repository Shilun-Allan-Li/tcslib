<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.card_resilientSharpnessPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the resilient sharpness prefix

**Claim.** If $k<n-1$, the prefix consisting of the first $k+1$ coordinate indices has cardinality $k+1$.

**Proof.** The prefix is the initial interval of indices strictly below $k+1$. Since $k+1$ is an index bound in the range of the $n$ coordinates, this interval contains precisely the indices $0,1,\ldots,k$, and hence has cardinality $k+1$.
