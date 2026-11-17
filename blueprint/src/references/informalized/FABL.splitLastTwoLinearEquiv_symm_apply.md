<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.splitLastTwoLinearEquiv_symm_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a Vector from Coordinates

**Claim.** The inverse of the coordinate identification sends $(x,(a,b))$ to the vector obtained by appending $a,b$ to $x$.

**Proof.** It suffices to show that the vector obtained by appending $a,b$ to $x$ maps under the coordinate identification to $(x,(a,b))$, since a linear equivalence is injective. Splitting the appended vector recovers its first $m$ coordinates $x$ and its last two coordinates $(a,b)$. Thus it maps to the specified pair, and applying the inverse identification to that pair gives the appended vector.
