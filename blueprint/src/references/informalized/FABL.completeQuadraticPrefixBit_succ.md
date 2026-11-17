<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticPrefixBit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Prefix Recurrence

**Claim.** For $k<n$, the quadratic value of the prefix of length $k+1$ is the value at length $k$ plus the product of the linear sum of the first $k$ mapped coordinates and the mapped coordinate $w_k$.

**Proof.** The truncation at length $k+1$ is the truncation at length $k$ with just the coordinate $k$ added, carrying value equal to the image of $w_k$ (`completeQuadraticTruncation_succ`). Adding a single coordinate to the quadratic form changes its value by that coordinate's value times the quadratic derivative at that position (`completeQuadraticBit_add_single`). For the length-$k$ truncation, this derivative is the sum of the first $k$ mapped coordinates (`completeQuadraticDerivativeBit_truncation`). Substituting these two facts gives the stated recurrence; the remaining rearrangement is the distributive and commutative algebra of $\mathbb F_2$.

**Key facts.** `FABL.completeQuadraticTruncation_succ`, `FABL.completeQuadraticBit_add_single`, `FABL.completeQuadraticDerivativeBit_truncation`.
