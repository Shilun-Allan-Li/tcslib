<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.exists_completeQuadraticBit_affine_independent_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition of the Complete Quadratic Bit

**Claim.** For every $n$, the complete quadratic bit on $n$ coordinates is an affine function plus a sum of $n/2$ products of pairs of linear functions, with the $2(n/2)$ linear functions linearly independent.

**Proof.** Write $n=r+2k$ with $r=n\bmod 2$ and $k=n/2$. The remainder satisfies $r\le1$, so the remainder decomposition result applies: in dimension $r+2k$, it expresses the complete quadratic bit as an affine function plus $k$ products of pairs of linear functions, with all $2k$ linear functions linearly independent (`FABL.exists_completeQuadraticBit_pairing_of_remainder`). The division identity gives $r+2k=n$. Transporting the decomposition across this dimension equality yields the claimed functions on the $n$-coordinate cube and preserves both the identity and linear independence (`FABL.completeQuadraticBit_decomposition_cast`).

**Key facts.** `FABL.exists_completeQuadraticBit_pairing_of_remainder`, `FABL.completeQuadraticBit_decomposition_cast`.
