<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacobiSym_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi symbol for an odd numerator

**Claim.** For natural numbers $A,N$, if both are odd, then $(A/N)$ equals $-1$ times $(N\bmod A/A)$ when both are congruent to $3$ modulo $4$, and equals $(N\bmod A/A)$ otherwise.

**Proof.** Quadratic reciprocity expresses $(A/N)$ as the reciprocity sign times $(N/A)$, with sign $-1$ precisely when both odd numbers are congruent to $3$ modulo $4$. Replacing the numerator of the latter symbol by its remainder modulo $A$ leaves the Jacobi symbol unchanged. Combining these identities gives the stated formula.
