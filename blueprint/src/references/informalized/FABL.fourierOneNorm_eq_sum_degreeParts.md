<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.fourierOneNorm_eq_sum_degreeParts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm by degree

**Claim.** The Fourier one norm of $f$ is the sum, over $k=0,\ldots,n$, of the Fourier one norms of its degree-$k$ parts.

**Proof.** For each $k$, the degree-part identity expresses its Fourier one norm as the sum of $|\widehat f(S)|$ over frequencies of size $k$ (`fourierOneNorm_degreePart_eq_sum_level`). Summing these identities for $k$ in the range $0$ through $n$ partitions all frequencies by their cardinality. Every subset of the $n$ coordinates has cardinality at most $n$, so this partition includes every term in the Fourier one norm exactly once.

**Key facts.** `FABL.fourierOneNorm_degreePart_eq_sum_level`.
