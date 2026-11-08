<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.sampledFourierPolynomial_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sampled Fourier Polynomial Evaluation

**Claim.** At each input, the sampled Fourier polynomial equals the Fourier one-norm times the empirical average of the signed Fourier atoms indexed by the sampled sets.

**Proof.** Let $\mathcal F$ be the family of sets appearing among the samples. By definition, the polynomial sums over $T\in\mathcal F$ the sampled coefficient at $T$ times the monomial at $T$. Expand the sampled coefficient as the Fourier one-norm divided by the sample count, multiplied by the sum of the signs over indices whose sampled set is $T$. Distribute these sums and use that, for each such index, $T$ equals the sampled set; the resulting summand is the signed Fourier atom at that sample. Finally, summing over $T$ regroups the terms by their sample indices: each sample belongs to $\mathcal F$, so the fiberwise sum identity applies. The expression becomes the Fourier one-norm divided by the sample count times the sum of the signed Fourier atoms over all samples, which is the asserted empirical average multiplied by the Fourier one-norm.
