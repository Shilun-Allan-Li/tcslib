<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFFormula.fourierOneNorm_satisfiedTermCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Norm of the Satisfied-Term Count

**Claim.** For a DNF formula, the Fourier one-norm of the function counting its satisfied terms is at most the number of terms in the formula.

**Proof.** Write the satisfied-term count as the sum, over all term indices, of the indicator function for that term being satisfied. The Fourier one-norm of a finite sum is at most the sum of the Fourier one-norms of its summands (by the triangle inequality for Fourier coefficients and summation). Each term's satisfaction indicator has Fourier one-norm $1$ (by `fourierOneNorm_trueIndicator`). Thus the total is at most the sum of one over all term indices, which is the number of terms.

**Key facts.** `FABL.fourierOneNorm_sum_le`, `FABL.DNFTerm.fourierOneNorm_trueIndicator`.
