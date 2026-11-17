<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.uniformLpNorm_sub_lowDegreePart_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error of Low-Degree Truncation

**Claim.** For $n,k\in\mathbb N$ and $f\colon\{-1,1\}^n\to\mathbb R$, the squared uniform $2$-norm of the difference between $f$ and its degree-at-most-$k$ Fourier part is the sum of the squared Fourier coefficients over subsets of size greater than $k$.

**Proof.** First identify the degree-at-most-$k$ Fourier part with the sparse Fourier approximation supported on subsets of size at most $k$ (\texttt{lowDegreePart_eq_sparseFourierApproximation}). The error formula for a sparse Fourier approximation (\texttt{uniformLpNorm_sub_sparseFourierApproximation_sq}) expresses its squared uniform $2$-norm as the sum of squared coefficient errors on the selected subsets, plus the sum of squared Fourier coefficients outside that support. On every selected subset the approximation uses the actual Fourier coefficient, so those coefficient errors vanish. The subsets outside the support are exactly those whose sizes exceed $k$, giving the asserted tail sum.

**Key facts.** `FABL.lowDegreePart_eq_sparseFourierApproximation`, `FABL.uniformLpNorm_sub_sparseFourierApproximation_sq`.
