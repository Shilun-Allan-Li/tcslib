<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.pow_two_half_le_thresholdOfParitiesSize_completeQuadraticBoolean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold parity size lower bound

**Claim.** If the complete quadratic Boolean function on a positive even number $n$ of bits has a polynomial threshold representation with at most $s$ nonzero Fourier coefficients, then $2^{n/2}\leq s$.

**Proof.** By the definition of a threshold parity representation, choose a polynomial threshold representation $p$ whose Fourier sparsity is at most $s$. The positive even-dimensional sparsity bound gives $2^{n/2}\leq \mathrm{polynomialSparsity}(p)$ (\texttt{pow\_two\_half\_le\_polynomialSparsity\_completeQuadraticBoolean\_of\_pos}). Combining this with the assumed upper bound on the sparsity yields $2^{n/2}\leq s$.

**Key facts.** `FABL.pow_two_half_le_polynomialSparsity_completeQuadraticBoolean_of_pos`.
