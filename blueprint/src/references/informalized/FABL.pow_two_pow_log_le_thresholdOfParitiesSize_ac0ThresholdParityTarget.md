<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.pow_two_pow_log_le_thresholdOfParitiesSize_ac0ThresholdParityTarget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constructed target parity size bound

**Claim.** For $m\geq 7$, if the constructed target Boolean function on $2^m$ signs has a polynomial threshold representation with at most $s$ nonzero Fourier coefficients, then $(2^m)^{\lfloor\log_2(2^m)\rfloor}\leq s$.

**Proof.** Choose a representing polynomial $p$ whose Fourier sparsity is at most $s$. The exponent simplifies as $\log_2(2^m)=m$, so $(2^m)^{\log_2(2^m)}=(2^m)^m=2^{m^2}$. The sparsity lower bound for this constructed target gives $2^{m^2}\leq\mathrm{polynomialSparsity}(p)$ (\texttt{pow\_two\_sq\_le\_polynomialSparsity\_ac0ThresholdParityTarget}). Since this sparsity is at most $s$, transitivity proves the result.

**Key facts.** `FABL.pow_two_sq_le_polynomialSparsity_ac0ThresholdParityTarget`.
