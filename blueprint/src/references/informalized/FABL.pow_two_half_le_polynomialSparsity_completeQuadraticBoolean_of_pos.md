<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.pow_two_half_le_polynomialSparsity_completeQuadraticBoolean_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic threshold sparsity bound

**Claim.** For positive even $n$, any polynomial threshold representation of the complete quadratic Boolean function has at least $2^{n/2}$ nonzero Fourier coefficients.

**Proof.** Apply the general sparsity bound for the complete quadratic Boolean function, which gives $2^{n/2}\leq \mathrm{polynomialSparsity}(p)$ provided $p$ is nonzero (\texttt{pow\_two\_half\_le\_polynomialSparsity\_completeQuadraticBoolean}). It remains to rule out $p=0$. If $p$ were identically zero, its threshold sign would be constantly $1$, so the representation condition would force the complete quadratic Boolean function to be constantly $1$. The result that this function is not constant $1$ for positive even $n$ (\texttt{completeQuadraticBoolean\_ne\_one\_of\_pos\_even}) gives a contradiction. Thus $p\ne 0$, and the general bound applies.

**Key facts.** `FABL.pow_two_half_le_polynomialSparsity_completeQuadraticBoolean`, `FABL.completeQuadraticBoolean_ne_one_of_pos_even`.
