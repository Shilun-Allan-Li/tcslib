<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.khintchine_of_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Khintchine bounds for $1\le p\le2$

**Claim.** For a sign-cube linear form and $1\le p\le2$, its $L_p$ norm is at most its $L_2$ norm and at least $e^{-(2/p-1)}$ times its $L_2$ norm.

**Proof.** A linear form has Fourier degree at most one (`fourierDegree_linearForm_le_one`). The degree-$k$ hypercontractive estimate with $k=1$ therefore gives $\|L\|_2\le e^{2/p-1}\|L\|_p$ (`lowDegree_two_le_expFactor_mul`). The exponential factor is positive, so dividing by it gives the stated lower bound, written as $e^{-(2/p-1)}\|L\|_2\le\|L\|_p$. For the other direction, monotonicity of uniform $L_p$ norms for positive exponents gives $\|L\|_p\le\|L\|_2$ (`uniformLpNorm_mono`).

**Key facts.** `FABL.fourierDegree_linearForm_le_one`, `FABL.lowDegree_two_le_expFactor_mul`, `FABL.uniformLpNorm_mono`.
