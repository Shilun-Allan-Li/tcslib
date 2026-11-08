<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.inner_hermiteL2_toLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficient as an Inner Product

**Claim.** The inner product of the $L^2$ class of the normalized Hermite function indexed by $\alpha$ with the $L^2$ class of $f$ equals the Hermite coefficient of $f$.

**Proof.** The normalized Hermite function belongs to $L^2(\gamma_n)$ by \texttt{hermiteFunction_memLp_two}, and $f$ belongs to that space by hypothesis. The inner product of two $L^2$ classes is the integral of the product of their representatives (\texttt{inner_toLp_eq_integral_mul}). Applying this identity gives the integral of the Hermite function times $f$; commutativity of multiplication identifies it with the defining integral for the Hermite coefficient.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`, `BooleanAnalysis.GaussianSpace.inner_toLp_eq_integral_mul`.
