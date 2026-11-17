<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.innerProductModTwo_ptf_sparsity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-product threshold sparsity

**Claim.** Every nonzero polynomial threshold representation of the inner-product function on $2n$ Boolean coordinates has sparsity at least $2^n$.

**Proof.** Apply the Fourier-mass bound for a nonzero polynomial threshold representation (`ptf_support_fourier_mass_of_ne_zero`) with the set of frequencies equal to the polynomial's support. Every nonzero coefficient is, by definition of support, indexed by a member of this set, so the required support containment holds. The bound says that the sum of the absolute Fourier coefficients over this support is at least $1$. Each such coefficient of the inner-product function has magnitude $2^{-n}$ (`abs_fourierCoeff_innerProductModTwo`). Therefore the sum is the support size times $2^{-n}$, and its being at least $1$ implies that the support size, hence the polynomial's sparsity, is at least $2^n$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.ptf_support_fourier_mass_of_ne_zero`, `BooleanAnalysis.ThresholdFunctions.abs_fourierCoeff_innerProductModTwo`.
