<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorOutput_realValue_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact real-valued recovery

**Claim.** Under the stated degree and sample-accuracy hypotheses, the real-valued function represented by the estimator's sparse Fourier hypothesis equals the target's real-valued sign representation everywhere.

**Proof.** Fix an input $x$. In the estimator's defining sum, each coefficient equals the true Fourier coefficient by exact coefficient recovery (FABL.exactDegreeFourierEstimatorOutput_coefficient_cast_eq). Hence the estimator's sum over the low-degree family is the sum of the true coefficients over that family. The family consists precisely of subsets of size at most $k$, so this is the corresponding restricted Fourier sum. By the degree bound, every coefficient indexed by a set of size greater than $k$ vanishes (FABL.fourierDegree_le_iff). Adding those zero terms shows that the restricted sum equals the full Fourier expansion. The Fourier expansion identity (FABL.fourier_expansion) says this full sum is the target's value at $x$. Since $x$ was arbitrary, the functions agree everywhere.

**Key facts.** `FABL.exactDegreeFourierEstimatorOutput_coefficient_cast_eq`, `FABL.fourierDegree_le_iff`, `FABL.fourier_expansion`.
