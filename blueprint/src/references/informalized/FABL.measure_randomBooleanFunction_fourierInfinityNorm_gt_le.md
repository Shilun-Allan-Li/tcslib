<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.measure_randomBooleanFunction_fourierInfinityNorm_gt_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier maximum tail bound

**Claim.** For \(n\ge2\), the probability that a uniformly chosen Boolean function has Fourier infinity norm greater than the stated threshold is at most \(2^{-n}\).

**Proof.** If the maximum absolute Fourier coefficient exceeds the threshold, then at least one coefficient is at least the threshold in absolute value; this event inclusion is recorded in \(\texttt{randomBooleanFourierMaximumBad_subset}\). By the union bound over all subsets of the coordinate set, its probability is at most the sum of the individual coefficient-tail probabilities. Each is at most \(2\exp(-2n)\) (\(\texttt{measure_randomBooleanFunction_fourierCoeff_atThreshold_ge_le}\)). There are \(2^n\) coordinate subsets, so the sum is at most \(2^n\cdot2\exp(-2n)\). The numerical inequality \(2^n\cdot2\exp(-2n)\le2^{-n}\), valid for \(n\ge2\), finishes the estimate (\(\texttt{two_pow_mul_two_exp_neg_two_mul_le_rpow_neg}\)).

**Key facts.** `FABL.randomBooleanFourierMaximumBad_subset`, `FABL.measure_randomBooleanFunction_fourierCoeff_atThreshold_ge_le`, `FABL.two_pow_mul_two_exp_neg_two_mul_le_rpow_neg`.
