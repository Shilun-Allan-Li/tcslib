<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_not_hasPrescribedFourierUniformApproximation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Typical prescribed Fourier approximation

**Claim.** Under the stated size condition on the nonempty family \(\mathcal F\), the probability that a uniformly chosen sign-valued Boolean function has no uniformly \(\varepsilon\)-accurate approximation with Fourier support in \(\mathcal F\) is at most \(2^{-n}\).

**Proof.** For each function \(f\), consider the prescribed Fourier approximation constructed from \(\mathcal F\) and \(f\). Its Fourier coefficients vanish outside \(\mathcal F\), by the support property of this approximation (\(\texttt{fourierCoeff_prescribedFourierApproximation_eq_zero}\)). If this particular approximation fails to be within \(\varepsilon\) of \(f\) at some input, its pointwise formula says that the absolute value of the prescribed off-center Fourier sum there is at least \(\varepsilon\). Thus every function with no suitable approximation belongs to the event that such a failing input exists. Monotonicity of measure bounds the probability of the former event by that of the latter. The supplied estimate for the probability of an off-center failure somewhere, under the same size and nonemptiness hypotheses, is at most \(2^{-n}\) (\(\texttt{measure_exists_prescribedFourierOffCenterFailure_le}\)).

**Key facts.** `FABL.fourierCoeff_prescribedFourierApproximation_eq_zero`, `FABL.prescribedFourierApproximation_apply`, `FABL.measure_exists_prescribedFourierOffCenterFailure_le`.
