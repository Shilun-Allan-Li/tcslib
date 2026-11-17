<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.measure_queriedFiniteFamilyFourierEstimatorOutput_failure_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queried Fourier estimator failure bound

**Claim.** Under the stated Fourier concentration hypothesis, the probability that the queried finite-family Fourier estimator has relative Hamming error greater than \(\varepsilon\) is at most \(\delta\).

**Proof.** Let the failure event be that the estimator's output differs from the target on a relative fraction greater than \(\varepsilon\) of inputs. If none of the coefficient-specific bad events occurs, every estimated Fourier coefficient is within its assigned accuracy. The deterministic error bound for the estimator under this condition and the assumed Fourier concentration says its relative Hamming error is at most \(\varepsilon\) (\(\texttt{relativeHammingDist_queriedFiniteFamilyFourierEstimatorOutput_le_of_no_bad}\)). Thus the failure event is contained in the union, over \(S\in\mathcal F\), of the event that coefficient \(S\) is estimated inaccurately. The probability of this union is at most \(\delta\), by the total-confidence estimate for the coefficient bad events (\(\texttt{measure_finiteFamily_someCoefficientBadSetWithTotalConfidence_le}\)). Monotonicity of measure gives the same bound for the estimator failure event.

**Key facts.** `FABL.relativeHammingDist_queriedFiniteFamilyFourierEstimatorOutput_le_of_no_bad`, `FABL.measure_finiteFamily_someCoefficientBadSetWithTotalConfidence_le`.
