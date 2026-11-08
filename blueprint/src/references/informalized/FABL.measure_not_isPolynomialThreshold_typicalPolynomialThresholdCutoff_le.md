<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_not_isPolynomialThreshold_typicalPolynomialThresholdCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Typical polynomial threshold degree

**Claim.** For every dimension \(n\), a uniformly chosen Boolean function has a polynomial threshold representation of Fourier degree at most the stated cutoff, except on an event of probability at most \(2^{-n}\).

**Proof.** Take the family of all coordinate subsets whose size is at most the cutoff, and use approximation tolerance \(1/2\). If a function has such a uniform approximation, the approximation itself is a polynomial supported on that family. At each input its value differs from the Boolean value by less than \(1/2\), so it has the same sign there; consequently thresholding this polynomial represents the function. Its Fourier degree is at most the cutoff, giving the implication from approximation to threshold representation (\(\texttt{isPolynomialThreshold_of_hasLowDegreeUniformApproximation}\)). Therefore a function that has no such threshold representation must also have no such approximation. The low-degree family is nonempty (\(\texttt{lowDegreeFourierFamily_nonempty}\)), and its cardinality meets the required size bound at this cutoff (\(\texttt{card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff}\)). Applying the prescribed-support approximation failure bound with tolerance \(1/2\), and using event inclusion and monotonicity of measure, gives the claimed probability bound (\(\texttt{measure_not_hasPrescribedFourierUniformApproximation_le}\)).

**Key facts.** `FABL.isPolynomialThreshold_of_hasLowDegreeUniformApproximation`, `FABL.lowDegreeFourierFamily_nonempty`, `FABL.card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff`, `FABL.measure_not_hasPrescribedFourierUniformApproximation_le`.
