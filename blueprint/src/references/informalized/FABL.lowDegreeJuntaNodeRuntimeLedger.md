<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaNodeRuntimeLedger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node Runtime Ledger

**Claim.** The node's Fourier scan work and polynomial learner work satisfy the two stated runtime envelopes, and the coefficient failure bits and runtime exponents obey the accompanying identities and inequalities.

**Proof.** Apply the Fourier scan work bound to the first component, the polynomial learner work bound to the second, and the coefficient failure-bit identity to the third. The runtime exponent ledger supplies the final two inequalities. Pairing these four conclusions in order yields the claimed conjunction; the particular restricted sample batch is allowed throughout the polynomial work bound.

**Key facts.** `FABL.lowDegreeJuntaFourierScanWork_cast_le`, `FABL.lowDegreeJuntaPolynomialWork_le_fixedParameterEnvelope`, `FABL.lowDegreeJuntaCoefficientFailureBits_eq`, `FABL.lowDegreeJuntaRuntimeExponentLedger`.
