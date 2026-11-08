<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.noiseOperator_apply_eq_pmfExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel Formula for the Noise Operator

**Claim.** For an admissible parameter, applying the noise operator to a function at a point equals the expectation of that function under the noise kernel based at that point.

**Proof.** The kernel representation theorem identifies the noise operator with the linear operator whose value at each input is the expectation under the noise kernel (`kernelNoiseOperator_eq_noiseOperator`). Rewriting by this equality leaves exactly the defining formula for that kernel operator, which is the stated expectation.

**Key facts.** `FABL.kernelNoiseOperator_eq_noiseOperator`.
