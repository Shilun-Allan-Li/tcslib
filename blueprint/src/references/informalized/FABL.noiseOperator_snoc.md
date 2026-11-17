<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.noiseOperator_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Operator on an Appended Coordinate

**Claim.** The noise operator applied to a function at a point with an appended sign $a$ equals the noise operator on the even part, plus $ho a$ times the noise operator on the odd part.

**Proof.** Represent the noise operator as expectation under the noise kernel (`noiseOperator_apply_eq_pmfExpectation`). Decompose this expectation by first sampling the last coordinate and then sampling the first $n$ coordinates, using the independent product expectation formula (`pmfExpectation_independentProductPMF_succ`). At each resulting point, reconstruct the function from its last-coordinate even and odd parts: $f(x\mathbin{\mathrm{snoc}}a')=f_{\mathrm{even}}(x)+f_{\mathrm{odd}}(x)\,a'$ (`lastCoordinate_reconstruct`). Linearity of expectation splits the two contributions (`pmfExpectation_add`) and pulls out constants (`pmfExpectation_const_mul`, `pmfExpectation_mul_const`); the expectation of the noisy last sign is $\rho a$ (`pmfExpectation_coordinateNoisePMF_signValue`), while the expectation of a constant is that constant (`pmfExpectation_const`). Thus the two terms are the noise-kernel expectations of the even and odd parts, with the latter multiplied by $\rho a$. Convert those expectations back to noise-operator values using `noiseOperator_apply_eq_pmfExpectation`; rearranging scalar factors gives the stated identity.

**Key facts.** `FABL.noiseOperator_apply_eq_pmfExpectation`, `FABL.pmfExpectation_independentProductPMF_succ`, `FABL.lastCoordinate_reconstruct`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_mul_const`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_coordinateNoisePMF_signValue`.
