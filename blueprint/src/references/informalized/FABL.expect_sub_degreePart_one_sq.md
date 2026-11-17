<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_sub_degreePart_one_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared error after removing the linear part

**Claim.** The expected squared difference between $f$ and its degree-one Fourier part is the second moment of $f$ minus its total Fourier weight at level one.

**Proof.** Set $a_i=\widehat f(\{i\})$. The degree-one part is the linear form with these coefficients (by `FABL.degreePart_one_eq_linearForm`). Expanding the square, its expectation is $\mathbb E[f^2]-2\mathbb E[fL]+\mathbb E[L^2]$. By linearity of expectation and the definition of the Fourier coefficients, the mixed term is $\mathbb E[fL]=\sum_i a_i^2$. Also, the second moment of this linear form is $\mathbb E[L^2]=\sum_i a_i^2$ (by `FABL.expect_linearForm_sq`). These two terms therefore combine to subtract $\sum_i a_i^2$ from $\mathbb E[f^2]$. The sum is exactly the level-one Fourier weight (by `FABL.fourierWeightAtLevel_one_eq_sum_singleton`), proving the identity.

**Key facts.** `FABL.degreePart_one_eq_linearForm`, `FABL.expect_linearForm_sq`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
