<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.centeredLinearSquare_singletonCoeffs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered square from first-level Fourier data

**Claim.** For a real-valued function $f$ on the Boolean cube and a point $x$ of that cube, the centered square of the linear form with singleton Fourier coefficients equals the square of the degree-one part of $f$ at $x$ minus the total squared Fourier weight at degree one.

**Proof.** By definition, the centered square is the square of the linear form with coefficients $\widehat f(\{i\})$, minus $\sum_i \widehat f(\{i\})^2$. The degree-one part equals this linear form (FABL.degreePart_one_eq_linearForm), and the Fourier weight at level one equals $\sum_i \widehat f(\{i\})^2$ (FABL.fourierWeightAtLevel_one_eq_sum_singleton). Substituting these two identities gives the claimed equality.

**Key facts.** `FABL.degreePart_one_eq_linearForm`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
