<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_linearForm_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment of a sign linear form

**Claim.** For a real coefficient vector on the sign cube, the fourth moment of its linear form equals three times the square of the sum of squared coefficients, minus twice the sum of their fourth powers.

**Proof.** Proceed by induction on the dimension. In dimension zero the linear form is identically zero, so the identity holds. In dimension $n+1$, separate the first coordinate: write the form as the first coefficient times that sign, plus the linear form in the remaining coordinates. The fourth-moment decomposition for a sign coordinate gives the fourth moment as the fourth moment of the first coefficient, plus six times that coefficient squared times the second moment of the remaining form, plus the fourth moment of the remaining form. Apply the induction hypothesis to the remaining form, and use the second-moment identity to replace its second moment by the sum of the remaining squared coefficients. Expanding the resulting expression gives the claimed identity after separating the first coefficient from each sum.

**Key facts.** `FABL.expect_fourth_eq_expect_odd_even`, `FABL.expect_linearForm_sq`, `FABL.linearForm_fin_cons`.

**Caveat.** The supplied informal statement describes the Bonami inequality, but the formal statement and proof establish an exact fourth-moment identity for linear forms.
