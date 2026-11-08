<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.affineLinearForm_neg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Negation of an Affine Form

**Claim.** For a real constant term and coefficients on the Boolean cube, evaluating the affine form at the coordinatewise negation of a sign vector gives the constant term minus the original linear form.

**Proof.** Expand the affine form and the linear form. At each coordinate, negating the sign negates its real value, by the sign-value negation identity (`FABL.signValue_neg`). Thus each summand becomes the negative of its original value, and the sum is the negative of the original linear form. Rewriting addition of that negative as subtraction gives the claimed identity.

**Key facts.** `FABL.signValue_neg`.
