<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_toReal_sub_degreePart_one_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Error and Level-One Weight

**Claim.** For a sign-valued function $f$ on the sign cube, the expected squared difference between $f$ and its degree-one part is $1$ minus the Fourier weight at level one.

**Proof.** Apply the identity expressing the squared error from the degree-one part as the second moment of $f$ minus its Fourier weight at level one (`expect_sub_degreePart_one_sq`). Because $f$ takes values in $\{-1,1\}$, its square is identically $1$, so its uniform average is $1$. Substituting this second moment gives the stated equality.

**Key facts.** `FABL.expect_sub_degreePart_one_sq`.
