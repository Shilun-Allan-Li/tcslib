<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.complexUniformInner_self_eq_expect_absSq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self Inner Product as a Mean Square

**Claim.** For a complex-valued function on a finite set, its uniform inner product with itself equals the uniform mean of its squared absolute value, written as the mean of the conjugate times the value.

**Proof.** Apply the identity expressing the uniform inner product of two functions as the uniform mean of their pointwise conjugate product, with both functions set equal to $f$. This gives exactly the asserted expression. (This identity is `complexUniformInner_eq_expect`.)

**Key facts.** `FABL.complexUniformInner_eq_expect`.
