<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.affineLinearRemainder_eq_two_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition of an Affine Remainder

**Claim.** When $i\ne j$, the affine remainder omitting coordinate $j$ is the remainder omitting both $i$ and $j$, plus $a_i x_i$.

**Proof.** In the sum defining the remainder that omits $j$, the distinctness of $i$ and $j$ ensures that the term at $i$ is still present. Separate that term from the sum. What remains is precisely the sum over coordinates omitting both $i$ and $j$; adding back the common constant term and rearranging yields the stated decomposition.
