<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.expect_sq_homogenizedAffineLinearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment under Homogenization

**Claim.** The expected square of the homogenized linear form on the $(n+1)$-dimensional sign cube equals the expected square of the corresponding affine form on the $n$-dimensional sign cube.

**Proof.** Average first over the added sign using the first-coordinate expectation formula (FABL.expect_fin_cons). When that sign is $1$, the homogenized form becomes $a_0$ plus the original linear form; when it is $-1$, it becomes $-a_0$ plus that linear form, by the evaluation formula for the homogenized form (FABL.homogenizedAffineLinearForm_fin_cons) and the values of the two signs (FABL.signValue_one, FABL.signValue_neg_one). The expected square of the second slice equals that of the affine form with constant term $a_0$ (FABL.expect_sq_neg_affineLinearForm). Consequently the two slice means agree, and averaging them gives the affine form's second moment.

**Key facts.** `FABL.expect_fin_cons`, `FABL.homogenizedAffineLinearForm_fin_cons`, `FABL.signValue_one`, `FABL.signValue_neg_one`, `FABL.expect_sq_neg_affineLinearForm`.
