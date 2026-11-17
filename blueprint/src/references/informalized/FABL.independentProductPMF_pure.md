<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.independentProductPMF_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent product of point masses

**Claim.** The independent product of point masses at the coordinates of an assignment is the point mass at that assignment.

**Proof.** Compare point probabilities at an arbitrary tuple of values. If the tuple equals the assignment, every coordinate point mass assigns probability one, so their product is one, as is the point mass at the assignment. Otherwise, there is a coordinate where the tuple differs from the assignment. The point mass at that coordinate assigns probability zero to the tuple's value, making the entire product zero; the point mass at the assignment also assigns zero to the distinct tuple. The point-probability formula for the independent product (\texttt{FABL.independentProductPMF_apply}) supplies the product expression, so the point probabilities agree everywhere.

**Key facts.** `FABL.independentProductPMF_apply`.
