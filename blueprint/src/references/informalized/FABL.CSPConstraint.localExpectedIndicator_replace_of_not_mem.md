<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPConstraint.localExpectedIndicator_replace_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Irrelevant Marginal Replacement

**Claim.** Replacing the distribution of a variable outside a constraint’s scope by a point mass does not change the expected satisfaction indicator of that constraint.

**Proof.** The local expected indicator depends only on the laws at positions in the scope. Since the specified variable is outside the scope, each scoped variable differs from it. Updating the law at the specified variable therefore leaves every scoped marginal unchanged, so the independent product and its expected satisfaction payoff are unchanged.
