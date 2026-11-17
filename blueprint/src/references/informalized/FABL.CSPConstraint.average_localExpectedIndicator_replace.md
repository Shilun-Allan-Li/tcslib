<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPConstraint.average_localExpectedIndicator_replace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging a Replaced Marginal

**Claim.** If a variable occurs in a constraint’s scope, averaging the local satisfaction probability after replacing its distribution by a point mass recovers the original local satisfaction probability.

**Proof.** Choose the unique position in the constraint’s injective scope occupied by the specified variable. Regard the laws at the scoped positions as a family of independent marginals. Replacing the law of the specified variable by the point mass at a label changes exactly the marginal at that position; injectivity of the scope ensures no other position is affected. The averaging identity for independent products says that averaging the payoff under these point-mass replacements, with the label drawn from the original marginal, equals the payoff expectation under the original independent product (`pmfExpectation_replace_independentProductPMF`). Applying this identity to the Boolean satisfaction indicator gives the claimed equality.

**Key facts.** `FABL.pmfExpectation_replace_independentProductPMF`.
