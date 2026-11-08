<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.pmfExpectation_replace_independentProductPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replacing a Product Coordinate

**Claim.** If a label is first sampled from the distribution at coordinate $a$, and then a product tuple is sampled with that coordinate fixed to the label and all other coordinate laws unchanged, the resulting expected payoff equals the expectation under the original independent product law.

**Proof.** View the two-stage sampling procedure as a single probability law: first sample the label from $p_a$, then sample the tuple from the product law whose coordinate-$a$ distribution is the point mass at that label. The expectation-under-binding formula identifies the left side with the expectation under this combined law. The law identity `bind_replace_independentProductPMF` says that this combined distribution is exactly the original independent product distribution, so their expectations of the payoff agree.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.bind_replace_independentProductPMF`.
