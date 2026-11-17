<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.exists_le_allOnes_inPPoly_not_computablePred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Noncomputable Polynomial-Size Language

**Claim.** There is a language of Boolean strings contained in the language of all-ones strings that is recognized by a family of well-formed Boolean circuits with fan-in at most two and polynomial size, but whose membership predicate is not computable.

**Proof.** Take the unary halting language $\mathrm{uhalt}$ as the witness. The unary-language inclusion theorem says that every word in this language consists entirely of true bits, so $\mathrm{uhalt}\leq\mathrm{allOnes}$ ( `Language.unary_le_allOnes`). The polynomial-size circuit theorem for $\mathrm{uhalt}$ gives $\mathrm{uhalt}\in\mathrm{PPoly}$ (`Language.uhalt_inPPoly`). Finally, the halting-language undecidability result says that membership in $\mathrm{uhalt}$ is not computable (`Language.not_computablePred_mem_uhalt`). These three facts establish all the required properties of the chosen witness.

**Key facts.** `Language.unary_le_allOnes`, `Language.uhalt_inPPoly`, `Language.not_computablePred_mem_uhalt`.
