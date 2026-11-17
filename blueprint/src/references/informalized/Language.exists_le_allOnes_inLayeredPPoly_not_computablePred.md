<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.exists_le_allOnes_inLayeredPPoly_not_computablePred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Noncomputable Language of Layered Polynomial Size

**Claim.** There is a language of Boolean strings contained in the all-ones language that is recognized by a standard-gate layered circuit family of polynomial size, although its membership predicate is not computable.

**Proof.** Choose the unary halting language `uhalt` as the witness. It is contained in the all-ones language ( `Language.unary_le_allOnes`), belongs to layered polynomial size ( `Language.uhalt_inLayeredPPoly`), and has a noncomputable membership predicate ( `Language.not_computablePred_mem_uhalt`). These three properties give the asserted example.

**Key facts.** `Language.unary_le_allOnes`, `Language.uhalt_inLayeredPPoly`, `Language.not_computablePred_mem_uhalt`.
