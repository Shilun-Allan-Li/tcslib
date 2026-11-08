<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.NumVal_ans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer Atom Valuation

**Claim.** For every selector and time and address tags, the numerical valuation of an answer atom is the answer function evaluated at the indices specified by those tags.

**Proof.** By definition, the valuation of an answer atom applies the answer function to the selector and to the time and address indices obtained from the corresponding tags. This is exactly the asserted expression, so the two sides agree by unfolding the definitions.
