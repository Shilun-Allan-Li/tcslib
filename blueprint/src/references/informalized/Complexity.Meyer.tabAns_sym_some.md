<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.tabAns_sym_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Selector Answer

**Claim.** For a work-tape selector, the table answer after the specified number of signed moves is the blank-symbol test applied to the symbol at the corresponding signed displacement from the selected tape's current head position.

**Proof.** Unfold the table answer and selector-answer function in the case of a selected work tape. The selector-answer function applies the blank-symbol test to the symbol currently scanned on tape $h$ after the prescribed walk. The walked-work identity identifies that scanned symbol with the original tape's contents at the head position displaced by the signed offset (walked-work identity, `Complexity.Meyer.walked_work`). Substitution yields the result.

**Key facts.** `Complexity.Meyer.walked_work`.
