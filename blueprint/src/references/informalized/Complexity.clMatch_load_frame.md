<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_load_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loader Configuration Embedding

**Claim.** Embedding a loader configuration into the matcher’s loading slots produces the matcher configuration in its loading state, with the new row and supplied stream cursor, while retaining the target words, clock, flags, and their head positions.

**Proof.** Both configurations have the same input-head position, and both have empty output. Their states agree because the loader state is mapped into the matcher’s loading-state summand. It remains to compare the work tapes and their head positions. The loading-slot placement sends the loader’s first $l$ tapes to the matcher’s row tapes and its final tape to the matcher’s stream tape. On those slots, the embedded configuration therefore has exactly the row words and stream supplied to the loader, with the stream head at the supplied cursor. The remaining four matcher tapes inherit their contents and head positions from the original matcher configuration; these are precisely the target words, clock tape, and flags tape with the head positions specified there. Thus every configuration component agrees.
