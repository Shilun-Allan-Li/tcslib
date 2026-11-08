<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.redirectTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Per-tape space is preserved

**Claim.** For each work tape and each time bound $t$, the redirected machine visits the same number of distinct cells as the original machine during the corresponding computation.

**Proof.** Per-tape space is the cardinality of the finite set of head positions visited from time $0$ through time $t$. The run correspondence used for this space calculation identifies the redirected run at each time $u$ in that range with the redirected image of the original run at time $u$ (`catalog_redirect_run`). Redirection preserves every work-tape head position, so the two functions sending each time $u$ to the head position on the chosen tape agree. Their images of the same time set are therefore equal, and hence have equal cardinality. This is exactly equality of the two space measures.

**Key facts.** `Turing.FinTM.catalog_redirect_run`.
