<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecRowOf_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of rows and configuration cores

**Claim.** For configurations $c,d$ on the same Boolean input, both within the window of radius $s$, their codec rows are equal exactly when their cores together with their output summaries are equal.

**Proof.** First suppose the codec rows agree. Equality of their state, input-head, work-symbol, work-head, and summary fields gives equality of the corresponding components of the encoded cores and of the output summaries. The window hypotheses provide bounds on each work-head position and on every nonempty tape cell (`Turing.Cfg.InWindow.core_bounds`). Under these bounds, equality of the windowed core codes implies equality of the original cores (`Turing.MultiTapeTM.ConfigCount.coreCode_inj`). Thus the core-summary pairs agree. Conversely, suppose those pairs agree. Equality of the core components gives equality of states, input-head positions, work tapes, and work-head positions; equality of the summaries gives equality of the output summaries. The codec-row construction records these same components (and the fixed input data), so the rows agree.

**Key facts.** `Turing.Cfg.InWindow.core_bounds`, `Turing.MultiTapeTM.ConfigCount.coreCode_inj`.
