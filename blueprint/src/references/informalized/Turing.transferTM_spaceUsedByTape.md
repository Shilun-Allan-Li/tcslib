<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.transferTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used by the Transfer Machine

**Claim.** At every time, the source and destination heads have each visited at most $|w_{\mathrm{src}}|+2$ distinct cells, while every other work-tape head has visited exactly one distinct cell.

**Proof.** Fix a tape and consider its head at every time. The transfer trace lemma (Turing.catalog_transfer_trace), instantiated with the source word and the initial configuration, describes the entire run. For the source and destination tapes, its trace keeps the head positions between one cell left of the initial position and $|w_{\mathrm{src}}|$ cells to the right. Since the initial positions are zero, the visited positions lie in the integer interval from $-1$ through $|w_{\mathrm{src}}|$. The general interval-to-space bound (Turing.catalog_space_bound) therefore gives at most $|w_{\mathrm{src}}|+2$ visited cells for each of these tapes. For any other tape, the trace shows that its head remains at zero at every time. The fixed-head space fact (Turing.catalog_space_one) then gives exactly one visited cell. These conclusions yield the three asserted bounds.

**Key facts.** `Turing.catalog_transfer_trace`, `Turing.catalog_space_bound`, `Turing.catalog_space_one`.
