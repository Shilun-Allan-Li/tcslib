<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.copyTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used During Copying

**Claim.** At every time, the copying run visits at most $|w_{\mathrm{src}}|+2$ cells on the source and destination tapes, while each other tape visits exactly one cell.

**Proof.** First apply the copying-trace formula (Turing.catalog_copy_trace) to the initial configuration. Its source-tape hypothesis holds because the initial source tape is the buffer representation of $w_{\mathrm{src}}$. The trace description, simplified in its forward and return cases, bounds every head position on the source and destination tapes between $-1$ and $|w_{\mathrm{src}}|$, relative to their initial positions, and shows that every other head remains at position zero. A head whose positions all lie in this integer interval can visit at most $|w_{\mathrm{src}}|+2$ distinct cells, by the general space bound for heads confined to such an interval (Turing.catalog_space_bound). For any tape other than source and destination, the fixed head position means that exactly one cell is visited, by the fixed-head space fact (Turing.catalog_space_one).

**Key facts.** `Turing.catalog_copy_trace`, `Turing.catalog_space_bound`, `Turing.catalog_space_one`.
