<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_transfer_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace of a Tape Transfer

**Claim.** For distinct selected tapes satisfying the stated source-content condition, the transfer machine follows the specified forward-copy, return-and-erase, and done-phase trace, with the stated final configuration.

**Proof.** First, at forward-pass index $0$, the proposed trace configuration is the starting configuration: the phase agrees by the state hypothesis, and the zero-length copied segment changes neither tape contents nor head positions. For each index before the word's length, the forward-copy step lemma (`Turing.catalog_copy_forward`) advances the trace by one: it copies the source symbol to the destination and advances the selected heads. At the end of this pass the source head reads blank, by the source-content hypothesis at offset $|w|$. The transfer machine therefore switches to the rewind phase; unfolding its action shows that the resulting configuration is the return trace at index $|w|$. For each positive return index up to the word length, the source head reads the corresponding symbol of $w$, so the machine erases that source cell and moves both heads back one position, producing the preceding return-trace configuration. At return index zero, the source head reads blank by the hypothesis at offset $-1$; the machine enters the done phase and moves the selected heads forward as specified by the trace's exit configuration. This exit configuration is fixed by the done-phase transition. The prescribed-trace theorem (`Turing.catalog_trace_run`), applied to these forward, turn, return, entry, and fixed-point facts, now gives the claimed run at every time.

**Key facts.** `Turing.catalog_copy_forward`, `Turing.catalog_trace_run`.
