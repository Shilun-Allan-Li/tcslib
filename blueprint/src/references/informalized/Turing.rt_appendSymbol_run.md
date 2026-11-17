<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_appendSymbol_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Appending of a Symbol

**Claim.** The constructed machine appends one symbol to the specified tape word, reaches its exit state at the stated time and not earlier, and keeps its work-tape heads within the asserted bound.

**Proof.** First let the machine scan right across $w$. The scan lemma (`Turing.skipTM_run_ofCfg`) places the head just past the word, reaches its designated boundary state for the first time, and bounds its head motion. Next, the three-step boundary machine (`Turing.rt_boundary_run`) moves left once, writes $b$ in the cell immediately before the scan endpoint, then moves right once. The resulting tape agrees locally with the buffer for $w\mathbin{++}[b]$: this follows from the list-append buffer identity (`Turing.FinTM.bufferTape_append`), while the original tape values remain at all other cells. The head is now at the far end of the enlarged word. The backward-scan lemma (`Turing.skipBackTM_run_ofCfg`) returns across that word to its starting boundary and reaches its exit state for the first time. The intermediate head bounds from these three phases give the claimed overall bound. Finally, the two seam applications (`Turing.rt_copy_seam`) combine the phases into the composite machine, preserving their first-arrival exit properties and head bounds; adding the phase lengths gives $2|w|+10$. The phase endpoint descriptions yield the claimed final configuration.

**Key facts.** `Turing.skipTM_run_ofCfg`, `Turing.rt_boundary_run`, `Turing.FinTM.bufferTape_append`, `Turing.skipBackTM_run_ofCfg`, `Turing.rt_copy_seam`.
