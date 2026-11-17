<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.clearTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing from a general configuration

**Claim.** Starting in the sweep state with the specified word on tape $i$, the clearing machine reaches the done state after $2|w|+2$ steps, has not reached done earlier, blanks the cells in the word’s interval while preserving all other cells, and keeps its heads within the stated bounds.

**Proof.** The proof first invokes the trace description (`catalog_clear_trace`): at every time, the actual run is the catalogued forward sweep followed by the return sweep, with the stated final configuration as its exit anchor. At time $2|w|+2$, the trace has completed both passes; unfolding its forward and return phases shows that the state is done and exactly the cells from the initial head position through the word’s last cell have been blanked. For any earlier time, the trace is in one of the sweep or rewind phases, so its state is not done. Finally, examining the trace’s head positions shows that the selected head remains between one cell left of its initial position and the right endpoint at distance $|w|$, inclusive; every other head remains fixed.

**Key facts.** `Turing.catalog_clear_trace`.
