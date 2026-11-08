<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.transferTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Behavior of the Transfer Machine

**Claim.** After $2|w|+2$ steps, the transfer machine is done, with the source word erased and copied to the destination tape, and every other tape cell unchanged. It does not enter the done phase earlier, and the source and destination heads remain within the stated bounds while all other heads stay fixed.

**Proof.** Use the explicit run description supplied by the transfer trace lemma (Turing.catalog_transfer_trace). It expresses the run at every time as a staged trace: a forward sweep copying the source word to the destination, a transfer and rewind phase that erases the source, and a final return to the done phase. Evaluating this trace at $2|w|+2$ gives the stated final configuration: the source interval is blank, the destination interval contains the buffer for $w$, and cells outside those intervals retain their original contents. The trace’s phase conditions show that done cannot occur before this time. Its head-position descriptions put the two active heads between one cell left of their initial positions and $|w|$ cells right of them; the other heads do not move. The initial state and source-buffer hypothesis are precisely the assumptions used to instantiate the trace description.

**Key facts.** `Turing.catalog_transfer_trace`.
