<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_row_inactive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of the Inactive Row Frame

**Claim.** For any two record words and any two row-copying control states, relocating the same row configuration into the designated tapes gives the same configuration, provided the other data and tape contents are fixed.

**Proof.** The relocated configurations have the same control state, input-head position, and output. Their work-tape contents and head positions are determined by the selected row configuration on the designated row tapes and by the unchanged recorder data on the remaining tapes. The record word and row control state affect only the record-buffer tape and the row machine's state; the row placement designates the row machine's tapes, while the recorder's record buffer lies outside those selected tapes. Consequently, changing either record word or row control state changes no work-tape contents or head positions in the relocated row configuration. Comparing the tape regions therefore gives equality of the configurations.

**Caveat.** The supplied definition of the row placement appears to select the first $F$ recorder tapes and the record-buffer tape. The proof source unfolds this placement directly; its invariance assertion follows from that tape-index calculation.
