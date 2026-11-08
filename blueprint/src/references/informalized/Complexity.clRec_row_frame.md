<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_row_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Frame During Row Copying

**Claim.** Placing the row configuration on the recorder's selected tapes, with control state corresponding to the source state, tag, and row state $(i,q)$, reproduces exactly the recorder configuration with that row state.

**Proof.** The two configurations have the same control state and input-head position by construction, and both have empty output. It remains to compare work tapes and head positions. The placement sends the row copier's first $F$ tapes to the recorder's counter tapes and its final tape to the record buffer. On the counter tapes, the row configuration stores the binary words for the counts $n$; the recorder configuration stores those same words. On the record-buffer tape, both store the given record. The other recorder tapes retain their original contents and head positions under the placement. Splitting the tape indices into these regions shows that contents and head positions agree everywhere, so the configurations are equal.
