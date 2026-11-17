<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Work-Tape Reads

**Claim.** For each original work tape, decoding the symbol under its head in the clock-stage configuration gives the possibly blank symbol under the corresponding head of $c$.

**Proof.** Fix an original tape index. In the clock-stage configuration, that tape's contents are obtained by mapping each symbol of $c$ to its tagged-bit encoding, and its head position is unchanged. Evaluating at that position and applying the decoder therefore returns the original symbol if the cell is occupied and blank if it is empty. This proves equality of the read functions at every tape index.
