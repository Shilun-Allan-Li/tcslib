<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbols Under Encoding

**Claim.** For a configuration on the input obtained by encoding each bit of $x$, mapping its possibly blank input symbol through $e$ gives the possibly blank input symbol in the original configuration.

**Proof.** The encoded configuration has the same input-head position as the original one, and the encoded input has the same length. If the head is at the left boundary or the right boundary, both input-symbol readings are blank, so mapping the encoded blank through $e$ still gives blank. At any other position, both readings select corresponding entries of the two inputs, which are related by the entrywise map $e$. Thus the mapped reading agrees in every case.
