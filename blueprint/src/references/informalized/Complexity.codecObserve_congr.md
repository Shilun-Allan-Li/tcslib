<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecObserve_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Observation from Core Data

**Claim.** If two configurations have equal core data and equal output summaries, then their Boolean observations agree at every encoded bit position.

**Proof.** Project the assumed equality of core summaries onto its two components. Equality of the first components gives equality of the configurations’ states, input-head positions, work-tape contents, and work-tape head positions. Equality of the second components gives equality of their output summaries. Now fix an encoded bit position and inspect its type. For input bits, both observations use the same input string; for input-head and state bits, the corresponding equal data make the equality tests agree. For work-tape bits, the observations compare the same tape contents or head positions, by the equal core data. For summary bits, they compare the same output summary. Thus the observations agree at every position.
