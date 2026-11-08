<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.prevSnapSrcs_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of previous-snapshot sources

**Claim.** When all blocks before instruction index $i$ have their prescribed configuration-expansion values and the snapshot index for time $t$ is below $i$, evaluating the sources for the snapshot immediately preceding time $t+1$ gives the encoding of the machine's snapshot at time $t$.

**Proof.** Compare the two lists entry by entry. At an index $j$ below the snapshot width, the source list at time $t+1$ selects the block source for the snapshot at time $t$ (the zero-time constant branch does not apply). Since that snapshot's instruction index is below $i$, `Complexity.eval_block` evaluates this source to bit $j$ of the corresponding configuration expansion. The index identity `Complexity.cfgExp_snapIdx` identifies that expansion with the snapshot expansion. By the definition of the snapshot expansion, its initial segment is the snapshot encoding; the bound on $j$ ensures the selected entry lies in that segment. Thus each list entry agrees, and the lists are equal.

**Key facts.** `Complexity.eval_block`, `Complexity.cfgExp_snapIdx`.
