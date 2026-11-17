<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Turing.FinTM.k_le_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work tape count and space usage

**Claim.** The number of work tapes is at most the total number of distinct work-tape cells visited through step $t$ from the initial configuration.

**Proof.** Write the number of tapes as the sum of $1$ over all tape indices. For each tape, the set of head positions visited through time $t$ is nonempty: it includes the position at time zero. Its cardinality is therefore at least one. Summing these inequalities over the tape indices gives the desired bound by the definition of total space used.
