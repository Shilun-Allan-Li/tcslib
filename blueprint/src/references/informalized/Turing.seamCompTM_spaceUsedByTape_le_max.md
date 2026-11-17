<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_spaceUsedByTape_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Space on One Tape Under Composition

**Claim.** If one component run visits only cell $0$ on a given tape, then the composed run visits at most the larger of the two component runs’ visited-cell counts on that tape.

**Proof.** By the visited-cell inclusion theorem (`seamCompTM_visitedByTapeHead`), the composed run’s visited cells lie in the union of the two component runs’ visited-cell sets. Each run includes cell $0$, since it is the head’s initial position. If the first set is the singleton $\{0\}$, it is contained in the second set, so their union is just the second set; inclusion and cardinality monotonicity bound the composed count by the second count, hence by the maximum. If instead the second set is $\{0\}$, the union is the first set and the same reasoning bounds the count by the first count, hence by the maximum.

**Key facts.** `Turing.seamCompTM_visitedByTapeHead`.
