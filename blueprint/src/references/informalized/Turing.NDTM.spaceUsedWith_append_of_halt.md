<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean :: Turing.NDTM.spaceUsedWith_append_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Usage After Halting

**Claim.** If the run from a configuration under a choice word has empty state, then appending any further choice word leaves its space usage unchanged.

**Proof.** Fix a work tape. Its visited positions under the concatenated word form a finite set. To show this set equals the one for the original word, prove both inclusions. Every position visited at a prefix length $j\le |w|$ is already visited under $w$: the first $j$ choices of $w w'$ are the first $j$ choices of $w$. If instead $j>|w|$, the prefix has already completed $w$. The run is then halted, and remains at that configuration through every additional choice: this follows from the run concatenation law (`runWith_append`) and the fact that a halted configuration is fixed by every continuation (`runWith_of_halt`). Thus its work-tape head position is the position at time $|w|$, which was included among the positions visited under $w$. This proves that every position in the longer run's visited set belongs to the shorter run's set. The reverse inclusion follows because every prefix of $w$ is also a prefix of $w w'$; formally, this is the visited-set inclusion (`visitedWith_subset_append`). Hence the two visited sets agree on each tape, so their cardinalities agree. Summing these cardinalities over all work tapes gives the asserted equality of space usage.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`, `Turing.NDTM.visitedWith_subset_append`.
