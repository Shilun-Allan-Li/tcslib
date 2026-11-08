<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.spaceUsed_eq_spaceUsedOfCfgs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space of the Computation Trace

**Claim.** The total number of distinct work-tape cells visited from the initial configuration through step $t$ equals the total number of distinct work-tape head positions occurring in the configurations at steps $0$ through $t$.

**Proof.** For each tape, the visited positions are obtained by taking the image of the step indices $0,\ldots,t$ under the map sending an index to that tape's head position in the corresponding configuration. The trace list is the same configurations indexed from $0$ through $t$; mapping the list to head positions and then taking its associated finite set therefore gives exactly the same set of positions. Thus the per-tape finite sets agree, so their cardinalities agree. Summing these equalities over all tapes proves the claimed equality of total space.
