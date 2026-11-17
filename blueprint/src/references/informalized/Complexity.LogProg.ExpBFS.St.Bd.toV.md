<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.Bd.toV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on State Coordinates

**Claim.** If each of the 17 counters of a state is at most $B$, then every coordinate of its state vector is at most $B$.

**Proof.** Unpack the hypothesis into the 17 individual bounds, one for each counter. Now fix a coordinate of the state vector. Its index lies among $0,1,\ldots,16$; checking these finitely many possibilities identifies the coordinate with the corresponding counter in the listed order. The bound for that counter, among the unpacked hypotheses, gives the desired inequality.
