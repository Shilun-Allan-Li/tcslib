<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.sum_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Neighbor Sum

**Claim.** For a finite regular multigraph and any rational-valued function of two vertices, summing over vertices and their indexed neighbors is unchanged when the two vertex arguments are interchanged.

**Proof.** First express each indexed-neighbor sum as a sum over all vertices, weighted by the multiplicity of the corresponding edge; this is the neighbor-sum counting formula (`Randomized.RegularMultigraph.sum_nbr_eq`). Interchange the two finite vertex sums. The resulting terms have the edge multiplicity in the reverse direction, which equals the original multiplicity by symmetry of the multigraph. Thus the total is unchanged when the arguments of the function are interchanged.

**Key facts.** `Randomized.RegularMultigraph.sum_nbr_eq`.
