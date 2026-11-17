<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.randProb_padWalk_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Probability of an Inaccessible Vertex

**Claim.** Under the stated symmetry, padding, and encoding hypotheses, if there is no finite sequence of relation-steps from $s$ to $t$, then the probability that the decoded random walk of any length $k$ visits $t$ is zero.

**Proof.** First, the degree bound $n\le D$ ensures $D$ is positive, so the uniform slot choices used to define the walk are nonempty. The decoding identity (`Randomized.RegularMultigraph.randProb_hits_decodeIdx`) identifies the probability of visiting $t$ along the decoded Boolean blocks with the $k$-step hitting probability in the padded regular graph. In that graph, the reachability equivalence (`Randomized.padGraph_reflTransGen_iff`) says that a path from $s$ to $t$ exists exactly when a path in the original relation exists. By hypothesis there is no such path, so the padded graph's hitting probability is zero by the zero-hitting-probability theorem for unreachable vertices (`Randomized.RegularMultigraph.hitProb_eq_zero_of_not_reachable`).

**Key facts.** `Randomized.RegularMultigraph.randProb_hits_decodeIdx`, `Randomized.padGraph_reflTransGen_iff`, `Randomized.RegularMultigraph.hitProb_eq_zero_of_not_reachable`.
