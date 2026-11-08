<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.transProb_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Transition Probability

**Claim.** For a regular multigraph of positive degree, the probability that a one-step walk from $u$ ends at $v$ is the multiplicity of the edge from $u$ to $v$ divided by $D$.

**Proof.** A one-step transition is the neighbor average of the zero-step transition probabilities (`Randomized.RegularMultigraph.transProb_succ`). At zero steps, the probability from a vertex $x$ to $v$ is $1$ if $x=v$ and $0$ otherwise (`Randomized.RegularMultigraph.transProb_zero`). Thus the neighbor sum counts exactly the indices whose neighbor of $u$ is $v$; this count is the edge multiplicity. Dividing by the degree gives the stated formula.

**Key facts.** `Randomized.RegularMultigraph.transProb_succ`, `Randomized.RegularMultigraph.transProb_zero`.
