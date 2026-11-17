<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.sum_mult_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Incoming Multiplicity

**Claim.** For a finite regular multigraph of degree $D$ and a vertex $v$, the sum over vertices $u$ of the number of neighbor indices at which $u$ points to $v$ equals $D$.

**Proof.** Apply the neighbor counting identity (`sum_nbr_eq`) at $v$ to the constant function with value $1$. The sum over the $D$ indices is then $D$, while the right side is the sum over all vertices $u$ of the multiplicity of indices leading from $v$ to $u$. Symmetry of multiplicity in a regular multigraph identifies this with the sum of multiplicities leading from each $u$ to $v$, proving the result.

**Key facts.** `Randomized.RegularMultigraph.sum_nbr_eq`.
