<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.uniform_stationary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Stationary Mass Identity

**Claim.** For a regular multigraph of positive degree on a finite vertex set, the total incoming transition weight at any vertex, when each source vertex is weighted uniformly, is again the uniform mass.

**Proof.** Let $D$ be the degree and fix a vertex $v$. Since $D>0$, its rational image is nonzero. Factor the constant $1/|V|$ out of the sum and combine the quotients to obtain
\[
\frac{1}{|V|}\cdot\frac{\sum_u \mathrm{mult}(u,v)}{D}.
\]
The total multiplicity of incoming neighbor indices is $D$ by the incoming-multiplicity identity (`Randomized.RegularMultigraph.sum_mult_left`). Thus the remaining quotient is $D/D=1$, giving $1/|V|$.

**Key facts.** `Randomized.RegularMultigraph.sum_mult_left`.
