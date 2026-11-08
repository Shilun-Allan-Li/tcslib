<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.uniformExcess_walkDist_two_mul_le_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary Uniform-Excess Bound

**Claim.** For a connected, nonbipartite finite regular multigraph of positive degree with a nonempty vertex set, every transition probability over $2|V|$ steps is at least $1/D^{2|V|}$. Consequently, $|V|/D^{2|V|}\le1$, and every probability function contracts uniform excess by the factor $1-|V|/D^{2|V|}$ over those steps.

**Proof.** The lower bound on each $2|V|$-step transition probability is supplied by `one_div_pow_le_transProb_two_mul`. Fix a vertex $v$; summing this lower bound over all starting vertices $u$ gives $|V|/D^{2|V|}\le1$, because the column of transition probabilities sums to $1` (`sum_transProb_left`). Finally apply the minorant contraction bound (`uniformExcess_le_of_minorant`) to the $2|V|$-step transition matrix, using its column sums of $1$ and the common entrywise lower bound $1/D^{2|V|}$. This gives the asserted uniform-excess estimate for every probability function.

**Key facts.** `Randomized.RegularMultigraph.one_div_pow_le_transProb_two_mul`, `Randomized.RegularMultigraph.sum_transProb_left`, `Randomized.uniformExcess_le_of_minorant`.
