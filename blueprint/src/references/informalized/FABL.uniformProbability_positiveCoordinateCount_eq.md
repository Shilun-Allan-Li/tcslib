<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.uniformProbability_positiveCoordinateCount_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-coordinate count distribution

**Claim.** For a uniformly chosen point of the $k$-dimensional sign cube, the probability of having exactly $r$ positive coordinates is $\binom{k}{r}/2^k$.

**Proof.** The uniform probability is the number of cube points with exactly $r$ positive coordinates divided by the cube's size. Identify each sign vector with the subset of coordinates where it equals $1$. Under this identification, the size of that subset is the positive-coordinate count (`FABL.signCubeEquivFinset_apply_card`), and the identification is a bijection, so it preserves the count of points. The qualifying subsets are exactly the $r$-element subsets of a $k$-element set; there are $\binom{k}{r}$ of them. Since the cube has $2^k$ points, the claimed ratio follows.

**Key facts.** `FABL.signCubeEquivFinset_apply_card`.
