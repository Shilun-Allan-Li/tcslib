<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.uniformProbability_exists_positiveCoordinateCount_eq_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Coordinate-Count Interval

**Claim.** For nonnegative integers $m,a,k$, the uniform probability that a sign vector in $\{-1,1\}^m$ has between $a$ and $a+k-1$ positive coordinates, inclusive, is $\displaystyle\sum_{j=0}^{k-1}\frac{\binom{m}{a+j}}{2^m}$.

**Proof.** The event that the positive-coordinate count equals $a+j$ for some $j<k$ is the disjoint union, over $j=0,\ldots,k-1$, of the events that the count equals $a+j$. Disjointness follows because distinct values of $j$ give distinct counts. Therefore its probability is the sum of the probabilities of those individual events. For a prescribed count $r$, there are $\binom mr$ sign vectors with exactly $r$ positive coordinates among the $2^m$ total vectors, so that event has probability $\binom mr/2^m$ (\texttt{uniformProbability\_positiveCoordinateCount\_eq}). Substituting $r=a+j$ yields the formula.

**Key facts.** `FABL.uniformProbability_positiveCoordinateCount_eq`.
