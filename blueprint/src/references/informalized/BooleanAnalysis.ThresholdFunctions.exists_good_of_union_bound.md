<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.exists_good_of_union_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A point outside finitely many small events

**Claim.** If each event in a finite family has outer measure at most $B$ and the family size times $B$ is less than $1$, some point lies outside every event.

**Proof.** The measure of the union of the events is at most the sum of their measures, by finite subadditivity (`measureReal_iUnion_fintype_le`). Each summand is at most $B$, so the sum is at most $|\beta|B$. The hypothesis makes the union's measure strictly less than $1$. If no point lay outside all the events, their union would be the whole space, whose measure is $1$ in a probability space. This contradicts the strict bound, so a point outside every event exists.
