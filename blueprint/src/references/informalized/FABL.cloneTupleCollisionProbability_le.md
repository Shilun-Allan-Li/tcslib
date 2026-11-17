<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.cloneTupleCollisionProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision probability for random tuples

**Claim.** For $M>0$, a uniformly chosen function from an $r$-element set to an $M$-element set fails to be injective with probability at most $r^2/M$.

**Proof.** For each function, assign an indicator to every ordered pair of inputs: it is $1$ when the inputs are distinct but have the same image, and $0$ otherwise. If the function is injective, its failure indicator is zero and is bounded by the sum of these pair indicators. If it is not injective, some distinct pair has equal images, so the sum is at least one and again bounds the failure indicator. Taking expectations preserves this inequality. Interchanging the finite sums and the expectation expresses the resulting bound as the sum of the pairwise collision probabilities. For each distinct pair, the probability that their images agree is $1/M$ (\texttt{uniformCloneTuple\_pair\_eq\_probability}); equal inputs contribute zero. There are at most $r^2$ ordered pairs, so the sum is at most $r^2/M$.

**Key facts.** `FABL.uniformCloneTuple_pair_eq_probability`.
