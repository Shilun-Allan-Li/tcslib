<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_card_remainingPartSlice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting vertices by part

**Claim.** For a finite set of vertices partitioned by their part labels, the sum over all parts of the number of vertices in each part equals the total number of vertices.

**Proof.** For each part, express the size of its slice as a sum over vertices in $R$: a vertex contributes $1$ if its part label is the chosen part, and $0$ otherwise. Interchange the two finite sums. For each vertex, exactly one part label matches its own, so its contributions across all parts sum to $1$. Summing these contributions over all vertices gives $|R|.
