<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.costProjection_le_of_mem_support_sequence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Bound for a Sequence of Programs

**Claim.** If an additive natural-number cost projection vanishes at zero and is at most $B$ on every supported outcome of each program in a finite sequence, then it is at most the sequence length times $B$ on every supported outcome of the whole sequence.

**Proof.** Proceed by induction on the list of programs. For the empty list, the sequence returns the empty output with zero cost, so the projection is zero by its value at zero. For a nonempty list, write it as a head program followed by a tail list. The sequence-run formula (`runWithCost_sequence_cons`) expresses its law by first running the head, then running the sequence of the tail, and combining the two outcomes with their costs added. Membership in the support of this bind yields a supported head outcome and a supported mapped tail outcome; unpacking the map gives a supported tail outcome whose cost is added to the head cost. The componentwise support bound applies to the head, while the induction hypothesis applies to the tail, since every program in the tail also occurs in the full list. Additivity of the projection turns the projection of the combined cost into the sum of these two projections. They are bounded by $B$ and by the tail length times $B$, respectively, so their sum is at most $(1+\text{tail length})B$, which is the length of the full list times $B$.

**Key facts.** `FABL.LearningProgram.runWithCost_sequence_cons`.
