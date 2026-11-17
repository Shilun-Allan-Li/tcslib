<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.map_output_eq_of_mem_support_sequence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Keys of supported sequence outputs

**Claim.** If every outcome in the support of the program indexed by an item has output whose key is that item, then every supported outcome of the sequence of programs indexed by a finite list has an output list whose keys, in order, are that list.

**Proof.** Proceed by induction on the indexing list. For the empty list, the sequence returns the empty output list, so the claimed equality holds. For a list with head $i$ and tail $L$, the sequence outcome law is the bind of the head program’s law with the tail sequence’s law, and the resulting output is the head output consed onto the tail output; this decomposition is given by \texttt{runWithCost\_sequence\_cons}. Membership in the support of a bind yields a supported head outcome and a supported continuation outcome. The latter is the image of a supported tail-sequence outcome under the map that conses the head output, so support membership for a map supplies such a tail outcome. The hypothesis on keys identifies the head output’s key as $i$, while the induction hypothesis identifies the keys of the tail output as $L$. Therefore the full key list is $i::L$.

**Key facts.** `FABL.LearningProgram.runWithCost_sequence_cons`.
