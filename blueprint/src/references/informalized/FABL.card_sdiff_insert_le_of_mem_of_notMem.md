<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.card_sdiff_insert_le_of_mem_of_notMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality after removing an inserted index

**Claim.** If $i\in J$, $i\notin P$, and $|J\setminus P|\le f+1$, then $|J\setminus(P\cup\{i\})|\le f$.

**Proof.** The hypotheses imply $i\in J\setminus P$. Removing $i$ from $P$'s complement within $J$ therefore removes one element: $J\setminus(P\cup\{i\})=(J\setminus P)\setminus\{i\}$. Its cardinality is consequently $|J\setminus P|-1$, which is at most $f$ because $|J\setminus P|\le f+1$.
