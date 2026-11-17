<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.runWithCost_queryInputBatchProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Query Batch

**Claim.** For any fixed inputs, the query batch program returns the sequence pairing each input with its target value, with probability one and cost $(0,m,m)$.

**Proof.** Proceed by induction on $m$. When $m=0$, the program is pure and returns the unique function on the empty index set; its cost is zero. For the induction step, the program first queries the target at the first input. The query answer is therefore its target value, and the query adds cost $(0,1,1)$. The remaining program handles the tail of the input sequence. By the induction hypothesis its output pairs each tail input with its target value, at cost $(0,m,m)$. Mapping this output by adjoining the first pair preserves the cost and gives the required full sequence. The costs add to $(0,m+1,m+1)$, and the output agrees pointwise with the desired function, separating the first index from the tail.

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.LearningCost.toTriple_injective`.
