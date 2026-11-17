<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.queryCount_nandAllTrue_eq_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Query Count on the All-Negative Input

**Claim.** A finite decision tree computing NAND on two sign coordinates makes exactly two queries on the input where both coordinates are $-1$.

**Proof.** For each coordinate $i$, change only that coordinate of the all-negative input to $1$. The resulting input has a different NAND value: the original evaluates to $1$, while the modified input evaluates to $-1$. Since the two inputs differ only at $i$, the decision-tree sensitivity fact says that coordinate $i$ must occur in the query trace on the original input (`mem_queryTrace_of_eval_ne_of_agreeExcept`). This applies to both coordinates, so the query set on that input is the full two-element coordinate set. The cardinality of the query set equals the query count (`card_querySet_eq_queryCount`), and therefore the count is $2$.

**Key facts.** `FABL.FiniteDecisionTree.mem_queryTrace_of_eval_ne_of_agreeExcept`, `FABL.FiniteDecisionTree.card_querySet_eq_queryCount`.
