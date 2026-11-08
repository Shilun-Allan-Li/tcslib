<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.mem_queryTrace_of_eval_ne_of_agreeExcept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Different Outputs Force a Query

**Claim.** If two inputs differ only at coordinate $i$ and the tree returns different outputs on them, then its query trace on the first input contains $i$.

**Proof.** Induct on the tree. At a leaf, both inputs produce the same label, contradicting the assumed difference. At a query node with coordinate $c$, if $i=c$, the trace contains $i$ immediately. Otherwise, the inputs agree at $c$, so the first query selects the same child on both inputs. The evaluations in that child still differ, and the inputs still agree away from $i$. The induction hypothesis applied to that child shows that its trace on the first input contains $i$; this is therefore also true of the original trace.
