<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.runWithCost_queriedRandomExampleBatchProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queried random batch run law

**Claim.** The queried random batch program draws a uniform sequence of cube inputs and returns their labels under the target, with cost $(0,m,mn+m)$.

**Proof.** The program first draws a uniform batch of $m$ inputs, then runs the queried input-batch program on that batch. The batch run law contributes $mn$ units of work for generating the inputs. The query-batch run theorem says the labels are then determined by the target and the querying phase has cost $(0,m,m)$. Combining these contributions gives $m$ queries and total work $mn+m$, with no random-example calls. Thus the law is the uniform input-batch law mapped to the labeled sequence and this fixed cost.

**Key facts.** `FABL.LearningCost.toTriple_injective`, `FABL.runWithCost_queryInputBatchProgram`.
