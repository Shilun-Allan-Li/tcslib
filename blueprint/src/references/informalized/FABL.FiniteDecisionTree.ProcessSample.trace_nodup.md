<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.ProcessSample.trace_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Repeated Queries in a Trace

**Claim.** A process sample's trace contains no repeated coordinate.

**Proof.** By the sample's defining trace condition, its trace is exactly the query trace of $T$ on the sample input. The query trace of a finite decision tree has no repetitions (the tree's trace nodup property, `FABL.FiniteDecisionTree.queryTrace_nodup`). Substituting this trace into that property proves the claim.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_nodup`.
