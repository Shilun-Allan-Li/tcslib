<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.ProcessSample.eval_eq_of_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Computed Function

**Claim.** If the tree computes $f$, then on the sample input its evaluation equals $f$ at that input.

**Proof.** The hypothesis that $T$ computes $f$ is the function equality $T.eval=f$. Evaluating both sides at the sample input gives $T.eval\,sample.input=f\,sample.input$, as required; the trace condition is not needed for this equality.
