<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitTail.evalFunction_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Layer Evaluation

**Claim.** Evaluating an output layer as a function gives the result of applying the chosen gate to the input functions at the selected indices.

**Proof.** At each point of the sign cube, evaluation of the output tail applies the chosen gate to the signs supplied by the input functions at that point. By definition, this is the value of the gate applied pointwise to those functions over the selected input indices. Thus the two functions agree at every point.
