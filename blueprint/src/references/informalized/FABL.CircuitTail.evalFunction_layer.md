<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitTail.evalFunction_layer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layered Circuit Evaluation

**Claim.** Evaluating a layered circuit tail pointwise is the same as evaluating its remaining tail with the dual gate on the functions produced by applying the chosen gate to each listed input set.

**Proof.** Both sides are definitionally the same function. At each cube point, evaluation of the layered tail applies the remaining tail to the dual gate and assigns to each of its inputs the chosen gate applied to the corresponding listed inputs. This is exactly the pointwise meaning of the right-hand side.
