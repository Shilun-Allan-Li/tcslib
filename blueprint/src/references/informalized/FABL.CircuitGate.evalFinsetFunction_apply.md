<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitGate.evalFinsetFunction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Gate Evaluation

**Claim.** Evaluating a gate on a family of Boolean functions at a cube point is the same as evaluating it on the functions’ values at that point.

**Proof.** The function obtained by applying the gate pointwise is defined at each input $x$ to be the gate applied to the signs $v_i(x)$, for the selected indices. Evaluating that function at $x$ therefore gives exactly the stated gate evaluation.
