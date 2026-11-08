<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitTail.exists_eq_const_evalFunction_of_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Inputs Yield Constant Output

**Claim.** If every input function is constant, then evaluating the circuit tail pointwise gives a constant Boolean function.

**Proof.** Proceed by induction on the circuit tail, allowing the gate to vary. For an output tail, take as the constant output the chosen gate applied to the input constants on the output's selected indices. At any cube point, each input function has its stipulated constant value, so the pointwise evaluation equals this sign. For a layered tail, define the constant assigned to each gate in the first layer by applying the chosen gate to the input constants on that gate's listed indices. Each gate function is then constant with this assigned value, since its inputs are constant. Apply the induction hypothesis to the remaining tail, using the dual gate and these gate functions. The layered evaluation identity (`FABL.CircuitTail.evalFunction_layer`) identifies this result with the evaluation of the original tail, which is therefore constant.

**Key facts.** `FABL.CircuitTail.evalFunction_layer`.
