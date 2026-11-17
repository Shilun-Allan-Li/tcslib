<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitTail.extendedSignRestriction_evalFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Commutes with Circuit Evaluation

**Claim.** Applying an extended sign restriction to the function computed by a circuit tail agrees with evaluating the tail on the individually restricted input functions.

**Proof.** Fix a point of the full sign cube and evaluate both sides there. The left side first assembles the restricted coordinates into a cube point and evaluates the circuit there. The right side restricts each input function using that same assembled point, then evaluates the circuit. Since circuit evaluation is defined by applying its gates to the input values pointwise, both expressions reduce directly to the same evaluation of the tail at the assembled point.

**Caveat.** The supplied informal statement describes random restrictions but does not state this theorem. The claim and proof follow the formal statement and proof source, which concern commutation of extended sign restriction with circuit evaluation.
