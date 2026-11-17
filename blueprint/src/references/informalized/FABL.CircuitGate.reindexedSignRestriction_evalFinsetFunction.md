<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitGate.reindexedSignRestriction_evalFinsetFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction commutes with finite gate evaluation

**Claim.** Restricting the result of applying a gate to a finite set of input functions gives the same function as first restricting each input function and then applying the gate to that set.

**Proof.** At each free-coordinate input, both sides evaluate the gate on the same selected signs: on the left, restriction first completes the full input by inserting the fixed signs and then evaluates each selected function; on the right, each selected function is evaluated on that very same completed input before the gate is applied. Thus the pointwise values agree for either gate, so the functions are equal.
