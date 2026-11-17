<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitTail.totalInfluence_evalFunction_eq_zero_of_width_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Influence at Width Zero

**Claim.** If every input function has a gate-appropriate normal form of width at most zero, then the function computed by the circuit tail has total influence zero.

**Proof.** For each input function, the width-zero normal-form fact says it is constant; choose its constant sign. The circuit evaluation fact for constant inputs then supplies a constant sign for the function computed by the whole tail. After converting that sign to a real-valued function, the result is still constant. A constant function has zero total influence, by the constant-function influence identity.

**Key facts.** `FABL.CircuitGate.exists_eq_const_of_hasWidthLE_zero`, `FABL.CircuitTail.exists_eq_const_evalFunction_of_values`, `FABL.totalInfluence_const`.
