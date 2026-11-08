<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.localExpectedValue_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value of a Pure Assignment

**Claim.** When each variable is independently fixed to its assigned label, the expected normalized value equals the value of that assignment.

**Proof.** For each constraint, the local expected satisfaction indicator under point masses at the assigned labels equals its satisfaction indicator for the assignment (`localExpectedIndicator_pure`). Summing this identity over the constraint multiset shows that the local expected count equals the assignment’s satisfied count; this sum identity follows by induction on the multiset, with the empty multiset immediate and the induction step adding the contribution of one constraint. Dividing both counts by the same nonzero constraint count gives equality of the normalized values.

**Key facts.** `FABL.CSPConstraint.localExpectedIndicator_pure`.
