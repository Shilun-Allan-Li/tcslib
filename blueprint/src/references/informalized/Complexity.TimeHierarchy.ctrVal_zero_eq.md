<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_zero_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Binary Value Characterization

**Claim.** If a Boolean list has binary value zero, then it is the list of false values of the same length.

**Proof.** Proceed by induction on the list. The empty list is the empty replication. For a list with head `true`, the value is at least one, contradicting that it is zero. Thus the head is `false`; the value equation then forces the tail to have value zero. By the induction hypothesis the tail is a list of false values, and adjoining the false head gives exactly the false list of the original length.
