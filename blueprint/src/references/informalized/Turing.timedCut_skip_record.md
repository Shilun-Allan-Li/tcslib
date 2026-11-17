<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_skip_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping One Serialized Record

**Claim.** After the interpreter skips the serialized record of an action, its table cursor is just past that record. Its state tape and state-tape cursor are unchanged, and its control either continues the skip request with the counter decreased by one or enters the destination continuation when the counter is zero.

**Proof.** The serialized record consists of eight fixed action bits followed by a unary state field: if the successor state has unary length $m$, the record length is $8+(m+1)$. First apply the fixed-field skipping result (`Turing.timedCut_skip_fixed`) for eight steps. This moves the table cursor to the start of the unary field and changes the control to unary skipping, without changing the state tape or its cursor. Then apply the unary skipping result (`Turing.timedCut_skip_unary`) to the $m$ ones and terminating zero. It advances the cursor by $m+1$ and makes precisely the required counter and destination transition. The run-composition law (`Turing.MultiTapeTM.runFrom_add`) combines these two runs into one of length equal to the record length; the cursor arithmetic gives the stated final position.

**Key facts.** `Turing.timedCut_skip_fixed`, `Turing.timedCut_skip_unary`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_record_shape`.
