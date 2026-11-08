<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleCall.lean :: Turing.OracleTM.step_of_answerAction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Under a Fixed Answer Action

**Claim.** If the machine is in a non-query state whose transition always emits $b$ and has no successor state, one step leaves the input position, tapes, and head positions unchanged, sets the state to empty, and appends $b$ to the output.

**Proof.** Since the current state is $q$ and $q$ is not the query state, the machine uses its transition action. By hypothesis this action is the answer action for $b$, regardless of the scanned symbols. That action has no successor state, does not move any head, and makes no tape writes; its only output is $b$. Applying it therefore preserves the input position, tape contents, and work-tape head positions, sets the state to empty, and appends the one-symbol list $[b]$ to the existing output.
