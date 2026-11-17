<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedAdmin_clock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock-Lane Administrative Action

**Claim.** For any timed control state $q$, optional Boolean value $b$, and movement sign $d$, the administrative action with successor state $q$, clock-lane instruction $(b,d)$, and no buffer-lane instruction equals the single-lane action on lane $4$ with that write and movement.

**Proof.** Both actions have input movement zero, no output, and successor state $q$. For each of the six work lanes, the administrative action assigns the default no-write, zero-movement instruction except at lane $4$, where it assigns $(b,d)$. This is exactly the instruction specified by the single-lane action, so the actions are equal.
