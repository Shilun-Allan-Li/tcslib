<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_end_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from Scanning to Querying

**Claim.** For any language $B$, input $x$, buffer $u$, and choice bit $b$, one step from the scan configuration at position $|x|$ yields the query configuration with buffer $u$.

**Proof.** At position $|x|$, the input head is at the right boundary, so it reads no input symbol. The scan-state transition rule `uw_step_scan` therefore applies with a blank input symbol. Substituting this boundary reading into the machine's transition rule shows that the step moves into the query state without changing the stored buffer or output, and places the query head at the endpoint. Comparing the configuration fields gives precisely the query configuration with buffer $u$.

**Key facts.** `Complexity.uw_step_scan`.
