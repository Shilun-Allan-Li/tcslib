<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStop_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step of the Call-Stopping Wrapper

**Claim.** When the original configuration is live and is not in the exit state if the flag is raised, one wrapper step from the configuration with flag $b$ gives the configuration obtained by taking one original-machine step and raising the flag.

**Proof.** Split on the state of the original configuration. If it is the halting state, the assumed liveness is contradicted. Otherwise it is some state $q$. The condition that would trigger the wrapper's stopping action—flag raised and state equal to the exit state—is impossible: if the flag is raised, the hypothesis rules out that state, while if it is not raised the trigger already fails. Thus the wrapper uses the original transition, changing only the state label by adjoining the raised flag. The other configuration components are exactly those produced by the original step, proving the equality.
