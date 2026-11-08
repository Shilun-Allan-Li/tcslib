<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.computesInTime_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of timed computation

**Claim.** A finite Turing machine computes $w$ from $x$ within $t$ steps exactly when its configuration after $t$ steps from the initial configuration on $x$ is halted and its output is $w$.

**Proof.** By definition, timed computation supplies a space value together with three properties: the run is halted, its output is $w$, and its space use equals that value. Forgetting the space equality yields the halted-state and output conditions. Conversely, if those two conditions hold, take the space value to be the actual space used by the run. Its equality with itself supplies the remaining condition in the definition.
