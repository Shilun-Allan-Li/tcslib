<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_succ_eq_step' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Run and One Further Step

**Claim.** The configuration reached after $t+1$ oracle-machine steps is obtained by taking one step from the configuration reached after $t$ steps.

**Proof.** The run is defined by iterating the one-step transition function. The iterate successor identity states that applying the function $t+1$ times is the same as applying it once more after $t$ iterations; this is precisely the asserted equation.
