<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Run Length

**Claim.** Running for $a+b$ steps gives the same configuration as running for $a$ steps and then for another $b$ steps.

**Proof.** A run of length $t$ is the $t$-fold iterate of the one-step update. The iterate law decomposes an iterate of length $b+a$ into first iterating $a$ times and then iterating $b$ times. Since $a+b=b+a$, this is exactly the stated equality.
