<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.exists_le_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A cube above every natural number

**Claim.** For every natural number $n$, some natural number $s$ satisfies $n\le s^3$.

**Proof.** Take $s=n$. Since $n\ge1$ implies $n^3\ge n$, and the case $n=0$ is immediate, this choice satisfies the inequality for every natural number.
