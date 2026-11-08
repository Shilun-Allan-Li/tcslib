<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_guard_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Guarded Run Segments

**Claim.** If the run from $c$ avoids state $q$ before time $a$, reaches $d$ at time $a$, and the run from $d$ avoids $q$ before time $b$, then the run from $c$ avoids $q$ before time $a+b$.

**Proof.** Fix $v<a+b$. If $v<a$, the first avoidance hypothesis applies directly. Otherwise $a\le v$, so write $v=a+(v-a)$. By the run composition law, the configuration at time $v$ from $c$ is obtained by running for $v-a$ steps from the configuration at time $a$. That configuration is $d$, so the state at time $v$ is the state of the run from $d$ at time $v-a$. Since $v-a<b$, the second avoidance hypothesis excludes state $q$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
