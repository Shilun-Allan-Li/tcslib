<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_guard_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Guarded Run Segments

**Claim.** If the run from $c$ avoids state $q$ before time $a$, reaches $d$ at time $a$, and the run from $d$ avoids $q$ before time $b$, then the run from $c$ avoids $q$ before time $a+b$.

**Proof.** Fix $v<a+b$. If $v<a$, the first avoidance assumption applies directly. Otherwise write $v=a+(v-a)$. The run composition law (`runFrom_add`), together with the fact that the run from $c$ reaches $d$ at time $a$, identifies the configuration at time $v$ with the configuration reached from $d$ after $v-a$ steps. Since $v<a+b$, we have $v-a<b$, so the second avoidance assumption applies.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
