<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSafe_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Anchor-Free Runs

**Claim.** If the run from $c$ avoids state $a$ through time $u$, and the run starting from the configuration reached at time $u$ avoids $a$ through time $v$, then the run from $c$ avoids $a$ through time $u+v$.

**Proof.** Take any time $j\le u+v$. If $j\le u$, the first avoidance hypothesis applies directly. Otherwise write $j=u+(j-u)$, where $j-u\le v$. The run-composition identity (`runFrom_add`) identifies the configuration at time $j$ from $c$ with the configuration at time $j-u$ from the configuration reached at time $u$. The second avoidance hypothesis therefore excludes state $a$ at time $j$ as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
