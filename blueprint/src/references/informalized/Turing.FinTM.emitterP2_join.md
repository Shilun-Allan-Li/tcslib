<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Computation Runs

**Claim.** If running the machine from $c$ for $a$ steps reaches $d$, and running it from $d$ for $b$ steps reaches $e$, then running it from $c$ for $a+b$ steps reaches $e$.

**Proof.** The run composition law identifies the run from $c$ for $a+b$ steps with the run from the configuration reached after $a$ steps, run for a further $b$ steps. Substituting the two hypotheses gives the run from $d$ for $b$ steps, which is $e$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
