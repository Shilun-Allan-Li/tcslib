<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.rounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Enumeration Rounds

**Claim.** Under the output-length and counter-bit-length bounds, for each $i\le |f(x)|$ the enumerator has a finite run from its initial configuration to the configuration containing the first $i$ output bits, asking with counter $i$, and every earlier configuration has the prescribed shape.

**Proof.** Proceed by induction on $i$. For $i=0$, take a run of length zero: its endpoint is the initial configuration with empty output and counter zero, and there are no earlier times to check. For the successor step, use the induction hypothesis to run from the initial configuration to the asking configuration containing the first $i$ bits and counter $i$. Since $i<|f(x)|$, the one-round result (`round`) supplies a run from there to the configuration containing the first $i+1$ bits and counter $i+1$. Concatenate the runs using the run-addition law (`rrun_add`). Any time before the combined endpoint is either before the first run's endpoint, where the induction hypothesis gives the shape bound, or is a time in the second run after its starting configuration, where `round` gives that bound. This proves the induction step.

**Key facts.** `Complexity.LogProg.rrun_zero`, `Complexity.ImplicitEnum.round`, `Complexity.LogProg.rrun_add`.
