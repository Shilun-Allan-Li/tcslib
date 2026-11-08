<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Commutes with Tape Embedding

**Claim.** Running the embedded machine for $t$ steps from the embedded configuration gives exactly the embedding of the configuration reached by the original machine after $t$ steps.

**Proof.** The one-step identity `Turing.embedEmit_step` says that embedding a configuration and then taking one step of the embedded machine gives the same result as first taking one original step and then embedding. The iteration principle `Turing.MultiTapeTM.runFrom_comm_of_step` lifts this one-step commutation to every natural number of steps. Applying it to the embedding map, initial configuration, and time $t$ proves the equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.embedEmit_step`.
