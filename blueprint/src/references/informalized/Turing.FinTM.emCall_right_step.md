<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Simulation of the Wrapper

**Claim.** For a live source configuration, one step of the right-boundary wrapper from its embedding equals the embedding of the source machine's one-step successor.

**Proof.** Split according to the source configuration's state. The case where it is absent contradicts the hypothesis that the configuration is live. If its state is $q$, the embedded configuration is in the wrapper's source-machine state corresponding to $q$. In that state the wrapper uses exactly the source transition, with its successor state embedded into the wrapper state space (including the designated fallback when the source transition halts). Consequently the wrapper's step agrees component by component with embedding the source machine's step.
