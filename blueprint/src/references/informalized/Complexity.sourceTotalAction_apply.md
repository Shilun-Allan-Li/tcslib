<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.sourceTotalAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Totalized action gives one machine step

**Claim.** For every finite binary Turing machine and configuration, applying its totalized source action to that configuration gives exactly the configuration obtained by one machine step.

**Proof.** Split according to whether the configuration is already in the halting state. If its state is none, the totalized source action is the action that leaves every component unchanged: it has no writes, no head movement, no output, and no successor state. Applying it therefore returns the same configuration, which is also the machine’s stipulated behavior in the halting state. If the state is some $q$, the totalized action is exactly the transition action for $q$, supplied with the symbols currently read on the input and work tapes. Applying that action is the definition of the machine’s step in state $q$, so the resulting configurations agree.
