<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clInput_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Arrival at the Return Configuration

**Claim.** For every Boolean word $x$, there is a time $t$ with $0<t\le 2|x|+2$ such that the copier is not in its return control at any earlier time and at time $t$ is in that control with $x$ on its work tape, both heads at their initial positions, and empty output.

**Proof.** The copier reaches the stated return configuration after $2|x|+2$ steps by the complete-run result, and its initial configuration is not in the return control. Moreover, the return control is absorbing: once entered, every step leaves the entire configuration unchanged. The first-arrival principle for a run ending in an absorbing control therefore supplies a positive time no later than the given run length at which the machine first reaches that control; it also guarantees that no earlier time is in the control and that the configuration at this first time is the stated endpoint.

**Key facts.** `Complexity.clInput_run`, `Complexity.clInput_idle`, `Complexity.clFirst`.
