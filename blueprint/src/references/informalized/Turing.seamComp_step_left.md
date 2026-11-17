<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_step_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step in the Left State Component

**Claim.** From a configuration whose state is not $exit$, one step of the seam-composed machine on its left embedding agrees with one step of $M_1$, followed by embedding the resulting state on the left.

**Proof.** Split according to whether the configuration has a state. If it has none, both machines leave the configuration fixed, and embedding the state preserves this equality. If its state is $q$, the assumption that it is not $exit$ implies $q\ne exit$. Therefore the seam transition uses the ordinary $M_1$ transition branch and embeds its successor state into the left summand. The tape actions are those of $M_1$ in both computations, so the resulting configurations agree.
