<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_step_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step in the Right State Component

**Claim.** From any configuration of $M_2$, one step of the seam-composed machine on its right embedding agrees with one step of $M_2$, followed by embedding the resulting state on the right.

**Proof.** Split on whether the configuration state is absent or is some state $q$. With no state, both runs leave the configuration fixed, and the right embedding preserves that equality. In the $q$ case, the seam transition on a right-summand state is defined using the transition of $M_2$, with its successor state embedded into the right summand. All tape actions are therefore identical to those of the $M_2$ step, giving the claimed equality.
