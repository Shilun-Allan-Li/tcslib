<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Register Copy Routine

**Claim.** The specified routine reaches its exit state, changes only the destination register by adding the source value, and keeps the register values within the bound at every earlier configuration.

**Proof.** First use the two-register transfer routine (`move2_run`) with the source, destination, and temporary register. It transfers the source value into the destination while using the temporary register to restore the source, and returns to the loop state with the required intermediate register updates. The register inequalities needed by that routine follow from the initial bound $v(dst)+v(src)\le B$, the zero initial temporary value, and the bound on every initial register. The transfer routine ensures the guard throughout this first phase.

For the second phase, bound all registers after the first phase by applying the register-update bound (`register_update_le`) successively to the source, destination, and temporary updates. The updated temporary value plus the source value is at most $B$. Now apply the zero-test transfer routine (`move_run`) to the temporary register and source: it drains the temporary value back into the source and exits at $l_x$. Its hypotheses hold because the registers are distinct and the temporary register has the value established by the first phase. The composed run reaches the desired assignment; equality of the nested register updates with the single destination update follows from the distinctness assumptions. Compose the two guarded runs using reachability transitivity (`AReach.trans`) and identify the final configuration with `reach_of_eq`.

**Key facts.** `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.move2_run`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.move_run`, `Complexity.LogProg.reach_of_eq`.
