<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_row_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Starting an inner multiplication row

**Claim.** From the state that clears register 9, the machine reaches the inner-loop state with register 9 equal to its initial register 2 value and register 10 equal to its initial register 8 value, preserving the prescribed validity and register bounds along the way.

**Proof.** The proof first clears register 9 in one transition, then uses the staged copy routine to copy register 2 into register 9. It next clears register 10 and uses the copy routine again to copy register 8 into register 10, reaching the inner-loop state. Each updated assignment retains the register bound because the copied source values were already bounded, and clearing a register also respects the bound. The copy reaches are chained with the one-step transitions using the reachability step and composition rules; the machine precondition lemma supplies the validity condition at the transition states.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.mult_copy`, `Complexity.mult_preconditions`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`.
