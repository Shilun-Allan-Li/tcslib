<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.abs_pos_lt_card_visited -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position bounded by visited-cell count

**Claim.** Any position occupied by a work-tape head at some time through $t$ has absolute value strictly less than the number of distinct positions that head visits through time $t$.

**Proof.** Track the head position as the integer sequence $p(j)$ along the run. Initially the head is at zero. Each step changes its position by at most one, by the one-step work-head movement bound (`workTapePos_step_le`), with successive run configurations related by `runFrom_succ_eq_step'`. The unit-step counting fact `abs_lt_card_image_of_unitSteps` says that for any such sequence starting at zero, every position in its image through time $t$ has absolute value strictly less than the cardinality of that image. The visited positions are exactly this image, so the stated bound follows.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`.
