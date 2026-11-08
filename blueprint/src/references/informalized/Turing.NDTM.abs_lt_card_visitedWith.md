<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.abs_lt_card_visitedWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Head Positions Bound Their Magnitude

**Claim.** If $z$ is a work-tape head position reached along some prefix of a choice word, then $|z|$ is strictly less than the number of distinct head positions reached along all prefixes, including the empty prefix.

**Proof.** Consider the integer-valued sequence whose $j$th term is the position of head $i$ after running the prefix of length $j$. At time zero this position is $0$, since the initial configuration has every work-tape head at zero. Between consecutive times, either the configuration is unchanged or one transition action is applied; in either case the head position changes by at most one, using the action head-movement bound (`workTapePos_apply_le`). The unit-step visited-image bound (`ConfigCount.abs_lt_card_image_of_unitSteps`) now says that every value in the image of this sequence over times $0$ through $|w|$ has absolute value strictly smaller than the cardinality of that image. This image is precisely the set of visited head positions in the claim.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps`, `Turing.NDTM.take_succ_action`, `Turing.workTapePos_apply_le`.
