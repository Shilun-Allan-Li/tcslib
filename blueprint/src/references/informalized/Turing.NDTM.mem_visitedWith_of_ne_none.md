<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.mem_visitedWith_of_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Written Cells Were Visited

**Claim.** If cell $z$ on tape $i$ contains a symbol after running from the initial configuration under $w$, then $z$ is one of the head positions visited at the initial time or after one of the first $|w|$ steps.

**Proof.** Consider the sequence whose $j$th configuration is the result of running on the prefix of $w$ of length $j$. Its initial work tapes are blank, so no cell initially contains a symbol. Between consecutive configurations, either the machine stays put or the next configuration is obtained by applying one action; this is exactly the step property for runs on successive prefixes (`Turing.NDTM.take_succ_action`). The general visited-position lemma (`Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none`) therefore applies: any cell containing a symbol at time $|w|$ must be among the head positions in this sequence from time zero through time $|w|$. By definition, these positions form `visitedWith` for $w$, which proves the claim.

**Key facts.** `Turing.NDTM.take_succ_action`, `Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none`.
