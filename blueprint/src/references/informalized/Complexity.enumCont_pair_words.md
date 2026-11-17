<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pair_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Configuration Identification

**Claim.** The two-ended configuration with $s$ on tape zero and the other endpoint tape blank is exactly the configuration represented by the state word containing $s$ on tape zero and blank words elsewhere.

**Proof.** Extensionality reduces equality of configurations to equality of their fields. The state, input-head position, and output already agree. For the tape functions, fix a tape index. If its index is zero, the two definitions both give the tape function represented by $s$. If it is not zero, the left side selects the blank interior tape or the blank last tape, while the state word assigns the empty word; both represent the everywhere-blank tape. Finally, the head-position functions agree: both put every work-tape head at zero, since the endpoint-head position parameter is zero.
