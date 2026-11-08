<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.canonicalTail_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Tail Loop

**Claim.** Under the specified loop transitions, register bounds, pointer-limit relation, and oracle answers, the loop terminates with the stated done-or-fail result, preserves the bounds and untouched registers, and satisfies the safety conditions throughout.

**Proof.** Proceed by induction on the word $w$, generalizing the register assignment and the default last bit. The reachability statements below use the invariant that every visited configuration satisfies the program's safety condition and has all registers bounded by $B$.

If $w$ is empty, the pointer equals the limit by the assumed length relation. The test therefore takes the branch determined by the supplied last bit, and no register changes. A one-step reachability fact (`AReach.single`) records this transition and its invariant.

Now let $w=b::w'$. The length relation gives enough room to advance the pointer by one stride without passing the limit. If the cap is zero, its binary expansion has length zero, so the nonempty word is too long for the cap. The test proceeds to the cap check, which immediately fails; the registers remain unchanged. These transitions are assembled with the reachability step rule (`AReach.step`).

If the cap is positive, the loop reads the oracle at the current pointer. The answer is $b$ by the hypothesis for index zero. It halves the cap and advances the pointer by the stride. The updated registers remain bounded: halving cannot increase the cap, and the pointer's new value is at most the limit, which was already bounded by $B$ (`register_update_le`). The updated pointer and limit satisfy the same length relation for the shorter word $w'$. Moreover, the oracle answers at all subsequent pointer positions are exactly the bits of $w'$, by shifting the index in the original oracle hypothesis. The induction hypothesis therefore applies to the updated configuration.

The cap-width identity (`access_width_half`) shows that halving a positive cap reduces the bit length by exactly one. Thus the original word fits within the original cap's bit length exactly when its tail fits within the halved cap's bit length. The final-bit convention is also preserved: the last-bit value of $b::w'$ is that of $w'$ when the tail is nonempty, and is $b$ when the tail is empty. The induction conclusion consequently gives precisely the claimed final branch. The pointer bound transfers back because the limit is unchanged; the induction's frame property says registers other than pointer and cap stay unchanged, and the two updates used in this iteration affect only those registers. Concatenating the finite transition segments gives the complete safe run (`AReach.trans`), with the increment segment justified by the fixed-stride transition result (`arm_increments`).

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.access_width_half`, `Complexity.LogProg.arm_increments`, `Complexity.LogProg.AReach.trans`.
