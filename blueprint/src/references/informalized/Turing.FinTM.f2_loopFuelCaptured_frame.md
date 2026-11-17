<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFuelCaptured_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Halting Configuration Frame

**Claim.** If a configuration of $F$ has no state, then its loop-fuel capture is exactly the specified loop frame, with the return state, inherited input-head position, blank flag and counter tapes, the output stored on the payload tape with its head at the output length, and empty output.

**Proof.** Show equality of configurations by checking their fields. The input-head position and output word agree by construction. For the state, capture maps the absent state through the embedding and uses the default return state; since the original state is absent, this is exactly the designated return state in the frame. For the work tapes, compare each index. At the final added index, capture stores the buffer tape for the original output, which is the frame's payload tape. At indices before that final index, split into the ranges used by the nested right extensions: the original $F$ tapes, the single intervening tape, and the added tapes preceding the payload. The right extensions make these added tapes blank; the frame assigns blanks to its flag and counter tapes, while its other intermediate tapes are inherited from the same captured configuration. The index inequalities ensure these assignments select the intended ranges. Finally, compare head positions in the same index ranges: the payload head is the output length, the flag and counter heads are at zero, and all remaining heads are inherited from the right-extended configuration. Thus every configuration field agrees.
