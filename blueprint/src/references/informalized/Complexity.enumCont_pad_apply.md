<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pad_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Commutes with Applying an Action

**Claim.** Applying the padded action to the padded configuration equals padding the configuration obtained by applying the original action.

**Proof.** Compare the configuration fields. The state, input-head position, and output agree directly: padding maps the successor state along the given map and leaves the other two fields unchanged. For each work-tape index, split into indices below $k$ and indices at least $k$. On the first $k$ tapes, padding preserves the original tape contents and head positions, so the same write, if any, is made at the same cell and the head moves by the same amount. On additional tapes, the padded action makes no write and no move, so their blank contents and zero head positions are preserved. Thus the work-tape contents and head positions agree as well.
