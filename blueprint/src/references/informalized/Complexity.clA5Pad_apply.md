<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pad_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Commutes with an Action

**Claim.** Applying an action padded to $K$ work tapes to a padded configuration gives the padding of the configuration obtained by applying the original action.

**Proof.** The state, input-head position, and output are unchanged by padding, so those components agree directly. For the work tapes, fix a padded tape index and split into the two cases. If its index is below $k$, both sides use the corresponding original tape and action; the tape contents and head position therefore agree after the update. If its index is at least $k$, the padded tape begins blank, its padded action makes no write and no movement, and it remains blank with head at zero. Thus the work-tape contents and head positions agree at every index, proving equality of configurations.
