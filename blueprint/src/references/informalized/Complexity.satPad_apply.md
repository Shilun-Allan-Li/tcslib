<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPad_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding commutes with an action

**Claim.** Applying an action padded to $K$ work tapes to a configuration padded to $K$ tapes gives the padding of the result of applying the original action to the original configuration.

**Proof.** The state, input-head position, and output agree directly, since padding preserves them and the action treats them identically. For each tape index, if it is among the original $k$ tapes, the padded action uses the original tape action, so both sides perform the same write, if any, and the same head movement. If the index is an added tape, the padded action makes no write and no movement, while the padded configuration has a blank tape and head at zero; this agrees with padding the result, which also leaves that tape blank with head at zero. Thus every component of the two configurations agrees.
