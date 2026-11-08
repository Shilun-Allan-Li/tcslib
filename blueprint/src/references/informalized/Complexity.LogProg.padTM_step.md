<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.padTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Preserves One Machine Step

**Claim.** If $k\le K$, then stepping the machine padded to $K$ work tapes from a padded configuration gives the padding of the original machine's one-step result.

**Proof.** Compare the two steps by cases on the configuration's state. In the halting state, both machines leave the configuration unchanged, so the identity follows. In an active state, each of the original $k$ padded tape readings is exactly the corresponding original reading; thus the padded transition uses the same action as the original transition. The state, input-head position, and output are therefore identical on both sides. For each tape with index below $k$, the action updates its contents and head position exactly as in the original machine. For each additional tape, the padded configuration has blank contents and head position zero, and the padded action makes no write and no movement, so those values remain unchanged. Hence the work tapes and all other configuration fields agree.
