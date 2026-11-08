<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecRowBits_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of encoded row bits

**Claim.** For any finite Turing machine, natural numbers $n,s$, and codec row $r$, its Boolean encoding has exactly one true input-head coordinate and exactly one true state coordinate. For each work tape exactly one head-position coordinate is true; at each work-tape cell the two symbol coordinates are not both true; and the two output-summary coordinates are not both true.

**Proof.** The input-head coordinates are the equality indicators for the row's input-head position, so precisely the coordinate naming that position is true. The state coordinates are likewise equality indicators for the row's state, and each work tape's head coordinates indicate equality with that tape's head position; each family therefore has exactly one true coordinate. For a work cell, if its optional symbol is absent, both symbol flags are false; if it is present, it is either false or true, making one corresponding flag true and the other false. The summary is one of empty, accept, or dead, so it cannot equal both accept and dead; hence its two flags are not both true.
