<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPad_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding canonical seam configurations

**Claim.** Padding a configuration with the specified word on tape zero, all other tapes empty, and output $o$ yields the corresponding configuration on $K$ tapes.

**Proof.** The state, input-head position, and output are preserved by padding. At tape index $i<K$, if $i<k$, the padded configuration retains the original tape and head, which are exactly those prescribed by the same single-word assignment on the larger tape set. If $i\ge k$, then $i\ne0$ because $k>0$, so the prescribed assignment on the larger set leaves this tape empty; padding likewise makes it blank with head at zero. Hence the tape contents and head positions agree at every index.
