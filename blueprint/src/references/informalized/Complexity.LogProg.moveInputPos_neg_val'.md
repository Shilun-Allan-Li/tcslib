<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.moveInputPos_neg_val' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Input-Head Movement

**Claim.** For every input word $x$ and every legal input-head position $ip$, moving the head one step left gives a position whose value is $ip-1$.

**Proof.** Apply the general formula for the value after a signed input-head move, with the negative movement sign. Its negative case gives exactly the original position value minus one.

**Key facts.** `Complexity.LogProg.moveInputPos_val`.
