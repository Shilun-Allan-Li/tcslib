<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.moveInputPos_pos_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Input-Head Movement

**Claim.** For every input word $x$ and legal input-head position $ip$ with $ip\le |x|$, moving the head one step right gives a position whose value is $ip+1$.

**Proof.** The general movement formula says a positive move gives the minimum of $ip+1$ and $|x|+1$. Since $ip\le |x|$, we have $ip+1\le |x|+1$, so this minimum is $ip+1$.

**Key facts.** `Complexity.LogProg.moveInputPos_val`.
