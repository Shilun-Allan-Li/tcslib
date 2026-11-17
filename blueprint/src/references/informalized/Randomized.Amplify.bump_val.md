<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.bump_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Counter Update

**Claim.** If $c\le r$, then increasing $c$ by one when $b$ is true and leaving it unchanged when $b$ is false gives value $c+1$ when $b$ is true and $c$ when $b$ is false.

**Proof.** If $b$ is false, the counter update leaves $c$ unchanged, so its value is $c$. If $b$ is true, the update is the minimum of $c+1$ and $r+1$. Since $c\le r$, we have $c+1\le r+1$, so this minimum equals $c+1$.
