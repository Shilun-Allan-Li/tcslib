<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.length_iterate_le_of_slack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterate Length Bound from Slack

**Claim.** Under the stated slack inequality and numerical hypotheses, every iterate of $g$ from $w$ has length at most $b(|w|+1)$.

**Proof.** Track the augmented quantity consisting of the current string's length plus $c$ times the length of the first projection of its second projection. Induction on the number of iterations, applying the slack hypothesis at each step, bounds this quantity by the maximum of the initial augmented quantity and $2$. The two projection-length bounds ($length_pairFstD_le$ and $length_pairSndD_le$) show that the initial inner projection has length at most $|w|$. Hence the initial augmented quantity is at most $(c+1)|w|$, and the assumptions $c+1\le b$ and $2\le b$ bound the maximum by $b|w|+b=b(|w|+1)$. Since the augmented quantity is at least the iterate's length, the desired estimate follows.

**Key facts.** `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`.
