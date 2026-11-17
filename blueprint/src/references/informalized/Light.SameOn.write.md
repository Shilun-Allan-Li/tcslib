<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.SameOn.write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing outside constrained indices

**Claim.** If $\mu'$ agrees with $\mu$ wherever $K$ holds and $K$ fails at $b$, changing $\mu'(b)$ to any integer $x$ preserves agreement wherever $K$ holds.

**Proof.** Fix an index $c$ satisfying $K$. It cannot equal $b$, since that would contradict the assumption that $K$ fails at $b$. Updating $\mu'$ at $b$ therefore leaves its value at $c$ unchanged, and the original agreement gives $\mu'(c)=\mu(c)$. Hence the updated memory still agrees with $\mu$ throughout $K$.
