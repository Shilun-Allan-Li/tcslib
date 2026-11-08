<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.val_moveInputPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Moved Input Head

**Claim.** For a head position $p$ among $0,[0m\ldots,n+1$ and a movement $mv\in\{-1,0,1\}$, the clamped new position has the stated value: it stays at $p$ for zero movement, advances to $p+1$ for positive movement unless already at $n+1$, and moves to $\max(p-1,0)$ for negative movement.

**Proof.** Let $p$ denote the natural-number value of the given finite head position, so $p<n+2$. If the movement is zero, the head position is unchanged by `moveInputPos_zero`, giving value $p$. For positive movement, the integer calculation before clamping yields $p+1$. If $p=n+1$, this reaches the upper boundary and the clamp returns $n+1=p$; otherwise $p<n+1$, so the new value is $p+1$. For negative movement, conversion of $p-1$ from the integers to a natural number gives zero when $p=0$ and $p-1$ when $p>0$, which is exactly the claimed truncated predecessor.

**Key facts.** `Turing.moveInputPos_zero`.
