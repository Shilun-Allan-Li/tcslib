<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clSigned_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Signed Positions

**Claim.** Two signed positions at coordinate $i$ are equal exactly when the first-bank count from one assignment plus the second-bank count from the other equals the reverse cross-sum.

**Proof.** Write the signed positions as $a-b$ and $c-d$, where $a,c$ are the first-bank counts and $b,d$ the second-bank counts for the two assignments. Equality of signed positions is $a-b=c-d$. Adding $b+d$ to both sides gives $a+d=c+b$, which is precisely the stated cross-sum equality. Conversely, subtracting $b+d$ from that cross-sum equality recovers equality of the signed positions.
