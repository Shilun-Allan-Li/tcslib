<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a pair encoding

**Claim.** For Boolean words $u$ and $v$, the pair encoding has length $2|u|+|v|+2$.

**Proof.** Each bit of $u$ contributes two copies in the flattened list, so the doubled portion has length $2|u|$. The separator contributes two bits and the final suffix contributes $|v|$ bits. Adding these lengths gives $2|u|+2+|v|$, which is the claimed expression.
