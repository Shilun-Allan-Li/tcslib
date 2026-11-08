<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.mulInv_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Multiplication Invariant

**Claim.** For every bit string $z$, the initial multiplication state formed from its two decoded components satisfies the multiplication invariant for $z$.

**Proof.** Choose the three witness strings in the invariant to be the two decoded components of $z$ and the empty string. By the definition of the initial state, it is exactly the required nested pair encoding. The arithmetic identity in the invariant reduces to the fact that the binary value of the empty string is zero, so its left side is the product of the decoded component values. The normalization requirement holds because the empty string is the binary expansion of zero. Finally, the length inequality holds with equality: the chosen first two strings are precisely the decoded components appearing on the right side of that bound.
