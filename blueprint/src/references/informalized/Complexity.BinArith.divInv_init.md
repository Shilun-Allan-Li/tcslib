<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.divInv_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial division invariant

**Claim.** The initial state formed from a bit string satisfies the division invariant, with the remainder and quotient components both empty and the reversed input bits stored in the remaining component.

**Proof.** Choose $R$ to be the reverse of the first projection of $z$, and choose both $r$ and $q$ to be empty. The state equation then follows from the definition of the initial state. Since the empty strings have length zero, the two length bounds hold immediately. If the second projection has positive value, the empty quotient and remainder contribute zero, while reversing $R$ recovers the first projection; hence the required value equation holds, and the remainder value $0$ is strictly less than the positive divisor.
