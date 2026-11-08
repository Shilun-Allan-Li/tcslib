<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Binary Expansion

**Claim.** The function sending each natural number to its binary digits, listed from least significant to most significant, with zero represented by the empty list, is primitive recursive.

**Proof.** Define a recursion in which zero has no dependencies, while each positive $n$ depends on its half $n/2$. For zero, the recursion returns the empty list. For positive $n$, it takes the previously computed list of digits of $n/2$ and prepends the least significant bit of $n$. The dependency decreases for every positive $n$, so this is a valid natural-number recursion. To verify the result, zero agrees with the specified convention. For positive $n$, the binary expansion identity says that adjoining the low bit of $n$ to the expansion of $n/2$ reconstructs the expansion of $n$. If $n/2=0$, the low bit is necessarily true, which is the boundary case required by that identity. Thus the recursion computes the binary digits, and the primitive-recursive recursion principle yields the claim.
