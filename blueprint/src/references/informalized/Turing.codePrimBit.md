<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Binary Bit Appending

**Claim.** The operation taking a Boolean bit $b$ and a natural number $n$ to $2n+b$ is primitive recursive.

**Proof.** Use primitive recursion's conditional construction to select between two primitive recursive functions according to the Boolean input. For $b$ false, return the double of $n$; for $b$ true, return the successor of the double of $n$. These are respectively $2n$ and $2n+1$, which together give $2n+b$.
