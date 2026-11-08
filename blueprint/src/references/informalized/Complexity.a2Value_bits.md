<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Value_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of Binary Expansion

**Claim.** For every natural number $n$, the little-endian value of its binary expansion is $n$.

**Proof.** Use the binary recursion for natural numbers. At zero, the binary expansion has value zero. In the successor step, write the number as a binary digit $b$ attached to a smaller number $n$, so its expansion is the expansion of $n$ followed by that digit. The value of this appended expansion is twice the value of the expansion of $n$, plus $1$ when $b$ is true and $0$ otherwise. By induction this is $2n+b$, which is exactly the value of the number represented by that binary step.
