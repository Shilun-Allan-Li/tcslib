<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.sumIdx_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output summary update

**Claim.** Appending an optional Boolean symbol to an output list updates its summary index according to the stated rule.

**Proof.** Split according to whether $u$ is empty, has one entry, or has at least two entries, and whether the optional symbol is absent, $0$, or $1$. In each case the definitions give the result directly. An empty output stays empty when nothing is appended; appending $1$ makes it the accepting one-bit output, while appending $0$ makes it dead. The accepting one-bit output remains accepting if nothing is appended and becomes dead upon either appended bit. Any output already classified as dead remains dead after appending. These cases are exactly the clauses of the update rule.
