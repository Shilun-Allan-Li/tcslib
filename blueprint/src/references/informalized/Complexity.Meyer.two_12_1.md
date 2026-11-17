<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.two_12_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the first updated position

**Claim.** After setting position $1$ to $a$ and then position $2$ to $a'$, the resulting function has value $a$ at position $1$.

**Proof.** The second update is at position $2$, so it leaves position $1$ unchanged. The first update set the value there to $a$, which is therefore still the value after both updates.
