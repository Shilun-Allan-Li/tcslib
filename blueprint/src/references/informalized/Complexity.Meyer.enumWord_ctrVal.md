<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.enumWord_ctrVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Word Recovers Its Value

**Claim.** For every finite Boolean word $u$, the width-$|u|$ little-endian binary word of the integer represented by $u$ is exactly $u$.

**Proof.** Induct on the word. The empty word has represented value zero, and the width-zero encoding is empty. For a word with head bit $b$ and tail $u$, its represented value is $b+2\,\mathrm{ctrVal}(u)$. The first encoded bit is therefore the parity bit $b$: for $b=0$ the value is even, and for $b=1$ it is odd. In both cases, dividing the value by two gives $\mathrm{ctrVal}(u)$. The remaining width is the length of $u$, so the induction hypothesis identifies the remaining encoded word with $u$. Thus the full encoding is $b::u$.
