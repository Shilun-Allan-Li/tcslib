<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Encoding of a Literal

**Claim.** Scanning the encoding of a literal $(v,b)$ followed by a suffix $r$ from clause-level state yields the encoding of $(v,\neg b)$ followed by the scan of $r$ from clause-level state.

**Proof.** Expand the literal encoding into $v+1$ copies of $1$, then the delimiter $0$, then the polarity bit $b$. The first $1$ moves the scanner from clause state to unary state; the remaining unary bits are preserved by the unary-scan property (`tautDual_unary`). The delimiter moves the scanner to polarity state, where the final bit is flipped. The scanner then returns to clause state, so the remaining suffix is scanned exactly as it would be from clause state. These bits are precisely the encoding with polarity $\neg b$, followed by the claimed scan of $r$.

**Key facts.** `Complexity.tautDual_unary`.
