<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidth_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Counter Update for One Literal

**Claim.** For a literal $\ell=(v,b)$, scanning its binary encoding from state $1$, counter $c$, and flag $g$ ends in state $1$, counter $\min(c+1,3)$, and flag $g\wedge[c<3]$.

**Proof.** The literal encoding starts with $v+1$ one bits. The first one bit, read in state $1$, moves the scanner to state $2$, increments and caps the counter, and conjoins the flag with $[c<3]$. The remaining $v$ one bits leave state $2$, counter, and flag unchanged, by the index-bits identity (`Complexity.satWidth_index`). The following zero bit returns the scanner to state $1$, and the final polarity bit is read there, producing the claimed result without further changing the counter or flag.

**Key facts.** `Complexity.satWidth_index`.
