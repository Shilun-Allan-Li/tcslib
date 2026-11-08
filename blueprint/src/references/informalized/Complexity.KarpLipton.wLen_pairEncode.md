<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.wLen_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length from the First Encoded Component

**Claim.** For all natural numbers $C,c$ and binary strings $x,u$, applying $wLen$ to the pair encoding of $x$ and $u$ gives $C(|x|+1)^c$.

**Proof.** By definition, $wLen$ depends on its string argument only through the length of that argument's decoded first component. Pair decoding recovers $x$ as the first component of the encoding of $x,u$. Substituting this identity into the definition gives $C(|x|+1)^c$.
