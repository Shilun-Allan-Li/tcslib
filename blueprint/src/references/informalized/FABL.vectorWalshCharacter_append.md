<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorWalshCharacter_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character of a Concatenation

**Claim.** For $a,x\in\mathbb{F}_2^n$ and $b,y\in\mathbb{F}_2^m$, the vector Walsh character indexed by the concatenation of $a$ and $b$, evaluated at the concatenation of $x$ and $y$, is the product of the characters indexed by $a$ and $b$ evaluated at $x$ and $y$, respectively.

**Proof.** Express each vector Walsh character at a point as the binary sign of the dot product (`FABL.vectorWalshCharacter_apply`). The dot product of the concatenated vectors splits as the sum of the two component dot products (`FABL.f₂DotProduct_append`). Since an additive character sends a sum to the product of its values, the sign of this sum is the product of the two signs. Rewriting those signs as the component Walsh characters gives the claimed identity.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_append`.
