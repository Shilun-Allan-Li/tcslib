<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arPos_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Block Coordinates

**Claim.** Two positions $(N+1)z+j$ and $(N+1)z'+j'$ are equal exactly when their block coordinates and offsets agree: $z=z'$ and $j=j'$.

**Proof.** Suppose the positions are equal. Apply the quotient-coordinate map $\mathrm{arCell}(N,\cdot)$ to both sides. The coordinate formulas for a position built from a block and an offset say that its quotient is the block, so $z=z'$. Applying the remainder-coordinate map $\mathrm{arIndex}(N,\cdot)$ likewise recovers the offset, giving $j=j'$. Conversely, if both coordinates agree, substituting them into the position formula gives equal positions immediately.

**Key facts.** `Turing.FinTM.arCoords`.
