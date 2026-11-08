<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.incFixed_enumWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing an enumerated binary word

**Claim.** If $v+1<2^w$, fixed-width increment sends the width-$w$ little-endian binary word of $v$ to that of $v+1$.

**Proof.** Induct on the width $w$, allowing the value $v$ to vary. At width zero the assumed inequality is impossible. For a positive width, split according to the parity of $v$. If $v=2k$, the least significant bit is false; increment changes it to true, while the remaining bits encode $k$ both before and after, so the recursive definition of fixed-width increment gives the word for $2k+1$. If $v=2k+1$, the least significant bit is true; increment changes it to false and carries one into the remaining bits, which encode $k$. The bound $v+1<2^{w+1}$ implies $k+1<2^w$, so the induction hypothesis increments that remaining word to the encoding of $k+1$. Together the new low bit and higher bits encode $2(k+1)=v+1$.
