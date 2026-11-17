<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitCount_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance condition for the split counter

**Claim.** For the associated counter configuration, the conjunction that the count has not exceeded $|w|$ and that its input head reads no symbol is equivalent to the count being exactly $|w|$.

**Proof.** Put $j=|s|+|c.\mathrm{output}|$. The counter configuration places its input head at the position representing $j$. By the input-reading rule for that position (`f2_splitPos_read`), the head reads a symbol exactly when $j<|w|$; otherwise it reads no symbol. Thus the conjunction in the claim says both $j\le|w|$ and $j\ge|w|$, which is equivalent to $j=|w|$.

**Key facts.** `Turing.FinTM.f2_splitPos_read`.
