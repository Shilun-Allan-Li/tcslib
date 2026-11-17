<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.decode_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layout of a Decoded Tableau Row

**Claim.** For the concatenated row consisting of a prefix of length $w$, three bits $a,b,c$, a block $F$ of length $k(w+1)$, and a final bit $d$, the prefix, designated entries, dropped suffix, and final indexed entry have the stated values.

**Proof.** Regroup the list as $\mathrm{pre} ++ (a::b::c::(F++[d]))$. Because $|\mathrm{pre}|=w$, taking the first $w$ entries returns exactly $\mathrm{pre}$. The append-index rule then shows that entries at offsets $w,w+1,w+2$ are $a,b,c$. Dropping $w+3$ entries removes the prefix and these three bits, leaving $F++[d]$. For the final index, after removing the prefix and the three bits, the remaining offset is $k(w+1)$, which is exactly $|F|$; hence that entry is the final bit $d$.
