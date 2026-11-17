<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.length_vecW_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Dynamic Program Length Bound

**Claim.** For every finite nondeterministic Turing machine $N$, bit string $x$, and natural numbers $s,V,t$, the word produced by the dynamic-programming encoding has length at most $V\bigl(2(2Vt+1)+2\bigr)$.

**Proof.** The vector encoding consists of one encoded binary representation for each of the $V$ indices. The general encoded-list estimate (`Complexity.BinArith.length_encWords_le`) bounds its length by $V(2c+2)$ once each representation has length at most $c$. For an index $a$, the value bound (`Randomized.BPLInP.dpVal_le`) gives $\mathrm{dpVal}(t,a)\le(2V)^t$. Since $2V<2^{2V}$, raising to the $t$th power yields $(2V)^t\le 2^{2Vt}$, and hence $\mathrm{dpVal}(t,a)<2^{2Vt+1}$. The binary-expansion length estimate (`Complexity.LogProg.length_bits_le`) therefore bounds its representation length by $2Vt+1$. Substituting this choice of $c$ into the encoded-list estimate proves the result.

**Key facts.** `Complexity.BinArith.length_encWords_le`, `Complexity.LogProg.length_bits_le`, `Randomized.BPLInP.dpVal_le`.
