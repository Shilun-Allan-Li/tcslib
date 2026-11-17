<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_cfgWord_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration encoding length bound

**Claim.** For every $s$ and configuration $C$, the encoding length is at most $(2W+2)(s+\mathrm{logSpace}(|x|)+1)$.

**Proof.** The exact encoding-length formula is $W(2s+1)+w_P(|x|)+1$ (`length_cfgWord`). The binary length estimate $(\mathrm{Nat.bits}\,n).\mathrm{length}\le \mathrm{Nat.log}\,2\,n+1$ (`length_bits_le_log`), applied at $n=|x|+1$, bounds $w_P(|x|)$ by $\mathrm{logSpace}(|x|)+1$: the logarithm of $|x|+1$ is at most the logarithm of $|x|$ plus one, including the case $|x|=0$. Substituting this estimate into the exact formula and expanding the two sides, the desired inequality follows from $W\ge1$ and the definitions of $\mathrm{logSpace}$ and the coefficient $2W+2$.

**Key facts.** `Complexity.Codec.length_cfgWord`, `Complexity.LogProg.length_bits_le_log`.
