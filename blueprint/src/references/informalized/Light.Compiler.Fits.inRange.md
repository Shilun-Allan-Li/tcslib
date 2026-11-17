<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Fits.inRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Word Values Lie in Range

**Claim.** Under the fitting assumptions, if $|v|\le w$, then $-2^W\le 2v<2^W$.

**Proof.** The word-fit inequality gives $2(2w+2)<2^W$. Since absolute values are nonnegative and $|v|\le w$, we have $w\ge0$; the fit inequality then implies $2w<2^W$. The standard absolute-value bound lemma states that if $2B<2^W$ and $|v|\le B$, then $-2^W\le2v<2^W$ (WordRAM.inRange_of_abs_le). Apply it with $B=w$ and the given bound on $v$.

**Key facts.** `WordRAM.inRange_of_abs_le`.
