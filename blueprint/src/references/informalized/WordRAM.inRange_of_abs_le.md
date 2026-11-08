<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.inRange_of_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric range from an absolute bound

**Claim.** If $2B<2^W$ and $|v|\le B$, then $-2^W\le 2v<2^W$.

**Proof.** The absolute-value bound is equivalent to $-B\le v\le B$. Multiplying these inequalities by $2$ gives $-2B\le 2v\le 2B$. The assumed strict bound $2B<2^W$ implies the upper conclusion $2v<2^W$; it also gives $-2^W<-2B\le 2v$, hence the required lower bound.
