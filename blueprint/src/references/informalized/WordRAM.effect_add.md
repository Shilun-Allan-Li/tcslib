<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Addition

**Claim.** If memory stores the encodings of $a$ and $b$ at addresses $j$ and $k$, respectively, then the effect of the addition instruction with destination $i$ updates address $i$ with the encoding of $a+b$.

**Proof.** By the definition of the effect of an addition instruction, it updates address $i$ with the sum of the words at $j$ and $k$. Substitute the assumed encodings at those addresses. The encoding operation preserves addition, so the sum of the encodings of $a$ and $b$ is the encoding of $a+b$ (\(\texttt{WordRAM.wd_add}\)). Thus the effect is exactly the stated update.

**Key facts.** `WordRAM.wd_add`.
