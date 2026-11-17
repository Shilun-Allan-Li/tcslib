<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Subtraction

**Claim.** If addresses $j$ and $k$ store the encodings of $a$ and $b$, respectively, subtraction with destination $i$ updates address $i$ with the encoding of $a-b$.

**Proof.** By the definition of subtraction’s effect, the new memory updates address $i$ with the difference between the words at addresses $j$ and $k$. The hypotheses identify these words as the encodings of $a$ and $b$. Subtracting those encoded words gives the encoding of their difference (`wd_sub`), which is the value written by the update.

**Key facts.** `WordRAM.wd_sub`.
