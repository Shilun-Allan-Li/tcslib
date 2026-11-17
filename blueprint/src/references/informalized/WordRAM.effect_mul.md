<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Multiplication

**Claim.** If addresses $j$ and $k$ store the encodings of $a$ and $b$, respectively, multiplication with destination $i$ updates address $i$ with the encoding of $ab$.

**Proof.** By the definition of multiplication’s effect, the new memory is obtained by updating address $i$ with the product of the words at addresses $j$ and $k$. The hypotheses identify these words as the encodings of $a$ and $b$. The product of two encoded integers is the encoding of their product (`wd_mul`), so the update has the stated value.

**Key facts.** `WordRAM.wd_mul`.
