<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_load -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Loading

**Claim.** Under the stated encoding and range hypotheses, loading through address $j$ into destination $i$ updates address $i$ with the word stored at address $a$.

**Proof.** By the definition of a load, its effect updates address $i$ with the memory word at the integer represented by the word stored at address $j$. The hypothesis identifies that stored word with the encoding of $a$, and the range fact says that this encoding converts back to the integer $a$ (`toInt_wd`). Thus the value written is exactly $m(a)$, as claimed.

**Key facts.** `WordRAM.toInt_wd`.
