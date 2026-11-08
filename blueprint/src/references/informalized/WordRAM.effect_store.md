<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_store -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Storing

**Claim.** Under the stated encoding and range hypotheses, storing through pointer address $i$ updates address $a$ with the word stored at address $j$.

**Proof.** By the definition of a store, the effect updates the address represented by the word at address $i$, using the word at address $j$ as the new value. The hypothesis identifies the pointer word with the encoding of $a$, while the range condition ensures that converting this encoding to an integer yields $a$ (`toInt_wd`). Therefore the update is at address $a$ and has value $m(j)$.

**Key facts.** `WordRAM.toInt_wd`.
