<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.loadWords_mem_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative-address loading

**Claim.** For every word width $W$, list of words $ws$, and negative integer address $a$, the loaded memory at $a$ is the zero word.

**Proof.** By definition, loading at a negative address returns the zero bit vector. Since $a<0$, the conditional in the definition selects this branch, and the zero bit vector is exactly $\mathrm{wd}(W,0)$.
