<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.loadWords_mem_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loaded word at a natural address

**Claim.** At a natural address $a$, the memory obtained by loading $ws$ contains the $W$-bit representation of the $a$th list entry, defaulting to zero if it is absent.

**Proof.** Substitute the natural address, viewed as an integer, into the definition of the loaded memory. A natural number is nonnegative, so the negative-address branch does not apply. Its natural-number conversion is exactly $a$, leaving the value $\operatorname{BitVec.ofInt}(W,ws.getD\ a\ 0)$, which is the stated word.
