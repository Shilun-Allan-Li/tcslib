<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.wd_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction of encoded integers

**Claim.** Subtracting the $W$-bit encoding of $b$ from that of $a$ gives the $W$-bit encoding of $a-b$.

**Proof.** Rewrite subtraction as addition of the additive inverse. The encoding of a negative integer is the additive inverse of its encoding, and encoding respects addition. Thus the difference of the encodings is the encoding of $a+(-b)=a-b$.
