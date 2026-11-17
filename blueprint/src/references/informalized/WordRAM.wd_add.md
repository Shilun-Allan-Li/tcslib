<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.wd_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of encoded integers

**Claim.** Adding the $W$-bit encodings of integers $a$ and $b$ gives the $W$-bit encoding of $a+b$.

**Proof.** A bit vector formed by encoding an integer represents that integer modulo $2^W$. Bit-vector addition is addition modulo the same modulus, so adding the encodings of $a$ and $b$ gives the residue of $a+b$. This is precisely the encoding of $a+b$.
