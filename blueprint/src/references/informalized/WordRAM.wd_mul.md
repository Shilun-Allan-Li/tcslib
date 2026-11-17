<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.wd_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication of encoded integers

**Claim.** Multiplying the $W$-bit encodings of integers $a$ and $b$ gives the $W$-bit encoding of $ab$.

**Proof.** A $W$-bit encoding records an integer modulo $2^W$, and bit-vector multiplication multiplies residues modulo $2^W$. The product of the residues of $a$ and $b$ is therefore the residue of $ab$, which is the $W$-bit encoding of $ab$.
