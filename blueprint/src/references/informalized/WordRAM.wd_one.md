<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.wd_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding one

**Claim.** The bit-vector value $1$ is the $W$-bit encoding of the integer $1$.

**Proof.** Both expressions have the same unsigned value, namely $1$ reduced to width $W$. Bit vectors of a fixed width are equal when their unsigned values agree, so the two values coincide.
