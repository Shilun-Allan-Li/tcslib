<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.flatMap_normChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Normalization by Chunks

**Claim.** For a bit string $w$ of length at most $N$, concatenating the specified first-bit chunks of its suffixes gives the least-significant-bit-first binary expansion of the natural number represented by $w$.

**Proof.** Induct on $w$. If $w$ is empty, every chunk is empty and the represented value is zero, whose binary expansion is empty. Now write $w=b::v$ and, as ensured by the length bound, write $N=M+1$. The first suffix contributes its chunk, and the remaining suffixes are those of $v$, so induction identifies their concatenation with the binary expansion of the value represented by $v$. If no bit of $b::v$ is $1$, then its represented value is zero: the characterization of zero value by absence of any $1$ (`bitsVal_eq_zero_iff`) also implies that $v$ represents zero. All chunks and the resulting binary expansion are therefore empty. Otherwise, the first chunk is $[b]$. The value represented by $b::v$ is $2\,\mathrm{bitsVal}(v)+b$; if $v$ represents zero, the nonzero assumption forces $b=1$. The binary expansion identity for doubling and adding a bit (`bits_two_mul_add`) then says that the expansion is $b$ followed by the expansion of $v$, exactly the concatenation obtained from the chunks.

**Key facts.** `Complexity.BinArith.bitsVal_eq_zero_iff`, `Complexity.LogProg.bits_two_mul_add`.
