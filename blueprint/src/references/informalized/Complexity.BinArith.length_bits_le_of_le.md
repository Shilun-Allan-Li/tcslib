<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.length_bits_le_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length from a Bounded Representation

**Claim.** If $n$ is at most the value of a bit string $w$ and the length of $w$ is at most $m$, then the binary expansion of $n$ has length at most $m$.

**Proof.** Binary expansion length is monotone in the represented number: from $n\le \mathrm{bitsVal}(w)$, `length_bits_mono` bounds the length of the expansion of $n$ by that of the expansion of $\mathrm{bitsVal}(w)$. The latter is at most the length of $w$ by `length_bits_bitsVal_le`, which in turn is at most $m$. Combining these inequalities proves the claim.

**Key facts.** `Complexity.LogProg.length_bits_mono`, `Complexity.BinArith.length_bits_bitsVal_le`.
