<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_str_rank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# String Recovery from Rank

**Claim.** For every bit string $s$, interpreting $r(s)+1$ in least-significant-bit-first binary and removing the last bit recovers exactly $s$.

**Proof.** The binary expansion of $r(s)+1$ is $s$ followed by the bit $1$ (\texttt{Complexity.ntc\_bits\_rank\_succ}). Removing the last element of a list formed by appending one element returns the original list, so dropping the last bit leaves exactly $s$.

**Key facts.** `Complexity.ntc_bits_rank_succ`.
