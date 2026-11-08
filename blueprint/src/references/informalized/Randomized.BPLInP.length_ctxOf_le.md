<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.length_ctxOf_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Context Encoding

**Claim.** For every pair of natural numbers $s,V$ and every bit string $x$, the context encoding of $x,s,V$ has length at most $2|x|+2s+4+V(2V+2)$.

**Proof.** The context is nested pair encoding: first the input with a pair containing the binary representation of $s$ and the encoded range list. Each pair encoding of words $u,v$ has length $2|u|+2+|v|$ (`Turing.length_pairEncode`). The binary representation of $s$ has length at most $s$ (`Turing.length_bits_le_self`), and the encoded range list has length at most $V(2V+2)$ (`Randomized.BPLInP.length_encWords_range_le`). Substituting these bounds into the two pair-length formulas gives the claimed estimate.

**Key facts.** `Turing.length_pairEncode`, `Turing.length_bits_le_self`, `Randomized.BPLInP.length_encWords_range_le`.
