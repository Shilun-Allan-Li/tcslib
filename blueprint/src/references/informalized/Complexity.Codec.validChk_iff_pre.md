<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.validChk_iff_pre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Check and Preliminary Conditions

**Claim.** The validity check is equivalent to the conjunction of its preliminary length, terminal-bit, and encoded-position bounds with acceptance of the verifier on the prescribed prefix.

**Proof.** Unfold the two predicates. Both state the same four conditions: the word has the specified length, the verifier accepts the prefix of length $W(2s+1)$, the value represented by the following $wP(n)$ bits is at most $n+1$, and the bit at the designated terminal position is true. The preliminary predicate groups the length, terminal-bit, and value-bound conditions together, leaving verifier acceptance as the remaining conjunct. Regrouping these equivalent conjunctions proves the equivalence.
