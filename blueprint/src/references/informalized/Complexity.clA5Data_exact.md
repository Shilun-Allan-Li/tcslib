<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Data_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact stored tableau data

**Claim.** The packed word stores the input length $m=|x|+C(|x|+1)^e$, the horizon $T=c(A(m+1)^d+1)^2$, the serialization of the first $T+1$ trajectory rows on the all-false input of length $m$, and the ordered list of the first $T+1$ visit rows for the specified parameters.

**Proof.** Unfold the packed-word construction and its stored-field projections. Each layer of the nested header is a pair encoding, so applying the decoding identity (\texttt{pairDecode_pairEncode}) recovers exactly its two components. Repeating this through the nested layers extracts the prescribed input-size and horizon fields; the lengths of the stored unary words give $m$ and $T$ by construction. The same decodings expose the trajectory record list and visit-row list placed in the packed word, yielding respectively the first $T+1$ records and the first $T+1$ visit rows. The remaining equalities are the direct length and list simplifications of these components.

**Key facts.** `Turing.pairDecode_pairEncode`.
