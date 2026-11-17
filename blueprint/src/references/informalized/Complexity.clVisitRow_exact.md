<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitRow_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact visit row on a canonical request

**Claim.** For the paired request consisting of a Boolean word $x$ and a unary word of length $t$, the visit row is exactly the packed list of visit codes computed with input length $|x|+C(|x|+1)^e$.

**Proof.** Decode the paired request. The pairing decoder recovers its two components exactly ($\texttt{Turing.pairDecode\_pairEncode}$). Consequently, the zeroth header field is $x$, and the tail after one decoding is the unary word of length $t$. Substituting these values into the definition of the visit row gives the stated input length and time, and leaves precisely the packed list in the claim.

**Key facts.** `Turing.pairDecode_pairEncode`.
