<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.verdict_encode_family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded circuit evaluation

**Claim.** For a fan-in-two circuit family whose circuits are well formed, evaluating the encoding of the circuit for the length of $x$ paired with $x$ returns the indicator of whether the family accepts $x$.

**Proof.** Let $m=|x|$ and take the circuit $C_m$. The encoding theorem says that the verdict on the encoding of $C_m$ paired with $x$ equals the evaluation of $C_m$ on the input function $i\mapsto x_i$, where out-of-range values are taken to be false (\texttt{Complexity.verdict_encode}). On indices in the range $i<m$, this function agrees with the usual list lookup, so the circuit output is $(C_m).\mathrm{eval}(x.\mathrm{get})$. By definition of the language accepted by the family, $x$ belongs to that language exactly when this output is true. Thus the verdict is true precisely on members of the language, which is the asserted equality of one-bit indicator strings.

**Key facts.** `Complexity.verdict_encode`.
