<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean :: Complexity.LogProg.TQBFARM.getD_quant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantifier Bits in a Paired Encoding

**Claim.** When $x$ encodes the pair of $q$ and the serialization of $\varphi$, the two positions $2k$ and $2k+1$ both contain $q_k$ for each $k<|q|$.

**Proof.** Apply the encoded-pair bit formula (\texttt{getD_enc}) at both positions. Since $k<|q|$, both positions are strictly inside the doubled prefix. At $2k$ the quotient by two is $k$, and at $2k+1$ it is also $k$; hence both bits are the corresponding bit of $q$.

**Key facts.** `Complexity.LogProg.TQBFARM.getD_enc`.
