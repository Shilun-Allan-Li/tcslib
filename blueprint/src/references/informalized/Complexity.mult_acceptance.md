<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_acceptance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Input Characterisation

**Claim.** The nested encoding of bit strings $a,b,c$ belongs to the binary multiplication language exactly when all three strings are canonical, $|c|\le |a|+|b|$, the carry after column $|a|+|b|$ is zero, and each output bit below that position is the parity of the incoming carry plus the corresponding product-column value.

**Proof.** Use the characterisation of membership in the multiplication language (Complexity.mult_membership): membership is equivalent to canonicality of the three strings together with the numerical identity $\operatorname{bitsVal}(c)=\operatorname{bitsVal}(a)\operatorname{bitsVal}(b)$. In the forward direction, this identity and canonicality let us replace each string by the bits of its value, using the canonical-word representation theorem (Complexity.LogProg.canon_eq_bits). The standard product-length bound for binary expansions (Complexity.mult_product_length) then gives $|c|\le |a|+|b|$. With this bound, the column-by-column multiplication criterion (Complexity.mult_columns_correct) translates the numerical identity into the zero final carry and the stated parity equations. Conversely, assume canonicality, the length bound, and those carry and parity conditions. The same column criterion gives the numerical identity, and membership follows from the membership characterisation.

**Key facts.** `Complexity.mult_membership`, `Complexity.LogProg.canon_eq_bits`, `Complexity.mult_product_length`, `Complexity.mult_columns_correct`.
