<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_absorb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing Polynomial Factors into an Exponent

**Claim.** For natural numbers $B,d,K$, there is a positive natural number $C\ge K$ such that, for every $u\ge2$, $BC^2u^d\le Cu^C$.

**Proof.** Choose $C=\max(4,\max(K,\max(d,B2^d)))$. Then $C\ge4$, $C\ge K$, $d\le C$, and $B2^d\le C$. The auxiliary estimate `codec_square_le_pow` gives $C^2\le2^C$. Consequently $(BC)2^d=(B2^d)C\le C^2\le2^C$. Since $C=d+(C-d)$, factor $2^C=2^{C-d}2^d$ and cancel the positive factor $2^d$ to obtain $BC\le2^{C-d}$. For $u\ge2$, monotonicity of natural-number powers gives $2^{C-d}\le u^{C-d}$. Multiplying by $u^d$ and using $u^{C-d}u^d=u^C$ yields $BCu^d\le u^C$. Multiplying by $C$ gives the desired inequality $BC^2u^d\le Cu^C$; the chosen $C$ is positive since it is at least $4$.

**Key facts.** `Complexity.codec_square_le_pow`.
