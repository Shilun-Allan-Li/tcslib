<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satToken_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Token Split of a Serialized Literal

**Claim.** For every literal $\ell=(v,b)$ and bit string $r$, splitting the encoding of $\ell$ followed by $r$ gives the token $1^{v+1}0$ and the suffix beginning with polarity bit $b$, followed by $r$.

**Proof.** For any $k$, induction on $k$ shows that splitting $k$ initial true bits followed by a false bit, $b$, and $r$ returns the token consisting of those $k$ true bits and the false delimiter, with suffix $b::r$. The base case splits immediately at the false bit; the inductive step consumes one leading true bit and applies the induction hypothesis to the rest. Taking $k=v+1$, which is the unary prefix in the literal encoding, proves the claim.
