<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Address_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Packed Address Closure

**Claim.** For fixed natural numbers $B,j$, if the unary words for $m(x)$ and $t(x)$ are polynomial-time computable, then so is the unary word for $m(x)+t(x)B+j$.

**Proof.** First use the polynomial-time closure for unary multiplication to obtain the unary word for $B t(x)$. The constant word consisting of $j$ ones is polynomial-time computable as well. Concatenate, in order, the unary words for $m(x)$, $B t(x)$, and $j$; concatenation preserves polynomial-time computability. The resulting word has length $m(x)+B t(x)+j$, which is the specified packed address since multiplication of natural numbers commutes.

**Key facts.** `Complexity.clA5Times_native`, `Complexity.clA5_pt_const`, `Complexity.clNative_append`.
