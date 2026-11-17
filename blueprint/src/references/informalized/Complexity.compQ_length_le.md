<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compQ_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial output-length bound

**Claim.** If every $x$ satisfies $|f(x)|\le C(|x|+1)^c$, then the transformation’s output on any $w$ has length at most $(2C+3)(|w|+1)^{c+1}$.

**Proof.** If parsing fails, or parsing succeeds but the second component is not the binary expansion of its value, the transformation returns the empty string and the bound is immediate. In the remaining case, parsing identifies $w$ as the encoding of some pair $(x,b)$, by `eq_pairEncode_of_pairDecode`. Hence `length_pairEncode` gives $|w|=2|x|+2+|b|$, so $|x|+1\le |w|+1$. The hypothesis on $f$ therefore bounds $|f(x)|$ by $C(|w|+1)^c$. Since $|w|+1\ge1$, both $(|w|+1)^c$ and $|w|+1$ are at most $(|w|+1)^{c+1}$. The successful output is the encoding of $(f(x),b)$, whose length is $2|f(x)|+2+|b|$. Using $2+|b|\le |w|+1$ and the preceding bounds, this is at most $2C(|w|+1)^{c+1}+3(|w|+1)^{c+1}$, as required.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`.
