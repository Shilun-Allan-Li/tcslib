<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceWords.lean :: Turing.certificateLength_strictMono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Growth of a Polynomial Expression

**Claim.** For natural numbers $C$ and $c$, the function $n\mapsto n+C(n+1)^c$ is strictly increasing.

**Proof.** Take $n<m$. Then $n+1\le m+1$, so raising both sides to the natural power $c$ gives $(n+1)^c\le(m+1)^c$. Multiplication by $C$ preserves this inequality. Adding it to $n<m$ yields $n+C(n+1)^c<m+C(m+1)^c$.
