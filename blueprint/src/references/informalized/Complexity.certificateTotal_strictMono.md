<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.certificateTotal_strictMono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict increase of padded length

**Claim.** For all $C,c\in\mathbb{N}$, the function $n\mapsto n+(C+1)(n+1)^c$ is strictly increasing.

**Proof.** Take $m<n$. Then $m+1\le n+1$, so raising both sides to the natural power $c$ preserves the inequality. Multiplying by the nonnegative number $C+1$ also preserves it. Adding the strict inequality $m<n$ to the resulting weak inequality gives $m+(C+1)(m+1)^c<n+(C+1)(n+1)^c$.
