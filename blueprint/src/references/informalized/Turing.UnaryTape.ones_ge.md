<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.ones_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary tape beyond its value

**Claim.** For $m\in\mathbb{N}$ and an integer cell position $c$ with $m\le c$, the unary tape of $m$ is blank at $c$.

**Proof.** The unary tape contains a symbol only when both $0\le c$ and $c<m$. The assumption $m\le c$ rules out $c<m$, so the defining conditional takes its blank value `none`.
