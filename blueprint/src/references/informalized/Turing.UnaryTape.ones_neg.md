<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.ones_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary tape at negative positions

**Claim.** For $m\in\mathbb{N}$ and an integer cell position $c<0$, the unary tape of $m$ is blank at $c$.

**Proof.** A symbol is present on the unary tape only at positions satisfying $0\le c$ and $c<m$. Since $c<0$, the first condition fails, so the tape's value is `none`.
