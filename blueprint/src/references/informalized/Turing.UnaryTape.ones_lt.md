<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.ones_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary tape below its length

**Claim.** If $0\le c<m$, then the unary tape of $m$ contains the symbol $1$ at position $c$.

**Proof.** The two assumptions are exactly the conditions in the definition of the unary tape for a cell to contain a symbol. Hence its value at $c$ is `some true`, representing $1$.
