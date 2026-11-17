<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.rg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Register Tuple

**Claim.** The constant function on the four register indices with value zero equals the register tuple $(0,0,0,0)$.

**Proof.** Two functions on the four register indices are equal if they agree at every index. The proof checks the four possible indices, $0,1,2,3$, using the exhaustive four-index case principle (`BoolCircuit.AdjWalk.fin4_cases`). At each index both the constant function and the register tuple have value zero, so the functions agree everywhere.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
