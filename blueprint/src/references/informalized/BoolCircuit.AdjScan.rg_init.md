<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.rg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-register initialization identity

**Claim.** The constant function assigning zero to each of the three registers equals the register assignment $(0,0,0)$.

**Proof.** Two functions agree if they agree at every input. The index set has exactly three elements, indexed by $0$, $1$, and $2$. At each of these indices, both the constant-zero function and the assignment $(0,0,0)$ take value zero (`fin3_cases`). Hence the functions are equal.

**Key facts.** `BoolCircuit.AdjScan.fin3_cases`.
