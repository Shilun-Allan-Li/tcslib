<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.upd_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First Register

**Claim.** Replacing the value of the register function at coordinate $0$ by $q$ gives the function with values $q,c,a$ at coordinates $0,1,2$.

**Proof.** Equality of the register functions follows by checking their values at the three coordinates. At $0$, the update gives $q$; at $1$ and $2$, it preserves the original values $c$ and $a$. These are the coordinates of the function $(q,c,a)$, and `fin3_cases` covers every coordinate.

**Key facts.** `BoolCircuit.AdjScan.fin3_cases`.
