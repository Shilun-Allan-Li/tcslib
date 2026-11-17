<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.upd_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Middle Coordinate

**Claim.** Replacing the value of the register function at coordinate $1$ by $q$ gives the function with values $p,q,a$ at coordinates $0,1,2$.

**Proof.** Two functions on $\mathrm{Fin}(3)$ are equal when they agree at every coordinate. There are exactly three coordinates to check: at $0$ and $2$, the update leaves the original values $p$ and $a$ unchanged; at $1$, it gives the new value $q$. These are precisely the values of the function with coordinates $(p,q,a)$. The three-coordinate case analysis is supplied by `fin3_cases`.

**Key facts.** `BoolCircuit.AdjScan.fin3_cases`.
