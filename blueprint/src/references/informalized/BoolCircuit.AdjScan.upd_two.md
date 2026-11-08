<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.upd_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Third Register

**Claim.** Replacing the value of the register function at coordinate $2$ by $q$ gives the function with values $p,c,q$ at coordinates $0,1,2$.

**Proof.** It suffices to compare the two functions at each coordinate of $\mathrm{Fin}(3)$. At $0$ and $1$, the update leaves the values $p$ and $c$ unchanged; at $2$, it gives $q$. This agrees with the function whose coordinates are $(p,c,q)$. The three cases exhaust $\mathrm{Fin}(3)$ (`fin3_cases`).

**Key facts.** `BoolCircuit.AdjScan.fin3_cases`.
