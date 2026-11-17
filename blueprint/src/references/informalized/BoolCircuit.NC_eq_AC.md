<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.NC_eq_AC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of NC and AC

**Claim.** The class $\textsf{NC}$, the union of the depth-$i$ classes $\textsf{NC}^i$ for $i\ge1$, equals $\textsf{AC}$, the union of the depth-$i$ classes $\textsf{AC}^i$ over all natural numbers $i$.

**Proof.** To prove equality, consider an arbitrary language. Membership in $\textsf{NC}$ is equivalent to having some degree $i\ge1$ for which the language belongs to $\textsf{NC}^i$ (`BoolCircuit.mem_NC_iff`); membership in $\textsf{AC}$ is equivalent to belonging to $\textsf{AC}^i$ for some natural number $i$ (`BoolCircuit.mem_AC_iff`). In the forward direction, keep the same degree: bounded fan-in circuits give well-formed circuits at that degree (`Language.InNC.inAC`), so the language is in $\textsf{AC}$. Conversely, if the language is in $\textsf{AC}^i$, the fan-in reduction theorem places it in $\textsf{NC}^{i+1}$ (`Language.InAC.inNC_succ`). Since $i+1\ge1$, it belongs to $\textsf{NC}$. These two implications establish equality.

**Key facts.** `BoolCircuit.mem_NC_iff`, `BoolCircuit.mem_AC_iff`, `Language.InNC.inAC`, `Language.InAC.inNC_succ`.
