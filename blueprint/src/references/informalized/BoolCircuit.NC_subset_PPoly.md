<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.NC_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Size of NC

**Claim.** Every language in $\textsf{NC}$ has polynomial circuit size: it is recognized by a fan-in-two circuit family whose size is bounded by $a(n+1)^k$ for some natural numbers $a$ and $k$.

**Proof.** Let $L\in\textsf{NC}$. By the characterization of membership in this union, there is a degree $i$ such that $L\in\textsf{NC}^i$ (`BoolCircuit.mem_NC_iff`). The polynomial-size circuit theorem for each $\textsf{NC}$ level then gives $L\in\textsf{PPoly}$ (`Language.InNC.inPPoly`), which is precisely the asserted polynomial size bound for a fan-in-two circuit family.

**Key facts.** `BoolCircuit.mem_NC_iff`, `Language.InNC.inPPoly`.
