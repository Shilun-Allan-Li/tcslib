<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.offsets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lupanov offset identities

**Claim.** The offsets satisfy $o_Z+1=n+2\cdot2^{n-k}$, $o_F+1=o_Z+2\cdot2^k$, $o_C=o_F+2^{2^k}$, and $T=o_C+2^{n-k}$; moreover, each of $2^{n-k}$, $2^k$, and $2^{2^k}$ is at least one.

**Proof.** The power-of-two successor identity gives $2^{a+1}=2\cdot2^a$, both for $a=n-k$ and for $a=k$. Substituting these into the definitions of $o_Z$ and $o_F$ yields the first two offset equations. The equations for $o_C$ and $T$ follow directly from their definitions. Finally, every natural-number power of two is at least one, giving the three lower bounds.

**Key facts.** `BoolCircuit.Lupanov.two_pow_succ_eq`.
