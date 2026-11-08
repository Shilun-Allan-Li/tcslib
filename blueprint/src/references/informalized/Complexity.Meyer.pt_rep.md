<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_rep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time bounded replication

**Claim.** For fixed $C_w,c$ and bit $b$, after applying the total first projection twice to $z$ to obtain $x$, the function outputting $C_w(|x|+1)^c$ copies of $b$ is polynomial-time computable.

**Proof.** The twice-applied total first projection $vx$ is polynomial-time computable (Complexity.Meyer.pt_vx). The unary polynomial bound result (Complexity.PolyHierarchy.unaryPT_poly) applied to $vx$ supplies polynomial-time computability for the length-dependent bound $C_w(|vx(z)|+1)^c$. The constant-output result (Complexity.Meyer.pt_constMap) and closure under composition (Complexity.PolyTimeComputable.comp) then give polynomial-time computability of the constant word whose length is that bound. By the definition of the bound, this output is exactly $C_w(|x|+1)^c$ copies of $b$, as required.

**Key facts.** `Complexity.Meyer.pt_constMap`, `Complexity.Meyer.pt_vx`, `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.PolyTimeComputable.comp`.
