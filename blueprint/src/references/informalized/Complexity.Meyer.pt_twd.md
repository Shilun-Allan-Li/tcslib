<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_twd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four polynomial-time transformations

**Claim.** For each of the four specified transformations, the resulting function on Boolean words is polynomial-time computable.

**Proof.** Split into the four choices of transformation. For the second component of the twice-nested pair parsing, use the established polynomial-time computability of $vt$ (Complexity.Meyer.pt_vt). For its fixed-width increment with empty output on overflow, compose the increment function with $vt$; both are polynomial-time computable, and polynomial-time functions are closed under composition (Complexity.PolyTimeComputable.comp). For each of the two replication choices, apply the polynomial-time bounded replication result with the corresponding bit, $0$ or $1$ (Complexity.Meyer.pt_rep). These cases cover all four transformations.

**Key facts.** `Complexity.Meyer.pt_vt`, `Complexity.Meyer.pt_inc`, `Complexity.PolyTimeComputable.comp`, `Complexity.Meyer.pt_rep`.
