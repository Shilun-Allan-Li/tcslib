<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.ImplicitlyLogspaceComputable.comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Implicit Logspace Computations

**Claim.** If $f$ and $g$ have polynomially bounded output lengths and their output-bit and output-length index languages are decidable in logarithmic space, then $g\circ f$ has polynomially bounded output length and both corresponding index languages are decidable in logarithmic space.

**Proof.** Write the polynomial bounds as $|f(x)|\le C(|x|+1)^c$ and $|g(y)|\le D(|y|+1)^d$. The composition length estimate gives $|g(f(x))|\le D(C+1)^d(|x|+1)^{cd}$ (`comp_length_le`). For the index languages, first use the implicit-computability of $f$ to obtain the logarithmic-space computation of its query word $\operatorname{compQ}(f,w)$ (`ImplicitlyLogspaceComputable.compQ`). Membership in the output-bit index language for $g\circ f$ is equivalent to membership of this query word in the output-bit index language for $g$ (`mem_indexLang_compQ_iff`); the logarithmic-space preimage theorem therefore gives the required logarithmic-space decision procedure (`mem_LOGSPACE_preimage`). The same equivalence and preimage argument applied to the output-length index language for $g$ proves the second membership. Together with the polynomial length bound, these are exactly the three conditions for implicit logspace computability.

**Key facts.** `Complexity.ImplicitlyLogspaceComputable.compQ`, `Complexity.comp_length_le`, `Complexity.mem_indexLang_compQ_iff`, `Complexity.mem_LOGSPACE_preimage`.
