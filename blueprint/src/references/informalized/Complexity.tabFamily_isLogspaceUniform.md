<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableau.lean :: Complexity.tabFamily_isLogspaceUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace uniformity of the tableau family

**Claim.** For every finite-state Turing machine $M$ with Boolean input and output alphabets and all natural numbers $C,d$, the tableau circuit family with time bound $(C+1)(n+1)^d$ is logspace-uniform.

**Proof.** Let $g(n)$ be the encoding of the $n$th circuit in the family. The unary front-word construction is logspace-uniform (Complexity.unaryLogspace_frontWord), and the counter-program uniformity theorem applies to a program that emits the circuit encoding when run on that front word. Its required run and output condition is supplied by the emission theorem (Complexity.emit_run), so the counter-program uniformity result (Complexity.UnaryLogspace.counterProg) yields that $g$ is unary logspace-uniform. The same run gives a polynomial bound on the output length: its time is at most $\mathrm{UTab.emitC}(M)(C+4)^3(n+1)^{3(d+1)}$, and the counter-program output-length bound (Complexity.CounterProg.length_out_le) converts this into a polynomial in $n+1$. Thus the output-length hypothesis required to turn unary logspace uniformity into implicit logspace computability is satisfied (Complexity.UnaryLogspace.implicitlyLogspaceComputable). Finally, extending $g$ to inputs of arbitrary form agrees with $g(n)$ on the unary word of length $n$ (Complexity.unaryExt_replicate). This is exactly the defining uniformity condition for the tableau family.

**Key facts.** `Complexity.unaryLogspace_frontWord`, `Complexity.emit_run`, `Complexity.UnaryLogspace.counterProg`, `Complexity.CounterProg.length_out_le`, `Complexity.UnaryLogspace.implicitlyLogspaceComputable`, `Complexity.unaryExt_replicate`.
