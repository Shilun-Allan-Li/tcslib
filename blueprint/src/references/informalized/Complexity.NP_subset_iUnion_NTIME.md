<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.NP_subset_iUnion_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Has Polynomial Nondeterministic Time

**Claim.** Every language in $\mathrm{NP}$ belongs to $\bigcup_{c\in\mathbb{N}}\mathrm{NTIME}(n\mapsto n^c+1)$.

**Proof.** Take $L\in\mathrm{NP}$, witnessed by a verifier language $V\in\mathrm P$ and certificates of length $C(n+1)^c$. The polynomial-time characterization of $\mathrm P$ (`mem_P_iff`) supplies a deterministic machine deciding $V$ within $A(n+1)^d$ time for some constants. The compilation theorem (`b2_compile`) combines that verifier with nondeterministic guessing of a certificate, producing a nondeterministic decider for $L$ whose running time is bounded by $K(n+C(n+1)^c+1)^r$ for suitable constants. The normalization theorem (`cont_guess_normalize`) absorbs this polynomial bound into one of the standard bounds $n^e+1$ and places $L$ in the stated union.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.b2_compile`, `Complexity.cont_guess_normalize`.
