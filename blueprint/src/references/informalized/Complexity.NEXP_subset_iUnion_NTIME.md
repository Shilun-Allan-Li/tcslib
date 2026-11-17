<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.NEXP_subset_iUnion_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NEXP lies in exponential nondeterministic time

**Claim.** Every language in the certificate-defined class $\mathrm{NEXP}$ belongs to $\bigcup_{c\in\mathbb{N}}\mathrm{NTIME}(n\mapsto 2^{n^c})$.

**Proof.** Take a language in NEXP, with its certificate-length parameters and verifier language. Since the verifier language is in P, the polynomial-time characterization of P supplies a deterministic machine and polynomial bound deciding it (Complexity.mem_P_iff). Apply the certificate-verification simulation theorem (Complexity.a2_compile) to obtain a nondeterministic machine deciding the original language within a bound polynomial in the input length and certificate length. The normalization theorem (Complexity.a2_normalize) converts that bound, with the certificate length specified by the NEXP witness, into a bound of the form $2^{n^e}$ for some natural number $e$. Thus the language lies in one member of the stated union.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.a2_compile`, `Complexity.a2_normalize`.
