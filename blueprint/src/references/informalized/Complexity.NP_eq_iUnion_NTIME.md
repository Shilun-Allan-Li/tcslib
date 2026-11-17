<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.NP_eq_iUnion_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier and Machine Characterizations of NP

**Claim.** The class NP of languages with polynomial-length certificates checked by polynomial-time verifiers equals $\bigcup_{c\in\mathbb{N}}\mathrm{NTIME}(n\mapsto n^c+1)$.

**Proof.** The proof establishes the two inclusions. First, every language in NP lies in the union of the nondeterministic time classes (`NP_subset_iUnion_NTIME`). Second, for each natural number $c$, every language in $\mathrm{NTIME}(n\mapsto n^c+1)$ belongs to NP (`ntime_poly_subset_NP`); taking the union over all $c$ gives the reverse inclusion. Together these inclusions yield equality.

**Key facts.** `Complexity.NP_subset_iUnion_NTIME`, `Complexity.ntime_poly_subset_NP`.
