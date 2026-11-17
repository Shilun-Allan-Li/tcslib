<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.NEXP_eq_iUnion_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NEXP as a union of time classes

**Claim.** The certificate-defined class $\mathrm{NEXP}$ equals $\bigcup_{c\in\mathbb{N}}\mathrm{NTIME}(n\mapsto 2^{n^c})$.

**Proof.** Prove the two set inclusions. The inclusion from $\mathrm{NEXP}$ into the union is supplied by the theorem that every certificate-defined NEXP language lies in some exponential nondeterministic time class (Complexity.NEXP_subset_iUnion_NTIME). For the reverse inclusion, take any language in the union; it belongs to one of the indicated time classes, and the corresponding containment theorem places that class inside NEXP (Complexity.ntime_expPow_subset_NEXP). The two inclusions give equality.

**Key facts.** `Complexity.NEXP_subset_iUnion_NTIME`, `Complexity.ntime_expPow_subset_NEXP`.
