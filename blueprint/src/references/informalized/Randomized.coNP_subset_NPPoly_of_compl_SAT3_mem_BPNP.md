<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP Circuit Certificates from Randomized SAT

**Claim.** If the complement of SAT3 belongs to BPNP, then every language in coNP has polynomial-size, fan-in-two circuit certificates, so coNP is contained in NPPoly.

**Proof.** Let $L$ be in coNP. Since SAT3 is NP-hard, its complement is NP-hard as well in the relevant reduction sense: the reduction theorem supplies a polynomial-time many-one reduction from $L$ to SAT3 complement (SAT3_NPHard). By hypothesis, SAT3 complement is randomly reducible to SAT3. Composing the polynomial-time reduction with this randomized reduction shows that $L$ is randomly reducible to SAT3 (RandReducible.of_polyTimeReducible_left). The theorem that every language randomly reducible to SAT3 has polynomial-size, fan-in-two circuit certificates then gives $L\in\mathrm{NPPoly}$ (BPNP_subset_NPPoly). Since $L$ was arbitrary, the claimed inclusion follows.

**Key facts.** `Complexity.SAT3_NPHard`, `Randomized.RandReducible.of_polyTimeReducible_left`, `Randomized.BPNP_subset_NPPoly`.
