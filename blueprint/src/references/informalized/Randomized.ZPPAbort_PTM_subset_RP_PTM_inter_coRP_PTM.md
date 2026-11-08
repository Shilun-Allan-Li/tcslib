<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.ZPPAbort_PTM_subset_RP_PTM_inter_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Abort class lies in RP and coRP

**Claim.** Every language in the polynomial-time abort class belongs to both RP and coRP.

**Proof.** Take a language in the abort class. The abort-to-zero-error result places it in abstract zero-error polynomial time (`inZPP_of_mem_ZPPAbort_PTM`). The characterization of zero-error polynomial time as the intersection of RP and coRP then gives both abstract properties (`zpp_eq_rp_inter_corp_polyTime`). Finally, the membership equivalences translate those properties into membership in the machine-based classes RP and coRP (`mem_RP_PTM_iff` and `mem_coRP_PTM_iff`).

**Key facts.** `Randomized.inZPP_of_mem_ZPPAbort_PTM`, `Randomized.zpp_eq_rp_inter_corp_polyTime`, `Randomized.mem_RP_PTM_iff`, `Randomized.mem_coRP_PTM_iff`.
