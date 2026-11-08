<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.ZPP_PTM_subset_RP_PTM_inter_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-error time lies in RP and coRP

**Claim.** Every language decidable in zero-error expected polynomial time belongs to both RP and coRP.

**Proof.** Take a language in `ZPP_PTM`. It has abstract zero-error polynomial time by `inZPP_of_mem_ZPP_PTM`. The abstract characterization of zero-error time yields both abstract RP and coRP properties (`zpp_eq_rp_inter_corp_polyTime`). Translating each property by the corresponding membership equivalence gives membership in the machine-based classes RP and coRP (`mem_RP_PTM_iff` and `mem_coRP_PTM_iff`).

**Key facts.** `Randomized.inZPP_of_mem_ZPP_PTM`, `Randomized.zpp_eq_rp_inter_corp_polyTime`, `Randomized.mem_RP_PTM_iff`, `Randomized.mem_coRP_PTM_iff`.
