<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-error characterization

**Claim.** The class of languages decidable in zero-error expected polynomial time equals the intersection of RP and coRP.

**Proof.** One inclusion is the result that zero-error polynomial time lies in RP intersect coRP (`ZPP_PTM_subset_RP_PTM_inter_coRP_PTM`). For the reverse, let a language belong to both machine-based classes. The membership equivalences give the corresponding abstract RP and coRP properties (`mem_RP_PTM_iff` and `mem_coRP_PTM_iff`). Their conjunction yields abstract zero-error polynomial time by the zero-error characterization (`zpp_eq_rp_inter_corp_polyTime`), and the realization theorem places the language in `ZPP_PTM` (`inZPP_subset_ZPP_PTM`).

**Key facts.** `Randomized.ZPP_PTM_subset_RP_PTM_inter_coRP_PTM`, `Randomized.mem_RP_PTM_iff`, `Randomized.mem_coRP_PTM_iff`, `Randomized.zpp_eq_rp_inter_corp_polyTime`, `Randomized.inZPP_subset_ZPP_PTM`.
