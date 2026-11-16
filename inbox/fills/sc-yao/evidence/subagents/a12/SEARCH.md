# GateHybridSecurity reuse search

Searched TCSlib and pinned Mathlib for selected_negligible, endpoint_negligible and
GateHybridSecurity before writing. Existing SelectedStepSecurity.selected_negligible
already proves the actual uniform-tape selected bound using B1, finite advice, fiber
averaging and SelectedLaw. Existing GateHybridChain.endpoint_negligible supplies absent
argument cases and the complete polynomial chain. SelectedFields.sample_eq_of_stageBit_eq
is reused for the actual sample congruence. The new helper only composes these contracts;
no reduction, semantic definition, probability identity or summation is copied/re-derived.
For concrete specialization the public List.ofFn_fin_append and innerLen_eq/PolyExpr eval
readers discharge the joint output equation and 7*n+2 fit. B1 is used only via the frozen
sliceMultiMessageSecure_of_prfOut applied to the supplied joint PRF assumption.
