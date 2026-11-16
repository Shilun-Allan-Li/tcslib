# GateHybridChain reuse search

Searched TCSlib and pinned Mathlib for chain_negligible/distAdv_chain_le and stage-step cases
before writing. SliceReduction.chain_negligible already supplies the complete polynomial
summation and negligible closure; it is consumed unchanged. GateStepCases.step_cases supplies
the exact unchanged-or-present argument dichotomy; no arithmetic case proof is copied.
SelectedFields.sample_eq_of_stageBit_eq is the actual-sample congruence for the hSameStage
parameter. No matching complete selected-step-to-endpoint wrapper existed. No general
probability identity is re-derived: unchanged samplers use the published distAdv_def and
sub_self/abs_zero; the probability library has no exact distAdv_self lemma, and the closest
EnsembleLemmas.distAdv_eq_zero_of_subsingleton has a different sample-space premise.
