# SelectedStep reuse and scope

This new module is a pointwise two-sided sampler contract, independent of the adversary.
It defines no new semantic garbling, message, view, distribution, or machine. It combines
already published reconstruction and stage-support readers. Missing arguments are handled
by c's separate GateStepCases; this theorem is called only with an actual argument p.

- plaintext_ne combines SelectedFields.stageBit_plaintext_ne_even/odd/next, using the
  three possible local phases. It does not repeat the symbolic-label/acyclicity argument.
- unselected_eq dispatches to SelectedFields.stage_first_unselected or
  stage_second_unselected for the actual position zero/one. It does not repeat assignment
  support, zero-row consistency, or selectedPosition search proofs.
- advice_next consumes SelectedPlan.advice_congr and
  SelectedFields.message_tail_stage_eq; it specializes those generic contracts to the
  two actual neighboring stage plaintext families and retains all other fields unchanged.
- reconstruct consumes SelectedTables.sample_reconstruct on each side and advice_next
  to use the identical before-stage advice. Output separation consumes the existing
  GateOccurrences.decoding_label_ne; no output-pair proof is copied.
- Inline argument Nodup/fanin facts unpack DAGCircuit.isFaninTwo_iff; completeness uses
  Finset.mem_toList and Finset.mem_univ. These are the same public-reader compositions
  used inline by SelectedAdviceBounds.sample_advice_budget; that theorem exports a length
  bound rather than these structural facts. No cardinality or encoding proof is repeated.
- Fin.getElem_fin normalizes finite-index and natural-index list notation before omega.
  Normal02 exposed that normalization need; normal03 and all subsequent checks pass.

Searches were the b5 reuse searches plus read-only inspection of SelectedFields' exact
phase/support readers and GateOccurrences' symbolic-label lemmas before implementation.
All imports remain within the already approved helper closure. No foreign source, frozen
file, probability law, or parent-owned file was modified. No new assumption about distinct
actual key values, positive key width, or globally nonempty gate/vertex types was introduced.
