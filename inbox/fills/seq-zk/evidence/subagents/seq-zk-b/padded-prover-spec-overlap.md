# PaddedProverSpec overlap and reuse

The lead approved this construction contract, including all-natural-index/all-natural-phase
reader fields and the two direct endpoint methods. The structure has no relation or B premise.

New declarations:
- PaddedProverSpec and its nine field projections package direct source construction equations.
  The nearest related contract is seq-zk-c's public Composability.PaddedVerifierSpec at
  SequentialZK/RepeatedVerifier.lean:38. The new structure is its prover-side counterpart:
  it has no terminal-verdict field, fixes the honest prover rather than the verifier, and
  allows any cheating verifier. Its original_count is for fixed π.P and arbitrary V, the
  dual of that contract's arbitrary-P/fixed-π.V local_length field. Its boundary reader holds
  at every natural phase index, as supplied by the owned global length readers. No foreign
  equation theorem is re-proved: the owned module will instantiate each field once from
  seqProver_next, seqRep_P, seqRep_rounds_eval, seqRep_verifierFirst, proverMoveIndex_exec,
  exec_fst_length/exec_snd_length, the public count readers and the mover-period reader.
- PaddedProverSpec.real_phase directly instantiates the new public exec_real_phase
  (RealPhases.lean:~92), with no repeated execution induction or arithmetic proof.
- PaddedProverSpec.padded_phase directly instantiates the new public exec_padded_real_phase
  (RealPhases.lean:~161), using the contract's original_count at phaseVerifier V and its
  phase-boundary fields. It does not repeat any filler or phase proof.

No equivalent padded-prover contract was found in TCSlib or pinned Mathlib. Raw searches are
in padded-prover-spec-searches.log. The contract and its methods are sequential-construction
specific and should remain in this helper; no frozen-file promotion/edit is requested.
