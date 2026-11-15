# RealPhases overlap and reuse

This helper imports no owned module. Source-only copies of author seq-zk-c's checked stable
Soundness and updated Phases modules were independently compiled in seq-zk-b's olean tree.
Hashes, provenance, and raw successful compile output are retained. Those sources were not
edited and no foreign olean was copied.

Raw searches are in real-phases-searches.log. They found no generic empty-prover suffix reader
or arbitrary-verifier real/padded sequential endpoint in TCSlib or pinned Mathlib.

New declarations:
- exec_snd_empty: nearest relative Composability.exec_prefix
  (SequentialZK/Soundness.lean:42) shows only that both earlier histories remain prefixes.
  Empty contents of all newly received prover messages require the stronger suffix statement.
  The elementary induction uses only public exec_succ, mover readers, and List append/replicate
  equations; no private lemma or proof block is copied. Its arithmetic identification uses
  the public List.length_append/length_replicate and Nat.add_sub_cancel_left readers.
- exec_real_phase: DIRECTLY REUSES the newly checked public
  Composability.exec_phase_of_moves (SequentialZK/Phases.lean:~58), with original P and the
  fixed-tape phaseVerifier V. It does not duplicate that real-phase induction. The verifier
  contract directly reuses phaseVerifier_next_phaseAux (WrappedVerifier.lean:128),
  Composability.exec_snd_take (Soundness.lean:76), and List.take_append_drop.
  Nearest source endpoint is owned Protocol.seqRep_exec_phase (base SequentialZK.lean:280),
  but that theorem couples two honest repeated parties, whereas this theorem handles an
  arbitrary cheating verifier and the zero-coin fixed-prefix wrapper. The new proof's local
  quotient/remainder equalities have the same arithmetic formulas as unexported local hmod/
  hdiv inside that owned proof; they are re-derived using public Nat.add_mul_mod_self_left,
  Nat.add_mul_div_left, Nat.mod_eq_of_lt and Nat.div_eq_of_lt. No private fact is referenced
  or copied. Index recovery and phase-start counts are supplied by the caller.
- exec_padded_real_phase: directly combines exec_real_phase and exec_snd_empty. The shifted
  filler-position remainder is proved through public Nat arithmetic readers. The exact
  number k-p uses caller-provided initial/final/local counts, rather than duplicating owned
  alternating-move count proofs. The arbitrary verifier's filler replies have no premise.

Promotion: exec_snd_empty belongs beside the interactive-execution API in Interaction.lean
at a shared-file window. The two sequential real/padded endpoint results belong in this
source-specific helper. No frozen-file edit or new host is needed.
