# WrappedVerifier searches, reuse and overlap

The lead approved this helper and the source-only copies of agent-a Normalization.lean and
NormalizationMachine.lean. Their provenance hashes are in wrapped-dependency-provenance.log.
Each copied source was compiled independently in seq-zk-b's olean tree. They were not edited.

Raw reuse searches are in wrapped-searches.log; additional read-only source comparison:
SecureComputation/Yao.lean:352 derives encodeMsgs=encWords locally before its decodeMsgs reader.
The new helper instead imports and reuses agent-a's public encodeMsgs_eq_encWords and
polyTimeComputable_encWords_decWords, avoiding a fresh encoding-equality proof.

New declaration overlaps:
- phaseAux, phaseAux_eq: phase-specific nested-pair data encoding; nearest construction
  LevinTransfer.liftVerifier (ZeroKnowledge/NPLemmas.lean:268) stores an original input and
  auxiliary input in a pair. This phase construction additionally stores a fixed verifier
  tape, phase index and arbitrary earlier message prefix, so the existing construction does
  not have its required interface.
- phaseAux_fields, phaseAux_z, phaseAux_tape, phaseAux_phase, phaseAux_prefix: specialized
  readers for the new encoding. They reuse public pairFstD_pairEncode/pairSndD_pairEncode,
  agent-a encodeMsgs_eq_encWords, BinArith.decWords_encWords (BinaryArith/Words.lean:116),
  and core List.length_replicate, rather than reproving a generic pair or decoder fact.
- phaseAux_length: specialized exact length, directly reusing Turing.length_pairEncode
  (TuringMachine/Encoding.lean:220). It retains the phase index in unary for later advice bounds.
- phaseVerifier, phaseVerifier_coins, phaseVerifier_next, phaseVerifier_coinLen,
  phaseVerifier_next_phaseAux: new fixed-tape, prefix-extending strategy and its readers.
  Nearest construction LevinTransfer.liftVerifier/liftVerifier_next (:268/:274) changes the
  common input and tape prefix rather than fixing an auxiliary tape and extending history.
  Neither that construction nor its statement can be reused directly.
- phaseVerifier_efficient: nearest relative LevinTransfer.liftVerifier_efficient (:295)
  and earlier SeqEfficiency.phase_poly. It uses the same existing uniform output/layout
  combinators, plus agent-a's canonical prefix reencoding and public
  CommitmentLemmas.encodeMsgs_append (:233). The imported published constituent lemmas
  are reused; no machine, private lemma, host or generic canonicalization proof is copied.

Promotion request: phaseAux and phaseVerifier are specific to this sequential-composition
construction and should stay here. A future shared fixed-tape strategy-preprocessing closure
lemma could subsume phaseVerifier_efficient and LevinTransfer.liftVerifier_efficient; no frozen
file change is needed for this delivery.

- phaseAux_poly: direct repeated use of public PolyTimeComputable.pairEncode followed by
  the new encoding equation. Nearest generic relative NUPPT.polyTimeComputable_layout
  (Randomized/Closure.lean:~180) assembles a different four-field machine layout, so the
  exact phase auxiliary encoding requires this short composition.

- phaseAux_length_le: directly applies the new phaseAux_length and public
  CommitmentLemmas.length_encodeMsgs_le (:241), then monotonicity of multiplication.
  It specializes the generic encoding bound to the new auxiliary layout; the generic
  message bound is reused rather than reproved.
