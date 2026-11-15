# Generic explicit-error repetition engine plan

The lead requested an abstract repeated protocol Π without importing owned SequentialZK.
Proposed packing is `PaddedVerifierSpec π Π x q p terminal : Prop`. At fixed x put
k=π.rounds.eval|x| and c=π.V.coinLen|x|. The terminal function has arguments z,r,hist.

Fields directly supplied from owned published readers:
1. Π verifier coin length q*c; Π rounds 2*k*q; same first mover.
2. Padded verifier next equation with arbitrary terminal at history length q*k, otherwise
   original π.V on block idx/(2*k), suffix dropping phase*k, and [] on filler moves.
3. Terminal equals the binary all-phases verdict using each phase's first p real prover slots.
4. Verifier move-index recovery on actual source histories for every arbitrary P and tapes.
5. Both histories after 2*k*j moves have length j*k, for j≤q.
6. Original verifier history after k moves has length p, for every arbitrary local prover.
7. Mover periodicity at offsets 2*k*j.

No additional arithmetic, efficiency, message-boundedness, output-shape, or witness premise
is required. The lead can instantiate each field from its existing owned definitions/readers.

First helper: phase_take for arbitrary cheating prover/fixed prover tape. Apply exec_phase
with global Π.V, local π.V, offset2*k*j and local verifier block j. Its reply contract is
obtained from padded next + recovered index + boundary history length. Before a real move
its history is not terminal. Modular arithmetic identifies idx residue and quotient. Then
exec_snd_take, phase-end length j*k+p, and List.take_drop identify the final aggregate phase
history with the local original execution. k=0 is an explicit empty-execution case.

Probability engine:
- q=0 gives rejection bound0 by uprob_nonneg.
- Fix cheating prover coins using Protocol.exists_proverCoins_le for acceptance.
- Read Π's verifier tape as q independent π.V coin blocks by FunFamily.blocks and the
  supplied coin-length equality. Use published ofFn/blocks readers, not manual slicing.
- For Good i pre fresh, fill a q-block table with pre below i and zero blocks afterwards.
  Execute Π to phase boundary i on this zero-tail tape; hardwire its earlier prover-received
  history and fixed prover tape with prefixProver. Good is original π acceptance on fresh.
- Every Good section has probability≤s(|x|) by prefixProver_accept_le. Obtain nonnegative
  s(|x|) by InteractiveProofErr.sound_nonneg.
- For an actual full block table, VerifierPrefix proves its phase-i earlier transcript equals
  that of its prefix-plus-zero-tail table. phase_take then identifies every aggregate phase
  test with Good i actualPrefix actualBlock. Thus aggregate acceptance implies all Good.
- uprob_adaptive_all_le gives acceptance≤s(|x|)^q; the binary aggregate output converts
  this to rejection≥1−s(|x|)^q.

Avoid untyped dependent probability calc chains: use explicit typed event/probability
intermediates, public uprob_comp_equiv/mono/product readers, and direct equality rewrites.
Split structure/phase support into RepeatedVerifier.lean if the main file would approach1000.

Nearest overlap relatives: own exec_phase and VerifierPrefix directly reused; original owned
seqRep_exec_phase is honest-only and does not give arbitrary-prover phase tests. Existing
GI.coinSlice_blocksEquiv (SoundnessRep.lean:223) is a compatibility inverse-block reader;
prefer direct canonical FunFamily.ofFn_blocks reuse rather than re-proving coin slices.
