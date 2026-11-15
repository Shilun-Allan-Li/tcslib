# seq-zk checkpoint 3

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Issued exchange pack: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
Local proof branch `fill/seq-zk` remains local. Complete three-commit series:
`a758032d636fd410b0c4b8a1530a96d000cc467a`,
`e978a28274fdeb545e622ae28747221088352512`,
`04c253e48d9c0ebb73943f39412365cd4d8e02db`.

This is checkpoint 3, not the final payload. Four whole frozen declarations are proved:

| Target | Status |
|---|---|
| InteractiveProof.seqRep | Proved, checked, standard axioms |
| InteractiveProofErr.seqRep | Proved, exact error s(n)^Q(n), standard axioms |
| EfficientProverProofErr.seqRep | Proved, checked, standard axioms |
| StatZK.seqRep | Proved, exact statistical error Q(n)*δ(n), standard axioms |
| ZK.seqRep | Original statement and admission remain; computational assembly in progress |

StatZK.seqRep and its proved consumers PerfectZK.seqRep and PerfectZKAbort.seqRep use only
propext, Classical.choice and Quot.sound. The remaining ZK target and its ThreeColoring
consumer retain sorryAx and are not claimed proved. All five statement headers are byte-for-byte
identical to the issue base. The source census records all359stored constants; every new or
changed declaration avoids sorryAx (56new/changed axiom-set rows versus checkpoint2).

## Proof and ownership

The statistical proof supplies a uniform strict-PPT machine using one cheating-verifier
tape and Q independent phase-simulator tapes. It validates every raw phase view, fixes the
known input/auxiliary/empty wrapper-tape fields, normalizes exactly p real prover slots of
at most B bits, and supplies empty honest-prover fillers. Malformed outputs use the canonical
fallback. Real phase views are fixed points by their exact count and bounded messages.
The arbitrary cheating verifier's filler replies remain unrestricted.

For each fixed global verifier tape, the caller-supplied sampler-recursion theorem combines
one-phase comparisons at arbitrary prefixes, using averaging, randomized postprocessing and
triangle inequality. Pairing the prefixes with their common verifier tape and averaging
preserves exactly Q*δ. Explicit finite split/block equivalences identify the real execution
and the uniform SQ machine, with no extra error. Zero phases, zero rounds, odd rounds and
either first mover are covered. Nonnegativity of δ is derived only at witnessed inputs,
from the original comparison; no new global sign assumption is imposed.

The three earlier proof-system results still use perfect completeness on independent slices,
the original negligible soundness for InteractiveProof, and the adaptive conditional product
bound s^Q for explicit error. Efficient-prover repetition preserves efficiency, the bound,
and completeness for every witness. The generic error engine covers q=0 with error1, so the
frozen hQ remains unused in InteractiveProofErr.seqRep; this native warning is disclosed.

Only the lead edited the owned module, committed fill/seq-zk, ran merged checks, and prepared
delivery. The main status and exact Contents list now describe the four proved targets.
StatZK's sketch names the endpoint contract/equivalences. No statement or global simp attribute
was weakened, and no foreign private proof was copied.

| Worker | Included proofs and source ownership |
|---|---|
| Lead /root, seq-zk | Four target bodies; owned bridges/specification instances; PrefixFolds, PrefixLaws, ProofTransfers, StatisticalTransfer; approved StatZK_iff |
| /root/zk_route, seq-zk-a | Normalization, NormalizationMachine, PhaseView, Statistical, ExecutionBounds, NormalizedStep, StatisticalRecursion, StatisticalPrefix |
| /root/efficiency, seq-zk-b | Efficiency, WrappedVerifier, SimulatorMachine, RealPhases, PaddedProverSpec, SuffixMachine |
| /root/soundness, seq-zk-c | Soundness, Phases, Congruence, VerifierPrefix, ErrSoundness, RepeatedVerifier, RepeatedSoundness, Advice, StatisticalPostprocess, EndpointSampling |

Thirty changed/new library files are delivered: the owned module,28helpers and the approved
Defs reader. The complete stored-constant inventory is checkpoint3-stored-constants.tsv.
Every public declaration's formula/docstring and reader is in src/. Canonical _eq readers
were added for phaseVerifier, phasePrefix and the three endpoint equivalences; existing
construction statements and bodies are preserved.

Additional computational work is retained only as labeled future evidence snapshots outside
this proof revision: BoundedMetadata, RealPrefixBounds, ComputationalReduction,
ReductionAdvantage, HybridRecursion, SuffixLaws, ComputationalAdvice, ContinuationProbability,
and ComputationalHybrid, with their author checks/attempts. Their source_status fields and
snapshots make the boundary explicit. ComputationalPhaseBound postdates the frozen receipt and is excluded
from this checkpoint. None of these future helpers is silently included in src/ or the three patches.
The original uncompiled StatisticalTransfer draft remains historical evidence; the real
clean checked source in src/ is authoritative.

## Host and environment

Host-wide cap: at most3Lean processes across all jobs. Every lead/subagent lean/lake/check
command uses the issued stable lean-slot.sh and default ~/.lean-slots, with seq-zk/a/b/c tags.
Only the lead runs Lake, with three slots for every narrowed cache get. Each agent has its
own worktree/olean tree and read-only package symlink to the lead; only completed lead TCSlib
oleans are APFS-cloned. No package tree is copied or merged. The genuine base tree remains
separate from the working tree. New runners also hold a per-olean-tree writer lock.

Mac preflight:12CPUs,19,327,352,832physical-memory bytes; initial headroom5,104,074,752bytes
(4.754GiB), APFS free229,666,520KiB (above12GiB). Later recorded headroom readings remain
above4GiB, including root's latest6.192GiB. No shortage, E-RES or RAM-disk path occurred.
Both issued packs and all237source hashes verified. The original76roots matched the pack.
All present packages match the pinned manifest; the four documentation packages are ABSENT.
No zero-size oleans; root-import cache probe passed. The host archive store initially held
32,667files/1,595,387,830bytes (earlier origin unknown). Initial fetch downloaded none and
unpacked2,107archives. Later Advice work adds exactly Mathlib.Data.Fintype.Lattice and
Mathlib.Data.Real.Archimedean: pins reverified, narrowed -k3cache exited0, no downloads,
901archives unpacked. No other new direct Mathlib root is included in this checkpoint.

Resource-only coordination with derand/sc-garble/Ladner followed Seyoon's explicit permission.
Normal slot waits and boundary gaps are logged, not classified as E-RES. No other worker's
working tree, process or slots were edited, removed or interrupted.

## Checks completed and final checks remaining

- Exact-base bootstrap:237modules,0errors/nonzero exits, exactly23admission warnings.
- Every included helper checked by its author and by the lead in the merged working tree.
- Owned module passes with0errors, one original ZK admission, and the disclosed unused hQ.
- Full stored-constant/consumer axiom census:359rows; all new/changed declarations standard.
  Four targets and both perfect/aborting consumers are standard. ThreeColoring's joint ZK
  consumer correctly retains sorryAx from the still-admitted ZK target.
- Five frozen statement headers exact; all30library files≤100columns/1,000lines (owned958).
- Style lint remains92FAIL/101WARN. No new FAIL. The only WARN-line difference is the
  approved StatZK reader improving Defs missing-reader count3→2. Full line-set diff retained.
- Independent git-am replay reproduced EACH of all three exact commit hashes and all30source
  files, using complete author/committer dates/identities and signing metadata.
- Base strict/coe×eval-excluded/included seals completed for the two existing changed files.
  Owned passes all4cells. Defs has10inherited diagnostics in6declarations, unchanged below.
- Complete stable checkpoint1helper/Defs matrix:20cells; four helpers pass every variant,
  Defs retains the inherited failures. Projection-only FinDist CoeFun exclusion changes no
  failure; native classifier and exact exclusions are retained. A excludes eval; B includes it.
- CP3owned canonical coe/eval-excluded seal passes0errors, all1,880native requests verified
  at installation and EOF, including identity/home/component/instance-mask guards.
- Paired controls:5unsealed probes pass; each of5sealed negatives fails exactly once at its
  expected declaration, while each published-reader positive passes. All singleton native
  guards verify. Targets:padFin/inArg in A/B and eval in B; unrelated archived controls
  absent from these request sets are explicitly marked absent.

The final merged full sweep and admission census, complete final matrices for newer helpers
and final owned source, and explicit-unfold scan remain final-delivery work. Prepared or
historical draft sources are never claimed passing. Any reused stable seal must match source,
import closure, pins and exact request sets byte-for-byte; otherwise it reruns. The issued
route requests this whole-declaration checkpoint now. Sending it before final-only checks
is the same disclosed timing judgment under Seyoon's best-judgment instruction as earlier
checkpoints; this report does not claim final intake completion.

Inherited Defs seal failures in each baseline/stable cell: perfectZK_zeroRounds;
AbortRetry.attempt_poly; AbortRetry.exists_retrySimulator; AbortRetry.statClose_retry;
PerfectZKAbort.statZK; negligible_inv_pow_sqrt_div. Their10raw diagnostics/source-line
attributions and strict/coe/eval variants are retained rather than suppressed.

## Exceptions and corrected compiler diagnoses

Seyoon's exact best-judgment/resource-coordination instruction is retained in coordination.
There have been10authorized own-child proof-debugging interruptions:8in seq-zk-a
(StatisticalRecursion01 and NormalizedStep01–07),1in seq-zk-c (ErrSoundness01), and1by the
lead (StatisticalTransfer01). Every exact child/command/parent was reverified before SIGINT;
wrappers flushed and released normally. Complete sources, raw logs, process/resource readings,
authorizations and samples/markers are preserved. They are diagnosed debugging exceptions,
not elapsed-time timeout commands or E-RES. No other job was interrupted.

The final diagnoses correct earlier tentative source-stage interpretations:
- NormalizedStep was missing ZeroKnowledge.Defs, leaving NUPPT.simulate unresolved in its
  signature. Root/c missed this import defect during source review. Reducible-only explicit
  applications exposed the actual error promptly. Adding the precise import and correcting
  the application layout yielded a clean successful proof (then a checked public fixed-point
  reader). No library defect is inferred from the earlier stalls.
- Root StatisticalTransfer01 similarly followed an invalid API argument: phaseVerifier_efficient
  has implicit {V}; root supplied V positionally. The read-only review missed this binder
  mismatch. Attempt02 exposed it; the correct named V argument and explicit typed applications
  passed clean03 in2.18s. All temporary diagnostic IO/markers were removed before intake.
- Earlier statistical-recursion/ErrSoundness diagnoses and successful typed/reader rewrites
  remain in their exact ledgers. Tentative dot-reader/calc-stage claims are qualified there.

Large raw samples are losslessly numbered ZIP parts with exact entry lists, raw SHA/length
and byte-verified extraction; originals remain outside the payload. Root's smaller complete
3,184,721-byte sample is delivered directly (SHA dd018e025215ac0fcd5fcefbc316af0f572ab518c3d16b94e53c7c8a73f7b158).
No raw diagnostic bytes are omitted and no live log was moved. Closed-file manifests freeze
and hash-verify each subagent snapshot. Raw failures and invalid dependent/missing-prerequisite
checks are retained and explicitly separated from mathematical findings. CP2's evidence-copy
schema corrections and CP3's stale future-source hash rejection are recorded; neither changed
a checked proof result. No automatic approval-review rejection occurred.

## Remaining computational obligation

ZK.seqRep still needs the common witness-uniform negligible phase bound from bounded
witness-free advice, followed by the checked conditional hybrid and exact endpoint transfer.
The selector ranges over finite bounded metadata while witnesses remain arbitrary; the
machine never decides relation/reachability validity. Uniform suffix/reduction and generic
hybrid helpers are checked future work. The final error is Q times the absolute negligible
bound, using the published polynomial-times-negligible theorem. No target has been weakened,
and no target-falsity or missing-fact escalation is claimed.

## Overlap and reuse

Searches before implementation are in `lead-searches.log` and each subagent's search logs.
Every overlap below is either direct reuse or a disclosed generalization; no foreign private
lemma was copied.

- `ProverBounded.seqRep`: nearest Interaction.lean:383 `ProverBounded.mono` changes the bound,
  not the protocol; the new lemma reads the repeated prover and reuses proverBounded_iff.
- `seqVerifier_exec_first`: nearest owned original `seqRep_exec_phase` (base line 287) assumes
  the honest repeated prover. The new induction covers an arbitrary unchanged prover in
  phase zero, using the published move-index readers rather than that stronger honest premise.
- `seqRep_outV_eq`: combines owned `seqVerdict_eq` (base :233) and Interaction.lean:449 outV_eq
  with the existing move count. It publishes the final-history specialization.
- `seqRep_exec_phase_take`: combines original seqRep_exec_phase, the new generic exec_snd_take,
  and core List.take_drop; it adds final-history restriction, not a duplicate phase induction.
- `seqRep_complete`: nearest graph-specific completeness arguments in
  ZeroKnowledge/ThreeColoring/ProtocolProofs.lean and GraphIsomorphism/Proofs.lean; directly
  reuses HardcoreBit/Basic.lean:110 forall_of_uprob_eq_one and :123 uprob_eq_one_of_forall,
  Adversary.lean:98 length_coinBlock and :216 ofFn_padFin_of_length.
- `seqRep_reject_of_first`: new aggregate-conjunction consequence of the first-phase reader;
  nearest original seqRep_exec_phase has the different honest-prover premise noted above.
- `seqRep_sound_first`: reuses HardcoreBit.pushesUniform_restrict/prodMap and public
  Asymptotic/ReductionSupport.lean:288 take_ofFn_castLE. GI/Proofs.lean:813
  pushesUniform_castLE is a specialization of the same restriction reader, not copied.
- `seqProver_efficient` and `seqVerifier_efficient`: construction-specific bridges directly
  reuse SeqEfficiency.phase_efficient and verifier_efficient; no machine argument is repeated.
- `StatZK_iff`: exact defining reader, analogous to Defs.lean:164 ZK_iff; added only with the
  explicit scope approval below, in its defining file.
- `encodeMsgs_eq_encWords`: exactly matches the local have in SecureComputation/Yao.lean:352,
  outside the allowed closure. It is re-derived from published encoding nil/cons readers.
  ThreeColoring/Machines.lean:911 encodeMsgs_eq_flatMap is another nearest relative.
- `normalizeMsgs` and its reader/invariants are new canonical-slot operations. Their length,
  per-message, fixed-point, and encoding bounds directly reuse decWords_encWords,
  List.take_of_length_le, and BinaryArith/Words.lean:81 length_encWords_le.
  CommitmentLemmas.lean:241 gives the same generic encoding-size bound with a larger dependency;
  no copy is used. `length_encodeMsgs_normalizeMsgs_le` specializes the directly reused bound.
- `polyTimeComputable_encWords_decWords`, `polyTimeComputable_decWords_getD`, and
  `polyTimeComputable_encode_normalizeMsgs`: directly reuse Words.lean:221 mapW,
  BinaryArith/Loops.lean:391 getW, EncodingMachines.lean:459 truncate_poly, and
  ThreeColoring/Machines.lean:159 counted emission, rather than copying hosts.
- `take_encodeMsgs` uses CommitmentLemmas.lean:233 encodeMsgs_append plus List.take_append;
  its new encoded-prefix formula had no public match in the searched closure. `takeMsgs_poly`
  directly composes this with the public drop/count machinery. `phase_poly`,
  `phase_efficient`, `verdict_poly`, and `verifier_efficient` reuse GI/Proofs.lean's
  efficient_of_polyTime and GI/EfficiencyRep.lean's message-count/coin-slice readers and the
  public bounded-index search. All per-declaration details are in seq-zk-b/searches.md.
- `exec_prefix`, `exec_fst_take`, and `exec_snd_take` are execution specializations of
  published exec_succ and core prefix_iff_eq_take, not copies of a prior execution lemma.
- `uprob_adaptive_all_le` generalizes ThreeColoring/Protocol.lean:307 `uprob_adaptive_escape` from rate 1-1/m to arbitrary nonnegative s. It
  directly reuses OneWayFunctions/Basic.lean:90 uprob_and_le_mul and Fin.snocEquiv.
  Its local cast algebra re-derives the general-type versions of private :275/:286
  challengesBefore_snoc_castSucc/last, which are specialized and private. No private lemma
  is referenced or copied; this overlap is explicitly disclosed.


### Additional overlap and reuse in checkpoint 2

Every relative below is direct reuse or an explicitly disclosed generalization. Raw searches
precede implementation in the lead and subagent search logs. No private proof was copied.

- exec_boundary_lengths factors the arithmetic previously local to original
  seqRep_exec_phase (issue-base SequentialZK.lean:280); it reuses owned length/count readers.
- seqRep_verifierSpec and seqRep_proverSpec instantiate each abstract field from the
  construction's published coin/round/mover/next/index/count readers, avoiding import cycles.
- PrefixFolds realStep/simStep and realPrefix/simPrefix are typed semantic counterparts of
  SimulatorMachine.phasePrefix (same helper directory). They directly use existing core
  Fin.foldl, introduce no machine/control host, and give both real and simulated families.
- PrefixLaws zero/succ/snoc readers directly reuse core Fin.foldl_zero/foldl_succ_last and
  Fin.snoc_castSucc/last. simPrefix_eq_phasePrefix directly reuses phasePrefix_succ_simulate;
  it does not repeat tape/block interpretation or a machine-efficiency proof.
- ProofTransfers.next_length_le specializes the PaddedProverSpec next field, analogous to
  owned ProverBounded.seqRep but abstract in the source protocol. The owned construction
  result is unavailable to its imported helper without a cycle. ProofTransfers.complete
  directly reuses Protocol.ProverBounded.exists_complete (InteractiveProofs.lean:249)
  with a local relation pairing the original bound and pointwise complete witness.

Additional per-declaration records are included verbatim below. Source line references
are from the revisions actually searched; their sources/checks are preserved in evidence.

### PaddedProverSpec overlap and reuse

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


### RealPhases overlap and reuse

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


### SimulatorMachine overlap, reuse and host record

The lead approved phasePrefix as a public mathematical semantic recursion, realized using the
published ColMachines.polyTimeComputable_loopState' host. No new control host, transition
machine, or private machine is built. PhaseView was copied as an authorized stable source;
its hash and independent compile log are retained. It was not edited; no agent-a olean copied.

Raw searches are in simulator-searches.log. Earlier Efficiency/WrappedVerifier searches cover
coin slicing, uniform output/layout combinators, and canonical prefix reencoding. No exact
normalized-prefix simulator was found in TCSlib or pinned Mathlib.

New declaration nearest relatives and reuse:
- phasePrefix / zero / succ / succ_simulate: public mathematical sequence of canonical
  normalized simulator calls, following the issued source sketch. Nearest repeated-simulator
  code is PerfectZKAbort.retry (ZeroKnowledge/Defs.lean:337) and attempt (:319): their input is
  fixed and output stops at the first success, rather than changing auxiliary prefix and
  accumulating normalized messages. S.simulate_eq, S.runAt_eq and S.runAtL readers are reused
  to match the published simulator convention exactly.
- length_phasePrefix: new exact i*k count obtained from public
  length_normalizePhaseMsgs (PhaseView.lean:~97) and List append/replicate length readers.
- length_le_of_mem_phasePrefix: new prefix bound obtained by induction from public
  length_le_of_mem_normalizePhaseMsgs (PhaseView.lean:~105) and empty fillers.
- length_encodeMsgs_phasePrefix_le: direct use of public
  CommitmentLemmas.length_encodeMsgs_le (CommitmentLemmas.lean:241), together with the two
  preceding prefix readers. No generic encoding-size proof is copied.
- encode_emptyMsgs_poly: counted emission of the fixed chunk pairEncode [] [] through public
  ColMachines.polyTimeComputable_flatMap_range (ThreeColoring/Machines.lean:~158).
  Core List.map_const' and flatMap_map identify the result with existing encodeMsgs_eq_flatMap.
  This generic encoding composition has no exact prior counterpart found by the searches.
- phasePrefix_poly: existing ColMachines.polyTimeComputable_loopState' (:101), unary arithmetic,
  GI.coinSlice_poly (GraphIsomorphism/EfficiencyRep.lean:376), agent-a's public normalized-view
  machine, phaseAux_poly, and NUPPT output/layout readers are reused. The only new invariant is
  the exact identity of the existing host's state with the encoded semantic prefix. Nearest
  concrete consumers are ThreeColoring proverRepStr_poly and PerfectZKAbort.retry_poly
  (Defs.lean:412); their fixed protocol/first-success outputs prevent direct reuse.
- exists_phaseSimulator: uses public NUPPT.ofPolyTimeUniform and its uniform/coins/activation
  readers. Nearest relative exists_retrySimulator (Defs.lean:433) uses n retries on the same
  input, whereas this simulator threads phaseAux data and emits the entire canonical view.

Promotion requests: phasePrefix and the simulator construction are source-specific and stay
in this helper. The small encode_emptyMsgs_poly composition could later move beside the shared
encoded-history machines. No frozen-file changes or scope requests are needed.


### WrappedVerifier searches, reuse and overlap

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


## ExecutionBounds continuation

ExecutionBounds.lean is 88 lines, maximum width 94, with no admissions or simp attributes.
It imports only stable Normalization.lean; the previous four source hashes were asserted
unchanged when this report was finalized. Public searches found no existing generic message
length bound for Cryptography.exec.

New declarations and overlap:

- exec_snd_bounded derives a bound on every verifier-received message from a fixed prover
  tape's uniform next-message bound. It uses only Interaction.lean's exec_zero and exec_succ
  readers (lines 262 and 266 in the base). Related
  Games/Protocols.lean:316 execT_trace bounds concern a different oracle protocol and only message
  counts; they do not provide this statement. No private argument was copied.
- exec_snd_slice_bounded directly specializes exec_snd_bounded through the public core
  List.mem_of_mem_take and List.mem_of_mem_drop readers. It adds no list-membership lemma.
- length_encodeMsgs_exec_snd_le applies Words.lean:81 length_encWords_le through the checked
  encodeMsgs_eq_encWords bridge and exec_snd_bounded. It is execution-specific. No duplicate
  generic encoded-history bound was added; the nearest existing generic
  CommitmentLemmas.lean:241 length_encodeMsgs_le is subsumed by the Words theorem reused.

Promotion request: generic execution-message bounds belong beside the execution readers in
Interaction.lean at a future shared-file window. No frozen-file edit was made or needed.

ExecutionBounds check01 passed with one unused simp argument; the argument was removed in
its single proof block. Check02 passes with no diagnostics, RSS 1,560,723,456 bytes and
1.77 seconds compiler wall time. Both raw attempts, preimplementation searches, width/hash
ledger, diagnostic summary and own-tag slots are retained. No Lake command ran. The hybrid
outline now marks the execution-message-bound obligation resolved by this checked helper;
the separate cheating-verifier padded-phase endpoint reader remains a lead obligation.

## Prefix-hardwired prover and offset execution

After approving the proposed interface, the lead assigned a NEW helper `Phases.lean`,
importing the stable Soundness helper. The new public construction `prefixProver` fixes
an earlier received history, auxiliary input and prover tape; generated `coins` and `next`
readers expose its zero coin polynomial and append contract. The new theorem `exec_phase`
identifies any corresponding segment of the full execution, under the mover and verifier
reply hypotheses, with a run of this prefix-hardwired prover. No owned definitions are
imported or unfolded. The optional bounded verifier-congruence theorem remains a design
proposal only and has not been added.

Overlap and promotion:
- `prefixProver` is a fixed-tape/fixed-prefix strategy wrapper. The nearest owned wrapper is
  `Protocol.seqProver`, original `SequentialZK.lean:200`; the latter slices prover coins and
  drops earlier received messages, while this one fixes the original tape and prepends
  earlier received messages. It does not restate that construction. No equivalent public
  wrapper was found by the recorded searches for `hardwir`, fixed tape, prefix strategy,
  zero-coin strategies, and prover next-message append calls.
- `prefixProver_coins` and `prefixProver_next` are generated field readers of this new
  construction, not re-proved foreign readers.
- `exec_phase` shares the induction architecture of the owned honest-run
  `Protocol.seqRep_exec_phase` (`SequentialZK.lean:280` at issue base), but applies to any
  prover and any two verifier strategies under an explicit real-phase contract. It uses
  only published `exec_zero`/`exec_succ`, generated prefixProver readers, and core List
  append/drop equations. No proof block or private declaration was copied.
- The nearest other general execution comparison is public
  `LevinTransfer.exec_congr` at `ZeroKnowledge/NPLemmas.lean:88`; it compares whole runs
  from empty histories under equality on all histories. It cannot supply an execution
  segment with fixed nonempty earlier histories. It is outside the supplied bootstrap
  closure and is not imported.
- Promotion request: prefixProver and exec_phase belong beside the interactive-execution
  API in `ZeroKnowledge/Interaction.lean` at a shared-file window. The permitted helper
  retains them for this fill.

Phases check history:
- Attempt 01: exit 1 with one unresolved false-mover branch. The branch retained
  `if false = true`; adding the public Bool false-equality and if-false simplification
  closed it. Max RSS 2,147,205,120 bytes. Raw log retained.
- Attempt 02: exit 0 with 0 errors and 0 warnings, fresh olean produced. Max RSS
  2,154,381,312 bytes. Raw log retained.

Final Phases.lean: 96 lines, maximum width 94, SHA-256 `22d94a4e178f0a0f34b4fabb3609a7ca33a171a9e38cf275d8dcf0e79e33a9e2`. No admissions.

## Congruence along the reached source histories

The lead assigned a NEW `Congruence.lean` for checkpoint 2 tape nonanticipation and later
ZK. It imports only `ZeroKnowledge/Interaction.lean` and introduces the public theorem
`exec_congr_reachable`. Its hypotheses compare replies only at active positions before
`g`, on each source execution's actual received history; prover and verifier tapes may
both differ. The conclusion is equality of the complete executions after `g` moves.
It uses only published `exec_zero` and `exec_succ` readers and public Bool equalities.
No previous helper source was changed.

Overlap and promotion:
- Nearest relative: public `LevinTransfer.exec_congr`,
  `TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean:88`. That theorem permits different
  inputs but requires each party's replies to agree on **every** possible history.
  The new theorem has a weaker reached-history premise at a bounded number of moves,
  and identical common/auxiliary inputs. The published theorem cannot directly discharge
  this premise and is outside the supplied order closure. No existing proof block was
  copied; the standard induction is re-derived from the public execution readers.
- Searches for `exec_congr|exec_eq_of|next_eq_on|reachable.*exec|exec.*reachable` across
  TCSlib and for execution congruence/reachability under pinned Mathlib/Computability
  found no closer reusable theorem. Raw output is in congruence-searches.log.
- Promotion request: `exec_congr_reachable` belongs beside `exec_succ` in
  `ZeroKnowledge/Interaction.lean` in a shared-file window.

Congruence check attempt 01: exit 0 with 0 errors and 0 warnings, fresh olean produced.
Max RSS 1,549,713,408 bytes; raw log and structured result retained. The invocation used
this sub-agent's own olean tree and tag through the host-wide shared slot wrapper.

Final Congruence.lean: 68 lines, maximum width 94, SHA-256 `724fb756e96ac9f210b2a0f75dd9d403bddc2a0c226225a4ba01e9f284efcb56`; no admissions.

## Earlier verifier blocks determine the earlier transcript

The lead assigned NEW `VerifierPrefix.lean`. The public theorem
`exec_eq_of_verifier_blocks` accepts an arbitrary padded verifier, an arbitrary terminal
reply function, and a move-index recovery hypothesis on the actual source run. It proves
that agreement of verifier coin blocks below `j<q` gives equality of the full transcript
before move `2*k*j`, against the same arbitrary prover and fixed prover tape.

The zero-round case has no moves. In the positive-round case the recovered index gives
`2*received.length ≤ t+1`, excluding the terminal history `q*k` before the cutoff. The
phase index is below `j` by the public core theorem `Nat.div_lt_of_lt_mul`. Reusing
`exec_congr_reachable` and the supplied padded reply reader then identifies the runs.
The proof does not unfold any owned definition or the body of `coinBlock`; `dsimp only`
reduces the local `let idx` appearing explicitly in its own hypothesis.

Overlap and reuse:
- Directly reuses this sub-agent's published `Composability.exec_congr_reachable` in
  `SequentialZK/Congruence.lean:42`. No congruence proof is duplicated.
- The nearest owned construction reader is `Protocol.seqRep_exec_phase`, original
  `SequentialZK.lean:280`, which compares an honest phase with an original execution.
  That theorem neither handles arbitrary cheating provers nor compares two full verifier
  tapes, so it cannot give this nonanticipation statement.
- The lead's new `Protocol.seqVerifier_exec_first` handles phase zero against the original
  verifier; it also does not identify earlier transcripts for arbitrary two tapes and a
  phase cutoff. The new helper contains no copy of that proof.
- Specialized earlier transcript readers such as `GI.exec_vfirst_eq` in
  `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:90` describe history-independent
  verifier messages. Here the underlying verifier may depend on its within-phase history,
  so that interface cannot be reused. No specialized proof was copied.
- The move-index arithmetic is supplied by the lead, not re-proved from a foreign count
  function. Core `Nat.div_lt_of_lt_mul` is directly reused rather than copied.
- The statement belongs to this fill's padded-phase helper layer; no frozen-file promotion
  or reader request is required for it.

Searches for coin-block execution/prefix and verifier-tape dependencies in TCSlib and
pinned Mathlib/Computability are recorded in verifier-prefix-searches.log. No equivalent
published padded-verifier nonanticipation theorem was found. No new Mathlib root was
added, and no earlier helper was changed.

VerifierPrefix attempt 01: exit 0, 0 errors, 0 warnings, fresh olean produced. Max RSS
2,170,912,768 bytes. Exact invocation, raw log, source audit, and slot lines are included.

Final VerifierPrefix.lean: 89 lines, maximum width 94, SHA-256 `6be4e9f9c220e9ba15798dc0b61bc9a7cafc5c9ea1ec62a673de7c2d5e26c7f7`; no admissions.

## Explicit soundness error and fixed-prefix section bounds

NEW `ErrSoundness.lean` contains three checked declarations:
- `InteractiveProofErr.uprob_accept_le`: for every no-instance and prover, acceptance
  probability is at most the stated error `s(|x|)`.
- `InteractiveProofErr.sound_nonneg`: the error is nonnegative at every no-instance length.
- `Composability.prefixProver_accept_le`: when the earlier received messages and original
  prover tape are hardwired, the acceptance probability over a fresh original verifier
  tape alone is at most `s(|x|)`. The wrapper's public zero-coin reader shows that every
  local prover coin string is empty. Published output/transcript equations, `uprob_prod`,
  and `HardcoreBit.uexp_const` then remove its unused coin coordinate.

Search and overlap disclosure:
- No `InteractiveProofErr` acceptance or nonnegativity bound was found by the recorded
  TCSlib/Mathlib searches. Nearest public relative is
  `InteractiveProof.exists_uprob_accept_lt` at `ZeroKnowledge/InteractiveProofs.lean:193`.
  It returns a strict bound for an existential negligible error; it cannot provide the
  frozen arbitrary explicit-error value `s`. The new acceptance proof adapts the same
  complement-of-rejection argument, directly reusing `uprob_mono`, `uprob_not`, and the
  public soundness field. This overlap is explicit; it is not a copied private theorem.
- `sound_nonneg` directly specializes the public Mathlib order equivalence
  `sub_le_self_iff` generated at
  `Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:214`, using `uprob_le_one`. No order or
  probability fact is re-proved.
- `prefixProver_accept_le` specializes the new acceptance bound to the existing public
  prefixProver wrapper. Its marginalization is direct reuse of the uniform product and
  constant-average readers. It does not re-prove the generic uniform second-projection law
  (`HardcoreBit.pushesUniform_snd`, HardcoreBit/Basic.lean:210) or the averaging statement
  `Protocol.exists_proverCoins_le` (Interaction.lean:548).
- Promotion request: the first two generic methods belong in
  `ZeroKnowledge/InteractiveProofs.lean` at a shared-file window. The prefix-specific bound
  remains in this fill's helper layer. No frozen file was edited.

Diagnosed elaboration and authorized proof-debugging exception:
- Attempt 01 started 09:37:03 UTC, acquired its slot at 09:37:08, and was running rather
  than queued. The sub-agent initially inferred a slot wait from the empty buffered output;
  the lead corrected this status, and the process snapshot confirmed the running child.
- A read-only one-second stack sample showed active `evalCalc`/`elabCalcSteps` and deep
  `isExprDefEqExpensive` recursion in the probability calculation. Mac headroom measured
  by the lead was 6.438 GiB, above the floor; this was not E-RES.
- The lead explicitly authorized a graceful interruption under Seyoon's best-judgment
  exception. Its verbatim instruction is preserved in err-soundness-debug-authorization.md.
  The exact child PID96807 and parent96799 and full Lean command were re-verified before
  SIGINT. Only that child was signaled; no wrapper or other job was touched.
- The complete attempt source, raw checker output, process inspection, interruption record,
  and stack sample are retained. Lean exited130, checker exited1, and no olean was produced.
  It ran619.72s with maxRSS3,831,316,480 bytes. This was diagnosed proof debugging, not an
  elapsed-time timeout, resource shortage, or claimed proof failure.
- Replaced only the pathological probability calc with an explicit reader-based product
  proof. Attempt02 passed with 0 errors and 0 warnings, fresh olean, runtime6.63s,
  CPU1.43s, maxRSS2,164,834,304 bytes. No previous helper source changed.

Large raw diagnostic representation:
- Raw sample size145,047,604 bytes, SHA256
  `440251c95334e50dfb92d8140690daa5315ec081bb69b6135602a9ce0187deec`.
- Deliver the lossless numbered part `err-soundness-diagnostics-01.zip`, with its entry list
  and verification log. Its sole member is the complete original err-soundness-sample.log;
  streamed decompression was SHA256-checked byte-for-byte, with the original length.
- ZIP size1,916,631 bytes. The original raw local sample remains outside the payload at
  `.lake/seq-zk-c-raw-diagnostics/err-soundness-sample.log`. The completed sample was moved
  only after verified compression; no running log was moved. No raw bytes are omitted.

Final ErrSoundness.lean: 85 lines, maximum width 94, SHA-256 `4ada2d316efd3efd4d387dde0880b9360ea66fff55581b2535081dc09ac76705`; no admissions.

## General phase-coupling extension for the simulator worker

At the lead's request, added `exec_phase_of_moves` to Phases.lean with arbitrary local
strategies, auxiliary inputs and tapes. Each supplied active-move equation reads a local
party on the reached source history with its fixed old prefix dropped. The generic
induction proves both prefix-append history decompositions. The previous `exec_phase`
statement is unchanged and now applies this theorem; its prover premise follows from
`exec_prefix`, the public List prefix append equation, and prefixProver_next. Its sketch
was synchronized. There is only one phase induction; no duplicate proof was retained.

Overlap: the new theorem generalizes this same file's prior exec_phase, whose old source
and source audit are retained as phases-before-generalization files. The new generic
induction replaces that old induction; the old API is a direct published-theorem reuse.
No foreign or private proof was copied. This belongs beside the generic interactive
execution API at a shared-file window, extending the prior promotion request.

Phase generalization check01: exit0, no errors/warnings, fresh olean, runtime4.67s,
maxRSS2,155,839,488 bytes. Dependent ErrSoundness recheck: exit0, no errors/warnings,
fresh olean, runtime2.70s, maxRSS2,165,014,528 bytes. It is the only owned helper directly
importing Phases; the simulator worker was sent the exact checked signature and source
and will recheck its new consuming helpers in its own tree. Existing API preserved.

Current Phases.lean: 142lines/max94, SHA256`dcec347fe5aaf7407861a8248809c400c4d1f8ad85b6c6195bacd4a7261d13be`.

## Full generic explicit-error repetition engine

The lead approved the PaddedVerifierSpec interface before substantial implementation.
`RepeatedVerifier.lean` supplies the public proposition-valued structure and its two
phase readers. `RepeatedSoundness.lean` supplies the actual probability engine. Neither
imports or unfolds the owned SequentialZK module, and no target statement is weakened.

New declarations and formulas:
- `PaddedVerifierSpec π ρ x q p terminal`: the nine displayed coin/round/first-mover,
  padded-next, binary-terminal, actual-index, boundary-length, original-length, and mover
  periodicity properties. Every public field has a formula docstring in Lean argument order.
- `PaddedVerifierSpec.phase_exec`: both histories of a real phase equal their fixed earlier
  histories followed by an original-verifier execution against prefixProver.
- `PaddedVerifierSpec.phase_take`: taking the p real prover slots of a final phase history
  recovers that original-verifier history. The k=0 branch is explicit.
- Private `phaseTape` and `phaseTape_block`: table coins are read through the canonical
  FunFamily.blocks equivalence and its published ofFn reader.
- Private `zeroTail`: a finite table with prescribed earlier blocks and explicit all-false
  future blocks. Private `phaseGood`: original acceptance with its induced earlier
  received history and fixed prover tape. Private `phaseGood_section` specializes the
  checked prefixProver acceptance bound. Private `phaseGood_of_test` identifies actual
  phase tests using VerifierPrefix and phase_take.
- `PaddedVerifierSpec.outV_eq`: repeated output equals its terminal function on the
  complete source transcript, through public Protocol output/transcript readers.
- `PaddedVerifierSpec.accept_le`: original explicit error s gives aggregate acceptance
  probability at most s(|x|)^q against every prover.
- `PaddedVerifierSpec.sound`: the binary aggregate verdict gives rejection probability at
  least1-s(|x|)^q. The q=0 branch is explicit. No q-positivity premise is added to this
  helper, and the frozen owned statements retain their original hypotheses.

Overlap and reuse, including every restatement/specialization:
- PaddedVerifierSpec's fields package the owned equations as caller-supplied hypotheses;
  they are not new proofs or claims that an arbitrary protocol satisfies them. Nearest
  original SequentialZK.lean readers: seqVerifier/its generated readers at236;
  seqVerdict_eq at222; seqRep_rounds_eval at261 and seqRep fields at254;
  verifierMoveIndex_eq at117 and verifierMoveIndex_exec at182; exec_fst_length at153 and
  exec_snd_length at163 with countP_moverIsV at133/countP_not_moverIsV at143;
  proverMoves_eq at127; moverIsV_two_mul_add at128. They cannot be imported into a helper
  without a cycle; the lead instantiates each field from exactly these published readers.
- phase_exec directly reuses exec_phase, including its generic induction. Its nearest
  owned relative is honest-only seqRep_exec_phase (issue-base line280); the new reader
  permits an arbitrary prover and an abstract verifier specification. Its quotient and
  remainder arithmetic directly reuses the core Nat add-multiple division/modulo readers;
  it does not copy a private lemma or add another execution induction.
- phase_take directly reuses phase_exec, exec_snd_take and the supplied length readers.
  Nearest lead checkpoint1 reader: Protocol.seqRep_exec_phase_take at owned line478
  (source queried during this work); that theorem is honest-only and unavailable to the
  abstract helper. The new reader generalizes the final-phase restriction to every prover.
- Private phaseTape is a local string alias for (FunFamily.blocks q c).symm. Nearest alias
  is public GI.blocksEquiv at GraphIsomorphism/SoundnessRep.lean:207. Private phaseTape_block
  has nearest relative public GI.coinSlice_blocksEquiv at that file:224. It is not a copy
  of the latter's entrywise proof: it directly specializes the already-imported canonical
  FunFamily.ofFn_blocks reader (Asymptotic/Adversary.lean:277), using Equiv.apply_symm_apply.
  This canonical public reader is the reused interface; no GI implementation is duplicated.
- Private zeroTail has nearest public relative extendStream at
  Pseudorandom/Functions/LazySampling.lean:196 (inside the supplied closure). extendStream
  returns a stream on all naturals and uses Classical.arbitrary beyond its prefix. The new
  finite-table leaf uses the explicitly requested all-false fallback, including truncation
  if i exceeds q; extendStream does not publish that exact fallback. Mathlib Function.extend
  (Logic/Function/Basic.lean:686) is a choice-based extension along a map, not this explicit
  total finite-prefix/truncation leaf. The two-line conditional definition is disclosed;
  no existing extension theorem or private proof was copied or re-proved.
- phaseGood is a local predicate naming the original verifier/prefixProver test, rather
  than a new iteration host. phaseGood_section directly reuses prefixProver_accept_le;
  it merely substitutes the earlier transcript of the zero-tail table as its fixed prefix.
- phaseGood_of_test directly reuses exec_eq_of_verifier_blocks and phase_take. Its only
  extra table fact reads the prescribed prefix of zeroTail; Fin casts reduce by the core
  projection equations. There is no duplicated nonanticipation or phase induction.
- outV_eq's nearest lead reader is Protocol.seqRep_outV_eq, owned line453 when queried.
  The new theorem is the abstract-spec counterpart; it directly reads supplied rounds,
  first-mover, boundary, and next equations through published Protocol readers. It cannot
  import that construction-specific owned theorem without a cycle.
- accept_le directly reuses Protocol.exists_proverCoins_le (Interaction.lean:548), the
  canonical FunFamily.blocks equivalence/readers, VerifierPrefix through the phase-test
  reader, prefixProver_accept_le through phaseGood_section, and uprob_adaptive_all_le.
  Nearest specialized repetition proof is GI.gniRep_accept_le at
  GraphIsomorphism/SoundnessRep.lean:344, with its protocol-specific 2^-n+sampling-error
  rate. It does not supply arbitrary s or this abstract padded verifier; no proof was copied.
- sound uses outV_eq, the supplied binary terminal equation, OneWay.uprob_congr,
  uprob_not, and Mathlib sub_le_sub_left directly. The nearest specialized complement
  conversion is GI.gi_rep_efficientProverProofErr at SoundnessRepGI.lean:438. Its
  protocol-specific conclusion cannot supply this generic reader. No probability
  complement or order fact was re-proved.

Promotion/readers: PaddedVerifierSpec and these abstract padded-phase readers belong in
this topic helper layer. General prerequisites already carry the earlier Interaction and
InteractiveProofs promotion requests. No frozen-file edit, scope extension, private host,
new Mathlib root, or new simp attribute was introduced.

Validation history and resource evidence:
- RepeatedVerifier01: syntax cascade from reserved capital Π; changed the bound protocol
  name to valid ρ. RepeatedVerifier02: explicit first-mover projection case split was
  needed for the index arithmetic; fixed through if_pos/if_neg on its equality. Both raw
  failures retained. RepeatedVerifier03 passed spec+phase_exec. RepeatedVerifier04 passed
  the complete phase_take extension with0errors/0warnings, actual runtime2.87s,
  maxRSS2,194,358,272. Its slot wait was10:04:53–10:15:32 UTC, normal host contention;
  not a stall or E-RES.
- RepeatedSoundness01 found one local-notation simplifier mismatch. Attempt02 fixed the
  outer block but exposed the inner occurrence's local c alias. Attempt03 normalized that
  local proposition explicitly and passed the full engine with0errors/0warnings, fresh
  olean, runtime2.41s, maxRSS2,172,452,864 bytes. All raw logs and structured results remain.
- The full engine uses explicitly typed probability intermediates and public product/
  equivalence readers; no pathological dependent calc or proof-debug interruption occurred.
- Each check used this sub-agent's own olean tree and shared wrapper/tag. Source files
  remain below1000lines and100characters. The lead owns the final merged sweep, axioms,
  seals, lint, commits and delivery.


### Statistical checkpoint additions: overlap and reuse

The per-declaration records below supplement the earlier complete overlap list. Raw searches
precede implementation, and no private proof was copied.

- StatisticalTransfer.statZK_of_padded_spec directly combines StatZK_iff (Defs.lean:187),
  phaseVerifier_efficient (WrappedVerifier.lean:154), exists_phaseSimulator
  (SimulatorMachine.lean:~305), PaddedProverSpec.statClose_prefix, StatClose.map,
  statClose_average, and statClose_view_endpoints. Nearest earlier complete construction is
  PerfectZKAbort.statZK (Defs.lean:433ff): it retries a fixed input until success, whereas
  this proof threads bounded normalized prefixes. Its machine is reused through the public
  exists_phaseSimulator, and no retry/loop/postprocessing proof is copied. This generic
  padded-prover transfer belongs in this topic helper layer; no frozen-file promotion needed.
- NormalizedStep.normalizePhaseMsgs_viewV publishes the real fixed point originally local
  to the same file's statistical theorem; that theorem now reuses it, with one proof retained.
  It directly uses PhaseView.normalizePhaseMsgs_of_encode and ExecutionBounds.exec_snd_bounded.
- Canonical phaseVerifier_eq/phasePrefix_eq and the endpoint _eq readers are home-definition
  equations, added for literal reader compliance; no foreign equation is re-derived.


## StatisticalRecursion checked continuation

StatisticalRecursion.lean introduces no definition or host. Its sole public theorem
statClose_recursion takes caller-supplied zero and snoc equations for arbitrary real/simulated
sampler families and updates. Shared-prefix averaging replaces the final update at cost
delta; the existing randomized test-set reader transports the induction hypothesis through
the same simulated final update. Public transitivity and Fin.snocEquiv close the successor.
No Nonempty assumption on either coin type is required, because empty coin tables have
explicit inhabitants in the base case.

Nearest relatives: OneWayLemmas.lean:276 statClose_pi handles independent copies of one fixed
sampler comparison; Statistical.lean:59 statClose_chain handles a supplied full-sampler chain.
Neither is a caller-supplied state-dependent snoc recursion theorem, and neither proof was
copied. Directly reused readers are Statistical.lean:44 statClose_average,
Sampling.lean:237 StatClose.abs_uprob_sub_le_prod, Sampling.lean:167 StatClose.trans,
Sampling.lean:179,185 seed-equivalence transports, and Mathlib Fin.snocEquiv/snoc_init_self.
Promotion beside generic StatClose support is requested at a shared-file window.

The first source triggered stack-diagnosed pathological implicit sampler unification and
was interrupted only by exact lead authorization, with the raw source, sample, resource
reading, process chain and authorization preserved. The explicitly typed rewrite passed
check02 with no diagnostics in2.45s, maxRSS2,121,269,248 bytes. It is139lines, maxwidth94,
SHA256 fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
Its precise rewrite patch and large lossless sample ZIP part001 are delivered.

## NormalizedStep pending compiler diagnosis

NormalizedStep is not yet claimed checked. Its stronger zero-verifier API was approved by
the lead and independently reviewed as mathematically/type-consistent by seq-zk-c. The exact
phase-wrapper reader-only instantiation recipe is normalized-step-instantiation.md.

compiler-diagnosis-summary.md and the numbered authorization/process/source/marker records
retain each targeted own-process proof-debugging interruption. All were authorized by the
lead under Seyoon's best-judgment exception, never elapsed-time timeouts or E-RES, and no other
job or slot was changed. Every created native stack sample is delivered losslessly in ZIP
parts with raw SHA256, entry lists and verified extraction. Current work is localizing the
scalar test comparison declaration with robust direct-file IO markers; no false proof claim
or statement weakening is made. All diagnostic IO/trace must be removed before a final clean
source check and intake.

## Checkpoint 2 closed-evidence boundary

compiler-diagnosis-summary.md is the authoritative corrected closed ledger through
NormalizedStep attempt07. It supersedes earlier tentative source-stage descriptions in this
historical report. Eight own exact-process interruptions are recorded: StatisticalRecursion01
and NormalizedStep01–07, all separately lead-authorized proof debugging rather than timeouts
or E-RES. No own Lean is active at this boundary. NormalizedStep remains unverified; the checked
StatisticalPostprocess dependency and completed fixed-point/pointwise markers do not imply
that its full concrete instantiation passed. The next opacity/instance correction awaits the
lead's three-slot cache completion. Complete prerequisite sources and lossless native-sample
ZIP parts are included so all closed raw evidence has its sources and verification tools.


## Final normalization and statistical-prefix extension

NormalizedStep is now clean-checked with no diagnostics. Its final source hash is
07c9fed43664eeaa47b712f02b72f09addbe0ceb8dc134917cd0b33f6754e689
(101lines,maxwidth96;nativecheck10=2.22s). The compiler ledger now explicitly records the
missing ZeroKnowledge.Defs import exposed by attempt08 and corrected before09. Prior
elaboration-stage diagnoses were incomplete because invalid simulate fields in the
signature remained buffered. The corrected exact-source check is retained in full.

StatisticalPrefix is clean-checked with no diagnostics. Its final source hash is
5275167b11df6074d08df53ae24486e94ccb1149eaf5d6541e88ad9fe1727d64
(151lines,maxwidth94;nativecheck02=2.31s). PaddedProverSpec.statClose_step specializes the
zero-verifier comparison at every index and prefix using an explicit coin-length equality,
coin equivalence and public ofFn reader. PaddedProverSpec.statClose_prefix instantiates the
public sampler-recursion bound using the public zero/snoc fold readers. It assumes only
a direct prover-message cap and raw phase closeness at every auxiliary input; S need not
be uniform. Neither proof uses a target theorem or creates a host.

Nearest overlap relatives: StatisticalRecursion's generic caller-supplied family bound,
NormalizedStep's generic zero-verifier bound, PrefixLaws zero/snoc readers,
PaddedProverSpec.original_count, public StatClose.comp_equiv_left/nonneg, and Mathlib
List.ofFn_congr. StatisticalPrefix is their concrete composition, not a duplicate generic
loop or statistical law. Exact searches are statistical-prefix-searches.log.

The lead authorized APFS clones of completed helper oleans into this isolated olean tree.
Eight completed immutable prerequisite source/olean pairs were copied with provenance in
prefix-prerequisite-seed.json. Their sources are reused unchanged; no other owner file was
edited. The lead will perform final source, axioms, seals and sweep checks.

## BoundedMetadata overlap plan

Nearest existing material is ColZKMachine's finite maximizing domain with a bounded
sigma-word, plus the public padFin/ofFn_padFin_of_length codec. The new metadata type
only assembles those standard finite representations into the five actual reduction
fields. It defines no selector, maximizing principle, interpreter or machine. c's Advice
selector will consume the resulting finite nonempty type. The exact packed-size formula
is b's public reductionData_length; it is reused directly, not re-proved.


## Complete checked helper handoff

seq-zk-a proved ten helper modules: Normalization, NormalizationMachine, PhaseView,
Statistical, ExecutionBounds, StatisticalRecursion, NormalizedStep, StatisticalPrefix,
BoundedMetadata and RealPrefixBounds. All final source bytes are in source-snapshots with
owner/status/hash rows. No target or frozen file was edited. The lead alone integrates,
commits, seals, sweeps and delivers the target declarations.

At lead request, NormalizedStep11 exposed normalizePhaseMsgs_viewV without any statistical
premise. The existing comparison calls it; no second normalization proof was added. The
new final source hash is76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5
(126lines;clean native11=2.50s). This supersedes the earlier101line clean10 source.

BoundedMetadata final03 passed2.38s,0diagnostics. It defines finite nonempty five-field
PhaseMetadata, exact raw data/length readers and exact coverage. An initially redundant
direct Mathlib.Data.Fintype.Sigma import was removed before final03; the final source
imports only ComputationalReduction and requires no new Mathlib root. Source hash
f94e6c8ff89a1674aaed5047e479856ebe3e2a1623e2d2ccdeb46f4ae6f8959b.
Its raw01failure and exact source are retained (product RHS parenthesization and a proof
where simp had already changed reflexive equalities to True);02passed,03removed the
redundant import and added the direct packed-data cover corollary.

RealPrefixBounds final02 passed2.27s,0diagnostics. Its aggregate theorem gives exact j*k
message count, the uniform B cap, and encoding length at most(j*k)*(2*B+2) for every
real prefix j≤q. It reuses the public raw coin-table inverse/block reader and endpoint,
the specification's boundary/reply readers, and ExecutionBounds. No generic word-length
estimate is duplicated. Source hash
1a50f8656f00e280506a67947a16a0583cdcc5fb9242efa3e15a3fc160f390d8.
Its raw01failure is retained; split_ifs generated both first-mover cases as well as the
active/filler cases, so02applied the same bounded/empty branch argument to all four.

The retained FullOwnHelpersAxioms.lean probe checks42public declarations across all ten
owned modules. It passed5.09s with0diagnostics and only propext,Classical.choice,Quot.sound.
It also synthesizes Fintype and Nonempty of PhaseMetadata for arbitrary five natural
bounds. The smaller MetadataAndStatisticsAxioms.lean is a prepared but unused predecessor
probe retained for completeness; the full probe is the executed evidence.

All copied dependencies preserve their owner's exact checked bytes: c StatisticalPostprocess
and final EndpointSampling, b final ComputationalReduction, and lead-completed helper
sources/oleans cloned only after completion authorization. Provenance JSON files record
source hashes/check rows. seq-zk-a ran no lake command and touched no other worker process.
There were no new compiler interruptions after the historical eight own authorized events.


## Checkpoint3 closed-evidence boundary

The lead reports CP3 proof revision04c253e48d9c0ebb73943f39412365cd4d8e02db. The first eight
seq-zk-a helper sources are part of that proof revision. BoundedMetadata and RealPrefixBounds
are fully checked future support sources OUTSIDE CP3, as is b's ComputationalReduction
dependency; all three exact sources are retained under source-snapshots for replay of the
new checks and the full axioms/Fintype probe. Their outside-CP3 status is explicit in the
checkpoint3-closed-files.tsv source_status column. No own process is active at this boundary.
After producing that receipt, every named byte is frozen until the lead confirms copying.

The preceding agent report includes explicitly labeled future BoundedMetadata and
RealPrefixBounds, outside CP3. Its source_status receipt is authoritative for that boundary.
## Scope requests

One explicit request: add the nine-line StatZK_iff reader in frozen
TCSlib/Cryptography/ZeroKnowledge/Defs.lean. Seyoon answered **"Approve this reader addition"**.
The exact request, answer and diff are in evidence/scope-request/. No other frozen file changed.
Seyoon later authorized best judgment on exceptions and messaging workers for shared Mac
resources; that instruction is retained in evidence/coordination/. Shared-slot coordination
with derand, sc-garble and Ladner is recorded there. No other worker's tree or process was
edited, removed or interrupted.

## Promotion and reader requests

At a shared-file window, consider moving the Strategy/BinArith encoding bridge, encoded-prefix
reader and generic exec-prefix readers beside encodeMsgs/exec in Interaction.lean; decoded
canonicalization/lookup beside the BinaryArith word-list hosts; generic repetition-machine
closure facts into a shared encoded-interaction layer; and the arbitrary-rate adaptive bound
into the probability layer. These are promotion requests, not frozen-file edits in this payload.

## Payload and replay

patches/ contains the complete format-patch series at the issue base. COMMITS.tsv includes
all author/committer metadata and the signing column; commits use commit.gpgsign=false.
src/ contains every changed/new repository file. evidence/ includes input packs, tools,
probe/seal/control preparations, raw successful and failed logs, requests, source snapshots,
subagent records and manifests. Its SHA256SUMS covers every evidence file except itself.
The top-level SHA256SUMS covers every delivered file except itself; exact path equality and
hashes are verified before the exchange commit/push. Delivery touches only inbox/fills/seq-zk/.


## Endpoint helper overlap record (verbatim)

# EndpointSampling implementation record

Author: seq-zk-c. Assigned by lead after the checkpoint2 closed-evidence manifest was
sealed. This record and all endpoint-* files are future evidence, outside checkpoint
source e978a28274fdeb545e622ae28747221088352512. All72 files in the sealed manifest remain
byte-for-byte unchanged. The lead owns final integration, commits, frozen seals and delivery.

## Supplied interface and coordination

Read root PrefixFolds/PrefixLaws, b PaddedProverSpec/SimulatorMachine, and a
StatisticalRecursion. Coordinated the joint `(verifier tape, prefix)` domain with a and
b before coding. The lead approved generic tape block equivalences, real prefix
identification by the published padded-phase reader, and the optional joint statistical
endpoint convenience theorem. No sibling or main source was edited or checked in its
foreign tree. There is no target change or added cryptographic premise.

The stable new module is EndpointSampling.lean,269lines/max95columns, SHA256
76827a0f531b095aeccd1460ef56ad13bb13612a861f9e7af82bad9069c1c048.

It publishes:
- coinTableEquiv(hlen:m=q*c) and its block reader, for the real prover tape.
- coinBlocksEquiv(v,q,c,hlen:m=v+q*c) and its verifier-take/phase-block readers.
- statClose_reindex, for supplied endpoint equivalences and pointwise endpoint readers.
- PaddedProverSpec.realPrefix_eq_exec, for j<=q and supplied block equalities.
- PaddedProverSpec.realCoinsEquiv, with domain actual `(rho.withV V).ExecCoins` and codomain
  `V.Coins |x| x (Fin q -> pi.P.Coins |x|)`, plus tape/block readers.
- PaddedProverSpec.viewV_eq_realPrefix, the actual encoded real-view endpoint.
- simulate_eq_simPrefix, the typed simulator endpoint from the published raw split reader.
- statClose_view_endpoints, consuming joint real/simPrefix closeness and returning actual
  encoded repeated view versus SQ.simulate with exactly the same error. Its only extra
  readers are p=the original mover count, SQ coinLen=v+q*S.coinLen, and the supplied SQ
  split-tape endpoint; the lead derives them directly from existing readers.

## Search, overlap, reuse, and promotion

Raw exact searches are in endpoint-sampling-searches.log.

- coinTableEquiv is the canonical FunFamily.blocks composed with a finite-length cast.
  The nearest existing assemblies are RepeatedSoundness.accept_le (verifier blocks) and
  GI.gniTapes (graph-specific sampler blocks). Neither exports the required general
  length-cast table equivalence. The block proof directly reuses FunFamily.ofFn_blocks
  and List.ofFn_congr, rather than duplicating the GI.coinSlice_blocksEquiv entrywise proof.
  Promotion request: a named length-cast block equivalence/reader belongs in
  Asymptotic/Adversary.lean if accepted; it is frozen here.
- coinBlocksEquiv directly reuses splitCoins and ofFn_splitCoins_fst/snd from
  Asymptotic/CollectionsHelpers.lean:145ff, then FunFamily.blocks/ofFn_blocks. No sum split,
  take/drop proof, block equivalence, or entrywise window proof was reproduced.
  Its distinct combined codomain is one verifier tape and a finite table of phase tapes.
  Promotion request: combined uniform-tape layout reader in the shared sampling layer.
- statClose_reindex is only published comp_equiv_left/right followed by supplied pointwise
  function equalities. Searches found no combined endpoint-reader interface. It does not
  reproduce probability invariance or a statistical switch. Nearest public declarations
  are StatClose.comp_equiv_left/right (Sampling.lean:179/185). Promotion request to Sampling.
- realPrefix_eq_exec directly composes realPrefix_zero/succ and PaddedProverSpec.padded_phase.
  Its induction is on the number of phase updates, not a duplicated execution/phase proof.
  Nearest real endpoint is b's padded_phase; its single-phase conclusion does not identify
  the finite fold with all phases. The lemma belongs in this topic helper layer.
- realCoinsEquiv and its readers are the typed composition of coinTableEquiv,
  Protocol.withV_vCoinsEquiv/ofFn and product commutation. viewV_eq_realPrefix directly
  combines that interface with Protocol.viewV_withV and the real fold reader.
- simulate_eq_simPrefix directly reuses root simPrefix_eq_phasePrefix and the combined
  block readers; its raw endpoint is supplied by b's exists_phaseSimulator. It contains
  no second simulator recursion or reconstruction of the simulator machine.
- statClose_view_endpoints directly maps joint prefixes to canonical View encoding and
  reuses statClose_reindex plus both endpoint readers. It adds no per-phase statistical
  argument and preserves the error without a triangle/normalization loss.

No frozen source, new simp attribute, foreign-definition unfolding tactic, Lake command,
new iteration host, witness bound, target assumption, or new direct Mathlib root.
CollectionsHelpers was already inside the issued cached TCSlib closure.

## Isolated prerequisites and validation

The lead approved source-copying exact checkpoint helper sources plus b's final canonical
WrappedVerifier/SimulatorMachine public-reader additions, followed by native own checks.
endpoint-prerequisite-sources.json records all source provenance and SHA256s. Own helper
sources were retained. B's two final hashes were verified before copying. No sibling
oleans were copied.

The initial prerequisite Normalization check passed. NormalizationMachine then failed
because the initial209-module own bootstrap lacked ThreeColoring/Machines.olean. This
complete missing-import attempt is preserved, with no source edit to the prerequisite.
Using the lead's explicit existing authorization, APFS-cloned28 missing BASELINE oleans
from root's completed working tree; all source bytes were verified against both own/root
sources and exact checkpoint e978a28274fdeb545e622ae28747221088352512, all olean bytes hashed,
and no existing artifact overwritten. All SequentialZK modules were excluded from seeding.
endpoint-root-baseline-seed.json records each source/artifact hash and path.

Native own-tree checks then passed, one module at a time, in this order:
NormalizationMachine (retry02), PhaseView, WrappedVerifier, RealPhases, PaddedProverSpec,
PrefixFolds, SimulatorMachine, PrefixLaws. Each raw attempt and structured result is retained.

EndpointSampling check01 passed with0errors/0warnings, a fresh own olean,2.45s actual
runtime and maximum resident set size2,236,170,240bytes. The exact attempt source is saved.
Every Lean invocation used LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot wrapper,
/usr/bin/time -l, scripts/lean_check_tree.sh and the separate seq-zk-c olean tree. There was
no interruption, timeout, sampling, or resource exception in this task.

The stable checked source/hash/API were sent to lead and a. No own Lean process remains.

Final reader-compliance amendment: at the lead's request, added full canonical
coinTableEquiv_eq, coinBlocksEquiv_eq, and realCoinsEquiv_eq, each rfl in its home module.
No existing body/reader changed. Check02 passed0diagnostics,2.66s actual runtime,
maxRSS2,237,087,744bytes. Final source/hash sent to lead and a; source remains stable.

## Uniform advice selector and opaque statistical post-processing

At the lead's request, inspected the published NUPPT closure/advice APIs and nearest
ThreeColoring finite-selector/hybrid proofs. The initial finite-kernel alternative is
unnecessary: maximizing the finitely many real suprema over arbitrary witnesses gives a
selector independent of the eventual negligible bound. The lead approved that route.
The complete design and remaining concrete obligations are recorded in
computational-advice-design.md; exact raw API searches are in advice-postprocess-searches.log.

Advice.lean introduces only exists_uniform_bound_selector: finite nonempty metadata,
arbitrary witness type, and a common nonnegative upper bound yield a metadata value whose
nonnegative uniform witness bounds also bound every metadata/witness pair. The proof
directly reuses Mathlib Finite.exists_max, le_csSup, and csSup_le. The nearest existing
ColZK.exists_hidingView_bound (ColZKMachine.lean:323) selects among finite colour/advice
triples and has a specialized commitment conclusion; it does not supply the arbitrary
witness-domain implication. No proof was copied. Promotion request: place this generic
bounded-family selector in a future shared order/probability helper. New precise imports
Mathlib.Data.Fintype.Lattice and Mathlib.Data.Real.Archimedean were approved by the lead;
both pinned olean files were already cached, and the lead owns required roots/pin/cache
updates. This agent ran no Lake command. Check01 passed with0errors/0warnings, 1.69s actual
runtime and maxRSS1,466,220,544 bytes. The slot wait from10:55:20 to10:57:10 UTC was normal
host contention, not an elapsed-time diagnosis, interruption, or resource shortage.

NormalizedStep's concrete elaboration remained slow inside the raw test bound despite
explicit public-reader arguments. The lead and a requested an opaque generic helper;
StatisticalPostprocess.lean introduces only statClose_map_fst. Its pair-indexed fixed-point
hypothesis matches a's existing proof directly. The ignored product factor is explicitly
Nonempty, necessary for the uniform-probability projection law (and automatically true
for verifier coin function spaces even with zero bits). It directly reuses StatClose.map,
statClose_iff, OneWay.uprob_congr and uprob_fst. Searches found no combined public map/fst
law. Nearest laws are those four imported public readers; no statistical switch, uniform
product, or event congruence proof was duplicated. Promotion request: this general law
belongs in Asymptotic/Sampling.lean if accepted; that file is frozen, so it stays in the
approved topic helper. Check01 passed with0errors/0warnings, 2.19s actual runtime and
maxRSS2,110,701,568 bytes. Source/API/hash sent to a and lead for independent copying and
checking. No concrete protocol or NUPPT appears in the helper, and no NormalizedStep edit,
check, sample, or interruption was performed by this agent.

Both new source files are stable. Every own Lean-running command used the shared wrapper,
seq-zk-c tag, one module, and own olean tree. Full raw checks, source hashes, searches,
structured attempt results, and refreshed source/diagnostic audits accompany this record.
No new simp attribute, frozen-file edit, scope extension, admission, or target change.

The computational suffix/hybrid sections above are labeled future evidence; they are not
part of checkpoint3src at the stated proof revision.
