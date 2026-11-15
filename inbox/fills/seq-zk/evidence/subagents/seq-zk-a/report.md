# seq-zk-a final helper report

Agent `/root/zk_route`, tag `seq-zk-a`, branch `fill/seq-zk-a`, issue base
107f1e8c218733eac12d6b9bee6fece441271317. Worktree:
`/Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange`.
Own olean tree: `.lake/seq-zk-a-oleans`, seeded by the lead from completed base modules.
`.lake/packages` is a symlink to the lead's exact-pin packages and read-only to this agent.
No commits, Lake commands, frozen edits, or SequentialZK.lean edits were made by this agent.

## Checked source

- Normalization.lean: 98 lines, maximum width 94; encoding bridge, bounded slot normalizer,
  exact count, per-message length bound, canonical bounded-list fixed point, encoded-size bound.
- NormalizationMachine.lean: 97 lines, maximum width 95; polynomial-time canonical reencoding,
  total decoded lookup, and encoded bounded-slot normalization for arbitrary polynomial-time
  raw input and unary-computable slot count and bit cap.
- PhaseView.lean: 168 lines, maximum width 95; canonical view metadata/tape/encoding validator,
  fixed-point and malformed-view fallback, bounded normalized messages and polynomial-time
  validator/encoded-normalizer theorems.

All three compile without final diagnostics or admissions, and add no simp attributes.
Source hashes are recorded in final-width-and-hashes.log. The first two source files were
held byte-stable after checking so seq-zk-b could reuse them with recorded provenance.

## Overlap and reuse

### Normalization.lean

- encodeMsgs_eq_encWords exactly matches the local `have henc` inside
  SecureComputation/Yao.lean:352. That provider is outside the supplied closure; this helper
  derives the general statement from public nil/cons readers of both encodings. The same
  representation occurs in ThreeColoring/Machines.lean:912 encodeMsgs_eq_flatMap.
  Promotion request: a general Strategy/BinArith encoding bridge belongs beside
  Strategy.encodeMsgs in ZeroKnowledge/Interaction.lean during a shared-file window.
- normalizeMsgs and normalizeMsgs_eq publish a new bounded-slot operation. No existing
  normalization with this shape was found in TCSlib or Mathlib searches.
- length_normalizeMsgs specializes List.length_map and List.length_range, directly reused.
- length_le_of_mem_normalizeMsgs uses List.length_take and Nat.min_le_left; this is the same
  arithmetic as List.length_take_le, specialized to the new operation.
- normalizeMsgs_encodeMsgs reuses BinArith.decWords_encWords (Words.lean:116) and
  List.take_of_length_le. No decoder or list host is copied.
- length_encodeMsgs_normalizeMsgs_le directly specializes public Words.lean:81
  length_encWords_le to the new invariants. CommitmentLemmas.lean:241 length_encodeMsgs_le
  offers the same generic encoded-size bound but introduces larger cryptographic imports.

### NormalizationMachine.lean

- polyTimeComputable_encWords_decWords specializes Words.lean:221 polyTimeComputable_mapW
  to the identity payload and uses mapW_pairEncode at line 208. No host is copied.
- polyTimeComputable_decWords_getD composes canonicalization with Loops.lean:391
  polyTimeComputable_getW and its reader getW_pairEncode at line 375.
- polyTimeComputable_encode_normalizeMsgs uses these lookups, EncodingMachines.lean:459
  truncate_poly, and ThreeColoring/Machines.lean:159 polyTimeComputable_flatMap_range. The
  published counted-emission argument is reused. Its import is within the supplied closure
  and was confirmed with the lead. No extra size premise or new private host is introduced.
- Promotion request: the generic canonicalization and total decoded-lookup lemmas belong
  beside the BinaryArith word-list hosts at a future shared-file window.

### PhaseView.lean

- phaseViewPayload and its eq reader are a new canonical-view validator; no matching
  validator was found. normalizePhaseMsgs and its eq reader compose it with normalizeMsgs.
- phaseViewPayload_of_encode specializes Interaction.lean:302 View.encode_mk, public pair
  projection equations, and Words.lean:116 decWords_encWords. All are directly reused.
- phaseViewPayload_of_ne is the new validator's failed-branch equation, proved by if_neg.
- normalizePhaseMsgs_of_encode directly reuses Normalization.lean:76
  normalizeMsgs_encodeMsgs after the canonical payload reader.
- length_normalizePhaseMsgs, length_le_of_mem_normalizePhaseMsgs, and
  length_encodeMsgs_normalizePhaseMsgs_le directly reuse Normalization.lean:60,66,89 after
  the new definition reader. They are its three phase-view specializations.
- normalizePhaseMsgs_of_ne specializes the normalized-empty-payload formula; its list
  calculation directly reuses core getD/getElem?/take/map-constant/range equations.
- polyTimeComputable_phaseViewPayload composes the existing canonical reencoder with
  Loops.lean:426 polyTimeComputable_eqW and PolyTimePairing.lean:290
  polyTimeComputable_ite. It introduces no host or machine construction.
- polyTimeComputable_encode_normalizePhaseMsgs directly reuses
  NormalizationMachine.lean:72 after validation. No additional promotion is requested for
  these phase-specific operations.

Searches and closest relatives are recorded in searches.md, searches.log,
normalization-machine-searches.log, map-identity-search.log, phase-view-searches.log and
phase-view-ite-search.log. Searches consulted the lead's Mathlib source read-only.

## Scope and mathematical assessment

The agent discovered the missing StatZK reader and supplied scope-StatZK-iff.patch without
applying it. The lead reports Seyoon approved the addition and the lead applied it. This
agent changed no frozen file. route-assessment.md records the independent mathematical
review of the ZK/StatZK route, auxiliary bounds and edge cases. No mathematical counterexample
was found; that assessment itself is not a checked composition proof.

## Checks and evidence

Every check used LEAN_SLOT_TAG=seq-zk-a, the assigned TCSLIB_OLEANS, the issued host wrapper,
/usr/bin/time -l, and scripts/lean_check_tree.sh for one module. All raw attempts are retained.

- Normalization passed attempt 01: 0 errors, 0 warnings; RSS 1,564,000,256 bytes.
- NormalizationMachine attempt 01 had one map-identity proof error and two unused simp
  arguments. Core List.map_id' fixed the lambda identity; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,213,593,088 bytes.
- PhaseView attempt 01 had one missing true-conditional simplification and one unused simp
  argument. Public if_true completed the payload proof; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,224,095,232 bytes.

check-summary.json counts both error: and error(...) diagnostic forms. slots.log records
all this tag's acquisitions/releases and their timestamps; it supplies the module start/end
for the first normalization raw log, which contains only the timing report. Later raw logs
include START/END timestamps, including any normal slot wait. Axiom/seal/campaign-lint checks
are the lead's final merged-branch responsibility. No probe/check logs have been omitted.

## Statistical helper continuation

Statistical.lean adds the sole missing sampler-level shared-prefix averaging lemma
`statClose_average`. It directly reuses statClose_iff (Asymptotic/Sampling.lean:133),
StatClose.abs_uprob_sub_le (Sampling.lean:138), abs_uexp_sub_le (Sampling.lean:210), and
uprob_prod (Foundations/Probability.lean:153). This is a new packaging of those published
interfaces, not a copied averaging proof. Promotion beside StatClose in Sampling.lean is
requested at a future shared-file window.

The lead approved an explicit nonnegative error premise to cover an empty shared seed space.
statistical-api.md records the exact counterexample to the draft interface without that
premise, and explains why it is not a frozen-target flaw. Actual phase coin spaces are
nonempty and one-phase closeness also supplies nonnegativity for witnessed inputs.

No randomized postprocessing wrapper was added: StatClose.abs_uprob_sub_le_prod already
provides the exact test-set bound, and statistical-api.md gives its two-line consumer.
The new file imports only Asymptotic.Sampling, within the supplied closure; no new host,
cache root, frozen edit or simp attribute is introduced.

Statistical.lean passed wrapped check 01 with no diagnostics; peak RSS 2,110,177,280 bytes,
3.22 seconds compiler wall time, after a normal shared-slot wait. The raw log includes
START/END timestamps. statistical-searches.log retains the searches before implementation.
The final source width/hash ledger, check summary, and own-tag slot log are updated.

## Finite-chain and actual-kernel outline continuation

After fresh public TCSlib and Mathlib searches, Statistical.lean now also publishes
statClose_chain for an arbitrary same-seed family f : Nat -> Omega -> O. The proof only
uses public StatClose.refl (Sampling.lean:153) and StatClose.trans (Sampling.lean:167), with
natural-cast arithmetic. It has no sign premise on delta, including q=0. Nearest relatives
are Probability.lean:218 abs_sub_le_sum_hybrids (a scalar probability-gap theorem) and
OneWayLemmas.lean:276 statClose_pi (independent products of a fixed sampler comparison).
Neither is an arbitrary-family StatClose chain; neither argument is copied. Promotion of
this generic chain lemma beside StatClose is requested at a shared-file window.

Statistical check02 passes with no diagnostics; RSS 2,114,224,128 bytes and 3.67 seconds
compiler wall time. All check summaries, own slot records, and final source hashes are
updated. The earlier Statistical hash is superseded by final-width-and-hashes.log.

hybrid-outline.md gives a precise semantic proof plan for the actual one-phase kernels,
using b's approved phaseAux/phaseVerifier and phasePrefix simulator-fold readers. It includes
normalization's real fixed point, common paired real/simulator coin tables, shared-prefix
averaging, existing randomized suffix data processing, full chain, and endpoint coin-law
transports. It explicitly records remaining execution-reader obligations rather than
assuming them. The outline has been coordinated with seq-zk-b; it proposes no private host
or frozen edit and weakens no target. Raw extra API searches are retained in
statistical-chain-searches.log and hybrid-execution-searches.log.

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
