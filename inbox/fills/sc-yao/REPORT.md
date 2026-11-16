# sc-yao · checkpoint 3

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip: `303e62b64db871df1f070ed2d89e8650e1d1e111`.
The proof branch `fill/sc-yao` remains local; only inbox/fills/sc-yao is delivered.

## Status and scope

`yaoHybrid_polyTime` is proved with its frozen signature, standard axioms only, and no
transitive admitted dependency. `yaoHybrid_simulators` retains its base admission and sketch.
The full simulator objective continues; this is a checkpoint, not a partial final.

This checkpoint adds proved generic two-move view/statistical contracts, a fixed uniform
Bob simulator with internally derived efficiency, all-occurrence/symbolic-label contracts,
seed and complete-tape relabeling, and exact generic sampler endpoint identities. The
completed endpoint contracts are included early as whole declarations. The selected-key B1
reconstruction, its actual tape-law specialization, and the final concrete security assembly
are not claimed complete. No unfinished source declaration is exported under src/.

The two sc-garble statements remain frozen admissions at the issue base. No unmerged
sc-garble, #318 or sc-compose proof declaration is consumed. No new frozen-file region is
changed in this checkpoint. Yao remains1062 lines,1090 after sc-garble's28-line addition,
within the1,200-line SY-2 cap. Every other file is below1,000 lines; width is at most100.
The hub imports all46 children; src/ has50 changed/new files including the three frozen
files. Complete line inventories, source hashes and signatures are under evidence/interfaces/.

## Contributions and fixed simulators

| Agent | Contributions, cumulative through this checkpoint |
|---|---|
| Lead /root | CoinRead, BobIO, BobInit, ProtocolEfficiency, CallEquations, Strategies, SliceReduction, SimulationBound, OTAnswerWords, AliceStatistical; frozen readers/efficiency body; facade and integration/audits/delivery |
| /root/decoder, sc-yao-a | ChunkScanner, DescriptionDecoder, CoinGarbling, Garbling, WordLists, RowFromCoins, TablesFromCoins, AllTables, GarblingProgram, AliceProgram; FakeObjects, FakeProgram, FakeMessage, FakeSimulator; CoordinateSwap and BobViewShape (the latter generalized from the lead's checked view probe) |
| /root/evaluation, sc-yao-b | RunWithHost, Decryption, FirstTagged, EvalGate, GarbledRun, BobTables, BobProgram, BobSimulator and GateOccurrences |
| /root/lengths, sc-yao-c | Lengths, OTInputs, TwoMoveViews, StatisticalSwitch, AliceSimulator, CoinRelabel, RelabelGarbling, CoinSeedRelabel, GateHybrids, GateHybridMessage and SamplerEndpoints |

Only the lead edits frozen files, commits the local proof branch, checks the merged source
and delivers. Every child has a separate worktree/olean tree and read-only package symlink.
No child commits or delivery pushes occurred.

AliceSimulator.simulator p is a uniform copying machine, fixed before inputs or D. The new
AliceStatistical.distAdv_real_ideal_le derives its statistical simulation bound from the
shared output-word equation, rounds/move order, p, the canonical-tape bad-event bound and
correctness off that event. It normalizes the actual tape and proves the view agreement;
it assumes no real/ideal sampler identity. AliceGenericGlue is a passing concrete Yao-body
application using yaoHybrid_correct and the supplied yaoSeed_good_whp bound.

FakeSimulator.Data is the input contract of the new simulator construction: algorithms,
polynomial counts, unary generator and canonical shape, original circuit/output/seed family
and its addressed readers. Its seed is a parameter depending only on n and the raw tape;
no concrete Yao semantic definition is copied. The input-range condition permits a larger
input count. message_poly/answers_poly derive actual fake-message and answer computation
internally from FakeProgram, with no PTC fake-message or reconstruction hypothesis.
simulator d coins then uses the existing BobSimulator. uniform/coins/runAtL/runAt/idealB
readers expose the same fixed uniform machine before D, n or private inputs. The canonical
parameter adapter normalizes the unary parameter even on malformed words.

## Interface (SY-1)

The efficiency body and its interfaces remain as in checkpoint2. AliceProgram.message_poly
uses the uniform description, public encoded-table/key/pair readers and exact seed blocks;
BobProgram.output_poly uses the generic runWith/evalGate machine on arbitrary messages and
answers. CallEquations and the answer-independent message bound finish polyTime_iff.

The simulator-route hypotheses and intended concrete readers are explicit:

| Generic contract / premise | Concrete owned-body discharge |
|---|---|
| AliceStatistical: p and Alice coin polynomial, rounds2/Alice-first | yaoCoins, yaoAlice_coins, yaoMain_rounds/verifierFirst, owned rfl |
| AliceStatistical: equal functionality output words | yaoFunctionality_f / owned rfl |
| AliceStatistical: bad-event bound, correctness off bad | frozen yaoSeed_good_whp, yaoHybrid_correct first conjunct; AliceGenericGlue PASS |
| realB_output_switch: actual output equality off bad and bad probability | yaoHybrid_correct second conjunct; strategyTapeEquiv_ofFn, uprob_comp_equiv/uprob_fst; BobOutputSwitchGlue PASS |
| BobViewShape: rounds/move order, Bob zero coins, Alice sender | yaoMain_rounds/verifierFirst, yaoBob_coins, yaoAlice_next_nil |
| OTAnswerWords.answersB_eq_active: call count and point reader | yaoHybrid_calls, yaoHybrid_answersB_getD; wire values from values_getD_input |
| FakeSimulator.Data.make: PT evaluators / normalized generator | hE1/hE2, Y.uniform, encodeCircuit_eq and encodeMsgs_eq_encWords |
| Data.make: count/range/output/fan-in | Y.inA/inB/outLen/sizeBound, Y.outs_lt, isFaninTwo_iff; original Y.circ/outs supplied |
| Data.make: seed key/nonce/XOR equations | keyAt_yaoSeed, yaoSeed_snd_fst/snd_snd, readBits_apply, assignIdx_eq, xorShift_apply; owned rfl |
| SamplerEndpoints: full tape bound, fan-in and four seed readers | Y.size_le, isFaninTwo_iff and the same original seed readers |
| SamplerEndpoints: real encoded-view equation | BobViewShape, OTAnswerWords, yaoMsg/tables/keys/pairs readers and actual input values |
| SamplerEndpoints: final result and ideal coin/view reader | Y.output_apply, C.values readers; FakeSimulator.idealB_eq/make_messageAt/make_answersAt; existing NUPPT.coinsEquivPoly/ofFn |

The probes are body-instantiation harnesses; reductions of Yao's own definitions are allowed
in the future owned theorem body. No helper imports/names YaoCircuit, yaoSeed or yaoHybrid.
Complete formal signatures and all implicit section parameters are printed in stored-constant
logs, and source headers are exported under evidence/interfaces/.

SliceReduction.reconstruction_negligible takes a fixed total polynomial-time rebuild,
finite nonempty advice choices with a polynomial word bound, fitting offsets/lengths and
two deterministic message families. It chooses the maximizing advice at each n and builds
one parameter-preserving NUPPT reduction with the original D coins before invoking B1's
uniform bound. It does not assume an embedding exists. distAdv_fibers_le averages independent
auxiliary randomness; distAdv_chain_le and chain_negligible use the published hybrid bound
and polynomial-times-negligible closure. SimulationBound combines the common statistical
switch and uniform Bob bound for fixed SA/SB. The remaining embedding must discharge these
premises concretely; that work is not hidden as a PTC or sampler-identity hypothesis.

## Gate 27 hand-off

1. Gate/row sub-hybrids: GateHybrids.rowWith/tableWith, outputBit/stageBit and exact
   even/odd/start/end readers. outputBit_first_unchanged and outputBit_second_unchanged
   isolate the two selected inactive-argument substeps. Zero/one/two arguments are included.
2. All occurrences/padding: GateOccurrences.mem_occurrences_iff, exhaustive,
   per_row_unique, occurrences_nodup, length_occurrences_le (at most4*gates) and
   padded_occurrences_some_iff include occurrences in every gate. No key-value distinction
   is assumed; the address is a symbolic vertex/bit label.
3. No-dependence: selected_wire_lt, hybrid_plaintext_ne_of_used, active_label_ne and
   decoding_label_ne establish symbolic separation using acyclicity, prior fake gates,
   active input/answer keys, outs_sink and args.Nodup. The final selected-fill specialization
   to actual substeps and shared descriptor advice remains work in progress.
4. Exact sampler endpoints: RelabelGarbling gives per-seed key/row/table/output-pair
   identities; CoinSeedRelabel.seed_relabel identifies the full addressed tape action,
   including unused assignment codes, shifts and n=0. SamplerEndpoints composes these with
   the supplied real view equation and acceptProb_comp_equiv. The final stage is the
   canonical FakeObjects.message and active answers, transported through any given ideal
   coin/view reader. The actual selected-coordinate law is ongoing, not inferred from a
   uniform distribution over all permutations.
5. Polynomial-time reconstruction: real/fake garbling, generic decoder/evaluator and
   simulator view machines are proved. B1 challenge row/table/view reconstruction and its
   polynomial advice envelope are ongoing in b5 and not exported in this checkpoint.

## Overlap and reuse

Searches preceded probability, list, coin and machine proofs. Detailed searches and nearest
relatives are retained under each agent's evidence. These disclosures include inline proofs.

- The description decoder reuses DAGCircuit.decode/decode_encode where validation fits; its
  new streaming host recodes the gate fields for computation. CVAL decides a language and
  does not supply a generic data-returning evaluator, so it cannot replace these contracts.
- DescriptionDecoder.dbl_pair reuses public MultiMsg.dbl_append at
  Encryption/PrivateKey/FromPRF/ReductionMachine.lean:235. An unpublished local duplicate was
  removed before checking.
- Garbling.fixedTable_poly re-derives the finite pairing assembly of private
  Complexity.clNative_fields, Complexity/CookLevin/Hardness.lean:4000. That private helper is
  inaccessible and outside the allowed closure. The generic replacement uses public pairing
  and word-list readers. Promotion/deduplication review is requested.
- WordLists directly reuses ColMachines.polyTimeComputable_flatMap_range and public
  ofFn_eq_map_range. No range/flatten identity is copied.
- Garbling.gateOut_small and private keyList_small specialize published gate, argument-key
  and word-list readers at arity at most two. The nearest private map_range_getD_ofFn bridge
  in Garbling.lean cannot be imported; the bounded calculation is disclosed here.
- ChunkScanner.flatMap_scan has changing finite control, unlike the fixed-position
  BitLists.flatMap_range_drop. It uses the public emitting-loop construction.
- RowFromCoins.assignmentFold_eq_two computes the exact two-bit assignment index. Its SY-5
  relative is sc-garble Garbling/CoinBlocks.lean:38 assignmentFold_small (exchange a73072f1),
  which instead proves bounds/injectivity. No unmerged declaration is used.
- RunWithHost reuses stateFind and the published runWith equations, plus H14 clean_install
  and Clean.envelope for the same-machine time/head contract. No time-to-space proof is copied.
- The tagged decryption contract generalizes SpecialEncryption.polyTimeComputable_spDecFun,
  whose message length is fixed to the key length; the outer nested layer needs 4n+2.
  FirstTagged directly reuses the public first-index search host.
- BobIO and BobInit compose public getW/countW/padding/window/vector-map contracts. CoinRead
  uses existing drop/pad machines and public getElem/ofFn readers; it adds no getD/ofFn or
  headD/drop utility. CallEquations reuses finite-product, ofFn and Nat division readers.
- Strategies specializes GI.efficient_of_polyTime (GraphIsomorphism/Proofs.lean:594) and its
  existing interactive-layout readers. ProtocolEfficiency specializes the existing transcript
  equation and two singleton membership cases.
- Lengths.length_spEncStr_le differs from SpecialEncryption.length_spEncStr: its upper bound
  holds for arbitrary evaluator output lengths. The nested bound's nearest unavailable SY-5
  relative is sc-garble GarblingSecurity/NestedBounds.lean:37 length_nestedInner, an exact
  canonical-pad length theorem. All encoded-list estimates reuse BinArith.length_encWords_le.
- encodeMsgs_eq_encWords generalizes the local henc at Yao.lean:352 using the existing
  nil/cons readers. No private list-encoding injectivity lemma is copied.
- TwoMoveViews reuses Protocol transcript/view/output readers. SY-5 relatives are #318
  ObliviousTransfer/Shape.lean:192 exec_five and :203 transcriptWith_isOT, ViewA.lean:93
  realA_realCoins (f62a25b3), and sc-compose ComposeSecurity/Runs.lean:466/536
  realA_compose_eq/realB_compose_eq (bdfdcb76). Their protocol shapes differ and are unavailable;
  these are general two-message specializations, with no copied code.
- StatisticalSwitch reuses MultiMsg.abs_uexp_sub_le_uprob, statClose_iff and uprob readers.
  AliceSimulator uses the existing same-coins switch and coin equivalences; it does not
  introduce another probability/expectation inequality.
- CoinRelabel reuses FunFamily.blocks/blocksEquivX, Fin.appendEquiv and xorPerm. Its exact
  decomposition includes shifts and is invertible on the entire tape, including n=0/S=0.
  SY-5 relatives are sc-garble CoinBlocks.lean:51 pushesUniform_bits_of_blocks, :83
  key_row_blocks_injective and :162 pushesUniform_key_row_blocks. Those are marginal
  uniformity results, not this full relabeling. No probability proof is copied.
- Seal tooling is adapted from sc-garble's evidence generator; this is tool reuse, not proof
  reuse. The source version and subsequent runner changes are retained.


Additional checkpoint3 disclosures:

- CoinSeedRelabel.assignmentFold_injective/assignmentEmbedding re-derive the general
  arity<=2 assignment-code bound/injectivity of unmerged sc-garble
  Garbling/CoinBlocks.lean:38 assignmentFold_small (a73072f1), through the already published
  two-bit equation. The finite permutation extension, padded masks and whole seed identity
  consume those facts. No unmerged declaration is imported. This SY-5 debt is explicitly
  requested for proof-only re-pointing/promotion review after both sides land.
- RelabelGarbling reuses argKeys/garbledTable/keyAt/inputKeys readers and xorPerm_apply;
  double-XOR cancellation is inline from Bool equations, nearest the private involution
  proof inside xorPerm. No public probability or list theorem is copied.
- GateHybrids/GateHybridMessage are new parameterized hybrid objects with readers; they
  consume existing real/fake semantics and specialize via exact equalities. They do not
  reimplement the real/fake sampler. The unmerged sc-garble searches found no corresponding
  hybrid family. SamplerEndpoints directly composes those identities with existing
  acceptProb_comp_equiv/acceptProb_fst; no probability measure or counting fact is added.
- CoordinateSwap reuses published uniform reseeding and ignored-coordinate laws. Its new
  content is a simultaneous partial matching involution retaining arbitrary control and
  padded coordinates. It assumes neither distinct coordinate values nor uniformity of a
  derived permutation over all permutations. Reuse searches are in a5/SEARCH.md.
- OTAnswerWords.length_answersB and answersA_nil are bit-OT specializations of the general
  unmerged sc-compose ComposeSecurity/Lengths.lean:51/58 HybridProtocol.length_answersA/B
  (bdfdcb76). They use the public answers/OT-output/list-length equations and do not import
  sc-compose. Disclosed SY-5 proof-only deduplication is requested after landing.
- SliceReduction reuses NUPPT.exists_compParam/exists_withAdvice and public coin congruence,
  B1/slice readers, uprob_prod/comp_equiv, abs_uexp_sub_le, abs_sub_le_sum_hybrids and
  negligible_polyExpr_mul. The advice-maximization and adapter are new; the probability,
  chain inequality and negligible closure are not re-proved.
- FakeProgram/FakeSimulator extend the existing generic garbling and BobSimulator contracts
  using the actual fake row/table/result readers. BobViewShape is a generic extraction of
  the lead's checked concrete view proof; it consumes TwoMoveViews rather than re-proving
  transcript semantics. These provenance details and every development log are retained.

## Scope requests and readers

SY-1–SY-6 apply. The only frozen circuit insertions are the exact SY-3 readers:
isFaninTwo_iff (byte-identical to sc-garble), encodeList_nil/cons, GateKind.encode_and/or/not,
DAGGate.encode_eq and DAGCircuit.encode_parts. Removing them restores the base bytes.
The encode_parts name avoids an existing downstream encode_eq name. Their24 reader-necessity
controls remain delivered:8 unsealed direct passes,8 sealed negatives each exactly1error,
and8 sealed reader passes, counting both diagnostic forms.

The four user-approved extra imports and verbatim answers are in evidence/scope-request/:
ThreeColoring.Machines; FromPRF.ReductionMachine; FromPRF.HybridLemmas; and
Asymptotic.BlockEncryptor. Their closure is193 original/approved modules; no extra Mathlib
root was added for the fourth import. BlockEncryptor's consumer is ongoing b5, not this src/.
The user also explicitly authorized the full objective, edits/commits/delivery and wrapper
checks despite AGENTS: “Yes, follow the full objective and wrapper rules”. These approvals
persist across all relocations. No further frozen scope was assumed.

## Hosts, promotion and reader requests (SY-4)

Request promotion and registry review at landing. No frozen registry file is edited here.

| ID | Host | Status / provenance | Consumers |
|---|---|---|---|
| H-SY-decoder (draft) | Circuit-description recoder: DescriptionDecoder.decodeDescription_host. One H14 clean machine maps a paired circuit/output description to the unary input count, encoded gate records and unchanged output word; canonical correctness for every DAGCircuit, polynomial first-halt time and all-time work-head envelope for that same machine. | Proved in sc-yao, public generic SY-4 contract; promotion to the circuit-complexity construction layer requested. Built from emitting-loop, finite branching, pairing and clean_install/Clean.envelope. | Alice garbling; output decoding; garbled evaluator; simulator/reduction reconstruction. |
| H-SY-eval (draft) | RunWithHost.exists_machine: encoded topological evaluation generic in gate records, input-dependent value types, leaf step, initial values and polynomial round/state envelopes. One clean machine with polynomial time and all-time work-head envelope. garbledRunWith_poly derives envelopes for fixed-width key encodings. | Proved in sc-yao; promotion and registry gate requested. Built from stateFind and H14. | Bob evaluator; fake-garbling simulator; reduction reconstruction. |

The supporting ChunkScanner is also public with a same-machine clean/time/head contract.
No private host is introduced. The read-only source/signature inventory identifies every
new public definition and its published reader.


## Validation and evidence

All Lean/Lake/tree commands use /private/tmp/sc-yao-lean-slot.sh and tags sc-yao/a/b/c,
with at most THREE Lean processes host-wide. Python is python3 -I; never lake build or
unfiltered cache get. Pins/packs and packages were verified at bootstrap. Children use
separate TCSlib artifact trees and read-only package symlinks. The latest resumed preflight
has6.368GiB headroom against4GiB and no orphan proof process. Wrapper SHA256 is unchanged.
The first resumed lead normal batch lacked access to shared slot files and never acquired
one; its waiting process group was stopped, its log retained, then all6checks reran with
required access and passed. No Lean run or resource failure occurred in that first attempt.

All integrated new helpers, hub, Yao and YaoReal pass ordinary checks. The complete audit
prints1082 stored constants including704 helper constants, private/generated constants
included. Every helper uses only propext/Classical.choice/Quot.sound, with empty transitive
sorry closure. The efficiency target also has exactly those axioms and empty closure.
yaoHybrid_hbcSecure still reaches the simulator admission only; yaoProtocol_hbcSecure
additionally reaches the two frozen OT targets and hbcSecure_compose. Base and current
consumer traces remain delivered.

The lead's16 new full-file variants pass (SimulationBound, OTAnswerWords, AliceStatistical,
hub); final-source SimulationBound also has4/4rerun after a module-inventory documentation
correction. Its own stored-constant trace passes. All integrated agents' full-file seals
and controls pass, with their exact source/version records. Definition seals cover every
imported TCSlib definition and generated matcher, excluding only authorized notation.
All commands use -DmaxErrors=0 and count both error: and error(...). Earlier failed sources,
unused-tactic warnings, repairs and documentation-only comparisons are retained.

Frozen-file diagnostics remain the previously audited baseline. DAGCircuit:0errors in all
variants. Uniform:4inherited errors in two old declarations. Yao canonical A strict/coe
passes; B strict/coe each17errors=15unchanged base diagnostics plus2efficiency call-input
applications requiring the explicitly exempt PolyExpr.eval notation. These two are fully
attributed in efficiency-seal-summary.json. No simulator body has changed at this checkpoint.

The source/header/order/scope checker passes with both one-error controls. The full four-tip
namespace-resolved name scan reports492 new explicit names and0unexpected clashes; the
approved byte-identical fan-in reader is the sole intentional overlap. Downstream checks
also validate generated names. The explicit-definition scan reviews1399tactic references
across8949files including core/Mathlib. Its9candidates are local h/hv/hi/heq/hNext binders,
with exact context review and source hashes,0foreign-definition violations. Earlier scan
versions are preserved.

Exact line-set lint: Cryptography92 FAIL/102 WARN, base92/101; the only new WARN is Yao's
approved1062-line size. Circuits0 FAIL/79 WARN, unchanged counts, with missing-reader text
improved11→10 and2→1 in the two SY-3files. No new FAIL or undisclosed WARN is introduced.
Width, generic visibility, complete facade child imports and no-helper-admission scans pass.

All240 modules pass with0 errors and fresh artifacts. The source snapshots match the committed source, and the complete issued-plus-approved order is covered. Comparing declaration names against base-sorries.txt gives31remaining admissions, exactly the removal of yaoHybrid_polyTime; no admission was added. See evidence/checkpoint3-sweep-summary.json and the complete checkpoint3-sweep raw logs/results.

The complete unsigned five-patch series and COMMITS.tsv include author/committer identities,
dates and signing=none. All five commit hashes reproduced exactly from the issue base in a fresh shared scratch clone, using the recorded identities/dates. Top-level and evidence manifests are checked
for exact file-set equality, no leading ./ and SHA256 byte equality before delivery.

Evidence completeness includes every retained raw source/log/results file, probes, tools,
header/seal/control/search/clash records, sub-agent handoffs and relocation notes. Large
raw stack samples remain losslessly in the two numbered ZIPs with entry hashes and verified
decompression. The later relocation ZIP separately preserves all four source/evidence trees;
its48MB archive is checksummed, and incomplete development material inside evidence is not
part of the exported proof source. Current b5/TapeValues/SelectedLaw development is outside
this source snapshot; nothing from it is claimed as a completed checkpoint theorem.

Prior pushed deliveries remain in exchange history: checkpoint1 f0a9a6163c5c91599147eb550fd5bb929cc68aa0;
checkpoint2 816971fc6922646f056a47efd41b1407f762320d. This checkpoint is delivered only under
inbox/fills/sc-yao from the clean dedicated delivery worktree, after rebase and without a
force push. No final-security completion or PR merge is claimed.
