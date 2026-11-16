# sc-yao · checkpoint 1

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip for this checkpoint: `f5f6fae4b4b45cb20bd42e1c9d9119e232c59513`.
The proof branch `fill/sc-yao` stays local. Only this payload is delivered to the exchange.

## Status

The decoder, garbling-from-coins program, garbled evaluator, message bounds and call-input
machines are proved as whole generic declarations. The payload also includes completed
view/simulator and coin-bijection infrastructure. Both owned target bodies and their proof
sketches remain exactly as issued in this checkpoint. The single approved hub import connects
the infrastructure. No helper contains an admission.

The concrete `yaoHybrid_polyTime` proof has separately passed in the lead worktree and is
reserved for checkpoint 2. It is not represented as proved by this checkpoint's source.
`yaoHybrid_simulators` remains open. The full security route is still being developed.

The results are developed at the exact issue base; no unmerged proof declaration is consumed.
The sc-garble statements remain frozen admissions, and are not needed by the efficiency helpers.

## Files, ownership and interfaces

`src/` is the exact tree of changed/new source files at the checkpoint tip. `patches/` is the
whole unsigned local commit series from the issue base. `patches/COMMITS.tsv` records complete
author and committer identities and dates, including the `signing` column. The source-file
line inventory and complete declaration signatures are in `evidence/interfaces/`.

The hub is `TCSlib.Cryptography.SecureComputation.Yao.HybridProof`. All helpers live below
its directory and are imported by that facade. They never import Yao, YaoReal, OT or Compose.
Yao.lean has 943 lines at this checkpoint, or 971 after sc-garble's 28-line addition, below
SY-2's 1,200-line combined cap. Other source files are below 1,000 lines and width 100.

| Agent | Proved contributions |
|---|---|
| Lead `/root` | CoinRead; BobIO; BobInit; ProtocolEfficiency; CallEquations; Strategies; facade; approved frozen-file readers; concrete efficiency glue and integration checks |
| `/root/decoder`, tag sc-yao-a | ChunkScanner; DescriptionDecoder; CoinGarbling; Garbling; WordLists; RowFromCoins; TablesFromCoins; AllTables; GarblingProgram; AliceProgram |
| `/root/evaluation`, tag sc-yao-b | RunWithHost; Decryption; FirstTagged; EvalGate; GarbledRun; BobTables; BobProgram; BobSimulator |
| `/root/lengths`, tag sc-yao-c | Lengths; OTInputs; TwoMoveViews; StatisticalSwitch; AliceSimulator; CoinRelabel |

Only the lead edits the three frozen files, commits the proof branch, runs the merged checks
and delivers. Each agent has its own worktree and olean tree. No agent commits or pushes.

## Interface (SY-1)

The main efficiency contract is `AliceProgram.message_poly`. Its conclusion is the actual
encoded vector of `garbledTable (nestedSpecial E1 E2 n)`, selected Alice keys and decoding
pairs. Its hypotheses are polynomial-time raw selectors for width, size bound, input and
output counts, description, private input and tape; a canonical description equation; input
and output vertex bounds; fan-in two; and exact key/nonce/XOR-shift seed equations. It requires
no unproved garbler or reconstruction assumption.

`BobProgram.output_poly` computes the actual runWith/evalGate result and decoding comparisons
from arbitrary message and answer words. Its hypotheses are a polynomial-time uniform
description map, output validity, polynomial-time raw parameter/message/answer selectors,
and exact initial-list/table/pair readers. The traversal derives its own polynomial state
and round bounds from the polynomial-time encodings.

The concrete body in checkpoint 2 discharges those hypotheses with `Y.uniform`,
`encodeCircuit_eq`, `encodeMsgs_eq_encWords`, `Y.outs_lt`, `isFaninTwo_iff`,
`keyAt_yaoSeed`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `readBits_apply`, and owned-definition
`rfl`. Bob's shape equations use `yaoBobInit_eq`, `yaoBobTables_eq`, `yaoBobValues_eq`,
`yaoBobOut_eq` and `decodeOut_eq`. The strategy wrappers reuse `GI.efficient_of_polyTime`
and its canonical-layout readers for every history, including malformed words.

`CallEquations.inputA_eq/inputB_eq` identify the generic affine coin/quotient machines with
the finite-product call indices. `twoMove_message_length_le`, together with the explicit
ciphertext/table/key/pair bounds, gives a bound independent of all ideal answers.

The public decoder contracts cover arbitrary raw words and every canonical DAGCircuit.
The evaluator contracts cover data-dependent key types, arbitrary initial words and tables,
constant/one/two-input gates, missing keys and malformed ciphertexts. Zero widths/counts are
included; the call proofs require no positive-width assumption.

## Gate 27 hand-off

This checkpoint does not claim the B1 embedding or security theorem.

1. Gate/row sub-hybrids: pending.
2. All occurrences and padded challenge slots: a generic contract is in development, not yet
   part of this source snapshot.
3. No-dependence argument: pending the all-occurrence contract and embedding. Accidental key
   equality is not excluded.
4. Exact sampler identities: CoinRelabel supplies the full tape/block bijection and exact
   coordinate readers, including shifts and unused coordinates. The circuit-seed and view
   identifications remain.
5. Polynomial-time reconstruction: the real garbler/evaluator and copying-view machines are
   complete. The fake program and challenge-substitution reconstruction remain.

The final target will consume only the frozen B1 statement, not reprove its PRF hybrid or
collision bound. Alice's generic statistical coupling and Bob's generic view machine are
already whole proved declarations here, but their concrete security instantiation is pending.

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

## Scope requests

The issued SY-1–SY-6 rulings apply in full. Only the listed SY-3 readers were added:
isFaninTwo_iff, encodeList_nil/cons, GateKind.encode_and/or/not, DAGGate.encode_eq and
DAGCircuit.encode_parts. The fan-in reader is byte-identical to sc-garble. The circuit
encoding reader name avoids the existing LogspaceUniformAdjBasic.encode_eq declaration.

Three extra helper imports were explicitly approved. Verbatim requests and answers are under
`evidence/scope-request/`: ThreeColoring.Machines (ordered loop), FromPRF.ReductionMachine
(doubling/concatenation), and FromPRF.HybridLemmas (expectation switch). Their dependency
closure extends the 184-module order to 192. No other frozen file was edited.

The user explicitly authorized the full objective, commits/delivery and wrapper checks
notwithstanding the supplied AGENTS prohibition: “Yes, follow the full objective and wrapper
rules.” That permission persists across the pause/resume interruption.

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

All Lean/Lake invocations use the shared lean-slot.sh with tags sc-yao and sc-yao-a/b/c,
with at most THREE Lean processes host-wide. There is no lake build. Only the lead fetched
narrowed Mathlib roots with all three slots. Python ran as python3 -I. The package trees
match all eleven present pinned packages; four documentary packages are absent as at base.
The agents' packages are read-only symlinks to the lead's own tree, and only completed
TCSlib artifacts were APFS-cloned to their separate olean trees.

Initial headroom was 6.060 GiB, later 5.589 GiB, and after resume 7.327 GiB; each exceeds
4 GiB. Free disk exceeded 150 GiB. The supplied packs and source pins passed SHA-256 checks.
The original 184-module bootstrap passed with 32 base sorry warnings; the eight approved
extra dependencies also passed. The lead rechecked every integrated helper. Timing,
source snapshots, raw logs, slot records and both diagnostic error forms are retained.

The original agent-a seals exposed a derived gate-kind comparison and a default-size
reduction. Both were repaired through public readers; all original failures and repaired
checks remain in the evidence. A source-directed BobIO elaboration was manually stopped
for instrumentation (not a resource failure); its raw sample, source and resolution are
preserved. Some earliest agent-a source versions were reconstructed and are explicitly
marked as reconstructed, rather than represented as original snapshots.

Every checkpoint helper uses only standard axioms and has no sorried dependency. The two
owned targets remain admitted in this checkpoint. Whole-file A/B and strict/coe seals,
paired negative controls, SY-3 reader controls, explicit-unfold scan, header/scope controls,
name clash scan and lint comparisons are retained in evidence. The final merged audit
summary identifies each completed check and any baseline diagnostic differences.

The name scan compares explicit public/private names against the entire issue base,
sc-garble a73072f1, #318 f62a25b3 and sc-compose bdfdcb76: no unexpected collision. The
single expected coincidence is the approved byte-identical fan-in reader. Lint comparisons
use complete line sets. No new FAIL is introduced. The efficiency worktree's only new WARN
is the explicitly approved SY-2 size exception; the checkpoint1 source itself has 943 lines.
The old Yao target-size INFO disappears when the new directory makes it a facade.

Large raw stack samples are delivered losslessly in numbered evidence ZIP parts with
entry lists, to respect the exchange's per-file limit. They are not omitted or abbreviated.
Both evidence and top-level manifests are exact path-set manifests, with no leading ./.
