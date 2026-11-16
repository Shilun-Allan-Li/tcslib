# sc-yao · checkpoint 2

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip for this checkpoint: `9b7b1147b2b27a1bfb9845f7b9c5ab104574c860`.
The proof branch `fill/sc-yao` stays local. Only this payload is delivered to the exchange.

## Status

`yaoHybrid_polyTime` is proved with its frozen signature. It uses only propext,
Classical.choice and Quot.sound and reaches no admitted declaration. The proof covers
arbitrary histories/private words/tapes and arbitrary answer strings of the required lengths.

`yaoHybrid_simulators` remains admitted with its issued body and sketch unchanged. All
checkpoint1 helper declarations remain proved. Completed simulator-route contracts are
preserved as whole declarations; the full security route continues after this checkpoint.
The complete fake program, tape-to-seed relabeling and all-occurrence contracts are verified
in separate agent handoffs for later integration, not claimed as part of this source snapshot.

The results are developed at the exact issue base; no unmerged proof declaration is consumed.
The sc-garble statements remain frozen admissions, and are not needed by the efficiency helpers.

## Files, ownership and interfaces

`src/` is the exact tree of changed/new source files at the checkpoint tip. `patches/` is the
whole unsigned local commit series from the issue base. `patches/COMMITS.tsv` records complete
author and committer identities and dates, including the `signing` column. The source-file
line inventory and complete declaration signatures are in `evidence/interfaces/`.

The hub is `TCSlib.Cryptography.SecureComputation.Yao.HybridProof`. All helpers live below
its directory and are imported by that facade. They never import Yao, YaoReal, OT or Compose.
Yao.lean has 1062 lines at this checkpoint, or 1090 after sc-garble's 28-line addition, below
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

The proved concrete body discharges those hypotheses with `Y.uniform`,
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

Three extra helper imports in this source were explicitly approved. Verbatim requests and answers are under
`evidence/scope-request/`: ThreeColoring.Machines (ordered loop), FromPRF.ReductionMachine
(doubling/concatenation), and FromPRF.HybridLemmas (expectation switch). Their dependency
closure extends the 184-module order to 192. No other frozen file was edited.

A fourth helper-import request for the ongoing security work was approved with the verbatim
answer “Yes”: Asymptotic.BlockEncryptor, for public encodeList_eq_flatMap. It adds exactly
one module and no Mathlib roots. The approved module is bootstrapped and included in the
224-module sweep; its future consumer is not yet part of this source snapshot. The request
and approval are under evidence/scope-request/block-encoding.md.

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
The original184-module bootstrap passed with32 base sorry warnings. The first eight
approved extra dependencies and the subsequently approved BlockEncryptor module also passed. The lead rechecked every integrated helper. Timing,
source snapshots, raw logs, slot records and both diagnostic error forms are retained.

The original agent-a seals exposed a derived gate-kind comparison and a default-size
reduction. Both were repaired through public readers; all original failures and repaired
checks remain in the evidence. A source-directed BobIO elaboration was manually stopped
for instrumentation (not a resource failure); its raw sample, source and resolution are
preserved. Some earliest agent-a source versions were reconstructed and are explicitly
marked as reconstructed, rather than represented as original snapshots.

Every checkpoint helper uses only standard axioms and has no sorried dependency. The simulator target remains admitted; the efficiency target is proved. Whole-file A/B and strict/coe seals,
paired negative controls, SY-3 reader controls, explicit-unfold scan, header/scope controls,
name clash scan and lint comparisons are retained in evidence. The final merged audit
summary identifies each completed check and any baseline diagnostic differences.

The name scan compares explicit public/private names against the entire issue base,
sc-garble a73072f1, #318 f62a25b3 and sc-compose bdfdcb76: no unexpected collision. The
single expected coincidence is the approved byte-identical fan-in reader. Lint comparisons
use complete line sets. No new FAIL is introduced. The efficiency worktree's only new WARN
is the explicitly approved SY-2 size exception; the checkpoint2 source has 1062 lines under the explicit SY-2 exception.
The old Yao target-size INFO disappears when the new directory makes it a facade.

Large raw stack samples are delivered losslessly in numbered evidence ZIP parts with
entry lists, to respect the exchange's per-file limit. They are not omitted or abbreviated.
Both evidence and top-level manifests are exact path-set manifests, with no leading ./.


## Checkpoint1 audit carried forward

The exact exported checkpoint source passes header/order/frozen-region checks and both
negative controls. It has 34 changed/new files. The required public/private name scan at
that exact source tip reports zero unexpected clashes. Its first three unsigned patches were
applied in order in a fresh shared scratch clone with the recorded committer metadata:
all three commit hashes were reproduced exactly (`evidence/patch-reproduction.log`).

All 40 current-source agent-a whole-file variants pass after the two disclosed proof-only
repairs. All 24 lead-helper variants pass. The evaluator's24 variants, BobProgram's4,
BobSimulator's4, and agent-c's12+8+4 variants pass. The lead dynamically enumerated769 stored
constants across the integrated modules and consumers, including391 helper constants;
every helper has standard axioms only and an empty sorry closure. The raw signature/axiom
probe includes private/generated constants. The efficiency proof is included in checkpoint2; its dependency audit reports an empty
sorry closure. Only the simulator target remains an issued admission.

The24 SY-3 controls have the required outcomes:8 unsealed direct proofs pass,8 sealed direct
proofs fail exactly once,8 sealed reader proofs pass. Every count includes error: and
error(...). The12 frozen-file variants have exactly the same declaration-level diagnostic
lists at base and checkpoint1. DAGCircuit has zero errors in all variants. Uniform has four
inherited errors per variant, in length_encode_le_of_isFaninTwo and IsPUniform.isPolySize.
Yao has zero A errors, and15 inherited B errors per variant: yaoCoins_eval; yaoHybrid;
yaoHybrid_callA/B; yaoHybrid_answersB_getD; yaoSeed_good_whp; yaoHybrid_simulators; and
yaoHybrid_hbcSecure. Exact counts, source locations, raw messages and immutable per-row
snapshots are in evidence/checkpoint1-audit-summary.json. No new seal failure is introduced.

Exact-snapshot lint: Cryptography92 FAIL/101 WARN (the base values), circuits0 FAIL/79 WARN
(the base values). There is no new failure. The circuit warning text changes only to remove
newly supplied readers: DAGCircuit's missing-reader count falls11→10, Uniform's2→1.
The explicit-unfold scan finds only two unchanged owned-definition unfolds in DAGCircuit;
there is no helper unfold/delta, helper admission or new axiom. See source-scan and lint diffs.

The initial frozen audit runner used repeated basenames across base/final groups. A concurrent
archiver preserved all48 completed raw logs and source snapshots under immutable-rows before
any basename was reused; each is hashed and checked against its record. The runner now uses
unique path-derived labels. This history and all original diagnostics are retained.

The390,055,049-byte BobIO sample and190,677,129-byte table sample are complete in the two
numbered raw-parts ZIPs, with entry names, original SHA-256 hashes, and decompression checks.
The payload's source/patch reproduction evidence is copied alongside all completed development
and sub-agent records. Active post-checkpoint repair output is excluded until its run finishes;
no checkpoint1 check is in progress. Evidence and top-level manifests are checked for exact
path-set equality and byte hashes before delivery.


## Efficiency proof and checkpoint2 validation

The fourth local commit proves only the frozen efficiency target, updates its proof sketch
and splits the allowed Main results bullet. There is no new declaration in Yao.lean and no
other frozen-region edit. The full header/definition/order/scope checker passes with controls.
The proof instantiates AliceProgram.message_poly, BobProgram.output_poly, the two generic
strategy constructors, both call-input equations, and the answer-independent message bound.
The complete elaborated target signature is unchanged.

All four whole-file variants were rerun after replacing one padded-key definitional closure
with padFin_apply. The canonical A strict and coe variants both pass. B strict and coe each
have17 diagnostics:15 in the same unchanged base declarations plus two applications in
yaoHybrid_polyTime. In those applications, sealing PolyExpr.eval prevents identifying
(yaoHybrid Y E1 E2).calls.eval n with Y.inB.eval n*n. This evaluation is explicitly exempt
notation under the issued ruling; the canonical variants both pass. Every new B failure is
attributed in evidence/efficiency-seal-summary.json, with raw logs and source snapshots.
The original padFin failure and repaired runs are also retained.

The target's axiom set is exactly [propext, Classical.choice, Quot.sound] and its transitive
sorry closure is empty. yaoHybrid_hbcSecure still reaches yaoHybrid_simulators only;
yaoProtocol_hbcSecure additionally reaches the two OT targets and HybridProtocol.hbcSecure_compose.
Those are the frozen sc-ot/sc-compose admissions, not new dependencies of this proof.
The base/final consumer traces are retained and the unwrapped array summary names them all.

The ordinary complete narrowed sweep uses the original184 modules, the nine explicitly
approved extra-import modules, and31 infrastructure helper/facade modules,224 in total.
The first27 passed before the user's relocation; the requested SIGINT then stopped the
current EXP check. On resume the process inventory showed no orphan, fresh preflight gave
6.463GiB headroom, and the197 remaining modules resumed in a new log phase from EXP.
All source snapshots, timing, process-pause record and both error forms are retained.
The completed sweep and sorry-warning comparison are recorded in the checkpoint2 summary.

Exact source lint adds no FAIL. Its only new Cryptography WARN is Yao's1062-line size, the
explicitly approved SY-2 exception. The frozen circuit missing-reader warning replacements
reduce the listed missing-reader counts and add no new issue. Width100 and combined1090
lines are within the issued budgets. This checkpoint's complete four-patch series is
reproduced from the issue base using its recorded author/committer dates before delivery.


## Completed checkpoint2 sweep and export

All224 modules passed with0 errors and fresh artifacts. The comparison against the issued
base-sorries.txt identifies31 remaining declarations and exactly one removed admission:
yaoHybrid_polyTime. No admission was added. The two sweep phases are joined in their original
module order in evidence/checkpoint2-sweep-summary.json; the user-interrupted partial EXP log
is retained and the resumed EXP check passed. The full sweep includes YaoReal and the
SecureComputation facade, so the new target is checked through its actual consumers.

The exact9b7b1147b snapshot passes header/order/frozen-region controls and the four-tip name
clash scan. Lint is92 FAIL/102 WARN for Cryptography, compared with92/101 at base; the sole
new warning is the approved Yao size exception. Circuits remains0 FAIL/79 WARN, with only
the disclosed missing-reader warning improvements. Four unsigned patches applied in a fresh
scratch clone reproduce all four hashes exactly. Source inventory/signatures, full metadata,
reproduction log and exact path-set/hash manifests are delivered. Checkpoint1 remains in the
exchange history at f0a9a6163c5c91599147eb550fd5bb929cc68aa0.
