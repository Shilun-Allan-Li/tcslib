# sc-yao · final

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip: `6e7ef601ad9a05d5e26d09f32eadb9c17a4a6cbc` (eight unsigned commits).
The proof branch `fill/sc-yao` remains local. Delivery is restricted to
`inbox/fills/sc-yao/` on `exchange/pass-shelat-ch5-8`, from the separate
`codex/sc-yao-delivery` worktree.

## Result and proved-modulo boundary

Both requested frozen theorems are proved with their original signatures:

| Theorem | Result and admitted dependency closure |
|---|---|
| `yaoHybrid_polyTime` | Proved; only `propext`, `Classical.choice`, `Quot.sound`; no admitted dependency. |
| `yaoHybrid_simulators` | Proved modulo exactly frozen `yaoSeed_good_whp` and `sliceMultiMessageSecure_of_prfOut`, the sc-garble statements that remain admitted at the issue base. No new admission. |

The simulator proof retains both evaluator equations, both polynomial-time hypotheses and
all three PRF hypotheses, including the joint family. It chooses fixed uniform `S_A`, `S_B`
before the distinguisher and inputs, then obtains one negligible bound before all `n,x,y`.
This proves [PS10, Protocol162.6/Theorem163.7] in the OT-hybrid model with the stated
one-active-key [LP09] simulation. The real-protocol consumer additionally depends on the
separate sc-ot and sc-compose statements; those units are outside this fill.

No declaration added by the unmerged sc-garble, #318 or sc-compose deliveries is imported or consumed. The two
sc-garble statements are cited exactly as frozen, not replaced by new assumptions or
re-proved B1/PRF/collision machinery. The maintainer lands sc-garble first and rebases this
fill afterward, including the shared main-results-bullet conflict.

The final exact-source sweep passed all261 modules, including the last documentation
revision. The admission comparison is32→30: exactly the two target admissions disappear.
All272current-source helper seals pass; four documentation reruns replace the four
superseded Garbling rows, with all276raw runs preserved. The final1490 constant trace
confirms the table above. No proof code or declaration changed in the English sketch edit.

## Source, exports and frozen scope

The single hub is `TCSlib.Cryptography.SecureComputation.Yao.HybridProof`. It imports all
67 children once; the68 helper/hub files contain14306 lines, with maximum577 lines per file
and width≤100. There are71 changed/new Lean sources including the three approved frozen
files. Yao has1152 lines and width99; adding sc-garble's28 lines gives1180≤1200 under SY-2.
All other delivered Lean files are below1000 lines. Full hashes and source/elaborated
signatures are exported under `evidence/interfaces/` (`source-inventory.json`, `source-signatures.md`, `full-stored-signatures.md`).

The frozen changes are exactly the two theorem bodies, their proof sketches, the permitted
main-results bullet, one hub import immediately after the original imports, and the eight
SY-3readers below. No new declaration is added to Yao. All other existing headers,
definitions, bodies, variables, sections, imports, comments and frozen prose restore the
issue-base bytes after masking these approved spans. The old statement-phase title and
the entire `yaoSeed_good_whp` statement/sketch/admission remain unchanged.

The readers are `DAGCircuit.isFaninTwo_iff` (byte-identical to sc-garble),
`encodeList_nil`, `encodeList_cons`, `GateKind.encode_and`, `GateKind.encode_or`,
`GateKind.encode_not`, `DAGGate.encode_eq`, `DAGCircuit.encode_parts`. Removing the
insertions restores both circuit files exactly. `encode_parts` avoids an existing
downstream name. No attribute, frozen definition change, additional hub import or other
frozen-file edit is introduced.

Root `TCSlib.lean` imports the SecureComputation facade, which imports Yao; Yao imports
this one hub. The67 children are therefore reachable without a frozen facade edit.
The supplied193original/approved upstream modules plus68helpers/facade form the complete
261-module narrowed order; root `TCSlib` is excluded as specified by the brief. The
maintainer performs the full-library/audits checks at landing.


## Contributions and ownership

| Agent | Cumulative contributions |
|---|---|
| Lead /root | CoinRead, BobIO, BobInit, ProtocolEfficiency, CallEquations, Strategies, SliceReduction, SimulationBound, OTAnswerWords, AliceStatistical, SelectedLaw; generalized CoordinateSwap's finiteness interface; corrected BobViewShape's import; eight approved readers and both target bodies; final Garbling proof-sketch correction; integration, merged checks, commits and delivery. |
| /root/decoder, sc-yao-a | ChunkScanner, DescriptionDecoder, CoinGarbling, Garbling, WordLists, RowFromCoins, TablesFromCoins, AllTables, GarblingProgram, AliceProgram, FakeObjects, FakeProgram, FakeMessage, FakeSimulator, CoordinateSwap, BobViewShape, FakeSimulatorFactory, BobStageZero, GateHybridChain, GateHybridSecurity; complete concrete simulator prototype. |
| /root/evaluation, sc-yao-b | RunWithHost, Decryption, FirstTagged, EvalGate, GarbledRun, BobTables, BobProgram, BobSimulator, GateOccurrences; NonceCoordinates, SeedCoordinates, SliceReconstruction, SelectedSlices, SelectedSeed, SelectedRows, SelectedPlan, SelectedTables, SelectedAdviceBounds, SelectedStep, SelectedStepChoices, SelectedStepSecurity. |
| /root/lengths, sc-yao-c | Lengths, OTInputs, TwoMoveViews, StatisticalSwitch, AliceSimulator, CoinRelabel, RelabelGarbling, CoinSeedRelabel, GateHybrids, GateHybridMessage, SamplerEndpoints, TapeValues, SelectedFields, GateStepCases, BobStatistical; shorter concrete assembly skeleton. |

Only the lead edits frozen files, commits and delivers. Children have separate worktrees,
separate TCSlib artifact trees and read-only package symlinks. All child evidence is under
evidence/subagents/. Ownership transfers and immutable handoff hashes are retained.


The final read-only review assignments preserve this ownership:

| Review agent | Contribution and evidence |
|---|---|
| final_seal_attribution, existing sc-yao-a worktree | Individually matched all24Yao B diagnostics in both variants to base/efficiency/prototype comparators; full excerpts and hashes under evidence/subagents/final-seal-attribution/. No Lean rerun or source edit. |
| final_requirements_review, existing sc-yao-c worktree | Reverified packages,24 reader controls, exact base seals, export reachability, host contracts/registry format, scope records, signatures and final requirement coverage; identified report/script-location gaps and reviewed publication inventory. Evidence under final-requirements-review/. No Lean rerun or source edit. |
| final_manifest_review, existing sc-yao-b worktree | Verified all272prepared probes exactly reconstruct68sources, their variants/base absence/shards; identified and re-reviewed shared-lock and result-hash guards; drafted this report. Evidence under final-manifest-review/ and final-manifest-review-strengthened/. No Lean rerun or library-source edit. |

The lead copied only verified immutable handoffs into its worktree, ran the merged final
checks, and retained the hashes and ownership transfers. No child pushed or committed.


## Generic interface and concrete proof assembly (SY-1)

Every helper is upstream of Yao and generic in the actual circuit, output selectors, seed,
strategies, protocol and functionality, supplied through parameters and published equations.
It cannot name/import `YaoCircuit`, `yaoSeed`, `yaoHybrid`, `yaoFunctionality`, YaoReal or the
in-flight OT/composition modules. No Yao seed/message/protocol semantic definition is copied.
The new gate hybrid semantics are defined once in GateHybrids/GateHybridMessage and read
through their interfaces. The two owned bodies instantiate them using Yao's own readers or
owned-definition reflexivity. Full stored signatures retain all implicit section parameters.


### Efficiency premises and their actual discharges

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



### Simulator premises and their actual discharges

The concrete simulator body was transferred from the checked complete a12 construction,
adding only the scoped helper-namespace opening. It preserves the full frozen declaration
and its section/include context. Its actual main-file normal check and canonical whole-file
A strict/coe seals pass; this is an installed target proof, not only a prototype.


`S_A = AliceSimulator.simulator (yaoCoins Y)`. `FakeSimulatorFactory.exists_simulator`
constructs one uniform `S_B` with the same coin polynomial and the exact ideal-view word
contract; both machines are chosen before the distinguisher and inputs. The factory uses
`Y.uniform`, `Y.circ`, `Y.outs`, `Y.outs_lt`, both actual evaluator algorithms and their
proved efficiency. Its description equation uses `encodeCircuit_eq` and
`encodeMsgs_eq_encWords`; its input-range equation is reflexivity under polynomial notation.
Arity follows from `DAGCircuit.isFaninTwo_iff` applied to `Y.fanin`.

| Premise | Actual instantiation/readers |
| --- | --- |
| Key blocks | `yaoSeed_fst`, `keyAt_eq`, `dif_pos`, `readBits_apply`. |
| Both nonce halves | `congrArg Prod.fst/snd (yaoSeed_snd_fst ...)`, `readBits_apply`, `assignIdx_eq`. |
| Row shifts | `yaoSeed_snd_snd`, `xorShift_apply`, `readBits_apply`. |
| Input wire values | `values_getD_input`, `Fin.castAdd/natAdd`, `Fin.append_left/right`, and public `ofFn` list readers. |
| Actual Bob view | `BobStageZero.acceptProb_eq_stage0`, with `yaoAlice_next_nil`, `yaoHybrid_answersB_getD`, main/coin/call readers, and `yaoMsg_eq`/`yaoTables_eq`/`yaoKeysA_eq`/`yaoPairs_eq`. |
| Ideal endpoint | `SamplerEndpoints.acceptProb_end_eq_ideal` and the factory's exact ideal word contract. `yaoCoins_eval`, `NUPPT.coinsEquivPoly_symm_ofFn`, and `ofFn_arrowCongr_finCongr` preserve the tape word. |

The negligible bad-event bound is the frozen `yaoSeed_good_whp` instantiated with the
actual `hGE₁`, `hGE₂`, `hG₁`, `hG₂`. `yaoHybrid_correct` supplies both off-bad output
equalities. `AliceStatistical.distAdv_real_ideal_le` and
`BobStatistical.statClose_real_output_switch` discharge the two statistical steps.

The computational call is `GateHybridSecurity.endpoint_negligible` with input family
`(Fin (Y.inA.eval n) → Bool) × (Fin (Y.inB.eval n) → Bool)`, counts
`S=Y.sizeBound`, `A=Y.inA`, `B=Y.inB`, `O=R=Y.outLen`, seed `yaoSeed Y`, output
selector `Y.outs`, wire values `((Y.circ n).values (Fin.append x y)).getD · false`,
Bob word `ofFn y`, and outer Alice word `ofFn (Y.output n x y)`. `Y.size_le`,
`Y.fanin`, `GateHybrids.values_consistent`, `Y.outs_sink`, and `List.length_ofFn`
discharge its structural/word bounds. The joint generator is exactly
`Fin.append (G₁ n s x) (G₂ n s x)`, with
`L = .add (.add .var .var) (.add .var innerLen)`. `List.ofFn_fin_append` proves its
word equation; public `PolyExpr.eval_add/mul/const/var` and `innerLen_eq` establish
`7*n+2 ≤ L.eval n`. B1 is exactly `sliceMultiMessageSecure_of_prfOut hG₁₂`.
`simulators_of_output_switch` combines the resulting computational bound with the
statistical bound. No assumed fake-message or active-answer efficiency remains.



`GateHybridSecurity.endpoint_negligible` derives its selected-key bound from B1 with
polynomial advice, then `GateHybridChain.endpoint_negligible` accounts for at most twice
the gate count. `SliceReduction.chain_negligible` uses the explicit envelope `2*S(n)` and
chooses `2*S(n)*|μ_B1(n)|`, negligible by the published polynomial-times-negligible theorem.
The selected bound is nonnegative, so this is the brief's `2*S(n)*ε_B1(n)` form. The output
switch adds the frozen bad-event bound `δ(n)`. `simulators_of_output_switch` supplies one
common negligible bound for both parties. No neighboring-security, reconstruction-PTC or
sampler-identity premise is left assumed in the concrete body.


## Gate 27 hand-off — selected-key embedding

Here `H/` abbreviates
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/`; declaration names are relative to
`TCSlib.Cryptography.SecureComputation.YaoHybridProof`. Agent b proved b5/v6/v7; supporting
shared contracts below retain their respective lead/a/c authorship.

| Gate 27 obligation | Declaration map and delivered contract |
| --- | --- |
| 1. Gate and row sub-hybrids | Shared `H/GateHybrids.lean` `outputBit`, `stageBit`, `outputBit_current_first/current_rest`, and `H/GateHybridMessage.lean` `sample_eq` specify the two substeps per gate. v6 `SelectedStep.unselected_eq`, `advice_next`, `reconstruct` (`H/SelectedStep.lean:60,91,145`) give both neighboring endpoints for each actual argument. v7 `SelectedStepSecurity.selected_negligible` (`H/SelectedStepSecurity.lean:176`) uniformly bounds them. Missing arguments use c's `SelectedFields.stage_first_of_arity_zero/stage_second_of_arity_le_one` and `GateStepCases`; no dummy selected vertex is required. |
| 2. All occurrences, with padding | `GateOccurrences.mem_occurrences_iff`, `length_occurrences_le`, `padded_occurrences_some_iff` enumerate every gate/permuted-row/selected-position occurrence, not merely the current gate. b5 `SelectedSeed.slotIndex_padded` (`H/SelectedSeed.lean:355`) and `SelectedPlan.slotReaders_of_padded/slots_fit` identify every real slot exactly. v7 `SelectedStepChoices.capacity` (`H/SelectedStepChoices.lean:100`) closes capacity for `q=4S`; its `offset`, `len`, `message` cover real and unused slots. |
| 3. No dependence on the selected inactive label | Acyclicity is `GateOccurrences.selected_wire_lt`; shared `SelectedFields.stageBit_plaintext_ne_even/odd/next`, consumed by v6 `SelectedStep.plaintext_ne`, exclude `(u,true)` from every plaintext label, including the already-fake producing gate. `GateOccurrences.decoding_label_ne` uses `outs_sink`; `SelectedFields.keyAt_false`, `activeAnswers_fill`, `decodePair_fill`, `message_tail_fill` keep Alice's active keys, Bob's OT answers and decoding tail fixed. b5 `SelectedSeed.argument_label_eq_iff` and `fill_argKeys_some/none` use argument Nodup to exclude double use within one row. v6 `reconstruct` discharges plaintext/output separation internally. These are inequalities of labels, never inequalities of actual key values. |
| 4. Exact coin and view sampler identities | b5 `SelectedTables.record_reconstruct/tables_reconstruct/tablesWith_reconstruct/view_reconstruct/sample_reconstruct` (`H/SelectedTables.lean:69,130,169,215,256`) are pointwise in every challenge key and nonce vector. v6 `SelectedStep.reconstruct` and v7 `SelectedStepChoices.rebuild_some` use the **same before-stage advice** for both sides. b5 `NonceCoordinates.pick_iff_place/nonce_read` and `SeedCoordinates.dataEquiv_fill` identify coordinate replacement. Shared `TapeValues.seed_on_inverse`, `CoordinateSwap` and lead `SelectedLaw.acceptProb_fill` retain the actual shifts/unused coordinates and close the uniform-tape law. The separate endpoint coin identities are shared `GateHybridMessage.sample_relabel/sample_end`, not redefined here. |
| 5. Polynomial-time reconstruction | b5 `SliceReconstruction.row_poly/tables_poly/rebuild_poly` (`H/SliceReconstruction.lean:98,149,216`) prove one total raw reconstruction on **every** input/advice string, requiring only the uniform `E₂` leaf's polynomial time. Advice construction and precomputed messages are offline, polynomial-length data. `SelectedAdviceBounds.sample_advice_budget` and v7 `SelectedStepChoices.advice_budget` close that length bound. Lead `SliceReduction.exists_adviceReduction` preserves `D.coins` and runs `D.distinguisherL n` at the same `1^n`. |

For evaluated polynomial bounds `s=S(n), a=A(n), b=B(n), o=O(n), r=R(n)`, the actual choices are

```
q(n) = 4s,                       slots = q(n)+1,
t(n) = 2a(2n+2)+2+o(6n+6),        i(n) = 2b+2+bn,
sampleBudget(n) = 2s(16(2q(n)+7n+8)+18) + 2t(n) + 2i(n) + r + 6.
```

These are the published `SelectedAdviceBounds.slotBudget`, `tailBudget`, `privateBudget`,
`sampleBudget` and evaluation readers; `sample_advice_budget` derives row count and capacity
from fan-in two, canonical rows and `C.size≤S(n)`. A record costs at most `2q+7n+8` bits.

The interface is nonadaptive: `SelectedRows.word/message/descriptor` precompute the inner
ciphertext when the selected key is outer, or wrap the inner challenge afterwards using
the known other key/nonce. `SelectedSlices.only_row/inner_row/outer_row` use precisely
`(0,n)` and `(2n,4n+2)`. Every challenge message is fixed before any challenge ciphertext;
unchanged/unused slots get equal messages. Repeated actual key values are allowed. The
actual tape law includes two independent nonce halves and keeps shifts plus all unread
padding; it never asserts uniformity over all derived permutations.

Zero-width keys, zero input/output counts and zero gates are included. The v7 choice type
is `Option (input × actual gate/argument) × fullTape`; `none` supplies empty advice and
zero-length messages, so no Nonempty input/gate/vertex premise is introduced. Constant
and one-argument missing substeps are equalities. Repeated or input output vertices need
no extra restriction beyond the original sink hypothesis.

The exact B1 route is v7 `filled_negligible` (`H/SelectedStepSecurity.lean:79`): apply lead
`SliceReduction.reconstruction_negligible` to this finite choice family, maximizing over
input, selected step **and the entire baseline tape**, with the explicit advice polynomial
and the fixed raw reconstruction. The empty option also forces the resulting negligible
bound nonnegative at every n. `selected_negligible` then uses
`SliceReduction.distAdv_fibers_le` and `SelectedLaw.acceptProb_fill` on both endpoints.
Thus one μ bounds all actual selected neighbors, with no assumed sampler identity or
unproved reduction premise. The caller supplies actual frozen B1
`sliceMultiMessageSecure_of_prfOut`, the concatenation/evaluation equations and joint pad
length at least `7n+2`. No D1–D4, PRF hybrid, collision bound or chain argument is rebuilt;
a's `GateHybridChain`/`GateHybridSecurity` perform the polynomial chain closure.



### Remaining edge-case and efficiency coverage

The exact tape decomposition includes all unused key/row/shift blocks, including wires
read by no gate and unused size-bound capacity. It retains the real XOR shifts; it does
not replace them by a uniform permutation over an unrestricted permutation group. A wire
may occur in several gates in both argument positions, placing both slice shapes under
the same unknown key. The argument is on symbolic vertex/bit labels, so accidental equal
sampled key values do not invalidate it.

Input/output counts and widths may be zero; empty circuits and constant/one/two-argument
gates are covered. Missing argument substeps are equalities. Output vertices may be input
vertices or repeated; only the frozen sink and validity hypotheses are used. The arbitrary
constant noncomputable assignment enumeration is handled generically, then instantiated.
Efficiency covers arbitrary malformed histories, private words, tapes, answers/messages
and the strategy parameter word, without confusing private-word length with `n`. The
public decoder/evaluator raw-word contracts and input-layout readers supply those cases.


## Overlap and reuse

Searches preceded probability, list, coin and machine proofs. Detailed searches and nearest
relatives are retained under each agent's evidence. These disclosures include inline proofs.

- The description decoder was compared with DAGCircuit.decode/decode_encode in
  Complexity/CircuitComplexity/DAGCircuitSatLang.lean, the existing validation decoder.
  DescriptionDecoder does not invoke those declarations: its public streaming host recodes
  the encoded grammar through ChunkScanner and the SY-3readers into data for computation.
  CVAL decides a language and does not supply a generic data-returning evaluator, so it
  cannot replace these contracts.
- DescriptionDecoder.dbl_pair reuses public MultiMsg.dbl_append at
  Encryption/PrivateKey/FromPRF/ReductionMachine.lean:235. An unpublished local duplicate was
  removed before checking.
- Garbling.fixedTable_poly re-derives the finite pairing assembly of private
  Complexity.clNative_fields, Complexity/CookLevin/Hardness.lean:4000. That private helper is
  inaccessible and outside the allowed closure. The generic replacement uses public pairing
  and word-list readers. Promotion/deduplication review is requested.
- WordLists directly reuses ColMachines.polyTimeComputable_flatMap_range and the public
  ofFn_eq_map_range in TCSlib/Cryptography/Foundations/BitLists.lean:128. The latter is a
  TCSlib lemma, not a Mathlib declaration. No range/flatten identity is copied.
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


Further disclosed general contracts:

- CoinSeedRelabel.assignmentFold_injective/assignmentEmbedding re-derive the general
  arity<=2 assignment-code bound/injectivity of unmerged sc-garble
  Garbling/CoinBlocks.lean:38 assignmentFold_small (a73072f1), through the already published
  two-bit equation. The finite permutation extension, padded masks and whole seed identity
  consume those facts. No unmerged declaration is imported. This SY-5 debt is explicitly
  requested for proof-only re-pointing/promotion review after both sides land.
- RelabelGarbling reuses argKeys/garbledTable/keyAt/inputKeys readers and xorPerm_apply;
  double-XOR cancellation is inline from Bool equations. Its nearest relative is the
  anonymous inverse proof inside xorPerm at Foundations/BitLists.lean:106–107, not a named
  private lemma. No public probability or list theorem is copied.
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

Additional completed-contract disclosures:

- The lead strengthened CoordinateSwap.acceptProb_swap to require finite whole coordinate
  spaces rather than independently enumerated coordinate index types. It uses the same
  matching/reseeding proof, with no new counting identity. This avoids costly typeclass
  search and accommodates the retained actual tape directly.
- SelectedLaw.acceptProb_fill composes public TapeValues/SeedCoordinates/CoordinateSwap
  readers with acceptProb_comp_equiv. Its new content is the exact actual full-tape
  specialization, retaining shifts and every unused block. It adds no probability inequality.
- FakeSimulatorFactory packages the already proved uniform fake machine with a public
  existential word contract. This avoids dependent matching against Data.make in the
  concrete owner-context A seal; no simulator semantics or efficiency proof is copied.
- BobStatistical is a direct specialization of the published generic output switch, with
  explicit actual strategy-tape transport. GateStepCases/GateHybridChain/GateHybridSecurity
  compose public stage readers, selected-neighbor security and the existing polynomial
  hybrid-chain bound. No new PRF/collision/probability-chain proof is introduced.


### Challenge-reconstruction reuse and nearest relatives

* Slice identities reuse `SecureComputation/SpecialEncryptionMulti.lean:107,125,152`
  (`sliceEnc_append_left/right`, `sliceMultiEncDist_apply`). The new declarations assemble
  selected-layer cases and exact full-view endpoints, not another encryption proof.
* Encoding/traversal reuse `Asymptotic/BlockEncryptor.lean:60` (`encodeList_eq_flatMap`,
  explicitly scope-approved), `Complexity/ClassP/BinaryArith/Words.lean:81,208,221`
  (`length_encWords_le`, `mapW_pairEncode`, `polyTimeComputable_mapW`). No DL-46 copy was added.
  Slot reads use `List.getD_eq_getElem`/`List.getElem_ofFn`; ranks use Mathlib
  `Data/List/Basic.lean:566` and `Data/List/Nodup.lean:120`. Padding consumes
  `Asymptotic/EnsemblesLemmas.lean:198,201`. No DL-47 roundtrip is re-proved.
* Coordinates compose Mathlib's `Equiv.curry`, `piCurry`, `piCongrRight`,
  `boolArrowEquivProd`, `sumArrowEquivProdArrow` and `funUnique`. New material is the
  all-occurrence rank/partial-inverse/fill contract. Bounds consume shared `Lengths` and
  `GateOccurrences`; v7 canonical-row and capacity facts publish reader compositions
  previously inline in `sample_advice_budget`, whose conclusion cannot supply those facts.
* Probability/maximizing/averaging are consumed from `H/SliceReduction.lean:52,80,139`
  and `H/SelectedLaw.lean:66`; base probability transport is
  `Cryptography/Foundations/Experiments.lean:107` (`acceptProb_comp_equiv`). b adds no
  competing probability, reduction-machine or hybrid-sum proof.
* Nearest **unmerged** relatives in sc-garble's delivered `Garbling/CoinBlocks.lean:162`
  (`pushesUniform_key_row_blocks`) and `Garbling/Probability.lean:62,92,102`
  (`pushesUniform_output_argKeys`, `pushesUniform_rowCoin`,
  `pushesUniform_output_argKeys_row`) establish key/row marginals. They do not retain the
  shifts/unused coordinates needed by permutation-dependent all-occurrence replacement.
  These b5/v6/v7 modules neither copy nor re-prove those lemmas: they consume the separately
  audited shared full-coordinate law. No #318 `ObliviousTransfer/*` or sc-compose
  `ComposeSecurity/*` result is re-derived here. The unmerged sources were inspected for
  this final comparison after the proofs were complete; no design/code was taken from them.

Search and inline-shape disclosures are in `evidence/subagents/b5/{reuse-search.log,
reuse-search-resume3.log,RECONSTRUCTION.md}`, `b6/REUSE.md`, and
`b7/{reuse-search.log,REUSE.md}`. Immutable b5/v6/v7 evidence records 12 exact-source normal
checks, 48 full-file A/B strict/coe seals and all 289 stored-constant closures: every sorry
closure is empty, with only `Classical.choice`, `Quot.sound`, `propext`. Source widths are
at most100, files below1000 lines, and scoped style lint is clean. No b source was changed
for this report fragment.


### Additional nearest-relative comparisons

The following additional nearest relatives were compared:

- sc-garble exchange a73072f1, GarblingSecurity/NestedBounds.lean,
  GarblingCoins.length_nestedInner: exact canonical-pad inner length versus c's
  arbitrary-evaluator bound; compared, not imported/copied.
- sc-garble Garbling/CoinBlocks.lean, GarblingProbability.assignmentFold_small:
  CoinSeedRelabel assignment-fold bound/injectivity is an explicit general re-derivation
  via the new public two-bit equation/digit bounds; later proof-only consolidation needed.
- Same CoinBlocks file: pushesUniform_bits_of_blocks, key_row_blocks_injective,
  pushesUniform_key_row_blocks are nearest relatives to CoinRelabel/TapeValues. Those prove
  restricted marginals; c proves a full invertible split retaining shifts/padding. No
  unmerged probability proof/helper import is used.
- sc-garble delivered Garbling.lean, inline hcardNat in uprob_not_good_le_of_perm:
  related card(A)*(card(A)-1)≤12; Lengths proves card(A)≤4 via public finite-cardinality
  and power-monotonicity APIs.
- #318 exchange f62a25b3: ObliviousTransfer/Shape.lean exec_five/transcriptWith_isOT;
  ViewA.lean realA_realCoins; Simulators.lean simAView/simAView_layout. Related five-message
  OT/view/coin calculations; not the two-move/copying contracts. No code copied/imported.
- sc-compose exchange bdfdcb76: ComposeSecurity/Runs.lean realA_compose_eq/realB_compose_eq;
  ComposeSecurity/Sim.lean ComposeSim.simV and assemblers. Related composition identities,
  not reusable two-move/copying contracts. No code copied/imported. Efficiency/Lengths
  were compared for the OT adapters.

Merged public lemmas are used directly: EncodingMachines.divNum/getBit,
BinArith.length_encWords_le, NUPPT.ofPolyTimeUniform, acceptProb_comp_equiv/fst, distAdv_def.
BobStatistical's within-team extraction from root BobOutputSwitchGlue and comparison with
AliceStatistical are disclosed in its CONTRIBUTION.md. Seal/control tooling adapts
sc-garble a73072f1 evidence/tools; reference copies/changes are in c/SEAL-PROVENANCE.md.
The consulted unmerged Lean source is preserved as evidence, not vendored/imported.



### Exact pinned locations of compared and reused interfaces

TCSlib locations are at issue base `6ce4658db08a1dc2a03a149987197660db078011`; Mathlib is pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; core is Lean `v4.25.0`. Existing unmerged exact-pin disclosures are unchanged.

These are source-location/relation clarifications for already cited material. No proof is changed and this is not a new theorem-equivalence audit. Full declaration contexts and source hashes are in `locations.json`.

Three report wording corrections matter: the existing validated decoder is a comparison rather than a consumed proof dependency; `ofFn_eq_map_range` belongs to TCSlib; XOR cancellation directly reuses public Bool lemmas, while `xorPerm` contains an anonymous inline involutivity proof. The finite-product `_apply_val` reader is generated by `@[simps]` and should cite its generating definition.

| Consumer / existing comparison | Exact pinned source locations | Relation |
|---|---|---|
| DescriptionDecoder | `DAGCircuit.decode` — `TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean:107`; `DAGCircuit.decode_encode` — `TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean:160`; `decodeList_encodeList` — `TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean:120` | Comparison only: existing decoder returns a validated DAG object. The new total polynomial-time scanner emits traversal records. Current proof invokes its own scanner and SY3 encoding readers, not DAGCircuit.decode/decode_encode. |
| DescriptionDecoder / generic evaluator | `CVAL` — `TCSlib/Complexity/CircuitComplexity/CircuitEval.lean:71`; `CVAL_mem_P` — `TCSlib/Complexity/CircuitComplexity/CircuitEval.lean:170` | Comparison only: CVAL is a Boolean decision language, not a data-returning generic runWith host. |
| DescriptionDecoder.dbl_pair | `MultiMsg.dbl_append` — `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean:235` | Direct reuse; approved extra import avoids duplicating doubling over append. |
| Garbling.fixedTable_poly | `Complexity.clNative_fields` — `TCSlib/Complexity/CookLevin/Hardness.lean:4000`; `PolyTimeComputable.pairEncode` — `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129`; `PolyTimeComputable.pairMapSnd` — `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:94` | General re-derivation of finite pairing assembly; nearest clNative_fields is private and outside allowed import closure. Public pairing combinators are consumed directly. |
| Garbling.gateOut_small / private keyList_small | `map_range_getD_ofFn` — `TCSlib/Cryptography/SecureComputation/Garbling.lean:193`; `gateOut_eq` — `TCSlib/Cryptography/SecureComputation/Garbling.lean:202`; `argKeys_eq` — `TCSlib/Cryptography/SecureComputation/Garbling.lean:250`; `keyAt_eq` — `TCSlib/Cryptography/SecureComputation/Garbling.lean:240` | Bounded arity specialization through public readers; nearest map-range bridge is private, so cannot be invoked. |
| WordLists | `ColMachines.polyTimeComputable_flatMap_range` — `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:159`; `TCSlib.Cryptography.ofFn_eq_map_range` — `TCSlib/Cryptography/Foundations/BitLists.lean:128` | Direct reuse. ofFn_eq_map_range is a merged TCSlib reader, not a Mathlib lemma. |
| ChunkScanner | `flatMap_range_drop` — `TCSlib/Cryptography/Foundations/BitLists.lean:171`; `polyTimeComputable_emitIter` — `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean:345` | Changing finite control differs from fixed-position flatMap_range_drop. Scanner consumes actual emitting-loop host emitIter, not a new loop machine. |
| RunWithHost | `polyTimeComputable_stateFind` — `TCSlib/Complexity/Randomized/Repetition.lean:241`; `runWith_nil` — `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:153`; `runWith_cons` — `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:157`; `runWith_append` — `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:161`; `runWith_singleton` — `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:166` | Direct reuse of stateFind and public gate-list recursion equations; no CVAL machine copy. |
| DescriptionDecoder / RunWithHost / ChunkScanner same-machine contract | `ModuleHost.clean_install` — `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:319`; `ModuleHost.Clean.envelope` — `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:244` | Direct H14 composition ties result, polynomial first halt and all-time work heads to one machine; no time-to-space argument is re-proved. |
| Decryption | `polyTimeComputable_spDecFun` — `TCSlib/Cryptography/SecureComputation/SpecialEncryption.lean:214` | Generalizes the existing tagged special-decryption computation: outer nested messages have width4n+2 rather than the existing key-width specialization. Uses existing polynomial leaf constructors. |
| Lengths.length_spEncStr_le | `length_spEncStr` — `TCSlib/Cryptography/SecureComputation/SpecialEncryption.lean:258`; `BinArith.length_encWords_le` — `TCSlib/Complexity/ClassP/BinaryArith/Words.lean:81` | Nearest length_spEncStr is an exact equality requiring sufficient evaluator pad. New upper bound works for arbitrary evaluator output lengths. |
| FirstTagged | `EncodingMachines.polyTimeComputable_firstIdx` — `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:324`; `BinArith.polyTimeComputable_mapW` — `TCSlib/Complexity/ClassP/BinaryArith/Words.lean:221` | Direct reuse of public first-index search; canonical word-vector normalization uses mapW. |
| BobIO / BobInit | `BinArith.polyTimeComputable_getW` — `TCSlib/Complexity/ClassP/BinaryArith/Loops.lean:391`; `BinArith.polyTimeComputable_countW` — `TCSlib/Complexity/ClassP/BinaryArith/Words.lean:369`; `BinArith.polyTimeComputable_mapW` — `TCSlib/Complexity/ClassP/BinaryArith/Words.lean:221`; `EncodingMachines.polyTimeComputable_of_getD` — `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:399` | Direct composition of word-vector selection/count/map APIs, not another list traversal. |
| CoinRead / raw window selectors | `polyTimeComputable_pairDropPoly` — `TCSlib/Complexity/Randomized/Primitives.lean:207`; `polyTimeComputable_pairTakePoly` — `TCSlib/Complexity/Randomized/Primitives.lean:194`; `EnsembleLemmas.polyTimeComputable_padL` — `TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:223`; `padFin_apply` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:178` | Direct public variable-window and padding reuse. No headD/drop or getD/ofFn copy. |
| OTInputs / parameter selectors | `polyTimeComputable_unaryPoly` — `TCSlib/Complexity/Randomized/Primitives.lean:155`; `EncodingMachines.unaryLength_poly` — `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:117`; `EncodingMachines.getBit_poly` — `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:174`; `EncodingMachines.divNum_poly` — `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:653` | Direct unary-polynomial, bit-read and quotient-selector composition. |
| Strategies | `GI.efficient_of_polyTime` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:594`; `GI.argX_ilayout` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean:302`; `GI.argZ_ilayout` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean:307`; `GI.argM_ilayout` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean:312` | Two-message specialization of the public interactive-layout efficiency wrapper; same layout readers handle arbitrary histories. |
| Strategies / history encodings | `Strategy.pairFstD_encodeMsgs` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:143`; `GI.pairSndD_encodeMsgs` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:93`; `GI.iterate_pairSndD_encodeMsgs` — `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:101` | Direct first/tail/history iteration readers, not an encoding injectivity copy. |
| TwoMoveViews / ProtocolEfficiency | `Protocol.transcriptWith_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:421`; `Protocol.transcript_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:509`; `Protocol.viewP_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:491`; `Protocol.viewV_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:470`; `Protocol.outP_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:458`; `Protocol.outV_eq` — `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:449` | Direct transcript/view/output APIs specialized to Alice-first two rounds; unmerged protocol-shape relatives remain separately disclosed. |
| StatisticalSwitch | `MultiMsg.abs_uexp_sub_le_uprob` — `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean:61`; `statClose_iff` — `TCSlib/Cryptography/Asymptotic/Sampling.lean:133`; `distAdv_le_of_statClose` — `TCSlib/Cryptography/Asymptotic/Sampling.lean:249`; `uprob_eq_uexp` — `TCSlib/Cryptography/Foundations/Probability.lean:80` | Direct published expectation inequality and StatClose/distinguisher readers; no new expectation bound. |
| CoordinateSwap / SelectedLaw / SamplerEndpoints | `acceptProb_comp_equiv` — `TCSlib/Cryptography/Foundations/Experiments.lean:107`; `acceptProb_fst` — `TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:73`; `uprob_comp_equiv` — `TCSlib/Cryptography/Foundations/Probability.lean:165`; `uprob_fst` — `TCSlib/Cryptography/Foundations/Probability.lean:175` | Direct uniform reindexing and ignored-coordinate laws. New content is the matching/actual-tape specialization, not counting. |
| SliceReduction averaging and hybrid chain | `uprob_prod` — `TCSlib/Cryptography/Foundations/Probability.lean:153`; `abs_uexp_sub_le` — `TCSlib/Cryptography/Asymptotic/Sampling.lean:210`; `abs_sub_le_sum_hybrids` — `TCSlib/Cryptography/Foundations/Probability.lean:218`; `EnsembleLemmas.negligible_polyExpr_mul` — `TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:377` | Direct product expectation, public averaging inequality, public hybrid telescoping and polynomial-times-negligible closure. |
| SliceReduction / simulator coin transport | `NUPPT.exists_compParam` — `TCSlib/Complexity/Randomized/Closure.lean:241`; `NUPPT.exists_withAdvice` — `TCSlib/Complexity/Randomized/Closure.lean:358`; `EnsembleLemmas.acceptProb_coins_equiv` — `TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:85`; `NUPPT.coinsCongr_ofFn` — `TCSlib/Complexity/Randomized/PPT.lean:252`; `NUPPT.coinsEquivPoly_symm_ofFn` — `TCSlib/Complexity/Randomized/PPT.lean:278` | Direct advice/composition machines and public coin-word transport readers; no reduction machine or coin congruence re-proof. |
| AliceSimulator / FakeSimulator | `NUPPT.ofPolyTimeUniform` — `TCSlib/Complexity/Randomized/PPT.lean:398` | Direct uniform polynomial-time constructor; simulation coupling composes the shared StatisticalSwitch rather than adding a new probability law. |
| CoinRelabel / TapeValues | `blocksEquivX` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:242`; `FunFamily.blocks` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:258`; `FunFamily.blocks_apply` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:262`; `Fin.appendEquiv` — `Mathlib/Logic/Equiv/Fin/Basic.lean:406` (Mathlib) | Direct typed block equivalences and their addressed readers; the new contribution keeps shifts and unused blocks. |
| SeedCoordinates / NonceCoordinates | `Equiv.curry` — `Mathlib/Logic/Equiv/Prod.lean:115` (Mathlib); `Equiv.piCurry` — `Mathlib/Logic/Equiv/Basic.lean:169` (Mathlib); `Equiv.piCongrRight` — `Mathlib/Logic/Equiv/Basic.lean:147` (Mathlib); `Equiv.boolArrowEquivProd` — `Mathlib/Logic/Equiv/Prod.lean:429` (Mathlib); `Equiv.sumArrowEquivProdArrow` — `Mathlib/Logic/Equiv/Prod.lean:362` (Mathlib); `Equiv.funUnique` — `Mathlib/Logic/Equiv/Defs.lean:563` (Mathlib) | Direct Mathlib function-space equivalences; no new general currying/coordinate equivalence is re-proved. |
| List windows / typed coin words | `List.getD_eq_getElem` — `Mathlib/Data/List/GetD.lean:30` (Mathlib); `List.getElem_ofFn` — `Init/Data/List/OfFn.lean:47` (Lean); `headD_drop_ofFn` — `TCSlib/Cryptography/Foundations/BitLists.lean:61`; `flatten_ofFn_one` — `TCSlib/Cryptography/Foundations/BitLists.lean:71`; `padFin_ofFn` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:211`; `ofFn_arrowCongr_finCongr` — `TCSlib/Cryptography/Asymptotic/Adversary.lean:232` | Direct merged/core list APIs; these source locations distinguish the reused DL46/DL47 readers from new semantic reconstruction. |
| CallEquations | `finProdFinEquiv_apply_val (generated)` — `Mathlib/Logic/Equiv/Fin/Basic.lean:325` (Mathlib); `Nat.add_mul_div_left` — `Init/Data/Nat/Div/Basic.lean:321` (Lean); `Nat.div_eq_of_lt` — `Init/Data/Nat/Div/Basic.lean:412` (Lean) | Direct generated finite-product address reader and Nat division lemmas. apply_val has no standalone textual declaration: it is generated by simps on the listed definition. |
| RelabelGarbling.keyAt_original / XOR cancellation | `xorPerm` — `TCSlib/Cryptography/Foundations/BitLists.lean:105`; `xorPerm_apply` — `TCSlib/Cryptography/Foundations/BitLists.lean:110`; `Bool.xor_assoc` — `Init/Data/Bool.lean:361` (Lean); `Bool.xor_self` — `Init/Data/Bool.lean:353` (Lean); `Bool.xor_false` — `Init/Data/Bool.lean:337` (Lean) | Actual proof directly rewrites public Bool cancellation lemmas. Nearest permutation packages an anonymous inline involutivity proof; it is not a separately named private theorem. |
| encodeMsgs_eq_encWords | `Yao local henc` — `TCSlib/Cryptography/SecureComputation/Yao.lean:352` | Generalizes the local encoding bridge henc in the frozen Yao file; helper uses published nil/cons equations, not the private injectivity proof. |

## Hosts, promotion and reader requests (SY-4)

Request promotion and registry review at landing. No frozen registry file is edited here.

| ID | Host | Status / provenance | Consumers |
|---|---|---|---|
| H-SY-decoder (draft) | Circuit-description recoder: DescriptionDecoder.decodeDescription_host. One H14 clean machine maps a paired circuit/output description to the unary input count, encoded gate records and unchanged output word; canonical correctness for every DAGCircuit, polynomial first-halt time and all-time work-head envelope for that same machine. | Proved in sc-yao, public generic SY-4 contract; promotion to the circuit-complexity construction layer requested. Built from emitting-loop, finite branching, pairing and clean_install/Clean.envelope. | GarblingProgram.gatesWord_poly and BobProgram.output_poly consume readCircuit_poly; FakeProgram uses the same description recoder. decodeDescription_host packages that computation with the output word. |
| H-SY-eval (draft) | RunWithHost.exists_machine: encoded topological evaluation generic in gate records, input-dependent value types, leaf step, initial values and polynomial round/state envelopes. One clean machine with polynomial time and all-time work-head envelope. garbledRunWith_poly derives envelopes for fixed-width key encodings. | Proved in sc-yao; promotion and registry gate requested. Built from stateFind and H14. | GarbledRun.garbledRunWith_poly via BobProgram.output_poly and yaoHybrid_polyTime. The fake-view simulator and B1 slot-substitution reduction do not execute this evaluator. |

The supporting ChunkScanner is also public with a same-machine clean/time/head contract.
No private host is introduced. The read-only source/signature inventory identifies every
new public definition and its published reader.



## Scope requests and execution authorization

SY-1–SY-6 apply in full. The user also explicitly authorized full proof edits, scoped
commits, delivery pushes and required shared-wrapper checks despite the supplied AGENTS
build prohibition: **“Yes, follow the full objective and wrapper rules”.** That approval
and all four import approvals persisted across relocations; no further permission or scope
was inferred. The imports add only the approved narrowed dependency closure. The following
questions and answers are reproduced verbatim from the delivered evidence records.


### Ordered emission

Record: `evidence/scope-request/ordered-emission.md`. The recorded question and answer follow verbatim.

Question sent via request_user_input_async:
Scope request: may the new garbling helper import
`TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines` to reuse its proved
`ColMachines.polyTimeComputable_flatMap_range`? This module is outside the issued order;
reuse avoids re-proving an existing public loop lemma. I would extend the narrowed bootstrap
and roots for this import.

User answer (verbatim): "Approve the extra helper import". Approved 2026-11-15.


### Doubling over concatenation

Record: `evidence/scope-request/dbl-append.md`. The recorded question and answer follow verbatim.

Question sent via request_user_input_async:
A second reuse scope request: may `Yao/HybridProof/DescriptionDecoder.lean` add
`import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine`? Its proved
`MultiMsg.dbl_append` is the exact encoding lemma the decoder needs, but the module is
outside the issued order. This adds no frozen-file edit.

User answer (verbatim): "Approve this helper import". Approved 2026-11-15.


### Expectation switch

Record: `evidence/scope-request/statistical-switch.md`. The recorded question and answer follow verbatim.

Question sent via request_user_input_async:
Scope request: may `Yao/HybridProof/StatisticalSwitch.lean` import
`TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas` to reuse
`MultiMsg.abs_uexp_sub_le_uprob`? The brief lists this public interface, but its module is
missing from the supplied order. I’ll extend the narrowed dependency checks for it.

User answer (verbatim): "Approve this probability-helper import". Approved 2026-11-15.


### Challenge-list encoding

Record: `evidence/scope-request/block-encoding.md`. The recorded question and answer follow verbatim.

Question sent via request_user_input_async:
May `Yao/HybridProof/SelectedSlices.lean` import
`TCSlib.Cryptography.Asymptotic.BlockEncryptor`? Its public
`encodeList_eq_flatMap` supplies the challenge-list encoding identity needed by the B1
sampler. The module is outside the issued order; approval lets us reuse it instead of
duplicating its proof.

User answer (verbatim): "Yes". Approved 2026-11-15.



The ordered-emission result is consumed through the generic WordLists/garbling construction;
the other approved providers supply the decoder list identity, statistical switch and B1
challenge-list encoding. The approved BlockEncryptor import adds no new Mathlib root.
All scope records and exact dependency/root extensions are retained under evidence.

### Shared-wrapper execution authorization

Question (verbatim):
May I execute the full fill in goal-objective.md—including proof edits, scoped commits and delivery pushes—and use its lean-slot.sh commands for required checks despite the supplied AGENTS.md prohibition?

User answer (verbatim): "Yes, follow the full objective and wrapper rules".

This records the existing authorization; it is not a new scope request. The four helper-import
approvals are recorded separately. The shared wrapper, host cap and narrowed-check rules remain binding.


## Dependency trace and axioms

`evidence/probes/AllAxioms.lean` enumerates constants by defining module and prints the
full elaborated type, axiom set and transitive admitted-root closure of every stored
constant in the changed/new modules, including private/generated constants. The completed
final audit prints1490 constants,1110from helpers. Every helper has an empty sorry closure
and only `propext`, `Classical.choice`, `Quot.sound`; no complexity-layer admission is used.
The efficiency theorem has the same standard axioms and empty closure. The security theorem
and both consumers have the standard axioms plus `sorryAx` only through the roots below.
The exact-source refresh passes in `evidence/final-publication-security-audit-summary.json`;
its complete elaborated types are also exported in `evidence/interfaces/full-stored-signatures.md`.

| Declaration | Issue-base admitted roots | Final completed trace roots |
|---|---|---|
| `yaoHybrid_polyTime` | itself | none |
| `yaoHybrid_simulators` | itself | `yaoSeed_good_whp`, `sliceMultiMessageSecure_of_prfOut` |
| `yaoHybrid_hbcSecure` | both target admissions | exactly the same two sc-garble roots |
| `yaoProtocol_hbcSecure` | both Yao targets; `otProtocol_polyTime`, `otProtocol_simulators`; `HybridProtocol.hbcSecure_compose` | both sc-garble roots; the two OT roots; the composition root |

At the issue base all four printed axiom sets contain the standard three plus `sorryAx`.
The base consumer evidence is `evidence/logs/base-axioms/`; the completed final all-stored
log and parsed summary are `final-all-stored-1` and `final-security-audit-summary.json`.
The final real-protocol roots are attributed to sc-garble, sc-ot and sc-compose respectively;
this fill does not claim those other units' admissions removed.

## Rule10 seals, controls and exact failures

Every full-file seal is run with `-DmaxErrors=0` and counts both `error:` and `error(...)`,
plus process exit and a fresh nonempty output artifact. The seal scans every TCSlib-origin
imported definition and generated matcher, including root-namespace models, not just the
direct imports. Authorized reducible abbreviations are excluded. A treats PolyExpr.eval as
Q1notation; B deliberately seals it. Both strict and projection-coercion-notation variants
are run; coe is canonical. No failure is hidden by a diagnostic cutoff.

The exact issue-base frozen seal sources, immutable rows, raw logs and restoration hashes
are retained under `checkpoint1-frozen-readers/immutable-rows`. Final frozen coverage is
12/12 with exact current-source reconstruction, including the3Uniform variants resumed
under a new phase after the pause. The interrupted version is preserved.

| File | Base A strict/coe | Base B strict/coe | Final A strict/coe | Final B strict/coe |
|---|---:|---:|---:|---:|
| DAGCircuit | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Uniform | 4 / 4 | 4 / 4 | 4 / 4 | 4 / 4 |
| Yao | 0 / 0 | 15 / 15 | 0 / 0 | 24 / 24 |

Uniform's four inherited diagnostics, in every variant, are exactly two in
`DAGCircuit.length_encode_le_of_isFaninTwo` and two in `IsPUniform.isPolySize`. They are
unchanged old-proof reduction issues, not failures in the new readers. Raw base/final
source reconstructions and diagnostic inventories are delivered.

Yao's B failing-declaration multiplicities in **each** strict/coe variant are:

| Declaration | Diagnostics |
|---|---:|
| `yaoCoins_eval` | 1 |
| `yaoHybrid` | 3 |
| `yaoHybrid_callA` | 1 |
| `yaoHybrid_callB` | 1 |
| `yaoHybrid_answersB_getD` | 4 |
| `yaoSeed_good_whp` | 1 |
| `yaoHybrid_polyTime` | 2 |
| `yaoHybrid_simulators` | 9 |
| `yaoHybrid_hbcSecure` | 2 |

Both canonical A variants pass. B24 is15base+2efficiency+7 new simulator-body diagnostics;
the prototype's B9 includes two baseline header diagnostics and is not added again.
The following individual attribution preserves every failing location and its comparator.


### Individual final Yao B diagnostics

Each row below occurs independently in **strict** and **coe**, at the same line/column with byte-identical normalized error text. Both canonical A variants pass. B deliberately seals the Q1-exempt `PolyExpr.eval`; these B failures are reported as failures, not passes.

| # | Original line | Sealed line | Declaration | Origin | Individual attribution |
|---|---:|---:|---|---|---|
| 1 | 283 | 325 | `yaoCoins_eval` | base | The unchanged yaoCoins_eval rfl requires the polynomial coin expression to evaluate to 10*S(n)*n+2*S(n). B seals PolyExpr.eval and blocks that owner-local arithmetic reduction. |
| 2 | 591 | 633 | `yaoHybrid` | base | The first yaoHybrid callA argument j has Fin ((Y.inB.mul var).eval n), whereas yaoCall expects Fin (Y.inB.eval n*n). Sealed polynomial evaluation blocks the definitional identification. |
| 3 | 592 | 634 | `yaoHybrid` | base | The second yaoHybrid callA use of yaoCall has the same explicit mul-evaluation index mismatch; it is a separate diagnostic in the unchanged definition. |
| 4 | 593 | 635 | `yaoHybrid` | base | The yaoHybrid callB use of yaoCall has the same explicit mul-evaluation index mismatch in the unchanged definition. |
| 5 | 599 | 641 | `yaoHybrid_callA` | base | The unchanged yaoHybrid_callA reader passes product-index j into the protocol call domain ((yaoHybrid...).calls.eval n), which no longer reduces under the B eval seal. |
| 6 | 607 | 649 | `yaoHybrid_callB` | base | The unchanged yaoHybrid_callB reader has the corresponding product-index/protocol-call-domain mismatch. |
| 7 | 718 | 760 | `yaoHybrid_answersB_getD` | base | The unchanged answersB getD proof calls callA with product-index j; the protocol call-count evaluation is opaque in B. |
| 8 | 719 | 761 | `yaoHybrid_answersB_getD` | base | The same unchanged answer-reader expression calls callB with product-index j; this is its separate call-domain mismatch. |
| 9 | 725 | 767 | `yaoHybrid_answersB_getD` | base | The later ofFn expression in the unchanged answer-reader proof again calls callA with product-index j, with the opaque polynomial call domain. |
| 10 | 726 | 768 | `yaoHybrid_answersB_getD` | base | The later ofFn expression separately calls callB with product-index j; the same eval multiplication reduction is blocked. |
| 11 | 817 | 859 | `yaoSeed_good_whp` | base | The frozen yaoSeed_good_whp signature supplies G1 with Fin(n+n) output, while PRFOut (.add var var) asks for Fin ((var.add var).eval n). This existing signature depends on exempt polynomial notation. |
| 12 | 917 | 959 | `yaoHybrid_polyTime` | efficiency | CallEquations.inputA_eq ranges over Fin (Y.inB.eval n*n), while the goal ranges over Fin ((yaoHybrid...).calls.eval n). Its ordinary/canonical-A application uses the authorized polynomial-evaluation notation; this exact failure already appears in the efficiency audit. |
| 13 | 929 | 971 | `yaoHybrid_polyTime` | efficiency | CallEquations.inputB_eq has the same product-domain versus opaque calls.eval mismatch. This exact failure is the second efficiency-only diagnostic. |
| 14 | 995 | 1037 | `yaoHybrid_simulators` | base | The frozen simulator G1 hypothesis has the same Fin(n+n) versus Fin ((var.add var).eval n) mismatch as the baseline; it is also prototype diagnostic1. |
| 15 | 997 | 1039 | `yaoHybrid_simulators` | base | The frozen simulator concatenation Fin.append has output length n+n+(var.add innerLen).eval n, whereas joint PRFOut expects the opaque outer add evaluation; this is baseline and prototype diagnostic2. |
| 16 | 1016 | 1058 | `yaoHybrid_simulators` | new simulator body | FakeSimulatorFactory is instantiated at inputs=.add Y.inA Y.inB. The actual circuit has DAGCircuit (Y.inA.eval n+Y.inB.eval n), while the sealed factory expects DAGCircuit ((Y.inA.add Y.inB).eval n). This is the first direct new body mismatch, corresponding to prototype diagnostic3. |
| 17 | 1020 | 1062 | `yaoHybrid_simulators` | new simulator body | The supplied Nat.le_refl proves A(n)+B(n)<=A(n)+B(n), while the factory expects A(n)+B(n)<=(Y.inA.add Y.inB).eval n. This is a second direct eval-add mismatch, prototype diagnostic4. |
| 18 | 1021 | 1063 | `yaoHybrid_simulators` | new simulator body | After diagnostic16 rejected the actual circuit family, the key obligation explicitly contains (sorry n).size and (sorry n q) rather than Y.circ/yaoSeed. The actual seed-key reader cannot close that poisoned dependent obligation. This is the matching prototype diagnostic5 cascade, not an independent unproved seed law. |
| 19 | 1022 | 1064 | `yaoHybrid_simulators` | new simulator body | The nonce0 simp step is a premise of the same factory whose circuit family was rejected in diagnostic16. The supplied actual nonce reader no longer matches that dependent family. The exact same source line/message is prototype diagnostic6; canonical A checks this premise successfully. |
| 20 | 1023 | 1065 | `yaoHybrid_simulators` | new simulator body | The nonce1 premise is the separate corresponding dependent-family simp failure after diagnostic16, matching prototype diagnostic7; canonical A checks the unchanged source successfully. |
| 21 | 1025 | 1067 | `yaoHybrid_simulators` | new simulator body | The factory permutation premise uses the actual seed/permutation readers, but the factory family is poisoned by diagnostic16. This separate simp-no-progress cascade matches prototype diagnostic8 and disappears in canonical A. |
| 22 | 1068 | 1110 | `yaoHybrid_simulators` | new simulator body | The GateHybridSecurity call supplies Fin.append G1 G2 at the exact joint polynomial L. B prevents reducing L.eval n to the explicit concatenation output length, so this body application fails just like prototype diagnostic9. |
| 23 | 1142 | 1184 | `yaoHybrid_hbcSecure` | base | The unchanged yaoHybrid_hbcSecure G1 hypothesis again requires n+n to identify with the opaque polynomial add evaluation. It is the penultimate baseline diagnostic. |
| 24 | 1144 | 1186 | `yaoHybrid_hbcSecure` | base | The unchanged yaoHybrid_hbcSecure joint-family header has the same explicit concatenation length versus opaque nested-add evaluation mismatch as the last baseline diagnostic. |

Per variant: **24 = 15 baseline + 2 efficiency + 7 new simulator body**. The seven new body errors are three direct polynomial-index mismatches and four dependent factory-premise cascades. Prototype B9 includes the simulator header's two baseline errors, so those two must not be added a second time.

The four cascade classifications are causal inferences from the rejected factory circuit family, the poisoned `(sorry n)` key goal, the shared dependent factory premises, exact prototype matches, and the one-flag A/B instrumentation difference. They are distinguished from the three direct new index mismatches.

Failing-declaration multiplicities: `yaoCoins_eval` 1, `yaoHybrid` 3, `yaoHybrid_callA` 1, `yaoHybrid_callB` 1, `yaoHybrid_answersB_getD` 4, `yaoSeed_good_whp` 1, `yaoHybrid_polyTime` 2, `yaoHybrid_simulators` 9, `yaoHybrid_hbcSecure` 2.

Every baseline/efficiency/prototype comparator was checked individually for identical normalized diagnostic text; prototype rows also have identical source lines. `ATTRIBUTION.json` contains all48 full final excerpts, full comparator excerpts and exact input hashes. No strict-only/coercion-only difference remains.

The complete comparator excerpts, source hashes and both final raw logs remain in
`evidence/subagents/final-seal-attribution/`. The lead's final frozen-file summary checks
all12 source reconstructions; this per-error review supplements that broader check.


### Helper seal matrix and controls

The lead's primary helper run covers272 variants (68 files×4) in three independent output-only
trees, with a single own read-only TCSlib bootstrap import path and the existing package
paths. It copies no dependency tree and joins no foreign TCSlib artifact path. Parent and
each runner hold shared import locks; ordinary module writers hold the exclusive lock.
This keeps surviving readers protected if the controller is interrupted. Initial probe
hashes are recorded before spawning and every result is compared after exact count/set/
uniqueness checks. Before/after imported-artifact hashes must agree. Each Lean process
still acquires the unchanged global slot wrapper; the independent output trees do not
raise the host cap. The preparation and strengthened guards were independently reviewed.

The current-source matrix is272/272PASS:268 unchanged-file rows plus the four exact-current
Garbling reruns. All68 files have A/B×strict/coe coverage, zero errors in both forms and
fresh outputs, and reconstruct their current unsealed source byte-for-byte. All276raw runs
remain delivered, including the four superseded rows. The primary parallel batch verified
that all261imported artifacts stayed unchanged and every initial probe hash matched.
An observed exclusive-writer lock attempt was rejected while the shared readers were live.
Current normal checks and the full stored-constant trace pass after the documentation edit.

All24SY-3necessity controls are independently reverified:8 unsealed direct passes,
8 sealed negatives each exactly1error,8 sealed reader passes. Their probe/snapshot/log hashes
and both diagnostic-form recounts match the recorded results. These are paired witnesses
that the published readers, rather than foreign definitional reduction, close the goals.

## Headers, names, explicit definitions and publication

The frozen checker reports zero unexpected header/definition/order/region changes. Yao's
76base declarations include72 public and4 private. Exact whole-file restoration after masking
the permitted spans, exact circuit-reader removal and the simple two target headers protect
the frozen byte boundaries independently of display-only header excerpts. The two controls
report exactly one one-character header difference and exactly one extra frozen-region-line
violation. The exact script copies are delivered under `evidence/headers/` and
`evidence/clash/`, with canonical copies under tools; the explicit-definition scan is also
copied under `evidence/unfold/`.

Auxiliary source-header excerpts are display aids: their lexer can stop early at Boolean
`||` or a `let` occurring inside a type. They are not treated as complete formal types.
The full stored elaborated signatures in AllAxioms, including implicit section parameters,
private and generated constants, are authoritative for the published interface. The frozen
byte-restoration checks above do not rely on those potentially shortened display excerpts.

The namespace-resolved name scan checks public/private names against the issue-base TCSlib
tree and sc-garble a73072f1, #318 f62a25b3 and sc-compose bdfdcb76. It reports764 new explicit
names and0unexpected clashes. The sole intentional coincidence is the byte-identical SY-3
fan-in reader. Downstream ordinary checks also validate generated names.

The explicit-definition scan includes both target bodies and all helpers, core and pinned
Mathlib:8970 files,2023tactic references,17review candidates. Fifteen are local proof binders;
two are same-file published `SelectedRows.length_eq` theorem references, not foreign
definitions. The final context/hash resolution reports0foreign-definition violations.
Whole-file seals additionally cover implicit TCSlib reductions. All earlier scan versions
and their corrections remain in evidence.

The publication inventory examines732 public helper declarations. The nestedDecTagged_eq
reader is a false positive: the lexer encountered a `let` in its type, while its entire
proof is `rfl`. Garbling.gateOut_small has14tactic lines (15including the `:= by` line);
the initial17-line lexical window also included the type continuation after Boolean `||`.
Its short English proof sketch was added in the eighth source commit. Headers/bodies
and the entire noncomment token stream are identical before/after. All3simps configurations
use `isSimp=false`; no new simp attribute is introduced. Remaining documentation gaps are0
in the reviewed inventory; the exact-source post-documentation checks pass as recorded above.
Public readers, formula docstrings, source tags/references and nontrivial English sketches
are preserved. No blueprint/reference source is edited outside the issued scope.

## Style and resource/environment record

Exact lint **line-set** comparison gives Cryptography92 FAIL/102 WARN versus base92/101.
There is no new FAIL. The sole new WARN is Yao's approved1152-line size. Its old target-size
INFO disappears when it becomes a facade. Circuit lint remains0 FAIL/79 WARN; missing-reader
warning texts improve11→10 and2→1. No new undisclosed warning is accepted. Width, per-file
size, complete facade imports, generic visibility and absence of helper admissions are
checked; current-source export hashes are in `evidence/interfaces/source-inventory.json`.

The host has12CPUs and18GiB RAM. macOS preflights use the prescribed free+inactive+
speculative+purgeable page formula. The memory/disk floors are4GiB/12GiB. The resumed
preflight has7.199GiB headroom, pre-helper-batch6.679GiB, and the live measurement5.222GiB;
all exceed the floor. Disk free is about144GiB. Raw sysctl/vm_stat/memory-pressure/df/mount
records, per-command /usr/bin/time -l records and slot histories are delivered. No clone,
package, scratch or artifact tree is on a RAM disk.

Every Lean/Lake/tree command uses `/private/tmp/sc-yao-lean-slot.sh`, with at most THREE
Lean processes host-wide shared with other jobs, tags sc-yao and sc-yao-a/b/c as appropriate.
No LEAN_SLOT_DIR/LEAN_SLOTS override is installed. The wrapper SHA256 remains
`ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a`.
Python is always python3-I; no lake build or unfiltered cache request is used. Cache get
acquires all3 slots and is lead-only. Each child has its own worktree/TCSlib artifact tree
and read-only symlink to the lead's packages. Source work and delivery use distinct indices.

Lean is4.25.0; Mathlib is pinned to
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Package URL/revision checks report
**11present /4absent,0mismatches**; absent documentation packages are not imported by the
narrowed order. Initial narrowed roots are76; approved ordered emission adds1, probability
reuse adds1, and BlockEncryptor adds0. Cache requests report “No files to download” and
decompress2082,941,566archives respectively, with overlapping sets rather than an additive
unique download count. Zero-length package-olean and root-import cache probes are retained.

The host cache archive store pre-existed: 32,667 files. Final inspection records 1,595,387,830
logical bytes and 1,623,212 KiB allocated, matching the initial count/du record. Its precise
earlier origin is unknown. These archives were available on the host before this job and
are not reported as downloaded by this session. No package-tree copying or manual repair of package archives/oleans was used.

## Historical repairs and evidence completeness

Every final check retains its exact source snapshot, raw log and result. Historical
unsuccessful/interrupted probes and repaired variants are also retained. Some earliest
agent-a failed-source versions were explicitly reconstructed rather than preserved as
original snapshots; those labelled reconstructions are not final proof evidence. In particular:

* CP3's BobViewShape had an unnecessary forbidden in-flight ObliviousTransfer import.
  CP4 removed only that import; all required readers were already supplied by
  TwoMoveViews→Hybrid→Defs. Its statement/proof are unchanged, and the narrower normal/
  four-seal checks pass. Current helpers have no forbidden in-flight import.
* The first CP4 delivery package contained a 157 MB SelectedLaw raw diagnostic sample.
  The owned delivery controller was stopped after read-only pull/rebase and before any
  push; its unpublished commit is kept on a local backup ref. A lossless raw-samples-03.zip
  with verified decompression hash replaced the raw delivered file, and the corrected
  package was pushed normally. No push refusal or force-push occurred; exporters now
  reject oversized individual files before delivery.
* The actual complete prototype had canonical owner-context A passes and diagnostic B9,
  not four passing variants. A real implicit foreign-distAdv reduction was fixed through
  the public `distAdv_def` reader. The installed source has its own normal/A/B evidence.
* Early c probes covered40 explicit source-root closures, not an exhaustive all-stored
  enumeration. Later c probes enumerated278 constants, and the lead's1490 constant audit
  closes the early coverage gap. The earlier loose “all stored” wording is not repeated.
* The long SelectedLaw candidate finished with five missing-finite-instance diagnostics
  after about 320 seconds and4.7 GB maximum RSS; measured headroom stayed above 4 GiB. It was
  already terminal when the guarded stop was considered, so no signal was sent to it.
  Later source-directed SIGINTs stopped only owned diagnostic groups, not other jobs.
* An early resumed batch could not access shared-slot files and never acquired a slot or
  started Lean; its waiting group was stopped and the required-access rerun passed.
  A later automatic approval timeout created no process, and the permitted retry passed.
  These are not Lean resource failures. No Lean 137/139/low-headroom E-RES occurred.
* The shortened c skeleton was 100 body lines and maximum width 100, correcting earlier prose
  saying 93. It is superseded historical evidence; the complete a12 construction/actual
  installed proof is separately recorded. Evidence-only sorry ladders are not exported as
  library source. The final doc inventory's false-positive reader and English-sketch repair
  are also preserved explicitly.

Large raw stack samples are preserved losslessly in numbered raw ZIP parts with entry
inventories and verified entry hashes, including raw03; none is omitted merely for size.
The relocation ZIP separately preserves all four source/evidence trees. The final payload
includes every retained probe/tool/manifest/request/control/search/seal/trace/log and
sub-agent handoff required by evidence/SHA256SUMS. The top-level and evidence SHA256 manifest verification includes exact
path-set equality, no leading ./ and every byte hash, at both top level and evidence level.
The refreshed sc-yao-tagged slot log and all new reviewer artifacts are included.

## Delivery and reproducibility

The prepared payload contains all eight unsigned format-patches from the fixed issue base.
COMMITS.tsv records every hash, author/committer identity and date, and signing=none.
All eight hashes reproduced exactly with git am in a fresh own shared scratch clone using
those recorded values; see evidence/patch-reproduction.log. The final71 source hashes and
width/line inventories are exported beside the full 1490 elaborated stored signatures.

Before publication, the exporter verifies top-level and evidence SHA256 manifests against
the exact actual file sets, with no leading ./, omission or extra file. Delivery uses only
inbox/fills/sc-yao in the dedicated worktree, commit.gpgsign=false, a pull with rebase
immediately before the non-force push, and a staged/committed path-scope check. A refused
push is kept and reported rather than forced or silently retried. The push result and
delivery commit are recorded in the chat receipt, outside this self-hashed payload.

The returned ZIP contains this identical payload under exactly sc-yao/. Its archive paths
and every file hash are compared against the staged payload before delivery; the ZIP digest
is recorded in the external receipt. The source branch remains local. The maintainer reviews
and rebases the material for a PR after sc-garble lands; Seyoon approves that PR.

Previously pushed checkpoint commits remain in exchange history:

| Checkpoint | Delivery commit |
|---|---|
| 1 | `f0a9a6163c5c91599147eb550fd5bb929cc68aa0` |
| 2 | `816971fc6922646f056a47efd41b1407f762320d` |
| 3 | `acc868271367d525350da2c1043e7f470f1c0a98` |
| 4 | `171a341ab208261d7a29865a32260c1640617158` |
