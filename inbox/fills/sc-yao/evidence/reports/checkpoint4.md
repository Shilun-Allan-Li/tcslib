# sc-yao · checkpoint 4

Issue base: `6ce4658db08a1dc2a03a149987197660db078011`.
Issued exchange pin: `f41e1b4ddaff2a140c893d510bdd8d227f83fed8`.
Local proof tip: `f2ec52e69731a81808bfad1fff0f31889a724f42`. The branch `fill/sc-yao` remains local.
Only `inbox/fills/sc-yao/` is delivered, from the dedicated delivery worktree.

## Status and scope

`yaoHybrid_polyTime` is proved with its frozen signature, standard axioms only and no
admitted dependency. `yaoHybrid_simulators` still retains its base body and sketch in
the exported Yao file. The full objective continues; this is checkpoint4, not a partial final.

All generic security contracts are now complete, including both exact sampler endpoints,
the full-tape selected-coordinate law, polynomial-time all-occurrence reconstruction,
uniform B1 reduction and the polynomial gate chain. The separate complete concrete
simulator prototype also passes normal and owner-context A seals. Its body has not yet
been installed in the frozen target; that installation and the final full-source audits
remain. Every exported helper is a whole declaration without an admission.

This checkpoint has67 helper children, their single HybridProof facade and the three
approved frozen files:71 changed/new source files. Yao has1062 lines,1090 after sc-garble's
28-line growth, below the SY-2 cap1200. All other files have<1000 lines; width≤100.
Only the two authorized bodies/sketches, main-results bullet and hub import may change
in Yao. The source/header checker reports zero unexpected differences and both one-error
controls pass; its Yao count is72 public plus4 private declarations.

No unmerged proof declaration is consumed. One scope correction is included: CP3's
BobViewShape unnecessarily imported in-flight ObliviousTransfer. This import is removed;
all required functionality/readers already come from TwoMoveViews→Hybrid→Defs. Its proof
and statement are unchanged. Four ordinary merged checks and all four exact-source
BobViewShape seals pass after removal. The earlier source is retained and the correction
is recorded in evidence/logs/checkpoint4-import-correction.json.

## Contributions

| Agent | Cumulative contributions |
|---|---|
| Lead /root | CoinRead, BobIO, BobInit, ProtocolEfficiency, CallEquations, Strategies, SliceReduction, SimulationBound, OTAnswerWords, AliceStatistical, SelectedLaw; generalized CoordinateSwap's finiteness interface; corrected BobViewShape's import; frozen readers and efficiency body; integration, checks, commits and delivery. |
| /root/decoder, sc-yao-a | ChunkScanner, DescriptionDecoder, CoinGarbling, Garbling, WordLists, RowFromCoins, TablesFromCoins, AllTables, GarblingProgram, AliceProgram, FakeObjects, FakeProgram, FakeMessage, FakeSimulator, CoordinateSwap, BobViewShape, FakeSimulatorFactory, BobStageZero, GateHybridChain, GateHybridSecurity; complete concrete simulator prototype. |
| /root/evaluation, sc-yao-b | RunWithHost, Decryption, FirstTagged, EvalGate, GarbledRun, BobTables, BobProgram, BobSimulator, GateOccurrences; NonceCoordinates, SeedCoordinates, SliceReconstruction, SelectedSlices, SelectedSeed, SelectedRows, SelectedPlan, SelectedTables, SelectedAdviceBounds, SelectedStep, SelectedStepChoices, SelectedStepSecurity. |
| /root/lengths, sc-yao-c | Lengths, OTInputs, TwoMoveViews, StatisticalSwitch, AliceSimulator, CoinRelabel, RelabelGarbling, CoinSeedRelabel, GateHybrids, GateHybridMessage, SamplerEndpoints, TapeValues, SelectedFields, GateStepCases, BobStatistical; shorter concrete assembly skeleton. |

Only the lead edits frozen files, commits and delivers. Children have separate worktrees,
separate TCSlib artifact trees and read-only package symlinks. All child evidence is under
evidence/subagents/. Ownership transfers and immutable handoff hashes are retained.

## Interface and concrete premise discharges (SY-1)

Helpers are generic in the actual circuit, seed, output selectors, strategy equations and
functionality; they cannot see or name Yao's definitions. Hybrid semantics are defined once
in GateHybrids/GateHybridMessage and consumed through readers. No seed/message/protocol
semantic copy is introduced. Source headers and complete elaborated signatures (including
implicit section parameters, private and generated constants) are exported in evidence.

The efficiency body uses AliceProgram.message_poly, BobProgram.output_poly, CallEquations
and the answer-independent message bound through ProtocolEfficiency. Uniformity supplies
the actual circuit description; canonical seed readers supply all key/nonce/shift blocks.
Strategies are efficient on arbitrary private words, tapes and malformed histories.

The following describes the checked prototype, not an exported proof of the frozen target.


### Concrete simulator assembly and premise discharge (agent a)

The complete a12 prototype preserves the full frozen target signature, including
`G₁`, `G₂`, both evaluator equations, both efficiency hypotheses, and all three PRF
hypotheses. Its checked body is124 lines (maximum width93); the computational `hBob`
instantiation is25 lines. It introduces no new admission or global Yao semantic definition.

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

### Verification and ownership qualification

The generic helper passes its normal check and all four full-file A/B × strict/coe seals.
Both stored helper constants have empty sorry closures and only `propext`,
`Classical.choice`, `Quot.sound`. The complete prototype's final normal check has zero
errors/warnings, and both owner-context canonical A seals pass. A genuine initial A issue
(implicit expansion of foreign `distAdv` at the final bound) was repaired with an explicit
`distAdv_def` rewrite; all affected checks were rerun and both versions are retained.

Each diagnostic B variant has9 errors:2 already in the unchanged PRF signature,
3 further polynomial add-index mismatches, and4 dependent-constructor cascades.
These arise when B deliberately seals the explicitly exempt `PolyExpr.eval` notation;
they are individually attributed in `a12/B-ATTRIBUTION.json`, not reported as passes.
Both error forms were counted with `-DmaxErrors=0`.

The prototype seals exempt exactly `TCSlib.Cryptography.SecureComputation.Yao` to emulate
its future owner-local theorem body; all other imported TCSlib definitions are sealed.
This is an owner-context prototype audit, not a substitute for the lead's final full-source
`Yao.lean` normal/seal checks after installing the body.

The focused trace visits18544 dependencies, excludes the old `yaoHybrid_simulators`,
and finds exactly these two authorized frozen admitted declarations:

* `TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp`;
* `TCSlib.Cryptography.SecureComputation.sliceMultiMessageSecure_of_prfOut`.

Thus the prototype is proved modulo sc-garble, with no new admission. Canonical source:
`a12/probes/CompleteSimulators.lean`, SHA256
`2438566d0ccd1ec9b4b40e1e12b4d4dc5fc4e98f1db5741e1603d4c079b7d300`.
Generic helper SHA256:
`197cdfbe60aa5ee5fffb13f45f62c4d3eacb51cbf9fa00f78a3220c337ca5170`.


## Gate 27 hand-off — selected-key embedding

In this fragment, `H/` abbreviates
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


Further disclosed general contracts:

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


## Overlap and reuse — b5/v6/v7

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


## Hosts, promotion and reader requests (SY-4)

Request promotion and registry review at landing. No frozen registry file is edited here.

| ID | Host | Status / provenance | Consumers |
|---|---|---|---|
| H-SY-decoder (draft) | Circuit-description recoder: DescriptionDecoder.decodeDescription_host. One H14 clean machine maps a paired circuit/output description to the unary input count, encoded gate records and unchanged output word; canonical correctness for every DAGCircuit, polynomial first-halt time and all-time work-head envelope for that same machine. | Proved in sc-yao, public generic SY-4 contract; promotion to the circuit-complexity construction layer requested. Built from emitting-loop, finite branching, pairing and clean_install/Clean.envelope. | Alice garbling; output decoding; garbled evaluator; simulator/reduction reconstruction. |
| H-SY-eval (draft) | RunWithHost.exists_machine: encoded topological evaluation generic in gate records, input-dependent value types, leaf step, initial values and polynomial round/state envelopes. One clean machine with polynomial time and all-time work-head envelope. garbledRunWith_poly derives envelopes for fixed-width key encodings. | Proved in sc-yao; promotion and registry gate requested. Built from stateFind and H14. | Bob evaluator; fake-garbling simulator; reduction reconstruction. |

The supporting ChunkScanner is also public with a same-machine clean/time/head contract.
No private host is introduced. The read-only source/signature inventory identifies every
new public definition and its published reader.

## Additional c overlap comparisons

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



## Scope requests and readers

SY-1–SY-6 govern. The only circuit insertions are isFaninTwo_iff, byte-identical to
sc-garble, plus encodeList_nil/cons, GateKind.encode_and/or/not, DAGGate.encode_eq and
DAGCircuit.encode_parts. Removing them restores base bytes. All24 reader controls are
retained:8 unsealed passes,8 sealed negatives each exactly1 error,8 sealed reader passes.
Both diagnostic forms are counted.

Four extra imports were explicitly approved, with verbatim requests/answers under
evidence/scope-request/: ThreeColoring.Machines, FromPRF.ReductionMachine,
FromPRF.HybridLemmas, Asymptotic.BlockEncryptor. The last is now actually used by
SelectedSlices via the public encodeList_eq_flatMap; no unapproved Mathlib root is introduced.
The full issued-plus-approved upstream order has193 modules, extended by68 helpers/facade.
The user authorized full edits, scoped commits/pushes and shared-wrapper checks despite
the supplied AGENTS prohibition: “Yes, follow the full objective and wrapper rules”.
Approvals persist across relocation. No other frozen-file change or scope is assumed.

## Validation and evidence

Every Lean/Lake/tree check uses /private/tmp/sc-yao-lean-slot.sh, with at most THREE Lean
processes host-wide, shared with all other jobs; tags sc-yao/a/b/c. Python is python3 -I.
No lake build or unfiltered cache fetch was used. Wrapper SHA256:
ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a.
Initial packs/pins/narrow cache and package checks remain delivered. Latest resumed
preflight headroom6.368GiB, later6.180GiB, both above4GiB; disk free>130GiB.
Shared-slot histories and all interrupted/failed development versions are retained.

The full261-module checkpoint sweep passes with0 errors and fresh artifacts. Every raw
source snapshot hash matches the committed source. Comparing declaration names with the
32 base admissions yields31, exactly removal of yaoHybrid_polyTime and no addition.
See checkpoint4-sweep-summary.json and logs/checkpoint4-sweep/results.jsonl.

The merged all-stored probe prints1488 constants including1110 helper constants. Every
helper has empty transitive sorry closure and only propext/Classical.choice/Quot.sound.
The efficiency target has those standard axioms and empty closure. The simulator target
and yaoHybrid_hbcSecure still reach the target's base admission; yaoProtocol_hbcSecure
additionally reaches the two OT target admissions and hbcSecure_compose. The probe used
the pre-import-correction artifacts; no declaration body changed in that correction.
The corrected source is independently rechecked/sealed and the final audit will be rerun.
Earlier c probes covered40 explicit source roots; later c probes dynamically enumerate
278 stored constants. The lead's complete1488-constant merged audit independently closes
the earlier coverage gap; the early source-root probes are not described as exhaustive.

Every new helper has exact-version A/B strict/coe evidence from its owner. The lead has
additionally rechecked all helpers in the full sweep; its complete facade4/4, strengthened
CoordinateSwap/SelectedLaw8/8 and corrected BobViewShape4/4 full-file variants pass.
All seals cover full imported TCSlib definition/matcher closures, use -DmaxErrors=0 and
count error: and error(...). Coercion notation variants are canonical. No failed check
is hidden by a cutoff. The prepared complete-helper seal manifests are for the next final
lead verification; their generated sources alone are not claimed to be executed runs.

Frozen-file baseline diagnostics remain: DAGCircuit0 in all variants; Uniform4 inherited
errors in two old declarations; Yao A strict/coe0, B strict/coe17=15 base plus2 efficiency
call-input polynomial-evaluation mismatches. Each is attributed in the retained baseline
and efficiency seal summaries. The a12 prototype has a separate individually attributed
B9, not a four-seal pass; its owner-context exemption is documented above.

Name scan:764 new explicit namespace-resolved public/private names,0 unexpected clashes
across issue base, sc-garble a73072f1, sc-ot f62a25b3 and sc-compose bdfdcb76. The sole
intentional coincidence is the byte-identical SY-3 reader. Explicit definition review:
8970 files,1909 tactic references,17 candidates:15 local binders and2 same-file published
SelectedRows.length_eq theorem references,0 foreign-definition violations. Full source
contexts/hashes are retained. Initial parser assertions and their fixes are preserved.

Exact lint line-set comparison: Cryptography92 FAIL/102 WARN versus base92/101; the only
new WARN is the approved Yao size. Circuits0 FAIL/79 WARN, with missing-reader warnings
improved11→10 and2→1. No new FAIL or undisclosed WARN. The old Yao target-size INFO
disappears when it becomes a facade. Source scope, width, line bounds, complete facade
imports and no-helper-admission scans pass.

SelectedLaw development evidence is preserved: the320-second candidate reported five
missing finite-instance diagnostics (4.7GB peak), with no resource shortage and no signal
sent to that already-finished run. Later source-directed SIGINTs were diagnostic stops
of owned groups, not resource failures. A tool approval timeout created no process; the
single retry succeeded. The genuine prototype foreign-distAdv reduction issue was fixed
through its published reader. No other job was killed and no137/139/low-headroom E-RES
occurred. The c shortened skeleton's width is100 (earlier prose said93); the final a12
complete prototype is124 body lines, width93. Exact metrics take precedence over old prose.

## Delivery and remaining work

The complete unsigned six-patch series from the issue base includes COMMITS.tsv with all
author/committer identities/dates and signing=none. All six hashes are reproduced with
git am in a fresh shared scratch clone before pushing. Top-level and evidence manifests
are checked for exact path-set equality, no leading ./ and SHA256 byte equality.

Every retained raw source/log/results file, probe, seal/control, request, tool and child
handoff is delivered. Large raw samples are losslessly in numbered ZIPs with entry hashes;
the relocation ZIP preserves all four trees. Evidence-only unfinished ladder versions
are historical probes and are not exported library source.

The157MB SelectedLaw diagnostic stack is losslessly retained in raw-samples-03.zip, with
verified decompression hash and entry inventory. An initial unpublished local delivery
commit included the raw file; its controller was stopped after pull/rebase and before
any push. That commit is preserved on a local backup ref and replaced by the corrected
package commit. No push was refused and no force-push occurred. The exporter and delivery
tools now reject oversized individual files before submission.

Prior pushed checkpoints: f0a9a6163c5c91599147eb550fd5bb929cc68aa0,
816971fc6922646f056a47efd41b1407f762320d, acc868271367d525350da2c1043e7f470f1c0a98.
This checkpoint is rebased and pushed only under inbox/fills/sc-yao, without force.
Remaining: install the complete concrete simulator body/sketch/main-results bullet,
run final exact-source normal/all-stored/seal/static/full-sweep audits, commit and deliver
the final payload and sc-yao-rooted ZIP. No final completion or PR merge is claimed.
