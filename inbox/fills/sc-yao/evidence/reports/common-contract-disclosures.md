## Overlap and reuse

Searches preceded probability, list, coin and machine proofs. Detailed searches and nearest
relatives are retained under each agent's evidence. These disclosures include inline proofs.

- The description decoder compares the existing DAGCircuit.decode/decode_encode validator,
  but does not invoke it. The new total streaming host recodes gate fields into traversal
  records through ChunkScanner and the SY-3 encoders. CVAL decides a language and cannot
  replace this data-returning contract.
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
  double-XOR cancellation is inline from Bool equations, nearest the anonymous inline involution
  proof inside the public xorPerm definition. No public probability or list theorem is copied.
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

