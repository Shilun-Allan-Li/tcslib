# Subagent c report fragment

Owner: `/root/lengths`, worktree sc-yao-c. Fifteen generic helper modules,3384lines,
216 public declarations plus13 private TapeValues helpers; every file<1000lines and
width≤100. No library-source admission, new simp attribute, frozen-file edit, child
commit or push. This report task made no proof edits and ran no Lean checks. Exact
source hashes, audit paths and count method are in INVENTORY.json.

| Module | Lines | Public declarations | Generic contribution |
|---|---:|---:|---|
| Lengths | 197 | 10 | Evaluator-independent ciphertext/message bounds; encoded tables ≤gates*(112n+82). |
| OTInputs | 128 | 8 | All-input polynomial-time affine sender-bit and quotient-indexed receiver-bit adapters. |
| TwoMoveViews | 164 | 10 | Generic Alice-first two-message transcript, view, output and real-sampler equations. |
| StatisticalSwitch | 74 | 2 | Same-coins/off-Bad StatClose and randomized-distAdv bound. |
| AliceSimulator | 150 | 10 | Uniform copying simulator, all-input polynomial time, exact run/coin readers and coupling. |
| CoinRelabel | 358 | 32 | Full 10*S*n+2*S tape↔key/row/shift blocks and coordinate relabeling. |
| RelabelGarbling | 202 | 16 | Per-seed key/nonce/permutation relabeling and exact row/table/key/pair identities. |
| CoinSeedRelabel | 399 | 29 | Padded arity≤2 XOR extension and four-reader tape→seed relabeling bridge. |
| GateHybrids | 346 | 35 | Parameterized rows/tables and exact two-substep gate clock/real/fake endpoints. |
| GateHybridMessage | 176 | 10 | Canonical encoded hybrid message/Bob-view sample and per-seed endpoint identities. |
| SamplerEndpoints | 238 | 8 | Exact initial/final acceptance transport through published coin-bijection APIs. |
| TapeValues | 464 | 23 | Complete tape↔Rest×actual key/nonce tables, exact seed/inverse readers. |
| SelectedFields | 320 | 20 | Selected-fill invariants, symbolic label separation and missing/unselected-row support. |
| GateStepCases | 91 | 2 | Every clock step is unchanged or names an actual gate argument, including absent positions. |
| BobStatistical | 77 | 1 | Canonical sender-tape bad bound→actual Bob-view output switch, uniformly in inputs. |

## Proof contributions and edge cases

Efficiency reuses EncodingMachines arithmetic/bit readers and BinArith.length_encWords_le;
length bounds allow arbitrary evaluator outputs, and Bob output length uses List.length_ofFn.
StatisticalSwitch specializes MultiMsg.abs_uexp_sub_le_uprob. AliceSimulator composes public
NUPPT.ofPolyTimeUniform/View/layout readers. BobStatistical extracts the root's
BobOutputSwitchGlue using SimulationBound.realB_output_switch, strategyTapeEquiv/ofFn,
uprob_fst/comp_equiv; no probability measure, finite-sum inequality or machine was rebuilt.

CoinRelabel reuses blocksEquivX/FunFamily.blocks and finite equivalences. RelabelGarbling
reads public Garbling/xorPerm equations. CoinSeedRelabel uses assignmentFold_eq_two and
viaFintypeEmbedding. TapeValues composes piEquivPiSubtypeProd/ofInjective; Rest retains
all shift bits and unused key/row coordinates. No uniform-full-permutation claim is made.
Root owns SelectedLaw, not c. GateHybrids/GateHybridMessage are the approved parameterized
hybrid objects, with real/fake endpoint readers. SamplerEndpoints takes real/equation as
parameters. SelectedFields reads fill_keyAt and reuses hybrid_plaintext_ne/selected_wire_lt;
GateStepCases reuses missing-argument and sample-congruence contracts. No Yao semantic def
is redefined in these helpers.

All tape/seed/nonce-half equivalences include n=0; no positive width premise. Empty gates
and indices require no selected witness. Arity0/1 unused Fin4 codes are fixed, missing
argument clock steps are exact equalities without dummy wires, and default/padded vertices
are explicit. OT adapters are total on malformed/short words and total quotient at n=0.
StatisticalSwitch includes empty finite seeds; actual zero-length tapes are nonempty function
spaces. Bob's independent tape has arbitrary length.

## Publication, attribution and SY-5 overlap

Every owned module has References and public formula docstrings/proof sketches. The primary
tag is [PS10], Pass–shelat, A Course in Cryptography (2010), Protocol162.6/Theorem163.7;
Lengths also cites Definition155.1. Additional existing tags: [Gol04,§7.3] TwoMoveViews;
[BMR90] CoinRelabel; [LP09] RelabelGarbling; [Gar26,§3.2,Lemmas3.2–3.3] SamplerEndpoints.
Pure technical readers/glue are identified as such. c did not edit blueprint/ingest sources.

Final REPORT.md Overlap and reuse should retain these exact relatives:

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

## Short skeleton versus completed assembly and report risks

c shortened verified a10 from117→100 bodylines, preserving the full signature and exact
one hBob hole byte for byte. BobStatistical replaces the long bad-probability/output switch.
Short source137lines,SHA5a361bb55a97fc8dc6ec96c617561d048f84e1f129cc5a39eceffd185c5263b8.
It is superseded evidence only, not a delivered admission. a12 adds GateHybridSecurity,
fills hBob in25lines with actual joint slice security and explicitly rewrites the final
bound by distAdv_def. Complete body124lines,total162,max93;
SHA2438566d0ccd1ec9b4b40e1e12b4d4dc5fc4e98f1db5741e1603d4c079b7d300.
Signatures are whitespace-identical; fixed SA/SB precede D. a12's18544-dependency closure
contains exactly frozen sliceMultiMessageSecure_of_prfOut and yaoSeed_good_whp; old
yaoHybrid_simulators is absent. This is security modulo sc-garble, not admission-free.

All existing c final normal checks and60 final helper A/B×strict/coe seals passed.
Exact trace coverage:40 explicit source-root closures in the first five modules, then
278 dynamically enumerated module constants in the later ten; every recorded closure
is admission-free with only propext/Classical.choice/Quot.sound. Do not call318 an
exhaustive module-constant enumeration. Early CONTRIBUTION prose calling explicit roots
'all stored' is too strong; lead final all-stored audit must confirm generated coverage.
Both diagnostic error forms and original failures are preserved.

Report-only correction: c short README/progress claimedmax93, but the hashed source is
max100 atline55; its final-metrics.json was correct. a12's actualmax93 is correct. Both
meet width100. a12 owner-A strict/coe pass; owner-B each has9 attributed diagnostics from
sealed PolyExpr.eval signature/index mismatches/cascades. Do not claim four complete-body
variants passed. Root final full-source checks/seals, hub exports, publication/blueprint
checks, SY-4 decoder/runWith host-promotion requests (owned elsewhere), final commits and
delivery remain lead-owned; this read-only review does not certify their final state.
