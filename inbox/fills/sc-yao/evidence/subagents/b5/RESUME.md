# Paused selected-key reduction work

User paused for relocation. No owned Lean process, slot wrapper, batch driver, or live
session remains. Last session 32001 completed SelectedTables check04 with exit zero.
A read-only process revalidation at pause found only that revalidation command itself.
No commits or delivery pushes were made. Immutable v1-v4a handoffs remain untouched.

## Verified declarations

- SliceReconstruction (last normal13): total raw fixed/direct/wrapped row interpreter;
  row/table/tables/rebuild polynomial time on every input; canonical record, nested table,
  view-layout readers; exact record and advice lengths; approved BlockEncryptor encoding
  bridge; tables_records generalizes the old canonical-challenge reader without copying it.
- SelectedSlices (last normal08): zero/only/inner/outer nested row slice identities;
  exact precomputed inner-message length 4n+2; direct/wrapped sampler slot readers; slice fit.
- SelectedSeed (last normal19): row/occurrence ranks and exact inverse readers; generic
  selected key/nonce fill; fixed/opposite coordinate readers; total keyAt reader; exact
  argKeys .set p k update and unselected-list identity; no key-value inequalities.
- SelectedRows (last normal08): fixed-data offset/length/message/descriptor plan, exact typed
  messages, pointwise selected-row reconstruction for every valid position in <=2 keys,
  explicit descriptor length bound, and fitting joint slices.
- NonceCoordinates (last normal08): nonce index type; partial pick/place; both inverse
  directions and iff; nonce_read identifies fill with partial coordinate replacement.
- SeedCoordinates (last normal06): key/nonce data equivalence and arbitrary-P extension;
  seed/challenge coordinate readers; full key+nonce partial inverse; dataEquiv_fill and
  seedEquiv_fill exact pointwise replacement identities, no equality on values required.
- SelectedPlan (last normal09): fixed padded all-occurrence messages/records/tables; exact
  typed-message words and fit; occurrence slot readers; common-advice record/table equality
  for plaintext families agreeing on unselected rows.
- SelectedTables (last normal04): record_reconstruct identifies every reconstructed original
  row, seed by seed, with nested encryption under SelectedSeed.fill and the fixed plaintext.
  It discharges shapes/messages from SelectedPlan internally, including zero/unselected rows.

Every current source declaration is complete; no admission appears in these eight files.
Full-file opacity seals and axiom/dependency traces for b5 have NOT started. Do not report
these as sealed or dependency-audited. Source width is checked in paused-summary.json.

SliceReconstruction and SeedCoordinates received only line-wrap formatting after their
last passing normal checks, to satisfy width100. Their next verification should use the
exact snapshotted source. Other sources match the last passing checks semantically/textually.

## Resume point

1. Revalidate no stale process or slot before a new check. Use only own TCSLIB_OLEANS and
   LEAN_SLOT_TAG=sc-yao-b through /private/tmp/sc-yao-lean-slot.sh. Do not run lake.
2. Finish SelectedTables: lift record_reconstruct through SliceReconstruction.tables_records
   and SelectedPlan.tables_eq to complete tables, then rebuild_layout to the explicit encoded
   view/output endpoint. Keep GateHybrids/GateHybridMessage as the sole hybrid semantic
   definitions; read their row/table/message/sample contracts rather than copying them.
3. Prove explicit descriptor/table/advice polynomial bounds. SelectedRows.descriptor_length_le,
   SliceReconstruction.record_lengths/advice_length, Lengths.length_nestedSpecial_enc_le and
   BinArith.length_encWords_le already supply the needed leaves. q=4S gives q+1 padding;
   GateOccurrences.length_occurrences_le gives capacity under fanin two.
4. Coordinate the actual sampler transport with c's TapeValues and a's CoordinateSwap.
   Actual XOR shifts must stay in arbitrary unchanged P, with unused key/row coins. Do NOT
   infer uniformity of the derived permutation over all permutations. TapeValues' structural
   key/nonce Data target composes with SeedCoordinates.paramEquiv/dataEquiv. CoordinateSwap
   acceptProb_fill needs only the exact coordinate fill identity and pick/place iff.
5. Finish public-reader/width/sketch scans, four full-file A/B strict/coe seals with maxErrors0,
   trace every stored constant/axiom/sorry closure, and immutable completed handoff.

## Relevant coordination

Agent c (/root/lengths) owns TapeValues after its stable GateHybrids/GateHybridMessage and
SamplerEndpoints work. At pause, TapeValues.equiv normal05 passed; it targets
Rest x ((Fin C.size -> Bool -> K) x (forall i, assignment_i -> K x K)), retaining all shifts
and unused keys/rows in Rest. Key/nonce and derived-permutation/seed readers were underway.
No cyclic import of b's Index/Data is required.

Agent a (/root/decoder) completed CoordinateSwap with normal05, four seals, and clean trace.
Immutable handoff: /private/tmp/sc-yao-a-coordinate-handoff-v5-20261116. Its acceptProb_fill
uses arbitrary P, seedEquiv/challengeEquiv, and an exact coordinate-fill equation. It assumes
no equality/distinctness on values. Root integrates/seeds a/c modules; do not edit them.

Root owns SliceReduction and the whole security/protocol glue. b independently verified its
successive current versions: lead-slicereduction-01/02/03/04 pass, with check04 including the
fifth chain_negligible theorem. Copied source is included separately as upstream-checked,
not a b-owned contribution. Root's later versions require root's own validation.

## Diagnostic and overlap notes

All raw development logs are preserved and paused-summary.json counts both error: and
error(...) forms. Source errors were ordinary elaboration/reader issues and have been
resolved in the last passing checks. selectedplan-07 is a local TCSLIB_OLEANS path typo;
noncecoordinates-01 and selectedslices-05 are missing-prerequisite attempts after a failed
upstream own-module check, not mathematical failures. Do not omit those histories.

The approved BlockEncryptor scope request is retained in scope-approval-blockencoding.md.
Encoding reuse is the public TCSlib.Cryptography.encodeList_eq_flatMap plus
BinArith.encWords_def. No public encoding lemma was copied. All loops reuse mapW/getW and
existing polynomial-time special-encryption/view pairing closures; no new machine host.

Core list reuse: find? and filterMap contracts from GateOccurrences; idxOf/getElem readers
from Mathlib, including the explicit decidable-equality BEq for occurrence ranks; public
getElem_set and ofFn readers for argument updates. Exact function congruence composes the
row-index equality into SelectedRows.offset/word because direct rw matching failed under
hidden dependent indices. Generic padFin/padL readers avoid rederiving a second word-vector
round trip. Coordinate equivalences compose Equiv.curry, piCurry, piCongrRight,
boolArrowEquivProd, sumArrowEquivProdArrow and funUnique. Probability laws remain owned by
CoordinateSwap/SliceReduction. The nearest pairing-only view builder is BobSimulator.raw_poly;
rebuild carries table descriptors/advice and retains Alice output, so that fixed constructor
cannot express this input layout. Final REPORT should disclose that proof-shape overlap.
