# Selected-key reconstruction handoff notes

Agent: `/root/evaluation` (`sc-yao-b`). Parent owns commits, integration, probability
assembly, and final delivery. No frozen or lead-owned source was edited by this agent.
The nine contributed modules are listed in `final-modules.json`.

## Exact deterministic contract

`SelectedTables.sample_reconstruct` is pointwise in every challenge key and all `q+1`
nonce blocks. It reconstructs the actual shared `GateHybridMessage.sample` with the
`SelectedSeed.fill` seed, Bob coins `[]`, and the retained actual Alice output.
Its only semantic separation assumptions are symbolic plaintext-label avoidance and
selected-wire exclusion from designated outputs; it never assumes unequal key values.
Every occurrence throughout the circuit is included. The zero-argument row is unchanged;
argument Nodup prevents two occurrences of the same symbolic selected key in one row.

`SelectedPlan.slotOffset` and `slotLength` do not depend on the plaintext family.
`SelectedPlan.advice_congr` gives identical raw advice for plaintext families agreeing on
unselected rows. A later SelectedStep helper will discharge these assumptions for both
neighboring actual hybrid stages through SelectedFields; root owns probability assembly.

## Runtime and advice bounds

`SliceReconstruction.rebuild_poly` needs only polynomial-time `E2`. It is one total raw
machine for arbitrary encoded input and advice, using existing mapW traversals, getW,
pairing, and special-encryption closures. Advice and slice messages are precomputed;
there is no unproved runtime hypothesis for their construction.

`SelectedAdviceBounds.sample_advice_budget` closes the entire actual view advice bound.
For size bound S, input bounds A/B, output count O, and actual Alice-output bound R, it
uses slot parameter Q=4S and polynomial

    2*S*(16*(2*Q+7*n+8)+18) + 2*T + 2*I + R + 6,
    T = 2*A*(2*n+2)+2+O*(6*n+6),
    I = 2*B+2+B*n.

It derives distinct arguments, complete canonical rows, at most four rows per gate, and
capacity from fan-in two, canonical enumeration, and C.size <= S(n). Zero widths/counts
are included. Selected-u contracts are pointwise and impose no global Nonempty Fin C.size
or Nonempty step-space assumption. Root handles missing selected arguments by equality.

## Distribution boundary

NonceCoordinates and SeedCoordinates give exact partial inverse coordinate maps and a
pointwise fill identity. `paramEquiv` retains an arbitrary unchanged P. Concrete tape
shifts and unused key/row coordinates remain in c's TapeValues.Rest; derived permutations
are not asserted uniform over all permutations. Root's SelectedLaw composes this with a's
CoordinateSwap and proves the actual sampling law. This agent did not duplicate that law.

## Overlap and reuse

- Slice identities reuse frozen proved `sliceEnc_append_left/right` in SpecialEncryption,
  nestedSpecial_enc and sliceMultiEncDist_apply. SelectedRows is the new selected-layer
  assembly of those identities; zero/one/two argument cases share the existing primitives.
- The encoding bridge consumes public `encodeList_eq_flatMap` in the explicitly approved
  Asymptotic/BlockEncryptor import, plus BinArith.encWords_def. No encoding proof is copied.
- Descriptor traversal uses public BinArith.mapW/getW and existing PTC closures. The nearest
  view-pairing proof is BobSimulator.raw_poly, but it has fixed leaf inputs rather than a
  challenge/descriptor/advice interpreter. The shared shape is pairing/list composition;
  rebuilding from descriptors is a different public input contract, not a copied simulator.
- SelectedSeed rank proofs use Mathlib idxOf/getElem/getD readers and GateOccurrences'
  complete/nodup occurrence readers. The explicit instBEqOfDecidableEq argument fixes the
  occurrence triple's BEq. Argument updates reuse List.getElem_set and ofFn readers.
- SelectedRows.message_ofFn consumes the existing padFin/padL vector roundtrip and word
  length, rather than re-proving a getD/vector identity. Its three-line proof carries a
  sketch because the repository lint counts following section variables as proof lines.
- Coordinate equivalences compose Equiv.curry, piCurry, piCongrRight,
  boolArrowEquivProd, sumArrowEquivProdArrow, and funUnique. New material is only the exact
  selected occurrence/nonce-coordinate indexing and its fill/readers, not a probability law.
- Advice bounds consume BinArith.length_encWords_le, Lengths' nested ciphertext/key/pair
  bounds, length_garbledTable_le, and GateOccurrences.length_occurrences_le. The inline
  four-row bound rewrites the existing garbled-table theorem to the canonical assignment
  list length; its cardinality proof is not repeated. Scalar polynomial inequalities use
  Nat monotonicity and omega. New constants account for this descriptor encoding.
- SelectedTables consumes c's GateHybrids.rowWith/tableWith and GateHybridMessage readers.
  It specializes the generic record traversal to these shared objects without defining a
  second semantic table, message, or view family. SelectedFields provides false-key,
  output-pair, and message-tail fill invariance, so those proofs are not duplicated.

Search record: `reuse-search.log` and the preserved development diagnostics. No unmerged
sc-garble, sc-ot, or sc-compose probability/host proof was copied in these nine modules.
The only additional scope import is recorded verbatim in scope-approval-blockencoding.md.

## Diagnostic history

Every raw development log remains. Both `error:` and `error(...)` forms are counted.
Known environment/invocation issues are preserved separately from mathematical failures:
selectedplan-07 used the wrong local olean path; noncecoordinates-01, selectedslices-05,
and selectedadvicebounds-07 tried a prerequisite absent after an earlier failed check;
selectedtables-06 met an incomplete seeded helper closure fixed by the parent; advicebounds
11/12 used respectively a dotted module name and an extension where the checker expects a
slash path without extension. These attempts did not establish a passing check. The later
checks with the correct environment and repaired source pass.

Final seal/trace results and exact source hashes are recorded in final-summary.json once
complete. Prior v1-v4a and the relocation v5-paused snapshots remain immutable.
