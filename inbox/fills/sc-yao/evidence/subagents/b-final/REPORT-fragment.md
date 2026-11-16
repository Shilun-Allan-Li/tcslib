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
