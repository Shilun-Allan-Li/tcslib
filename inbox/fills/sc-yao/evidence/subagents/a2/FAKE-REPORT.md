# Shared-core fake garbling program

## Completed mathematics

`FakeObjects.lean` defines only new simulated semantic objects:

* `row` encrypts the output wire's false key under the ordinary argument keys.
* `table` enumerates these rows after the ordinary seed row permutation.
* `decodePair` orders the output keys as `(key b, key (!b))` for prescribed output bit `b`.
* `activeAnswers` is the canonical flat finite tuple of consecutive false input-key blocks.

Every definition has a public `_eq` reader. No real definition from `Yao.lean` is copied.

`FakeProgram.lean` proves complete polynomial-time contracts for the actual encoded objects:
`activeAnswers_word`, `activeAnswers_poly`, `swapPairs_poly`, `outputPairs_poly`,
`inputKeys_poly`, `tables_poly`, and `message_poly`. The table and full-message contracts
use the same generic PT description/numeric/coin maps, circuit/seed family, fan-in bound,
and key/nonce/XOR readers as the real program. The message also takes a PT prescribed-result
word. There is no indexed reconstruction or substantial row-semantic hypothesis left to
consumers. Bob's answer contract takes a PT unary starting vertex/count and a valid input
range. The caller can use Alice's input count as that starting vertex.

## Shared-core refactor

`RowFromCoins.rowWordWith_enc` generalizes the existing real semantic bridge to an arbitrary
output-bit map. The old real theorem is a thin application plus the gate-truth reader.
`rowWordWith_value` exposes pointwise map transport. No old statement changed.

`TablesFromCoins.tableWordWith_of_encoded` generalizes the old real table's guard/cap/arity
normalization. The old real theorem is now a thin application followed by its row contract.
`tableWordWith_congr_at` transports arbitrary raw contexts pointwise, normalizing the natural
arity before opening the dependent finite assignment enumeration. Thus the real and fake
programs share the actual key, nonce, row, bounded-table, and range-assembly machines.

## Search and duplication

See `fake-search.md`. The canonical flat-answer identity directly cites the public
`FunFamily.ofFn_blocks_symm` and `blocks_symm_apply`; no finite-product or flatten identity
was re-proved. Active Alice keys reuse the real selected-key theorem at the constant false
input. Output pairs reuse the real output-pair theorem and indexed pair swaps. All traversal
uses the already approved `ColMachines.polyTimeComputable_flatMap_range` via `WordLists`.
There is no additional duplicate construction in this extension. The earlier nearest-relative
disclosure for the real bounded-table closure remains in `evidence/subagents/a/REPORT.md`.

The lead approved independent `c` ownership of assignment-bit-parameterized `GateHybrids`
semantic row/table objects importing stable `FakeObjects`. Their endpoint proofs are to
consume the existing real/fake equation readers. They introduce a different hybrid semantic
parameter, not a duplicate polynomial-time construction; no later refactor is required for
this handoff. These `c` files are not included in the child's owned source set.

## Normal verification

`FakeObjects` and the initial complete answer/key/pair contracts passed normal checks.
The arbitrary-output-bit row theorem, its thin real wrapper, and pointwise value reader
passed. The generic table normalization and repaired pointwise table congruence passed.
The full simulated table/message program passed `FakeProgram03` with zero errors, warnings,
and admissions. After the thin real table refactor, all five affected consumer checks passed
in `probe-runs/fake-normal-03/`: TablesFromCoins, AllTables, GarblingProgram, AliceProgram,
and FakeProgram. The later documentation lint found two missing sketches, both added before
those queued seal probes ran; all pre-lint versions were retained. Final lint has zero findings.

Failed raw source/log versions remain: FakeProgram's initial missing composition-normalization
step, and the initial table congruence attempt that opened a dependent domain too early.
Both have source-directed repairs. All checks use the shared wrapper and own olean tree.

## Final audit

The sixteen A/B by strict/coe whole-file seals, eight full-fake-closure controls, and the
complete twelve-module stored-constant axiom/admission trace are being recorded under
`probe-runs/fake-audit-01/`. Final results will be appended after completion.

Completed final audit: all sixteen new/refactored full-file seal variants pass. Combined
with the unchanged/repaired real-program evidence, all forty-eight final variants for all
twelve owned modules pass. Four full-fake-closure positive controls pass; four deliberately
sealed negative controls each report exactly one error. The complete trace covers 196
stored constants, including private/generated declarations, and has no transitive admission
closure. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`. Final style
lint has zero findings. See `fake-audit-summary.json`, `all12-final-seal-results.json`, and
the complete raw trace under `probe-runs/fake-audit-01/`.
