# Final machine helper preparation (source-only)

Nine helpers were installed in the owned helper directory. `Machine`, `Seed`, and `Closing`
were restored from `working-helpers/`; `Blocks`, `MachineSpec`, `Advice`, `Nonabort`,
`InversionProbability`, and `Realization` were copied from `drafts/`. No owned-module,
checked probability helper, or foreign source was edited. No Lean process was run.

The only proof edit during installation was the requested explicit form
`Nat.size_le.2 n.lt_two_pow_self` in `Advice.length_indexBits_le`. This matches uses of
`n.lt_two_pow_self` in the pinned Mathlib sources. `Machine.offset_poly` retains the root's
namespace correction `OneWay.polyTimeComputable_unaryMulPair`.

## Dependency and resource scope

`final-machine-helper-order.txt` lists parents before consumers. Existing issued/T1 modules
and previously installed checked helpers are treated as prerequisites. One additional
foreign prerequisite is required: `TCSlib/Cryptography/Games/Bridges/Experiments`, imported
by `InversionProbability` for its public `Bridge.prob_sample_eq_uprob` and
`Bridge.expect_sample_pair` laws. It precedes that consumer in the list.

The entire new-helper closure has 70 direct Mathlib roots, all contained in the issued
82-root set. **New Mathlib roots: none.** No cache or Lake command was run.

## Headers, documentation, and interface readers

All nine files have the copyright/import/options/module-docstring headers, references,
and immediate docstrings on every public declaration. Every file is below 1000 lines:

| Helper | Lines |
|---|---:|
| Machine | 355 |
| Seed | 73 |
| Closing | 94 |
| Blocks | 78 |
| MachineSpec | 228 |
| Advice | 134 |
| Nonabort | 64 |
| InversionProbability | 87 |
| Realization | 182 |

`Machine` publishes equations for each string function and readers for every data field of
its `handler` structure value (`stateLen`, `seedLen`, `init`, `run`, `advIn`, `out`). `Seed`
publishes forward/inverse application and word equations for `seedCoins`. `Advice` publishes
the `indexBits` equation, width/value readers, and the `expandIndex` equation and canonical
input equation. `Realization` publishes `machineForger_eq` and its query-cost contract.
The other new files only add theorems. There are no new public abbreviations.

There are no `sorry`, `admit`, new axioms, unsafe settings, or new simp attributes in these
nine source files. Native typechecking remains required. The Machine module docstring still
uses the word “draft”; remove that editorial status before the final delivery once checked.

## Rule 10 source review

The explicit rewrite/simplification lists in the nine files name public equation readers,
theorem APIs, or local definitions. `MachineSpec` reads `secretWord`, `publicWord`, planted
tables, signature blocks, and the machine string functions through their published equations.
Its only finite-tuple coin-block assumption is the owned module's existing public reader,
passed as a parameter to avoid an import cycle or a copied public proof.

`Realization` reads handler fields through `handler_*`, its oracle through `impl_apply` and
`answer_of_run_eq`, its seed through `ofFn_seedCoins_symm`, and its finalizer through
`PolyHandler.result_eq` and `out_nonabort`. Its `H`, `z`, `tree`, `rows`, and `plantedRows`
identifiers in proof steps are local definitions, not foreign library definitions. It uses
the foreign negligible-function closure only through public theorems. The exact T1
codec/output-width transport at `hsimulation'` still needs native elaboration, including the
requested A/B seals. This source review is not reported as a passed seal.

## Duplication and promotion ledger

Mandatory overlap records:

- **overlap: TCSlib/Complexity/ClassNP/TMSAT.lean tmsat_pt_take** — `Machine.take_poly`
  has the same general statement as that private helper. The new proof is independently
  derived from the published `polyTimeComputable_pairTakePoly` API, not its machine proof.
- **overlap: TCSlib/Complexity/CookLevin/Hardness.lean clA5Drop_native** —
  `Machine.drop_poly` has the same general statement as that private helper. It is independently
  derived from `polyTimeComputable_pairDropPoly`, without the private native tail iteration.
- **overlap: TCSlib/Cryptography/Authentication/Signatures/Lamport.lean lamportVerFun_sign.hflat**
  — `MachineSpec.publicWord_flatten` generalizes the same local serialization identity. It is
  derived from the published `encodeList_eq_flatMap`, `List.flatMap_def`, and `List.map_ofFn`.
  No local proof or private declaration was copied.

Promotion candidates:

- `Machine.take_poly` and `drop_poly`: the general FP variable-prefix wrappers belong beside
  the shared prefix/closure primitives when the frozen shared-file window reopens.
- `Blocks.flatten_ofFn_update`: a general fixed-width list/tuple update serialization fact.
- `MachineSpec.publicWord_flatten` and `headD_drop_ofFn`: generic encoding/list readers, suitable
  for the shared encoding/bit-list layer; the former has the overlap noted above.
- `Advice.indexBits` with its equation, length and value readers: a reusable bounded-index
  binary encoding from the published `bitsEquiv`; `expandIndex` and `exists_withIndexAdvice`
  are generic machine preprocessing/advice closure wrappers.
- `Closing.negligible_of_linear_bound` and `negligible_of_inversion_bound`: general
  nonnegative polynomial-loss closure. Its one-time-signature reduction closure lemmas could
  move to the shared signature interface rather than a foundations file.
- `Nonabort.safe_of_nonabort` is stated against this typed Lamport oracle; a broader
  one-query abort/safety interface could be promoted if another consumer needs it.

`Seed`, `Realization`, and `InversionProbability` retain Lamport table/experiment-specific
interfaces. Their proofs import public APIs rather than copying public or private theorems.
No new generic expectation/`uexp` bridge was added: `InversionProbability` reuses the existing
public bridge module instead.

## Reproduction and raw artifacts

Run `python3 -I evidence/tools/audit_final_helpers.py PROOF_ROOT EVIDENCE_ROOT` for the source
inventory, dependency/root census and recorded searches. Its delivered raw outputs are
`inputs/final-machine-helper-static-audit.json` and `logs/final-machine-helper-searches.log`.
The JSON holds every helper's SHA-256, declaration list, line count and header/docstring audit.
Searches include the two private overlap names, tuple-update/serialization patterns, exact
new helper names, and admission/unsafe/simp-attribute tokens. Source hashes and the proof
status are point-in-time observations; subsequent native fixes require regenerating them.
