# Reuse search before simulated program

Searches ran over TCSlib and the pinned Mathlib tree before writing fake helpers.

* No public `fakeRow`, `fakeTable`, `fakeGarbling`, `activeAnswers`, `rowWordWith_enc`,
  `tableWordWith_congr`, or indexed word transformation appeared in the owned prerequisite
  modules. The live real row/table raw cores already expose arbitrary output-bit and row maps.
* `WordLists.ofFnTable_poly` and approved `ColMachines.polyTimeComputable_flatMap_range`
  cover indexed encoded output and flat output loops; no new traversal machine is needed.
* `FunFamily.ofFn_blocks_symm` in Asymptotic/OneWay.lean:380 gives the exact canonical
  flat-tuple/flattened-block identity. `FunFamily.blocks_symm_apply` reads the inverse.
* Also found `EnsembleLemmas.ofFn_blocks_symm` at EnsemblesLemmas.lean:433,
  `MultiMsg.flatMap_ofFn` at FromPRF/ReductionMachine.lean:665, and Mathlib `List.ofFn_mul`.
  The first exact `FunFamily` form is sufficient; no finite-product identity is re-proved.
* `BinArith.polyTimeComputable_mapW` maps without an index, so output-pair swaps requiring
  the corresponding prescribed result bit use canonical indexed lookup with the existing
  word-vector assembler instead of adding an indexed traversal host.

FakeObjects contains new simulated semantic objects, not copies of real Yao definitions.
It reuses `argKeys`, `keyAt`, and the existing assignment enumeration convention.
