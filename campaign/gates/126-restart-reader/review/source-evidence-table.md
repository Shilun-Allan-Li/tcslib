## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `4c94bbe6651470bfd241f16f77c90d9171c5ecd3` Git blob; SHA256 `d3ceb7ca08b1e7adad821127e3dcefd3135599e8fb798d718cec4935ea751a3f` | `source/BASE/TCSlib/Complexity/TuringMachine/UniversalK.lean.txt` |
| HEAD owner | `f259e781e3abe3d7768c564f3614267ca891389c` Git blob; SHA256 `5f1f0757335087b8bfd08da9fc6b7445bccb6033024e36746a33d3d82b09b032` | `source/HEAD/TCSlib/Complexity/TuringMachine/UniversalK.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 3 roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same33 source files at each side; no capped listing | `screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |
| style-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-style-lint.txt`, `qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-campaign-lint.txt`, `qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-sizes.json`, `qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `evidence-inputs.json` and uncapped copied `inputs/` |
| New screen pairs | PREPARING until completed HEAD minus BASE comparison and every row disposition | ROOT-TO-BIND; no zero-new-pair inference |
| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |

