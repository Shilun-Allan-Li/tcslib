## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `433d0ce6e17ed264f0d7f650a8692d4da4744b4f` Git blob; SHA256 `5edd51e6190c39240edf2ddabeeb841ff03b8d00b31a3288cfa02cff31a393d0` | `source/BASE/TCSlib/Complexity/CookLevin/Hardness.lean.txt` |
| HEAD owner | `fbefdf84f456f96fdef04753ecc253f92f0661da` Git blob; SHA256 `422042d604d9bee9fb5e8c12827cb1ae046eb48a3a448bc47f38418dd7017cbc` | `source/HEAD/TCSlib/Complexity/CookLevin/Hardness.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 2 roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same33 source files at each side; no capped listing | `screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |
| style-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-style-lint.txt`, `qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-campaign-lint.txt`, `qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-sizes.json`, `qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `evidence-inputs.json` and uncapped copied `inputs/` |
| New screen pairs | PREPARING until completed HEAD minus BASE comparison and every row disposition | ROOT-TO-BIND; no zero-new-pair inference |
| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |

