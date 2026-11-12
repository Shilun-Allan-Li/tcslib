## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `123a5538616a3456ac3bcc2c7c4b67abdc3f4eea` Git blob; SHA256 `57e7dc52dedf3d146499ad5694270d1c6fee7255cad74338d4174c5cce3e1a73` | `source/BASE/TCSlib/Complexity/TuringMachine/CodeSimulator.lean.txt` |
| HEAD owner | `cf207e1467eb90836f13c784fbffba8fd509bf67` Git blob; SHA256 `33c27b4177ce01aa941fec28b0e3bb095fc51a03d90359671c7ae801b6f8793c` | `source/HEAD/TCSlib/Complexity/TuringMachine/CodeSimulator.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 1 roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same33 source files at each side; no capped listing | `screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |
| style-lint.txt | Byte-identical BASE/HEAD outputs | `qa/BASE-style-lint.txt`, `qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Byte-identical BASE/HEAD outputs | `qa/BASE-campaign-lint.txt`, `qa/HEAD-campaign-lint.txt` |
| sizes.json | Byte-identical BASE/HEAD outputs | `qa/BASE-sizes.json`, `qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `evidence-inputs.json` and uncapped copied `inputs/` |
| New screen pairs | PREPARING until completed HEAD minus BASE comparison and every row disposition | ROOT-TO-BIND; no zero-new-pair inference |
| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |

