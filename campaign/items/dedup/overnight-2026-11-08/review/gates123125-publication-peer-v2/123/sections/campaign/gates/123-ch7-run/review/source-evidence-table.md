## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `3ac162843c4363e2c31082efa4b66408fd184ce8` Git blob; SHA256 `1a7d25619fb88b51d012e48fb66b758ce08c199e7d3aad219c25f18a7e741b4d` | `source/BASE/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| HEAD owner | `188fdc7b1776e0141bcbf29bc088d06628ec6539` Git blob; SHA256 `b9014e1a466ec3a57207f01decce39f75d41dec30f522cc0ca3c4ba53c3f3cbd` | `source/HEAD/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 5 roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same33 source files at each side; no capped listing | `screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |
| style-lint.txt | Byte-identical BASE/HEAD outputs | `qa/BASE-style-lint.txt`, `qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-campaign-lint.txt`, `qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `qa/BASE-sizes.json`, `qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `evidence-inputs.json` and uncapped copied `inputs/` |
| New screen pairs | Exact completed comparison: 2,107 → 2,105; zero new, two BASE-only dispositioned | `screen/pair-delta.json`, `screen/pair-dispositions.json` |
| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |

