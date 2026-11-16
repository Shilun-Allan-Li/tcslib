# Final publication review

PASS: the Garbling change is exactly one documentation paragraph. All14 full declarations (13public,1private), their order, headers and bodies are byte-identical; every source byte outside gateOut_small's docstring is identical. The diff is5insertions/1deletion,398→402lines. The normalized noncomment code is identical.

The sketch accurately describes the proof: split the gate argument list into zero, one, two, or at least three entries; compute each gate kind via gateOut_eq_eval/DAGGate.eval_eq (plus List.range_succ); exclude the last case using hfan and omega.

Counting qualification: gateOut_small has15 proof-body lines including the :=by marker and14 tactic lines after it. The existing lexer cuts at Boolean || in the TYPE, so the publication audit's17candidate lines include type continuation. The added sketch remains appropriate and accurate. Decryption.nestedDecTagged_eq is a separate false positive: four statement-level lets span the type, while its only proof term is rfl. No change to that declaration is needed.

## Public abbreviation readers

All11 public abbreviations have a public same-file equation theorem with body rfl and a docstring. ChunkScanner.Phase intentionally uses lowercase phase_eq (line144), whose equation is Phase=(Bool×Bool×Bool).

| Module | Abbreviation | Reader | Reader line |
|---|---|---|---:|
| ChunkScanner | `Phase` | `phase_eq` | 144 |
| CoinRelabel | `Blocks` | `Blocks_eq` | 53 |
| NonceCoordinates | `Index` | `Index_eq` | 45 |
| SeedCoordinates | `Permutations` | `Permutations_eq` | 43 |
| SeedCoordinates | `Index` | `Index_eq` | 52 |
| SeedCoordinates | `ChallengeIndex` | `ChallengeIndex_eq` | 59 |
| SeedCoordinates | `Data` | `Data_eq` | 67 |
| SelectedStepChoices | `Selection` | `Selection_eq` | 47 |
| SelectedStepChoices | `Tape` | `Tape_eq` | 67 |
| SelectedStepChoices | `Choice` | `Choice_eq` | 76 |
| TapeValues | `Rest` | `Rest_eq` | 181 |

## Generated reader attributes

All3 simps attributes explicitly use `(config := { isSimp := false })`. No explicit simp attribute occurs in the helper code.

| Module | Definition | Attribute line |
|---|---|---:|
| CoordinateSwap | `swap` | 45 |
| CoordinateSwap | `equiv` | 89 |
| FakeSimulator | `Data.make` | 144 |

This report runs no Lean, edits no proof source, and certifies only the static publication repair. The lead's current-source4Garbling seals, full current261module sweep and stored-constant trace remain distinct required evidence. Full equations, attributes, source hashes, the exact diff and parser qualifications are in REVIEW.json and companion files.
