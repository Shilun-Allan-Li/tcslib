Completes the three audited Epoch 1 Batch C obligations in `Encoding.lean`, relative to `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. The existing theorem statements and attributions are unchanged; `exists_effectiveMachineCode` and its proof sketch remain byte-identical.

## Targets filled

- [x] `Turing.pairEncode_injective`: a private aligned two-bit parser recovers both components by induction, and equality after parsing proves injectivity, as sketched.
- [x] `Turing.computesFunInTime_pairEncode_diag`: an explicit six-state, zero-work-tape machine follows the audited schedule. Whole-configuration invariants prove completion by `4 * input.length + 5` transitions, including empty input; `ComputesInTime.mono` supplies the stated bound with constant 6.
- [x] `Turing.exists_codeTM`: relabel states with `Fintype.equivFinOfCardEq`, prove action/step/run correspondence, and recover both directions of the time/output equivalence. The tape-count equality is eliminated after destructuring the bundle, avoiding casts in transition proofs.

## New declarations

- [x] All 18 new explicitly declared helpers are private; no new public declaration is exported. In particular, the parser is not exported for the later canonizer fill.

| Private declaration in `Turing` | Purpose |
| --- | --- |
| `pairDecode` | Aligned doubled-bit parser; the separator leaves the suffix unchanged. |
| `pairDecode_pairEncode` | Parser round trip on encoded pairs. |
| `pairDiagTM` | Six-state diagonal-pairing controller. |
| `pairDiagCfg` | Configurations of the zero-work-tape controller. |
| `pairDiag_step` | One controller transition given its scanned input symbol. |
| `pairDiag_inner` | Read the input bit at an interior head position. |
| `pairDiag_right` | Read blank at the right boundary, including empty input. |
| `pairDiag_double` | Doubled-prefix invariant for the first pass. |
| `pairDiag_rewind` | Leftward rewind and return to initial input position. |
| `pairDiag_copy` | Prefix invariant for the second pass. |
| `pairDiag_separator` | Two separator emissions and the first unconditional left move. |
| `pairDiag_run` | Complete halted configuration by the audited time bound. |
| `codeMapAction` | Map only an action's successor state. |
| `codeMapCfg` | Map only a configuration's optional state. |
| `codeMapCfg_apply` | Action application commutes with state mapping. |
| `codeRelabelTM` | Transport a transition table through a state equivalence. |
| `codeRelabel_step` | Step commutation, including absorbing halting. |
| `codeRelabel_run` | Initialized run correspondence at every time. |

## Requested shared lemmas

- [x] At epoch merge, consider placing the generic state-renaming support in a non-vendored shared module: make the existing `Oracle.lean` action-state mapping available there, and share configuration mapping, action/step commutation, and run correspondence. This batch keeps `codeMapAction`, `codeMapCfg`, `codeMapCfg_apply`, `codeRelabelTM`, `codeRelabel_step`, and `codeRelabel_run` private to honor file ownership. Neither vendored file is edited.

## Escalations

- [x] None concerning theorem statements or proof obligations.

## Documentation and statement freeze

The only existing docstring change is an appended implementation note on `exists_codeTM`, identifying the private action mapper, elimination of the tape-count equality, and use of `runFrom_comm_of_step`. All existing proof sketches are retained. A comment-stripped comparison checked all 18 pre-existing declaration headers; none changed.

## Verification

- [x] Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- [x] Dependency-order bootstrap and repeated `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Encoding` checks completed. The final full sweep checked all 22 modules from `scripts/ab_ch1_module_order.txt`, including Universal, all Uncomputability files, and the facades: zero `error:` lines.
- [x] Exactly 18 remaining `sorry` warnings, all at declarations listed as out of scope in the brief. `Encoding.lean` has one, at `exists_effectiveMachineCode`. Its isolated check has no other warnings. The full sweep also reports three pre-existing linter warnings in frozen `Configuration.lean`.
- [x] A temporary `#print axioms` check showed no `sorryAx` dependency in any filled theorem. The temporary commands are absent from the final source.
- [x] `git diff --check` passes; the diff touches only `TCSlib/Complexity/TuringMachine/Encoding.lean`.

Verification used only the authorized direct-Lean script; `lake build` was never run. The environment required an executable-path compatibility shim mapping the running process's `/proc/<its-pid>/exe` lookup to `/proc/self/exe`; the pinned Lean binaries and sources were unchanged. After the initial full-cache attempt, a task-local cache download populated all direct imports and their transitive dependencies.

Elaborated axiom evidence:

```text
'Turing.pairEncode_injective' depends on axioms: [propext, Quot.sound]
'Turing.computesFunInTime_pairEncode_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_codeTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final full-sweep log tail:

```text
TCSlib/Complexity/ClassP/TimeConstructible.lean:85:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'


TCSlib/Complexity/ClassP/Examples.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:454:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:124:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:148:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Computable.lean:64:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Diagonalization.lean:98:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Halting.lean:139:8: warning: declaration uses 'sorry'



Full sweep: 22/22 modules checked.
```

