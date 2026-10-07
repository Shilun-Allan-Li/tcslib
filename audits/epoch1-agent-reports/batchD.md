This fills the two audited machine-construction proofs assigned by `briefs/epoch1-batchD.md`, based on `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. Both machines are explicit finite one-work-tape machines, with complete run invariants and all-length bounds.

## Targets filled

- [x] `Complexity.PAL_mem_DTIME_linear`: follows the audited copy/rewind/test construction, including all boundary transitions and early rejection; establishes the budget `3 * (n + 1)`, including the three-step accepting empty-input run.
- [x] `Complexity.timeConstructible_id`: follows the reaudit's four-state count/carry/rewind/emit table. Uses the **potential route**: `elapsed + 2 * popcount(i) ≤ 4 * i`. An increment with `r` initial true bits costs exactly `2 * r + 2`, while the potential changes by `2 - 2 * r`. Final emission writes exactly `Nat.bits n` and yields `5 * (n + 1)` total budget; empty input emits `[]` and halts in two steps.

The original theorem statements, names, hypotheses, imports, option headers, and `[AB09 …]` attributions are unchanged. Existing docstrings are retained. The only update to an existing docstring appends the explicit potential and `c = 5` calculation to `timeConstructible_id`'s proof sketch; neither construction deviates from its audited transition table.

## New declarations

- [x] All **35** new explicit declarations are private, in namespace `Complexity`; no new public declarations.

`TCSlib/Complexity/ClassP/Examples.lean` (15):

`palTM`, `palTape`, `palCfg`, `palTape_write`, `pal_copy_step`, `pal_copy`, `pal_copy_end`, `pal_rewind_step`, `pal_rewind`, `pal_test_start`, `pal_test_read`, `pal_test_step`, `palMatches`, `palMatches_succ`, `pal_test`.

`TCSlib/Complexity/ClassP/TimeConstructible.lean` (20):

`counterInc`, `counterCarry`, `counterInc_potential`, `counterInc_bits`, `counterInc_length`, `counter_bits_length`, `counterBump`, `counterTM`, `counterTape`, `counterCfg`, `counterTape_read`, `counterTape_write`, `counter_carry_step`, `counter_carry`, `counter_rewind`, `counter_start`, `counter_increment`, `counter_count`, `counter_emit_run`, `counter_emit`.

Standalone arithmetic/list lemmas worth considering for later promotion are `counterInc_potential` (the local carry/popcount identity), `counterInc_bits` (exact compatibility with `Nat.bits`), `counterInc_length`, and `counter_bits_length`. The tape representation and its read/write lemmas remain private to this construction.

## Requested shared lemmas

- [x] None required. No shared or vendored file was modified.

## Escalations

- [x] None. Both targets were proved as stated.

## Verification

- [x] Direct Lean checks after proof edits, using `scripts/lean_check_tree.sh`; both owned files now produce no warnings or errors.
- [x] Final complete sweep over all 22 modules in `scripts/ab_ch1_module_order.txt`, including every later module: **zero `error:` lines**. All 19 remaining `sorry` warnings correspond to the brief's untouched out-of-scope declarations.
- [x] `#print axioms` for both completed targets reports only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, additional axiom, or unchecked proof dependency.
- [x] Existing declaration headers compared byte-for-byte with the pinned base; unchanged. `git diff --check` passes.
- [x] Diff touches only the two owned files: `Examples.lean` and `TimeConstructible.lean`.

Toolchain: official Lean 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Dependency setup started with `lake exe cache get`; the cache download was narrowed to the chapter's exact imports and unpacked after a concurrent cache process removed the shared curl configuration. No dependency source was changed. The container needed a local executable-path compatibility shim: only the current process's `/proc/<pid>/exe` lookup is redirected to `/proc/self/exe`, because its PID namespace and mounted procfs differ. Lean's compiler, kernel, and library binaries were not modified. Verification used the designated direct-`lean` script, never a repository `lake build` command.

Final sweep command:

```bash
while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt
```

Final full-sweep log tail:

```text


TCSlib/Complexity/TuringMachine/Composition.lean:162:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:179:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:201:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:249:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:275:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:68:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean:76:8: warning: declaration uses 'sorry'


TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'



TCSlib/Complexity/TuringMachine/Encoding.lean:117:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:137:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:252:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:265:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:124:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:148:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Computable.lean:64:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Diagonalization.lean:98:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Halting.lean:139:8: warning: declaration uses 'sorry'
```
