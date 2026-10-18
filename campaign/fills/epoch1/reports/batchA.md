The audited phase-3/4 interfaces had not yet been checked together in the four Batch A assembly proofs. This PR fills those proofs using the stated normalization, coding, evaluator, and guarded-composition interfaces.

Base: `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. Head: `fill/epoch1-A`.

- [x] **Targets filled (4).**
  - `Turing.FinTM.Computes.exists_computesFunInTime`: follows the sketch, choosing halting times and taking their `Finset.univ.sup` over `List.Vector Symbol n`, then applying `ComputesInTime.mono`. No positivity, monotonicity, or nonempty-alphabet assumption is added.
  - `Complexity.UC_not_computable`: follows the audit derivation through binary one-work-tape normalization, `exists_codeTM`, `decode_encode`, and the two Boolean cases using output uniqueness. The statement still covers arbitrary `MachineCode`.
  - `Turing.universal_quadratic`: follows the sketch with one universal-machine witness, the normal-form code, only the forward evaluator clause, and the in-repo constant-absorption calculation.
  - `Complexity.UC_computable_of_HALT_computable`: follows the audit construction with three partial compositions, the fixed-word postprocessor, the constant branch, and `exists_cond`. The positive HALT witness justifies the forward evaluator clause; no totality of the evaluator or converse evaluator clause is used.
- [x] **New declarations added:** exactly one private helper, `Complexity.halts_iff_eq_of_computes`, in `Halting.lean`; no new public declarations. Its complete signature is below for audit restatement.
- [x] **Requested shared lemmas:** at epoch integration, consider moving the generic completed-output lemma below into `Finite.lean`, e.g. as `Turing.FinTM.Computes.halts_iff_eq`. This PR keeps its copy private in its owned file and does not edit the shared file.
- [x] **Escalations:** none.
- [x] **Verification evidence:** all 22 modules in `scripts/ab_ch1_module_order.txt` passed the final direct-`lean` sweep, with zero `error:` lines and exactly the 17 stipulated out-of-scope `declaration uses 'sorry'` warnings. Each edited module and every later module were rechecked during iteration. The final complete per-module log is included below.
- [x] **Diff touches only the owned files:** `Uncomputability/{Computable,Diagonalization,Halting}.lean` and only the `universal_quadratic` proof in `TuringMachine/Universal.lean`. All pre-existing statements, hypotheses, names, options, attributions, and docstrings are retained. The only removed lines are the four target `sorry`s. No new `sorry`, axiom, or admission was introduced. `git diff --check` passes.

```lean
private theorem halts_iff_eq_of_computes {Symbol : Type} {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x
```

All four delivered proofs match their existing sketches; no docstring updates were needed. As intended by the brief, they retain dependencies on the unfilled construction theorems. The full-sweep warning locations were checked against the brief's exact set of 17 declarations. The other three warnings are unchanged style/unused-variable warnings in the unowned `Configuration.lean`, also shown below.

Verification environment: Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, and the unchanged repository manifest. The full cache download was narrowed to the 15 Mathlib roots imported by this sweep and their transitive dependencies (876 cache files). All TCSlib checks used the prescribed `scripts/lean_check_tree.sh`; no `lake build` was used to check TCSlib. The cloud runner exposes a procfs/PID-namespace mismatch, so a local, out-of-repository compatibility shim maps only `readlink("/proc/<own getpid()>/exe", ...)` to the equivalent `/proc/self/exe`; no Lean binary, proof checker, dependency source, or repository script was modified. Cache archive extraction used `TAR_OPTIONS=--no-same-owner` for the runner's UID mapping. Each scratch `.olean` was removed before its check and required to be regenerated successfully.

Verified source commit: `3d1a82c9cb6dad4ca348a3d7cfc07f37da3e05cd`.

Final full-sweep log (exit 0; zero `error:` lines; 22 modules; 17 expected sorry warnings):

```text
[check] TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[check] TCSlib/Complexity/TuringMachine/Deterministic

[check] TCSlib/Complexity/TuringMachine/Finite

[check] TCSlib/Complexity/TuringMachine/Oracle

[check] TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Composition.lean:162:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:179:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:201:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:249:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:275:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:69:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:68:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean:76:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/ClassP/DTIME

[check] TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/ClassP/TimeConstructible.lean:85:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/ClassP/P

[check] TCSlib/Complexity/ClassP/ModelInvariance

[check] TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/ClassP/Examples.lean:69:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/Encoding.lean:117:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:137:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:252:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:265:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:165:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/Uncomputability/Computable

[check] TCSlib/Complexity/Uncomputability/Diagonalization

[check] TCSlib/Complexity/Uncomputability/Halting

[check] TCSlib/Complexity/TuringMachine

[check] TCSlib/Complexity/ClassP

[check] TCSlib/Complexity/Uncomputability
```
