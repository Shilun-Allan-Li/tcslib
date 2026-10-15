# Retrofit RB2 report

**Status: partial delivery under the brief's escalation rule.** Task 1 and Task 3
are complete. Task 2's length swap is complete; the inverse swap is complete at
all three private use sites, but its declaration and one frozen public use must
remain. Task 4 was not attempted. No admissions were introduced.

## Base and commit series

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `5588628cbbddea9546f616907364b608e15557fd`.
- Working branch: `fill/retrofit-rb2`.
- The brief was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`;
  the cloned branch was at the recorded base. The owned source is byte-identical
  between these two commits. No rebase, push, or PR was performed.
- Only `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` is changed in the commit series. Reports and evidence are
  delivery artifacts outside the repository.

```text
f2d1ad365091f7a6ce75708d0f97187e513fbfbd Retrofit RB2: delete 62 dead emitter and split-search privates
de1036e6a3eddd870ba99b16ee069558d86b7113 Retrofit RB2: reuse Encoding lemmas within freeze and refresh status notes
```

## Task 1: 62/62 deletions confirmed

Commit 1 deletes every listed private and its own docstring. The fresh Lean
check succeeds after deletion; no member required restoration and no unexpected
referencer was found. All other declarations, including the six private
instances, are byte-identical. Exactly 1,222 source lines were removed.

- **F24a eval (6):** `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`, `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- **F24b clear (13):** `emitterInterval`, `emitterCleared`, `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`, `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`, `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`, `emitter_clear_run`, `emitter_clear_first`.
- **F24c track (18):** `emitterSpan`, `emitter_span_extend`, `emitterSlots`, `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`, `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`, `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`, `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`, `emitter_span_interval`, `emitter_track_clearable`.
- **F24d bank (11):** `emitterBankSymbols`, `emitterBankPart`, `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`, `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`, `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- **F24e right (9):** `emitterRightTM`, `emitterRightCfg`, `emitter_right_step`, `emitter_right_run`, `emitterRightScan`, `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`, `emitter_right_computes`.
- **F24f eval closers (2):** `emitter_prepared_eval_first`, `emitter_width_eval_first`.
- **Split orphans (3):** `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`.

## Task 2: Encoding replacements and escalation

`catalogPair_length` and its docstring are deleted. Its one use is repointed to
`Turing.length_pairEncode`. All three private uses of `catalogPair_inverse` are
repointed to `Turing.eq_pairEncode_of_pairDecode`.

| Containing private declaration | Final source line | Repointed use |
|---|---:|---|
| `catalogPayload_length` | 2068 | `have hx := Turing.eq_pairEncode_of_pairDecode x a b hd` |
| `pairMap_computes` | 2701 | `(by simpa using Turing.eq_pairEncode_of_pairDecode x a b hd)` |
| `pairMap_computes` | 2721 | `rw [Turing.eq_pairEncode_of_pairDecode x a b hd, Turing.length_pairEncode]` |

**Escalation RB2-E1 — conflicting requirements.** The task requests deletion of
`catalogPair_inverse`, but binding ground rule 1 requires every public proof
body to remain byte-identical, except for the optional `splitSolve` change.
The public proof of `computesFunInTime_stripLast` contains this live reference
at original line 2880 / final line 2872:

```lean
          rw [catalogPair_inverse x u v hd]
```

The public Encoding theorem has the same explicit argument shape, so replacing
that line with the following would complete the use-site swap, but would
violate the public-body freeze:

```lean
          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
```

Following the escalation rule, that line and the complete original
`catalogPair_inverse` declaration/docstring (final line 2014) are
retained unchanged. It has exactly this one remaining code use. Completing
Task 2 requires an explicit exception for this public-body identifier change;
then the retained private can be deleted. No compatibility alias, new private,
notation, signature change, or import was introduced to work around the freeze.

## Task 3: exactly the three authorized comment blocks

Only the named module-note region (original lines 67–110) and the section notes
at original lines 4419–4439 and 5956–5959 were rewritten. The module-note region
now reads:

```text
**Implementation note (batch P).** The first eleven targets in the batch
brief's fill order and the four continuation targets `pairLenCheck`,
`stripLast`, `pairMapSnd`, and `splitSolve` are proved. The original spec-phase
prose above and on the contracts is retained as the audit record. The length
counter is obtained from the public `Complexity.timeConstructible_id`, whose
proved machine implements precisely the sketched amortized counter. The three
extractors share one private buffered parser, so suffix-only extraction also
buffers and replays silently before copying the suffix; its linear envelope
is unchanged. The fixed-width incrementer adapts the enumerator's carry
semantics to two native-input scans, validating before physical emission.


**Implementation note (batch P2).** The threaded length checker, marker stripper,
threaded map, and split search are proved. The length checker composes the existing
buffered first extractor with the unary generator, captures the result with
`capture_run`, then reparses and counts down on the native payload. Malformed
inputs emit only `[false]`. The marker stripper first guards on a valid
extracted suffix containing a true bit; the successful branch buffers the
whole original encoding, erases its final marker/false-run, and replays the
retained encoding. The guard is complete before any physical output. Both
routes reuse the in-file parser/scan invariant patterns and proved public
wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
component for the threaded map, with its time evaluated at the actual suffix
length; the retained-prefix/captured-output controller is proved below.


**Implementation note (batch P3).** The threaded map is proved.
`pairMapTM` captures `catalogPayload_computes` on the original physical input,
rewinds the capture and input, validates without emission, then replays the
original encoded prefix and captured result. `pairMap_computes` bounds this
controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
All original contract docstrings are retained as the audit record.

The split-search theorem is proved. Its private components include the unary
orbit/search bridges and
`splitSolve_of_body`, which closes the public result only when supplied the
actual startup and round contracts; a candidate-preserving unary-bank
preparer; a counted source-simulation correspondence; the generator's exact
loop endpoint; and a scratch-restoration controller with a positive first
return and no earlier visit to its return state. The combined `splitBodyTM`
and `splitBody_round` assemble these components and prove `hround`.
```

The two section notes now read:

```lean
/-! Emitter implementation. The append-bit and unary-token contracts are
proved below with coefficients one and three. The width-parametric split
contract is proved by the native `emitterP2*` controller.

The `emitterSplit*` layer generalizes the in-file loop closure without any
monotonicity assumption on the width function. The `emitterCompare*` family
is reimplemented in this file from the A-continuation's `e3c*` templates in
`ClassNP/Nondeterminism.lean` at base d7b5b6f94d28df8095165dd4dfe82fd09ba0d414.
Those originals are unchanged and are not cited as imported privates. The
native accepting emitter is `splitEmitTM`/`splitEmit_run`. The controller below
discharges `emitterSplit_of_body`'s literal configuration and strict-interior
anchor contracts. -/
```

```lean
/-! **Emitter P2 implementation.** The controller below proves the
width-parametric split contract. Its generic relocation layer is reimplemented
from batch L's `emCall` family in `Build/Loop.lean`, per the private-harvest
policy. It preserves inactive storage and follows observed returns, including
the mandatory first action when entry equals exit. -/
```

All surviving declaration docstrings and all other comments are unchanged.

## Task 4 and scope

**Not attempted.** This stretch is optional and the brief allows it only after
Tasks 1–3 are delivery-ready. The mandatory inverse swap remains escalated.
No new proof route or constant was introduced; `computesFunInTime_splitSolve`
is byte-identical, including its proof body. No additional private was deleted.
The complete F25a `emitterCompare*` and F27a `emitterP2Erase*` families are
unchanged. No import changed; Primitives does not import Catalog.

## Freeze, duplication, and size

- **Duplication ledger: new copies: none.** The existing inverse-lemma copy
  remains solely because of RB2-E1; it was not changed or copied elsewhere.
- New private declarations: **0**.
- Public declarations: **18 before / 18 after**, in the same order, with each
  complete declaration (docstring, signature, statement, and proof body)
  byte-identical. Six private instances are also byte-identical.
- Private declarations: **318 before / 256 after commit 1 / 255 final**.
- Source lines: **7,636 before / 6,414 after commit 1 / 6,398 final**.
- Comment/string-stripped source has zero `sorry`, `admit`, `axiom`, or
  `native_decide` tokens, both before and after.
- Source SHA-256, base: `72bf7361024c351f3ad9e1ba61106a8376638612769205d50f904184a340205d`.
- Source SHA-256, final: `f04e55a189047d1b061cd0ce4993df84c7959cf0e254f37ac9c9ff339aa5f68f`.
- Repository diff paths: exactly `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`. Final working tree: clean.

## Verification

Pinned Lean is v4.25.0, release commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib is
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
No `lake build` command was run.

The initial cache setup encountered unsupported archive ownership restoration;
it was retried with `TAR_OPTIONS=--no-same-owner`. The full-mathlib download was
stopped after 759 successful files and narrowed to the exact mathlib imports
of the bootstrap dependency closure. The successful `lake exe cache get`
invocation downloaded 847 additional required archives and unpacked all 969
needed module archives. Setup did not change dependency revisions or tracked
repository files. Setup logs and the exact root list are included.

All 65 modules in `scripts/ab_ch1_module_order.txt` were successfully elaborated
in the listed order into a fresh local olean tree, with exit 0 and zero error
diagnostics. The first runner became unavailable after 50 successful checks,
without a completed `Hardness` result or olean. The sweep resumed at that
unfinished module; none of the 50 completed checks was repeated. From that
point, an external launcher selects the stock Lean binary's `-j 1` option.
This changes worker count only; the repository check script is unchanged.
One additional baseline finding is the pre-existing admission in
`TuringMachine/CounterProgRun.lean`, `Complexity.CounterProg.sim_run_of_regs_le`
(declaration at line 343, `sorry` at line 346). The repository check exited 0
and produced a fresh olean, but the extra zero-sorry wrapper initially flagged
it. After confirming the unchanged source, the module was rechecked as an
explicit out-of-scope baseline admission. The raw log preserves both attempts
and the original wrapper failure; its two warning occurrences concern this
same existing declaration. Every other module on the 65-item list is
zero-sorry. No such exception is allowed for the owned file or final checks.
The current facades additionally require six modules absent from
that older order list: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`,
`Formulas/QBF`, and `Formulas/QBFEncoding`. These were compiled just before
their first use, with separate supplemental logs. The latter three each have
one existing out-of-scope chapter-3/4 admission. Thus the complete bootstrap
dependency closure has four existing admitted declarations, including the
counter-program row. None is new, none is in Primitives, and none occurs in
any of the 18 checked public axiom footprints. These are baseline facts, not
retrofit admissions or edits.

The changed file was checked before and after each commit. The initial second
post-commit runner ended without a completed result or olean; the exact same
committed source was rechecked in an isolated invocation. The interrupted log
is retained as `evidence/task23-postcommit-interrupted.log`. The completed
checks are:

```text
task1-precommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=91.9
task1-postcommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=129.4
task23-precommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.9
task23-postcommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.3
```

The final required sweep uses the final post-commit Primitives check as its
first check, immediately followed by the TuringMachine facade check. No source
changed between them. Both produced fresh oleans with zero errors and zero
sorry warnings; the full combined log is included:

```text
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6217:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6220:6: warning: 'simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6220:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6271:63: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.3

$ bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=9.3
```

Style lint command:
`python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`.
Result: **style_lint: 0 FAIL, 3 WARN over 7 files**. The three inherited size warnings concern files outside
the allowed splitting scope; this retrofit reduces Primitives by 1,238 lines.

All 18 final axiom footprints are identical to their separately printed
baseline footprints and use only the permitted standard axioms; no `sorryAx`:

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolveWith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_unaryToken' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_appendBit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The environment needs a self-executable lookup compatibility shim: stock
processes cannot resolve `/proc/<their numeric pid>/exe`, while
`/proc/self/exe` works. The external `LD_PRELOAD` shim only maps that exact
current-process path to `/proc/self/exe`. Its source is supplied in
`evidence/environment/self_exe.c`. It changes no kernel, proof term, toolchain
source, repository source, or axiom. It is unnecessary on a normal system.

## Archive contents and integration

The archive contains `REPORT.md`, the full modified source under its repository
path, two ordered `git format-patch` patches, an incremental git bundle against
the recorded base, `final-sweep.log`, `axioms.log`, supplemental verification
evidence, and `SHA256SUMS`. Apply the two patches to the recorded base, in
order, or fetch the supplied bundle. The bundle requires that base commit.
RB2-E1 remains an explicit uncompleted mandatory item; this archive does not
claim full completion of Tasks 1–3.
