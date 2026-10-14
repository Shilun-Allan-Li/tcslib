# W1 record tables — continuation, partial delivery

**1 of the 7 requested rows is newly proved: `Turing.exists_fieldsCopyTM`.**
The file now has **14 of 20 original targets proved**, plus the inherited derived
record-length corollary. All four new private lemmas are proved without admissions.
Append has a proved reverse copier and seek-and-copy prefix; its suffix and return
phases remain unfinished. Table find has a confirmed universe mismatch in its mandated
infrastructure. The other four record-machine rows remain admitted.

This is a ground-rule-9 partial continuation. No unfinished public row is presented as
proved, no admission was moved into a private helper, and no completed result is proved
modulo an admission.

## Base and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch: `complexity/arora-barak-ch3-4`.
- Base: `ae9e0af5b7e5b6fdd1330920cb408923562391c7`.
- Required ancestor: `820d23121a5847808d079f26bfe7efe0aee36ca3`.
- The required ancestor check returned exit 0 before proof work. The initial clone
  selected the exact campaign branch; the working branch is `fill/w1-recordtable-cont`.
- The previous delivery's report and its continuation frontier were read before any
  Lean was written, together with the original brief and binding design/audit guidance.
- Only tracked file changed: `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean`.
- Delivery commit: `945183c3d827b2025773b209eb08746212a3017e` (one local commit).
- No rebase, push, or PR.

The commits between the required ancestor and the base change only the campaign plan
and continuation briefs. They change no Lean source or verification/screen population.
The baseline sweep reports the expected **17** admitted declarations, with no parallel
fill difference. `logs/base-check.log`, `logs/base-sorries.txt`, and
`logs/bootstrap.log` record this baseline.

## Target status

| Row | Target (`Turing.` prefix) | Status |
|---|---|---|
| 14 | `exists_fieldsCopyTM` | **Proved**, all field counts and arbitrary tape-alphabet universes |
| 15 | `exists_tableFindTM` | Admitted; mandated-loop universe mismatch escalated below |
| 16 | `exists_tableAppendTM` | Admitted; reverse copy and complete seek-and-copy prefix proved |
| 17 | `exists_recordTemplateTM` | Admitted; original sketch retained |
| 18 | `exists_recordInitTM` | Admitted; original sketch retained |
| 19 | `exists_recordValidTM` | Admitted; original sketch retained |
| 20 | `exists_recordNextTM` | Admitted; original sketch retained |

The first thirteen target bodies, all nine inherited private declarations, every other
landed declaration, and all four imports are unchanged with comments stripped. All 28
public names, their order, and their signatures are unchanged. The six unfinished rows
are the only direct admissions in the file; each retains its original literal
“Proof sketch”. **Private helpers remaining `sorry`: none. Proved-modulo targets: none.**

## New declarations

| Private declaration | Role |
|---|---|
| `rt_copy_seam` | Bundles the public R2 endpoint, first-return, and visited-set contracts. Transfers a common head interval by the public union-of-visited-sets inclusion; no seam trace is re-proved. |
| `rt_copy_run` | Proves the frozen `rt_copyMachine` contract for every field count by strong induction, citing `rt_copy_run_base` for zero/one field. |
| `rt_fieldsCopy_reverse` | Uses `exists_fieldsCopyTM` and the public R1 embedding to copy from tape 1 onto tape 0. It transports the run at every time and transfers the exact frame, first-return cut, and head bounds. |
| `rt_append_copy` | Proves an existential seek-and-copy prefix for append, including its exact tape update, destination-head location at the old second trailing blank, first-return cut, and linear time/head bounds. |

All four have axiom closures contained in `propext`, `Classical.choice`, and `Quot.sound`.
`rt_copy_seam` and the tape-permutation transport in `rt_fieldsCopy_reverse` are shared
promotion candidates; they are private here as ownership requires. The former packages
existing public contracts; the latter transports an existing proved copier. Neither
introduces a second host, scanner, or copy trace.

## Copier proof and the inherited time correction

The inductive step uses the frozen controller in its specified order: copy the first
field, skip it on both tapes, copy the nonempty tail, and skip back on both tapes.
It intercepts every exit. The destination write proof handles the first field, the
blank separator, the tail, and the exterior frame separately, citing the existing
field-layout lemmas. The space proof composes the actual phase visited sets through R2.

The previous frontier's proposed exact additive constant **17** was two too large.
The six catalog phase times and five stationary dispatches sum to the tail time plus
**`6 * u.length + 15`**. Increasing the tail's linear constant by 20 still suffices.
This changes no frozen statement or machine. The executed continuation probe checks a
two-field example's exact first-return time **27**, including all earlier times, at
displaced heads. This is stronger than merely checking the exit state after arrival.

## Escalation: row 15's mandatory loop is universe-restricted

`exists_tableFindTM` quantifies over **`Γ : Type u`**. Its binding route requires
`counterLoopTMVia`, whose alphabet parameter is **`Γ : Type`**. The corresponding rich
loop run contracts have the same restriction. Direct application therefore cannot
instantiate the mandated loop at the frozen target's general alphabet universe.

`verification/FindUniverseProbe.lean` reproduces the mismatch with the minimal attempted
application, checked through `scripts/lean_check_tree.sh`. The relevant diagnostic is:

```text
Application type mismatch: The argument
  Γ
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
```

The same application with `Γ : Type` checks successfully in
`verification/FindUniverseZeroProbe.lean`. Thus this is an infrastructure-composition
obstruction, **not a counterexample to the existence statement**. Ground rule 4 requires
stopping on this item; ground rules 1, 2, and 7 forbid changing the shared loop, weakening
the target, or building a replacement loop privately. Row 15 was left unchanged, and work
continued with row 16. A discarded universe-zero round prototype is not shipped.

**Requested maintainer repair:** generalize the rich loop and its supporting transport/run
contracts to the alphabet universality needed by the frozen row, with a shared-file gate.
`phaseHostTM` is also currently universe-zero if that host is used for the inner finite
phases. No change to either shared file is included here.

## Continuation frontier

1. Row 14 is complete. Reuse `exists_fieldsCopyTM`; do not rebuild the copier or change
   its inherited state family, machine, anchors, or base contract.
2. Resume row 15 only after resolving the universe mismatch above. Keep the accepted-final-
   field escape before its skip, and use the required rich counter host.
3. Row 16 can consume `rt_append_copy`. Its destination head is exactly at the old second
   trailing blank; the source layout is already copied there. Source tape/head, native
   input position, and output are restored, and all other tape cells are unchanged.
4. For an empty fixed suffix, attach the public old-table rewind directly: its frame stops
   strictly before the current head, so the newly copied current cell is allowed to be
   nonblank. For a nonempty suffix, cross the known number of copied fields with catalog
   skips, write the fixed suffix with the public constant writers and skips, return over
   the known new fields, and invoke the same old-table rewind. Intercept every exit.
5. Prove the final mask equals the extended table layout using the existing layout
   restrictions. Do not assume the new fields are nonempty: append's statement permits
   empty fields, and `TableWF` need not be preserved. Consumers that seek afterward must
   enforce nonempty appended fields themselves.
6. Then fill rows 17–20 in order, along the original binding routes. R8.5c is proved;
   no proved-modulo allowance is needed or used. The increment-plus-overflow-extension,
   digit-tape isolation, finite verdict witnesses, and empty-tag obligations still apply.

The prefix lemma does not assert the full append contract or the extended table's
well-formedness. No proof obligation after the prefix is hidden in an admitted helper.

## Flagged documentation changes

- Module Status: 14 of 20 targets proved; six remaining rows; append prefix progress.
- Main results: field-list copy marked proved; find and append remain statements.
- Row 14 Fill appendix: the complete induction, frame/radius composition, and corrected
  exact additive constant 15.
- Row 16 Fill appendix: the two checked prefix lemmas and the remaining suffix/return
  frontier. The warning about empty appended fields and `TableWF` is preserved.
- No import, attribution, frozen sketch, or public signature change.

## Verification

Final owned-file size: **1,817 lines; 28 public / 13 private declarations**. File size is
reported, not used as a reason to split the file. `logs/freeze-check.log` records the
signature/body/import comparison and sole tracked path; `git diff --check` passes.

All Lean checks use `scripts/lean_check_tree.sh`. No `lake build` was run. Lean is pinned
to 4.25.0, mathlib to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
`lake exe cache get` was attempted; its redundant bulk download was interrupted after
confirming the existing pinned dependency cache was usable. Package-manifest equality and
the mathlib revision were checked. Development checks used matching-source cached upstream
objects; the baseline and final ordered sweeps each used their own freshly emitted olean
tree. Temporary proof work lived outside the owned source until the baseline sweep finished.

Following the previous delivery, checks used its narrow `readlink` compatibility
shim: Lean's lookup of `/proc/<its-own-pid>/exe` is redirected only to `/proc/self/exe`.
`verification/lean-self-exe.c` is included. Neither the Lean kernel/binary nor the check
script is modified. Ordinary environments do not need the shim.

The completed verification summary and duplication results follow below.

### Final Lean gate

The fresh final sweep completed with **exit 0, 85/85 modules, zero errors, and 16
sorry warnings**: the six explicitly unfinished owned rows and the same ten
out-of-scope declarations as the baseline. Exactly `exists_fieldsCopyTM` was removed
from the baseline warning-name set. The fresh owned check reports exactly its six
admissions and no other warnings.

The unchanged out-of-scope admissions are:

| Module | Names |
|---|---|
| `Build/OracleSim` | `FinOracleTM.exists_plain_simulation` |
| `CodeSimulator` | `exists_polyCanonizer`, `exists_uniformSimulator` |
| `Diagonalization/EXPCOM` | `NPOracle_EXPCOM_subset_EXP` |
| `Diagonalization/NTimeHierarchy` | `exists_timed_universal_NDTM`, `exists_ndAcceptsWithin_decider`, `exists_codeNDTM_accepts_linear`, `ntime_hierarchy`, `ntime_hierarchy_of_pos`, `NTIME_linear_ssubset_square` |

`logs/axiom-print.log` prints all twenty original targets and the derived corollary.
All completed declarations have standard axiom closures. Only the six listed unfinished
rows contain `sorryAx`. `logs/private-axioms.log` prints all four added private lemmas;
none contains `sorryAx` or any nonstandard axiom. These probes were rerun on the fresh
final olean tree.

| Executed evidence | Outcome |
|---|---|
| `S128bStatementsProbe.lean`, copied unchanged from the issued probe | Exit 0, no errors/warnings; both last-match and empty-field-append cases preserved |
| `EmptyTagProbe.lean`, retained from the previous delivery | Exit 0, no errors/warnings; empty-tag validity, empty enumeration, computed no branch, and zero-time controller |
| `CopyContinuationProbe.lean` | Exit 0, no errors/warnings; exact copier first return at 27, with restored heads/output |
| `FindUniverseZeroProbe.lean` | Exit 0, no errors/warnings; positive control for the rich-loop application |
| `FindUniverseProbe.lean` | Expected exit 1; the reported universe mismatch is reproduced |

The empty-tag probe is an executed sanity case, not a proof of the still-admitted general
`exists_recordNextTM`. The expected-negative universe probe is separate from the zero-error
85-module sweep and positive evidence gates.

`logs/style-lint.log` ends with `style_lint: 0 FAIL, 8 WARN over 20 files`.
The owned file's size warning is permitted by note 46. The mechanical audit says:

```text
bootstrap.log: 85 modules, 0 errors, 17 sorry warnings
final-sweep.log: 85 modules, 0 errors, 16 sorry warnings
Owned admissions: 6; unchanged out-of-scope admissions: 10
axiom-print.log: expected standard axiom closures; 6 reported unfinished rows
private-axioms.log: expected standard axiom closures; 0 reported unfinished rows
preship-probe.log: no errors or warnings
empty-tag-probe.log: no errors or warnings
CopyContinuationProbe.log: no errors or warnings
FindUniverseZeroProbe.log: no errors or warnings
FindUniverseProbe: expected negative route probe; universe mismatch reproduced
Lint: style_lint: 0 FAIL, 8 WARN over 20 files
Fresh final olean files: 85/85
```

Final sweep tail:

```text
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:326:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/Diagonalization
CHECK TCSlib/Complexity/TuringMachine/Build/InputLength
CHECK TCSlib/Complexity/TuringMachine/Build/RecordTable
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1271:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1545:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1597:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1648:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1706:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1767:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:184:4: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine
```

### Duplication gate

The exact 24-file population is `verification/screen-population.txt`. Both prescribed
full runs use the unchanged `audits/evidence/retrofit/copy-text-screen.py`.

Before (the complete output is `logs/screen-before.txt`, byte-identical to the issued baseline):

```text
declarations screened: 1416; copy pairs (target reproduces >= half of source): 1735; reproduced text: 580,484 chars
```

After (the complete output is `logs/screen-after.txt`):

```text
declarations screened: 1421; copy pairs (target reproduces >= half of source): 1735; reproduced text: 580,484 chars
```

The pair lists are **byte-identical**: zero added, removed, or changed pairs. There are
**no new cross-file pairs** involving the owned file, **no new in-file pairs** to justify,
and no new pair at the 90% threshold. The five additionally screened declarations are
the newly filled public copier and the four private proofs. The inherited seven in-file
pairs remain unchanged. The focused early comparison agrees with the complete after-screen.
**new copies: none.** No duplication exception is requested.

## Delivery and replay

- The full modified source is at its repository-relative path under `TCSlib/`.
- `patches/` contains the one-commit `git format-patch` series against the recorded base.
- `fill-w1-recordtable-cont.bundle` carries the same branch and commit, with the base as
  its prerequisite. `logs/bundle-verify.log` records successful verification.
- The patch applies to a temporary index at the base and produces exactly the delivery
  commit's tree (`logs/patch-check.log`). Integration can use `git am -3`.
- `logs/` includes complete baseline/final sweeps, both screens, their delta, axiom prints,
  probes, lint, freeze/scope checks, and validation summaries. The sole expected-negative
  log is explicitly named above; development drafts and failed intermediate proof logs
  are not part of this delivery.
- `verification/` contains the seven evidence modules, check order, screen population,
  compatibility source, and mechanical verification scripts. To replay the Lean evidence,
  place its `*Probe.lean` files in the repository's temporary `Verification/` directory,
  then invoke `scripts/lean_check_tree.sh Verification/<name>` after the ordered sweep,
  with the same `TCSLIB_OLEANS` directory. `FindUniverseProbe` must fail with the documented
  type mismatch; the other six must pass. The input statement probe is preserved unchanged.
- `SHA256SUMS` covers every other archive member. From the extracted archive root run
  `sha256sum -c SHA256SUMS`.
