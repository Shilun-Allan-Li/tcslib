# W1 record tables — continuation 3, partial delivery

**0 of 2 requested public rows is newly closed.** The file remains at **14 of
20 original targets proved**. This continuation proves the bound-field prefix
for row 17, including fixed-width increment, one-cell overflow extension,
canonical binary output, and transport onto an isolated rich-alphabet digit
bank. It adds **21 private declarations, with no new admissions**. The full
window pipeline and the dependent initial-record constructor remain unfinished.

This is a partial delivery under ground rule 9 of the committed continuation-3
brief. No public admission was moved into a helper. **Private helpers remaining
`sorry`: none. Proved-modulo targets: none.** Neither public row is presented
as proved, and its original explicit admission remains in place.

## Base, branch, and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch: `complexity/arora-barak-ch3-4`, checked out directly; `main`
  was never checked out.
- Base: `9e34c048e9d527744eec87766b385bb1b2ff7a98`.
- Required ancestor: `c0eefa8be8c277777dfecd8d2510d8e57218ce4c`.
  `git merge-base --is-ancestor` succeeded before proof development and was
  checked again by the delivered freeze audit.
- Working branch: `fill/w1-recordtable-cont3`, created directly from that base.
- Delivery commit: `bd5200604e01d98024548219137a8dc8370b560b`.
- Sole tracked changed path:
  `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean`.
- No rebase, push, PR, or change to another branch. The campaign branch still
  points to the recorded base, and the working tree is clean.

The committed brief was read first, followed by its named instructions and
predecessor report. There were no Lean-source differences between the required
ancestor and the actual base. No other batch's work enters the proofs or screen.

## Target status and continuation frontier

| Row | Target (under `Turing`) | Status |
|---|---|---|
| 17 | `exists_recordTemplateTM` | Admitted; the canonical bound-field prefix and isolated digit-bank transport are proved |
| 18 | `exists_recordInitTM` | Admitted; dependent field-by-field constructor not implemented |
| 15, 16, 19, 20 | Paused rows | Entire declarations and docstrings byte-identical to the base |

The remaining work is implementation and composition, not a demonstrated
contradiction in a frozen statement. **Statement or host escalations: none.**
No signature change, new public host, downstream citation, or duplication
exception is requested.

Resume row 17 as follows:

1. Obtain the bound writer from `rt_exists_digitBoundTM` and run it on a clean
   selected bank. Its Boolean source starts at native input position `1`, with
   arbitrary work-head origins and output `[]`; the rich forwarding frame
   supplies the host's prior output. Its exact endpoint contains
   `Nat.bits (|x| + 1)` on selected tape zero and restores all other bank tapes
   and all heads. The statement deliberately presents the initial and final
   configurations through `embedEmitCfg`; it does not assert that an arbitrary
   rich selected tape is a Boolean lift.
2. Connect that endpoint to the destination bound field and clear its scratch
   copy. Use the cited public copy/clear contracts and R2 dispatches. Rich
   generic copies can preserve arbitrary foreign symbols outside the local
   framed region. Keep every actual Boolean row on dedicated digit tapes; do
   not decode a foreign-symbol selected tape as though it were a pure lift.
3. Build the window with two independently copied radius counters. Each
   `expandTM [false]` consumes a counter to all `true`, so clear/repopulate the
   counter before the second expansion. Between the two expansions, use the
   advancing one-`true` writer with its first-return release handled by the
   public seam/phase infrastructure.
4. Map the completed digit window to `cell none`, clear the counters and
   remaining scratch, and rewind the heads. `rt_centeredWord` and
   `rt_template_fields` identify the resulting word and fields. Cite
   `counterOverhead_le` for the two expansion budgets and the template length
   identity to absorb `2*s + 1`; compose the component head envelopes.
5. Package row 17's finite state witnesses, time bound, complete first-exit
   cut and exact restoration. Its public body has not yet been connected to
   these private components.
6. Only then implement row 18 by the issued route: row 17 on scratch, state
   field, copied/zeroed position field with its leading `true`, `k` copied
   window fields, tag field, cleanup and return. The `k = 0` case has no tape
   fields, so retain the separate radius term in its space bound.

The continuation stops at this explicit frontier under the brief's partial
option. No incomplete machine wrapper or proof obligation is hidden in a
private admission.

## New private declarations

Counts refer to explicit source declarations, not generated recursors or
instances from `deriving`.

| Declaration | Role |
|---|---|
| `rt_succWord` | Fixed-width increment result, or zero word plus a high `true` on overflow |
| `rt_succWord_cons` | Carry through a low `true` reduces to the remaining word |
| `rt_succWord_bits` | Canonical successor identity; separates zero and one before recursing on a positive high part |
| `rt_incFixed_length` | Successful fixed-width increment preserves length |
| `rt_boundaryTM` | Three-step local writer replacing the delimiter immediately left of its entry head |
| `rt_boundary_run` | Exact endpoint, first exit and head interval of those three public one-step actions |
| `rt_appendSymbolTM` | Public skip, local boundary writer and public skip-back, joined by R2 seams |
| `rt_appendSymbol_run` | Exact append, complete first-exit cut, restored heads and linear displacement |
| `rt_succPhase` | Increment, extension and exit phases; derives finite control and equality |
| `rt_succControl` | Existing component state type for each phase |
| `rt_succControl_fintype` | Finite control-family instance |
| `rt_succControl_decidableEq` | Decidable control-family equality |
| `rt_succParts` | Catalog increment, append-symbol component and stationary exit |
| `rt_succRedirect` | Intercepts success/overflow verdicts and extension exit |
| `rt_succTM` | Instance of the public finite phase host |
| `rt_succ_increment` | Hosted increment prefixes through either first verdict and one dispatch |
| `rt_succ_run` | Complete variable-width successor contract, including empty width and overflow |
| `rt_exists_boundTM` | Public input-length row followed by the successor through an R2 seam |
| `rt_exists_digitBoundTM` | Whole bound-writer run lifted along `RecSym.digitEmb` and embedded on an isolated bank through R1 |
| `rt_centeredWord` | Center-marked range word equals two unmarked runs with one marked cell between |
| `rt_template_fields` | Canonical bound and centered window identify the frozen template fields |

Every new declaration has an axiom closure contained in `propext`,
`Classical.choice`, and `Quot.sound` (`logs/axioms.log`).

## Proved contracts and host discipline

`rt_appendSymbol_run` works over an arbitrary alphabet and tape count, at any
head origin, with an arbitrary preserved frame. It needs the delimited word
and one further blank on its right. It writes only the old right delimiter,
returns all heads, first exits at `2*|w| + 10`, and bounds every head's
relative displacement by `|w| + 4`. The three-step local boundary writer is
not a scanner or a pipeline controller.

`rt_succ_run` cites both catalog increment contracts. The public phase host
intercepts each verdict; only overflow invokes the append component. The
result is exactly `rt_succWord w`, with all other cells, heads, input position
and output restored. Time is at most `4*|w| + 14`, and every work head stays
within `|w| + 4` of its initial position. This includes `w = []`.

`rt_exists_boundTM` cites `exists_inputLengthTM`, not its private counter
implementation. It first exits within `C*(|x| + 1)`, writes
`Nat.bits (|x| + 1)` to tape zero of a globally blank bank, restores all scratch
and every head, and bounds displacement by
`C*(Nat.bits (|x| + 1)).length + C`. Its space bound is independent of the
native input length apart from the logarithmic output width.

`rt_exists_digitBoundTM` composes `MultiTapeTM.liftSymbols_runFrom` and
`embedEmitTM_runFrom`. The selected tapes are actual lifts of a blank Boolean
bank. Unselected rich tapes and prior rich output are arbitrary. It uses the
public selected-position and unselected-frame contracts, and never invokes
pure-lift transport on a configuration containing a foreign selected symbol.

The outer hosts of the proved components are `seamCompTM` and `phaseHostTM`.
All R2 contracts reuse the inherited `rt_copy_seam`. No new generic seam,
loop, trace, input-length counter, or elapsed-time head-bound proof is added.
Head bounds come from the catalog envelopes and exact public one-step
move/write equations for the fixed boundary component. No `f2_head_steps`
argument or `CfgRecord` private transport helper is copied.

**Promotion candidates:** the generic append-symbol leaf and its contract;
the variable-width successor and canonical-word facts; the input-length-plus-
one writer. The centered-word identity is also independent of this module.
All remain private here; promotion belongs to the maintainer. No shared file
was modified.

## Documentation and freeze

Two flagged **“Fill appendix (continuation 3, partial)”** additions document
the precise unfinished frontier on rows 17 and 18. All original prose is
retained. Imports, the module's status/Main-results text, public tags and all
public signatures and bodies are unchanged. There is no newly proved public
row to relabel.

The freeze audit removes only the new private block and these two appendices,
then checks byte-for-byte equality with the base source. Consequently all
14 proved targets, all four paused rows and all 33 inherited privates remain
untouched. It also checks inherited declaration order, imports, the sole
tracked path, the branch/base/ancestor, and `git diff --check`.

Final source size: **3,139 lines; 28 public / 54 private explicit declarations**.
The size warning is permitted by this brief's note 46 and exclusive ownership.

## Verification

All Lean module and evidence checks used `scripts/lean_check_tree.sh`, with
Lean **4.25.0** and pinned mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The dependency manifest and all
other tracked files are unchanged.

Both full sweeps completed with **exit 0, 134/134 modules, zero errors, and
exactly the same 26 admitted declarations as the base**. RecordTable has only
its six original sorry warnings; it has no other final warnings. The precise
base/final names are included in `verification/*-sorries.txt` and checked by
`verification/sweep_check.py`.

The final sweep used a fresh olean tree. Its 108 unchanged upstream modules
ran first; module 109 (RecordTable) and the 25 downstream modules ran after
the final source was installed. No development olean was substituted. All
three final evidence modules ran against this final tree.

| Evidence | Result |
|---|---|
| `S128bStatementsProbe.lean` | Exit 0; zero errors/warnings; byte-identical to the committed probe |
| `W1Cont3Sanity.lean` | Exit 0; zero errors/warnings; concrete cases below |
| `W1Cont3Axioms.lean` | Exit 0; both public rows and all 21 new private closures printed |
| Freeze/scope audit | Pass; inherited bytes restored exactly; one owned path |
| Style lint | `style_lint: 0 FAIL, 9 WARN over 20 files`; the warnings concern file size |
| Patch replay | One patch applied to an isolated temporary index at the base; resulting tree exactly matches the delivery commit |
| Bundle verification | Pass; only the requested working branch is advertised, with the recorded base as prerequisite |

The public axiom prints honestly remain:

```text
'Turing.exists_recordTemplateTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.exists_recordInitTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### Executed sanity cases

The evidence imports the actual committed successor machine through explicit
private-name syntax, not a reimplemented transition table. Each case checks
the endpoint state, every earlier exit cut, both entire head trajectories,
restored native input and output, the new word and delimiters, displaced heads
at `-3` and `7`, and preserved frame sentinels.

| Input word | Exact exit time | Output word |
|---|---:|---|
| `[]` | 14 | `[true]` |
| `[true, true]` | 22 | `[false, false, true]` |
| `[false, true]` | 3 | `[true, true]` |
| `[false, false]` | 3 | `[true, false]` |

The frozen `recordTemplate` and `cfgRecord_init` layouts are evaluated for
empty native input and radius zero, with both `k = 0` and `k = 1`, and for
`|x| = 3`, `s = 2`, `k = 1`. The zero-radius counter values are checked for
both `ws = []` and `[false, false]`; `[false, true]` is checked to encode 2.
These are **layout evaluations**, not executions of the still-unconstructed
public template and initial-record witnesses. End-to-end execution of those
machines is part of the remaining frontier.

### Runtime notes

`lake exe cache get` was attempted as instructed. Its automatic ProofWidgets
cloud-release fetch failed; `lake exe cache unpack` then successfully unpacked
1,239 already cached archives for the pinned dependencies. The complete fresh
baseline and final sweeps established that the resulting dependency cache was
sufficient. No explicit `lake build` command was invoked.

This runtime also needed the same minimal self-executable-path compatibility
shim documented by the predecessor: it redirects only `readlink` of the
process's own `/proc/<pid>/exe` to `/proc/self/exe`. The included C source and
runtime notes explain reproduction. Lean ran with `--threads=1`; the binary,
kernel, trust options and check script were not modified.

Final sweep tail:

```text
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Mult
CHECK TCSlib/Complexity/SpaceComplexity
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1112:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1148:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
CHECK TCSlib/Complexity/TuringMachine
```

## Duplication gate

Both full screens use the exact committed 31-file population and unchanged
`audits/evidence/retrofit/copy-text-screen.py`. The complete before output is
byte-identical to the committed issue-tree screen base. Full stdout is in
`logs/screen-before.txt` and `logs/screen-after.txt`; SHA-256 manifests identify
the base and final populations.

Before:

```text
declarations screened: 1851; copy pairs (target reproduces >= half of source): 2237; reproduced text: 748,156 chars
```

After:

```text
declarations screened: 1867; copy pairs (target reproduces >= half of source): 2237; reproduced text: 748,156 chars
```

```text
Before: declarations screened: 1851; copy pairs (target reproduces >= half of source): 2237; reproduced text: 748,156 chars
After: declarations screened: 1867; copy pairs (target reproduces >= half of source): 2237; reproduced text: 748,156 chars
Added pairs: 0; removed: 0; changed: 0
New owned cross-file pairs: 0; new owned in-file pairs: 0
New pairs at the 90% threshold: 0
PASS: exact before output matches the committed issue-tree base
PASS: all 31 final source hashes match the after-screen population
new copies: none
```

The inherited find scan/skip pair at 60–68%, inherited copier pairs, and the
rest of the inherited ledger are unchanged. No newly added in-file pair needs
justification, and no new pair reaches the 90% threshold. **new copies: none.**
No duplication exception is requested.

## Delivery and replay

The archive contains this report, the complete modified source under its
repository-relative `TCSlib/` path, one `git format-patch` patch, an incremental
git bundle, the full baseline/final logs, axiom log, both full duplication
screens, evidence sources, mechanical audit scripts, and `SHA256SUMS`.
Failed development drafts and the superseded screen are excluded.

Apply the patch at the recorded base using `git am`, or fetch the advertised
working-branch ref from the bundle. The bundle requires that base. The isolated
patch replay produced tree `c7acafb16e2d5a803535717c3852ecf80c99a74c` without
checking out or modifying another branch.

For a fresh replay, use the pinned toolchain/dependencies, set `TCSLIB_OLEANS`
to a fresh directory, and feed `verification/module-order.txt` to the required
check script. Copy the three supplied evidence modules to temporary
`Verification/` paths and check them with that same script and tree. The full
screen command and population are preserved. Run the freeze and sweep audit
scripts from the delivered evidence against the resulting repository/logs.

`SHA256SUMS` covers every other archive member. Run `sha256sum -c SHA256SUMS`
from the extracted root. The zip CRCs and every recorded member digest were
also checked after archive creation.
