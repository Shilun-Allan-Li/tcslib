# W1 record tables — continuation 4, partial delivery

**1 of 2 requested public rows is closed.** `Turing.exists_recordTemplateTM`
(row 17) is proved without admissions. `Turing.exists_recordInitTM` (row 18)
remains explicitly admitted. The file is now at **15 of 20 original targets
proved**. This continuation adds **28 private declarations, all admission-free**,
and performs the eight permitted whitespace-only line wraps.

This is a partial delivery under ground rule 9 of
`briefs/w1-fill-recordtable-cont4.md`: the continuation budget was spent on the
complete template construction, its reusable components, and verification.
The initial-record constructor was not implemented. **Private helpers remaining
`sorry`: none. Proved-modulo targets: none.** No public admission was hidden in
a helper. The four paused rows were not worked on.

## Base, branch, and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Exact campaign branch: `complexity/arora-barak-ch3-4`; `main` was never checked out.
- Base: `6aa9f67bc0b3181672d50eacb9d172e468070df3`.
- Required ancestor: `235de34386638aeab7d24424a69ae0a6d96c15b6`.
- `git merge-base --is-ancestor 235de34386638aeab7d24424a69ae0a6d96c15b6 HEAD`
  passed before development and again at delivery.
- Working branch: `fill/w1-recordtable-cont4`, created directly from that base.
- Delivery commit: `7158dd2b772135d49c7bc145b7ea37a88d56f603`.
- Sole tracked changed path:
  `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean`.
- No rebase, push, PR, or change to another branch. The campaign ref still
  points to the base; the working tree is clean.

The committed brief was read first, followed by its binding documents and the
predecessor's report. The ancestor-to-base changes contain only brief files;
there is no intervening Lean-source change or another batch's work in this tree.

## Target status and next continuation

| Row | Target under `Turing` | Status |
|---|---|---|
| 17 | `exists_recordTemplateTM` | Proved; axiom closure exactly `propext`, `Classical.choice`, `Quot.sound` |
| 18 | `exists_recordInitTM` | Original explicit admission retained; no constructor implemented |
| 15, 16, 19, 20 | Paused targets | Entire declarations and docstrings byte-identical to the base |

**Statement/host escalations: none.** No contradiction in a frozen statement was
found, no signature or attribution was altered, and no missing public host is
claimed. The remaining work is row 18's issued construction, using the now-proved
row 17:

1. Run `exists_recordTemplateTM` on a scratch destination, with the caller's
   radius tape as its radius input and a clean bank for its other tapes. R1
   supplies the surrounding rich frame and prior output. Unlike a raw Boolean
   lift, row 17 permits foreign symbols outside the framed radius word.
2. Write the state field at the record destination, then copy the template's
   bound field. Use the public rich mapping scan to zero that copied field,
   overwrite its first digit with `true`, and cross its delimiter. This is the
   initial native input position `1` from `cfgRecord_init`.
3. Cross the template's bound field once, then copy its window field `k` times,
   crossing each destination field. A fixed finite chain of public R2 seams or
   the public phase host must own this sequencing. Reuse existing copy/layout
   contracts; do not introduce a private run-trace host.
4. Write the tag, clear both template fields, and rewind both template and
   destination heads. Prove the exact `cfgRecord_init` field layout, complete
   first-exit cut and common head envelope.
5. Keep the separate radius term when `k = 0`: that record has no window field,
   but the scratch template still has its `2*s + 1`-cell window. Time also keeps
   the issued radius term. Execute the initial-record sanity cases once that
   machine exists.

Row 18's original signature, body and sketch are unchanged. Its new flagged
appendix records this frontier; there are no row-18 private stubs.

## Row 17 construction

The bound phase invokes the inherited `rt_exists_digitBoundTM` through a proved
clean-bank identification. Its selected tapes are genuine lifts of a blank
Boolean bank, with native input position `1`, arbitrary selected head origins,
and Boolean output `[]`; the rich host's prior output is the R1 prefix. The
canonical `Nat.bits (|x| + 1)` word is copied to the destination and its scratch
copy is cleared.

The window phase first copies the caller's radius into a separate globally
blank digit bank. Each half copies that preserved radius into a temporary
counter, invokes the public `expandTM [false]`, and clears the consumed all-true
counter. Between the halves, the advancing one-`true` writer uses the public
first-return release. The complete Boolean window is rewound before the rich
mapping scan converts digits to `cell none`. A rich copy/clear transfers the
window to the destination, and the copied radius is cleared. Every scratch
cell and every work head is restored by this window phase.

The final template machine has separate bound and window banks and uses R2 to
join the bound phase, destination skip, rich-window phase and final backward
skip. `rt_template_fields` and the public `fieldsTape_field` projections identify
the two word masks and their blank separator with the frozen template layout.
The proof keeps the original radius and surrounding rich cells intact.

All outer controllers are chains of `seamCompTM`; the expansions use the public
counter-loop row. Every actual Boolean phase runs lifted along `RecSym.digitEmb`
on a dedicated bank. The rich source/destination copies and mapping scan are
never treated as pure Boolean lifts. Every submodule is intercepted at its own
first exit, including the empty word and radius zero.

The rich-window component first exits within `26*(s + |ws|) + 48`, bounds every
head by `2*s + |ws| + 3` from its entry, and restores all fields except the
written destination interval. `counterOverhead_le` supplies the two expansion
budgets. The bound-field component retains linear input time and logarithmic
head displacement. Row 17 absorbs both through the public template-length
identity into its unchanged time and space bounds. No downstream admission,
termination premise, elapsed-time head-bound copy, private `f2_` helper, or new
transition-table controller is used.

## New private declarations

These are explicit source declarations, excluding generated declarations.

| Declaration | Role |
|---|---|
| `rt_expand_run` | Specializes the public expansion contract to a three-tape bank using `counter_cfg_eq` |
| `rt_repeatTM` | R2 composition of radius copy, expansion and counter clear |
| `rt_repeat_run` | Exact preserved-radius expansion, scratch restoration, first exit and envelope |
| `rt_writeReleased_run` | Generic released advancing-writer contract, including its cut at zero |
| `rt_adjacentWrites` | Two adjacent word masks equal one concatenated mask |
| `rt_advanceCfg` | Configuration after a contiguous word write and head advance |
| `rt_advanceCfg_append` | Merges consecutive advancing writes across a state relabeling |
| `rt_halfState` | Finite control alias for one window half |
| `rt_windowAdvTM` | Two half writers with the released center writer between them |
| `rt_windowAdv_run` | Complete advancing digit-window contract and linear budget |
| `rt_windowTM` | Adds public forward/backward skips to restore the destination head |
| `rt_window_run` | Digit-window contract with all three heads restored |
| `rt_windowCellMap` | Maps digits to `cell none`, preserving other rich symbols |
| `rt_cellWindowTM` | Lifted Boolean window followed by the rich mapping scan |
| `rt_cellWindow_run` | Exact cell-window output on a genuine lifted bank |
| `rt_embed_radius` | Extends a selected-bank envelope to every host tape using public R1 projections/frame |
| `rt_cellWindow_embed_run` | R1 window run with an arbitrary rich frame and prior output |
| `rt_embed_matches` | Identifies a forwarding configuration from public selected and unselected projections |
| `rt_exists_cleanDigitBoundTM` | Reuses the inherited bound writer from an arbitrary host with a blank selected bank |
| `rt_moveWordTM` | Rich generic copy followed by source clear |
| `rt_moveWord_run` | Exact copy/clear masks, restored heads, first exit `4*|w| + 5` and envelope |
| `rt_cellWindowState` | Finite control alias for the lifted/mapped window |
| `rt_cellWindow_ready_run` | Direct host contract for a globally specified pure digit radius bank |
| `rt_bufferMask` | A buffer is blank outside its written interval |
| `rt_richWindowState` | Finite control alias for scratch preparation, window and cleanup |
| `rt_richWindowTM` | Complete rich window, using four components and R2 seams |
| `rt_richWindow_run` | Full scratch restoration, first exit and head bound for the rich window |
| `rt_exists_boundFieldTM` | Canonical bound written to a rich destination, with its selected bank cleared |

All 28 axiom closures are subsets of `propext`, `Classical.choice`, and
`Quot.sound`. None depends on `sorryAx`.

**Promotion candidates / requested shared lemmas:** the preserved-radius
pattern expansion and its contract; the released advancing-writer adapter;
the adjacent advancing-write configuration identities; the generic R1 envelope
and configuration-identification lemmas; and the generic copy/clear word move.
The small buffer-mask fact is generic as well. They remain private under this
batch's file ownership. Record-specific window and bound adapters need no new
shared host. No shared file was edited and no duplication exception is requested.

## Documentation, freeze and style

Two flagged appendices were added: **“Fill appendix (continuation 4, proved)”**
on row 17 and **“Fill appendix (continuation 4, partial)”** on row 18. Prior
appendices and all original sketches remain intact; the new row-17 appendix
explicitly supersedes the previous admission status. The module Status
paragraph and Main-results tag now identify row 17 as proved. Imports and all
public signatures are unchanged; no public declaration was added.

The mechanical freeze audit reverses the exact eight line wraps, removes only
the new private block and flagged appendices/status updates, and restores row
17's old body after checking its signature byte-for-byte. The result is exactly
the base source. Thus all 14 previously proved targets, all 54 inherited
privates, and all four paused declarations/docstrings remain frozen, apart
from the expressly allowed whitespace changes.

| Previous delivery's 21 declarations | Before | After |
|---|---:|---:|
| Lean linter warnings | 0 | 0 |
| Lines over 100 characters | 8 | 0 |

The only inherited declarations touched for style are `rt_boundary_run`
(three lines), `rt_appendSymbol_run` (one), `rt_succControl_decidableEq` (one),
and `rt_succ_increment` (three). Every edit is whitespace-only; the token
streams, statements and definition/proof contents are unchanged. The entire
owned file has no non-sorry Lean warnings in the final sweep.

Final source size: **4,779 lines; 28 public / 82 private explicit declarations**.
The eight inherited wraps and the new proof code were checked in the final
fresh sweep. File size is reported, not used as a reason to alter the scope.

## Verification

Every Lean module/evidence check used `scripts/lean_check_tree.sh`. The toolchain
is Lean **4.25.0**, with mathlib pinned to
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. No tracked dependency manifest,
check script, Lean binary, trust option or other source file was changed.

| Check | Result |
|---|---|
| Fresh bootstrap | 134/134 modules, exit 0, zero errors, exact 26 base sorry declarations |
| Fresh final sweep | 134/134 modules, exit 0, zero errors, exact 25 sorry declarations |
| RecordTable in final sweep | Five sorry warnings; no other warnings |
| Other modules | Exact same 20 admitted declarations as the base |
| Pre-ship statements probe | Exit 0, zero errors/warnings; source identical to committed probe |
| Sanity evidence | Exit 0, zero errors/warnings; executed window tests and template bounded-run cases below |
| Axiom evidence | Both targets and all 28 new private declarations printed |
| Freeze/scope audit | Pass; one owned path, frozen signatures and paused bytes unchanged |
| Campaign style lint | `style_lint: 0 FAIL, 9 WARN over 20 files` (file-size warnings) |
| Patch replay | One patch applied in a separate temporary index at the base; tree equals delivery tree |
| Bundle verification | Pass; only the requested working branch advertised, with the base prerequisite |

The final sweep used a fresh `.lake/final-oleans` tree. Its 108 unchanged
upstream modules ran first; RecordTable (module 109) and its 25 downstream
modules ran after the delivered source was installed. No development TCSlib
olean was substituted. All three final evidence modules used that final tree.
`verification/sweep_check.py` checks the complete order and admission names,
not only warning counts. The sole removed admission is row 17.

```text
'Turing.exists_recordTemplateTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_recordInitTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### Sanity cases and their limits

`W1Cont4Sanity.lean` executes the actual committed `rt_richWindowTM`, referenced
by its private declaration name rather than a reconstructed transition table.
The selected bank is globally blank; caller tapes contain foreign frame
sentinels, all five head origins differ, and the prior output contains rich
symbols. Each case checks the first exit, all earlier exit cuts, every head
through that exit, exact final head/input/output restoration, and tape contents
on a frame covering every written interval and sentinel.

| Native input | Radius word | Radius | Executed first exit |
|---|---|---:|---:|
| `[]` | `[]` | 0 | 48 |
| `[]` | `[false, false]` | 0 | 80 |
| `[true, false, true]` | `[false, true]` | 2 | 128 |

The same evidence also instantiates the **actual public template witness** on
`x = [], s = 0` and on `|x| = 3, s = 2`. These are proved concrete bounded-run
examples, including the exact literal field lists, first-exit cut, head bound,
and preserved rich output; they are not numerical evaluations of a
`Classical.choose` witness. Their time bounds specialize to `4*C` and `15*C`,
and head bounds to `4*C` and `12*C`.

The initial-record definitions are evaluated for empty input/radius zero with
both `k = 0` and `k = 1`, and for `|x| = 3, s = 2, k = 1`. These are **layout
evaluations only**. Row 18's machine has not been constructed, so its required
end-to-end execution remains part of the explicitly reported partial frontier.

### Runtime

`lake exe cache get` was invoked as required. It downloaded 3,643 archives and
failed on 2,624 with HTTP 502 responses. The pinned dependency cache copied
from the predecessor workspace was sufficient: both full fresh TCSlib sweeps
and all final evidence checks completed. No `lake build` command was invoked.
The full cache attempt log is included.

The runtime required the predecessor's minimal self-executable-path shim:
`readlink` of the process's own `/proc/<pid>/exe` is redirected to
`/proc/self/exe`. Its C source is included for reproduction. Lean ran with
`--threads=1`; this did not change the binary, kernel, trust settings or check
script. `verification/runtime-notes.txt` explains how to reproduce the checks.

Final sweep tail:

```text
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Path
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

Both full text screens run the unchanged committed script over the exact
31-file population in `audits/evidence/fills-6/w1-fill-cont3-screen-population.txt`.
The before output matches the committed issue-tree base after its explanatory
header. Exact base/final source hashes are included.

Before:

```text
declarations screened: 1952; copy pairs (target reproduces >= half of source): 2249; reproduced text: 754,495 chars
```

After:

```text
declarations screened: 1979; copy pairs (target reproduces >= half of source): 2250; reproduced text: 755,392 chars
```

There are **no new cross-file pairs touching the owned file** and no new
pairs at or above 90%. The inherited pair ledger has no removals or changes.

The new in-file pair is:

- `RecordTable.lean::rt_richWindow_run` → `RecordTable.lean::rt_moveWord_run` (897/1606 = 56%): The shared text is R2 invocation and framed head-envelope bookkeeping for the outer copy and clear phases. The rich-window proof explicitly cites `rt_moveWord_run` for its transfer stage; it does not re-prove that component's copy/clear trace.

**new copies: none.**

```text
Before: declarations screened: 1952; copy pairs (target reproduces >= half of source): 2249; reproduced text: 754,495 chars
After: declarations screened: 1979; copy pairs (target reproduces >= half of source): 2250; reproduced text: 755,392 chars
Added pairs: 1; removed: 0; changed: 0
New owned cross-file pairs: 0; new owned in-file pairs: 1
RecordTable.lean::rt_richWindow_run reproduces RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
New pairs at the 90% threshold: 0
PASS: exact before output matches the committed issue-tree baseline after its header
PASS: all 31 final hashes match the after-screen population
new copies: none
```

Full outputs are in `logs/screen-before.txt` and `logs/screen-after.txt`.
`verification/screen_check.py` verifies the before baseline, every changed pair,
all final population hashes and the cross-file/90% gates. The inherited
find scan/skip pair and other inherited duplication remain in the base ledger.

## Delivery and replay

The archive contains this report, the full modified source, one `git
format-patch` patch, the incremental bundle, complete bootstrap/final logs,
axiom/probe/sanity/style/freeze logs, both duplication screens, evidence sources,
mechanical audits and `SHA256SUMS`. Failed development drafts and temporary
proof modules are excluded.

Apply the patch with `git am` at the recorded base, or fetch
`refs/heads/fill/w1-recordtable-cont4` from the bundle. Patch replay produced
tree `d1b4a8fd28d883f8092eb49e8da1906dc2b1c1f6`, exactly the delivery tree,
without checking out or modifying another branch.

For a fresh verification, use the pinned toolchain/dependencies, a fresh
`TCSLIB_OLEANS` directory, and the supplied `verification/module-order.txt` with
the repository's check script. Copy the three evidence modules into temporary
`Verification/` paths and check them against that same tree. Run the supplied
freeze, sweep and screen audit scripts with the repository root as their sole
argument. They are evidence tools, not tracked repository changes.

`SHA256SUMS` covers every other archive member. Run `sha256sum -c SHA256SUMS`
from the extracted root. ZIP CRCs and every member digest are checked after
archive creation.
