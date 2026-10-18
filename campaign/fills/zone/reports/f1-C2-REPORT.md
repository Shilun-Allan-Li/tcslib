# ZF-C2: both one-tape space targets complete

**2/2 continuation targets are proved.** The first uses a new demand-grown
witness; the binary composite cites it and the integrated alphabet theorem.

| Target | Result |
|---|---|
| `Turing.FinTM.one_work_tape_spaceUsed` | Complete, with all-input, all-time space containment. |
| `Turing.FinTM.one_work_tape_binary_spaceUsed` | Complete, with one common time/space coefficient. |
| `Turing.FinTM.alphabet_reduction_spaceUsed` | Received theorem unchanged; axiom print repeated. |

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Source branch: `complexity/arora-barak-ch3-4`.
Working branch: `fill/zone-f1-C2`.
Recorded base: `42627f368fef1fbdc5f0c8af777498d26be124bd`.
C2 issue commit: `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`.
The received `SingleTape.lean` is byte-identical between the issue commit
and this base. No rebase, push, or PR was performed.

The binding route is `briefs/zone-f1-batchC2.md`, the original
`briefs/zone-f1-batchC.md`, and
`audits/zone-agent-reports/f1-C-REPORT.md`, including its continuation
plan and the inherited three-round audit dispositions.

## Construction and resource proof

The witness for positive tape count and nonempty source alphabet is
`dgTM M a₀`. It has one work tape and uses the received
`SweepAlphabet`, interleaved `tapeZone`, tagged cells, and two boundary
symbols. The old `sweepTM` is never the space witness.

The new control wraps the old state type. Initialization, interior read
and write transitions, and the right-row generator delegate to the
received transition table through `Action.mapState Sum.inl`. Only
boundary decisions and the left-row writer are new. Entering the read
phase leaves the left boundary fixed. At the right boundary the last
row's old head flags and the pending source movements decide whether to
generate one row or turn immediately. On return, the shared reverse
transduction delivers the leftmost row's old head flags in finite
control; an outward left move generates one marked blank row, otherwise
that boundary stays fixed. Thus neither end grows unless a source head
crosses it on this transition. A halting source transition still completes
any required extension before the simulator halts.

`DGWindow` records a nonempty source-coordinate interval, containment of
current heads, blankness outside, and both directions of the history
correspondence: every represented coordinate has been visited, and every
past source head position is represented. Initialization represents the
origin. `dgWindow_step` adds only a crossed neighboring coordinate and
supplies its source head witness at the next source time. Consequently
the represented coordinates are exactly the union of the source tapes'
visited coordinates, and `dgWindow_space` bounds their count by the sum
of the per-tape visited counts.

`DGSpan` includes endpoint equality **and containment at every physical
prefix**. Forward and reverse prefix lemmas apply the generic
`sweep_run` / `sweep_run_reverse` APIs to a list prefix. Writer
containment specializes `sweep_generate` at every prefix, without another
writer induction. Initialization, both boundary branches, and the whole
macro-step compose these spans. A crossing's new cells are charged to
the source transition being simulated, including intermediate visits.
`dg_simulate` maintains the whole previous physical trajectory in the
monotonically growing interval.

At source coordinates `[a, a+n)`, the inclusive physical containing
interval is `[a*k-1, (a+n)*k]), of cardinality `n*k+2`. The two extra
cells are the boundaries. In `dg_all_inputs`, simulation reaches the
source's first halt; `MultiTapeTM.runFrom_of_halt` then proves the same
containment for **every later physical time**. Taking the visited set at
an arbitrary horizon therefore proves the required all-time space bound,
rather than merely an endpoint estimate.

For every native enlarged-alphabet word `x`, `dgRetract a₀` fixes the
embedded data symbols and sends other symbols to `a₀`. The transition
table applies it only to the currently scanned optional input symbol.
The word `x.map (dgRetract a₀)` is a mathematical source input in the
proof; the simulator never stores or materializes it. Its length equals
`x.length`, so both source hypotheses apply at that same length without
any monotonicity premise. `dgInput_read` and `dgPos_move` also cover
native input boundary positions.

The exact new cycle cost is `dgCost`. With width at most `2*t+1`,
`dgCost_le` proves it at most `(4*t+7)*k+4). Initialization costs
`2*k+2`. Only **after this new cost comparison** does the proof reuse
`sweepTime` and `sweepTime_le` as numerical summation bounds; it does
not apply the old machine's timing theorem to the new witness.
The common coefficient is `9*k+6), sufficient for quadratic time and
`n*k+2 ≤ (9*k+6)*(S x.length+1)`.

The zero-tape branch cites `unusedTapeTM`, `unusedTapeCfg`,
`unusedTape_step`, and `unusedTape_computes`; `dg_unused_space`
proves its sole head visits exactly one cell at every horizon. For an
empty source alphabet, outputs are empty and a local immediately halting
zero-tape machine, followed by that unused-tape embedding, supplies one
work tape. Both degenerate cases use coefficient 1.

The binary composite first invokes `one_work_tape_spaceUsed`, then the
public `alphabet_reduction_spaceUsed`. The coefficient
`c₂*(c₁+1)` absorbs both stages using exactly the brief's two
inequalities. All bounds use the original input length.

## New private declarations

There are 43 new explicit declarations, all private, and no optional
public exports. None is admitted.

| Declaration | Role |
|---|---|
| `dg_unused_space` | Exact one-cell all-horizon space for the received unused-tape embedding. |
| `dgRetract` | Total per-symbol retraction of the enlarged alphabet. |
| `dgRetract_embed` | Retraction fixes the received embedding. |
| `dgPos` | Same-length input-position transport to the native word. |
| `dgPos_move` | Native input movement commutes with that transport. |
| `dgInput_read` | Native reads retract to source reads, including boundaries. |
| `DGState` | Received control plus the new optional-successor left-row writer. |
| `dgCross` | Boundary-head/outward-movement test. |
| `dgTM` | Demand-grown machine with delegated unchanged transitions. |
| `dg_read` | Read-phase endpoint by the generic sweep and received zone transduction. |
| `dg_write` | Return-phase endpoint by the generic reverse sweep and received zone transduction. |
| `dg_sweep_prefix` | Exact forward head position at every sweep prefix. |
| `dg_sweep_reverse_prefix` | Exact reverse head position at every sweep prefix. |
| `DGSpan` | Endpoint equality together with all-prefix physical containment. |
| `dgSpan_add` | Concatenation preserves all-prefix containment. |
| `dgSpan_one` | One-step span from its two endpoints. |
| `dgStart` | Canonical boundary configuration using the received zone and native input. |
| `dg_native` | Received decoder on retracted data-summand symbols equals total retraction. |
| `dgSpan_generate_right` | All-prefix forward writer wrapper over `sweep_generate`. |
| `dgSpan_generate_left` | All-prefix reverse writer wrapper over `sweep_generate`. |
| `dgSpan_mono` | Widen a span's containing interval. |
| `dg_init` | Initialization endpoint and every-prefix containment on all native inputs. |
| `dg_right_span` | Delegated right-row generation with every-prefix containment. |
| `dgLeftRow` | Received blank row with precisely the incoming left-crossing heads. |
| `dg_left_span` | New left-row writer with every-prefix containment. |
| `dg_collect` | Read entry without allocation, followed by a contained full read sweep. |
| `dg_turn` | Delegated boundary turn performs one native source input/output action. |
| `dg_read_boundary` | Direct equation for the conditional right-boundary transition. |
| `dg_turn_without_growth` | No right crossing: immediate contained turn. |
| `dg_turn_with_growth` | Right crossing: exactly one row, then the contained turn. |
| `dgRev_write_optional` | Optional-successor stationary write, citing the received write lemma's projections. |
| `dg_end_without_growth` | No left crossing: install the successor or halt at the old boundary. |
| `dg_end_with_growth` | Left crossing: one row and boundary, then successor or halt. |
| `dg_new_left_row` | Identify the new marked blank row with the next source row. |
| `dgCost` | Exact conditional macro-step transition count. |
| `dg_step` | Correct complete source step with all-prefix containment. |
| `DGWindow` | Exact source-visited interval, blankness, head/history containment, and time-only width bound. |
| `dgWindow_init` | Origin window for positive tape count. |
| `dgWindow_step` | A demand-grown source step preserves the window invariant. |
| `dgWindow_space` | Window width is at most total source visited space. |
| `dgCost_le` | Fresh comparison of conditional cost with a linear-in-source-time majorant. |
| `dg_simulate` | Source-prefix simulation with a whole-trajectory span and quadratic time majorant. |
| `dg_all_inputs` | All-target-word correctness and all-horizon space, with explicit halt absorption. |

The private structure `DGWindow` also generates its constructor,
recursor, and projections `positive`, `heads`, `blank`, `visited`,
`size`, and `history`; these belong to that private declaration, not
new public exports. The optional permanent trajectory export and
stationary-scanner regression lemma were not added. The received
stationary-scanner warning remains byte-identical in the target docstring.

## Reuse-not-copy screen and freeze

**Ledger line — `Robustness/SingleTape.lean`: 43 new private
declarations; no copied proved declaration or copied proof family
introduced. Comment-stripped explicit declaration count: 57 at base,
100 final (4 public / 96 private). No pre-existing or new copied-material
family was identified in this file; cumulative identified count
0/100 = 0%. The fragment and design parallels screened below are
disclosed, rather than counted as copied declaration families.**

The construction cites the received `SweepCell`, `SweepAlphabet`,
`sweepEmbed`, `sweepBoundary`, `sweepSymbol`, `blankRow`,
`rightRow`, `headAt`, `readState`, `tapeRow`, `tapeZone`,
`readVisit`, `writeVisit`, `read_zone`, `write_zone`,
`tapeZone_append`, and their length/blank-row facts. The received
`read_row` and `write_row` remain the underlying proofs used by those
zone facts. No representation or transduction is cloned.

The new proofs consume `sweepCfg`, `sweepRevCfg`, `sweep_run`,
`sweep_run_reverse`, `sweep_generate`, the one-cell movement APIs,
and the local turn/stay/write zipper identities. They do not copy or
invoke the old `sweep_init`, `sweep_prepare`, `sweep_finish`, or
`sweep_step` proof families as proofs about the new machine.
The generic-API route is used; no agreement-transfer theorem is needed.
The transition delegate itself is an actual call to the received table,
with state transport, rather than a repeated table.

Borderline cases were screened explicitly:

- `dg_init` has the same required four physical initialization phases
  as `sweep_init`, but proves new all-native-input and all-prefix
  obligations by generic generation/reverse-sweep APIs and span
  composition. It cites `sweep_turn_left`, `sweepFold_id`, and
  `sweepRevCfg_write` instead of reproducing their proofs.
- `dg_right_span` and `dg_left_span` necessarily share finite-row
  indexing and list length/take/map glue with the old row generators.
  They instantiate the generic contained-writer wrappers. The reverse
  generator writes the new crossing-head mask; no old generator proof
  or induction is copied.
- `dg_read`, `dg_write`, and the sweep-prefix wrappers are direct
  generic API instantiations. They do not repeat the received row/zone
  induction. The forward/reverse wrappers are direction-specific
  applications of the shared API, not alternative sweep engines.
- `dg_turn` shares optional-output append/map algebra with the turn
  subproof of `sweep_finish`. Its physical update is proved by the
  existing `sweep_turn_left`; its input obligation is the new total
  retraction read/move correspondence.
- `dgPos_move` and `dgInput_read` resemble the old embedding
  transport obligations but run in the other direction on arbitrary
  native words. The old partial `sweepInput` decoder does not supply
  this total retraction.
- `dgRev_write_optional` handles a possibly halting successor by
  citing projections of the received `sweepRevCfg_write`, without
  copying its tape-function proof.
- The new exact-window, prefix-span, crossing, and cost ledgers are
  specific new obligations. The only old timing reuse is the numerical
  `sweepTime` majorant after `dgCost_le`; the old unconditional
  machine is not substituted for the new witness.

The generic all-prefix wrappers could be promoted to `Sweep.lean` in
a later shared-file window; they remain private under this batch's
ownership rule. There are no copies from `Build/Zone`, `Codes2Tape`,
or the §12 controller layer.

**Flagged import:** `TCSlib.Complexity.TuringMachine.StateRenaming`,
solely to cite `Action.mapState` for the delegated table's state
transport. No existing import was removed or changed.

The byte-level freeze check removes only that added import, the new
private appendix, and the two authorized proof replacements, then
reconstructs the base file exactly. It verifies that both signatures,
all received declarations and docstrings outside the replaced proofs,
and their order remain identical. No declarations were removed.
The only tracked diff is
`TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`.

The source is 2,319 lines. The size WARN is covered by the
**“A-S2 spec layer LANDED”** decision-log row in
`AroraBarakChapters3-4Plan.md`, line 492 at this base, as explicitly
directed by the C2 brief. Splitting remains reserved for the D7 window;
this delivery changes no shared file or plan.

## Verification

| Check | Result |
|---|---|
| Fresh required import closure | 39/39 modules passed; 0 errors; fresh project oleans. |
| Final `AlphabetReduction` | Exit 0, fresh olean, 0 errors, 0 sorry warnings. |
| Final `SingleTape` | Exit 0, fresh olean, 0 errors, 0 sorry warnings. |
| Final `Oblivious` and facade | Both exit 0, fresh oleans, 0 errors, 0 sorry warnings. |
| Three Z4 axiom prints | Each exactly the standard triple; no `sorryAx`. |
| Scoped campaign lint | `style_lint: 0 FAIL, 12 WARN over 45 files`. |
| Byte-level freeze | Every check passed; only the owned file differs. |
| Bundle and patch | Bundle verification and reverse patch applicability check passed. |

The two admission warnings in the 39-module closure are exactly the unchanged
baseline admissions at `CounterProgRun.lean:343` and
`NDCodes.lean:187`. Neither appears in the three target axiom closures.
`SingleTape` has only two benign tactic-style diagnostics, at lines 1994
and 2005. A final four-module source gate was run after clarifying a new
private docstring; its source hash matches the delivered file.

All three axiom prints, verbatim from `axioms.log`:

```text
'Turing.FinTM.alphabet_reduction_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_binary_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final sweep tail; the complete output is `sweep.log`:

```text
Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
PASS TCSlib/Complexity/TuringMachine/Robustness/Oblivious exit=0 seconds=15.76
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine exit=0 seconds=3.31
FINAL SOURCE GATE PASS: all 4 requested modules.
```

The final dependency closure was built into a fresh
`.lake/c2-final-oleans` directory, using only
`scripts/lean_check_tree.sh` for Lean elaboration and axiom prints.
There was no project `.lake/build/lib/lean` fallback. Pinned package
oleans were reused. No `lake build` was run.

Environment: Lean 4.25.0, compiler commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, as pinned by the repository.
The official Lean kernel and libraries are unchanged. This runtime used
the previously established self-path compatibility adapter, whose only
rewrite maps its process's own `/proc/<pid>/exe` lookup to
`/proc/self/exe`. It changes no proof checking. No adapter, C source,
binary, FFI declaration, or environment override is part of the delivered
patch or bundle. The host-specific adapter is also omitted from the
archive, consistent with the integration decision log's shim exclusion.

The evidence includes `verification/dependency-order.txt`,
`verification/Axioms.lean`, the freeze script and private inventory,
and the closure runner. The runner was executed with the repository at
the sibling path `tcslib`; on another layout its root should be adjusted.
The standard repository check script itself is unchanged.

## Integration

Delivery commit: `aec8a1bfe0d89d7de1e942d540cc68d29779d21d`.
One commit, changing only the owned Lean file.
Patch: `patches/0001-Prove-demand-grown-one-tape-time-and-space-bounds.patch`.
Bundle: `zone-f1-C2.bundle`.
The `git bundle verify` output is in `bundle-verify.log`;
the read-only reverse application check is in `patch-check.log`.
Delivered source SHA256:
`4b05f7dfbee29ca8b2dee1507f2187bf392134acca51389361d9c538c744dff7`.

The archive includes the full owned source, `REPORT.md`, format patch,
git bundle, final logs, verification inputs, and `SHA256SUMS`.
Apply the patch series to the recorded base with the campaign's
`git am -3` workflow, or fetch the bundle. The bundle declares the
recorded base as a prerequisite. Verify the checksums before integration.
Both continuation holes are closed; there is no remaining frontier in
this batch.

Glossary: `k=M.k` is the source work-tape count; `a` is the represented
leftmost source coordinate; `n` is the number of represented source
coordinates; `t` is a source step index unless explicitly called a
physical horizon; `c₁` and `c₂` are the first- and second-stage
coefficients. Other identifiers are the names in the Lean source.
