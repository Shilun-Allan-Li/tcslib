# External audit findings — §13d walk statement gate

**Verdict: PASS — 0 blockers, 0 majors, 2 minors.** The walk and its contract have the advertised first-exit behavior, including the empty-word and zero-direction cases. The skip specialization preserves its statement, and the contract refactor preserves the existing fields. The six wrappers faithfully package their framed rows. The two minors concern documentation; neither requires changing a theorem or a machine. This verdict covers the attached proposed unit, not a fresh Lean build or the unfinished G4 witnesses.

## Findings

`Build/…` abbreviates `TCSlib/Complexity/TuringMachine/Build/…`. Declaration locations refer to the proposed `unit/` files unless marked base.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `audits/evidence/s13d/g4-hosts/G4-HOSTS-SURVEY.md` §3 · proposed walk | The survey's displacement convention differs from the gated unit's by one cell. | The survey asks a length-`m` ruler to move both heads `m` cells in `m+1` steps. `walkTM` moves them `m+1` cells in `m+1` steps. With `w = [a]` and positive direction, the actual displacement is two, not one. The pack and the unit state the actual convention correctly. | Record an erratum in this gate's resolutions and make G4's fill brief use the actual convention. For a positive distance `m`, advance only the ruler head once and walk over the ruler's tail, of length `m−1`; the other head then moves exactly `m`. Treat distance zero separately. Include ruler restoration and control-transition costs. Preserve the historical survey as evidence. |
| 2 | minor | `Build/Catalog.lean` · `walkTM_run_ofCfg` proof sketch | The sketch names a helper that the proof does not use, and refers back to the skip that is now its corollary. | The sketch says `catalog_pass_contract`; the proof instead applies public `catalog_trace_run` with constant return family `fun _ => D`. The re-proved skip subsequently invokes the walk. The proof itself has no circular dependency. | Describe the forward configurations, the blank transition, and `catalog_trace_run` with a stationary return family directly. Remove the misleading helper reference and the backwards explanation through the skip. |

Repair or explicitly dispose of these minors in the resolutions. Under the pack's zero-blocker/zero-major rule, neither holds the gate open.

## Integrity, scope, and evidence limits

The supplied bundle's SHA-256 is exactly

`66f5d2706e470117524a45b2057569b765b555ddf2316193b541d4dd40622b6d`.

It contains **50 section headers with 50 distinct paths**. The inventory consists of the pack; three standards; the hosts survey; two earlier gate records; the G24 design note; 27 walk-evidence sections, including its manifest; three screening/lint tools; ten Lean source sections; and the machine-library design and backlog. All **26 entries** of the embedded `SHA256SUMS` match after removing bundle separators and the Markdown fences around fenced sections. The initial raw extraction's seven script mismatches disappear by removing exactly those enclosing fences; no source correction was needed.

I regenerated both proposed files from the attached bases using `mkwalk.py`; both are byte-identical to the supplied unit files. Their SHA-256 values are:

| Proposed file | SHA-256 |
|---|---|
| `unit/Catalog.lean.txt` | `f2d53676b6033838b0021e9c5f4a86c8a8be1d332992b77f264509dd76352e13` |
| `unit/Contract-Catalog.lean.txt` | `db8c98dd3ba50954e345e72b00415dd806f972cab40ecf4d1a103e0f26c21e44` |

The review covered the changed definitions and proofs, the wrapped framed statements, `Contract`'s fields, `Action.apply`, the public trace theorem, the existing sweep instances and frame/trajectory lemmas, the G4 row specifications and survey, and the supplied evidence scripts and logs. The existing G2–G4 findings and resolutions remain the governing records for their earlier obligations; this audit does not reopen their unrelated mathematics or certify all legacy Catalog proofs.

**I could not run Lean:** `lean`, `lake`, and `elan` are absent from the available command path, and no toolchain was found in the checked standard locations. The bundle also does not supply a complete dependency/olean snapshot. Consequently, elaboration and kernel-axiom results below are **supplied evidence**, not executions by this auditor. The reported Git identities `a9ee4701`, `b6e0344c`, and `2e79d0f7`, and the completeness of their downstream closure, were not independently authenticated against Git. Regeneration establishes correspondence with the attached bases only.

The new routines are technical construction-layer glue. Their fidelity target here is the supplied catalog/contract semantics and G4 requirements; this is not a new source audit of Arora–Barak §1.7.

## Definitions and the walk proof

The following are restatements from the declaration bodies, rather than acceptance of the docstrings as specifications.

| Definition | Meaning and ruling |
|---|---|
| `walkTM` | Start in `run`. Inspect only the symbol on `src`. Move every head selected by `moved` by `dir`, writing nothing, and remain in `run` on a present symbol or enter `done` on a blank. Every other phase is stationary. Input position and output are unchanged. **Accept.** |
| `framedContract` | Package a supplied run, first-exit, and head-bound theorem into a singleton-exit `Contract`. Preserve the given precondition, time, and endpoint. Use the supplied intervals for touched heads and singleton intervals at the starting positions for untouched heads. **Accept.** |
| `sweepContract` | Specialize that constructor to a delimited source word, time `2*length+2`, the supplied endpoint, and touched-head intervals from one cell before the start through the right delimiter. **Accept; definitionally the old data fields.** |
| `seekPost` | Change the state to the supplied live exit and update exactly one head to the supplied position. Preserve the tapes, other heads, input position, and output. **Accept.** |

The six wrapper definitions are restated field by field below. No additional premise has been silently inserted into their preconditions.

For the walk, the supplied precondition says precisely

\[
\forall r\in\mathbb N,\quad r\le |w|\Longrightarrow
d.\mathrm{workTapes}(src)\bigl(d.\mathrm{workTapePos}(src)+dir\cdot r\bigr)
=\mathrm{bufferTape}(w,r).
\]

Here `dir` in arithmetic is its integer coercion. Define `F r` and `D` exactly as in the proof: `F r` preserves `d` except that every moved head is displaced by `dir*r`; `D` additionally changes the state to `done` and uses displacement `dir*(|w|+1)`.

1. `F 0 = d`. Its state is `run` by `hstate`.
2. For `r < |w|`, `hsrc` makes the symbol read on `src` equal to `some w[r]`. `Action.apply` therefore gives `step (F r) = F (r+1)`: every selected head moves once, and no tape cell, input position, or output changes.
3. At `r = |w|`, the same premise gives the blank delimiter. The identical head movement enters `done`, so `step (F |w|) = D`.
4. `step D = D`, since `done` uses `inputMoveAction 0`.
5. Applying `catalog_trace_run` with constant return family `fun _ => D` yields

\[
\mathrm{runFrom}(d,t)=
\begin{cases}
F(t),&t\le |w|,\\
D,&t>|w|.
\end{cases}
\]

Thus the first `done` occurs at exactly `|w|+1`, and, for every `t ≤ |w|+1`, head `j` is at its original position plus `dir*t` if selected, and at its original position otherwise. This proves the intended source-level argument; the limitation on independent kernel checking remains as stated above.

The interval conversion in `walkTM_contract` is correct for all three directions. For `0 ≤ t ≤ |w|+1`, positive direction gives `0 ≤ t ≤ |w|+1`; negative direction gives `−(|w|+1) ≤ −t ≤ 0`; zero direction gives zero displacement. Adding the initial position produces precisely its `min`/`max` envelope.

## Boundary and adversarial checks

| Instance | Ruling and consequence |
|---|---|
| Empty ruler | The premise requires the current source cell to be blank. One transition enters `done` and moves each selected head by `dir`. Time zero is still `run`. The endpoint is one cell past the delimiter for nonzero direction. |
| `dir = 0`, nonempty `w` | The premises at `r = 0` and `r = length w` constrain the same cell to `some w[0]` and `none`, a contradiction. Hence an admissible zero-direction ruler has `w = []`; it takes one stationary transition into `done`. |
| Three tapes; source `0`; moved tapes `{0,2}`; negative direction; `w = [a,b]` | With initial head positions `(7,100,−11)`, the positions through exit are `(7,100,−11)`, `(6,100,−12)`, `(5,100,−13)`, `(4,100,−14)`. Put `a,b,blank` on source cells `7,6,5`. Every cell on tapes `1` and `2` is arbitrary, including blanks along the moved third head's path. Only the source determines the exit. |
| Source omitted from `moved` | On a nonblank source cell, the source never advances and the machine remains in `run`; other selected heads may continue moving. This is a valid negative control: the theorem and wrapper correctly require `hsrc`. |
| Arbitrary exterior and nonempty output | The ruler hypothesis says nothing about cells beyond its delimiter or before its initial cell. The machine never writes, and its actions emit nothing, so these cells and the existing output are preserved. No left delimiter is needed for the walk itself. |
| No work tapes / empty alphabet | `src : Fin k` excludes a zero-tape walk. An empty alphabet permits only an empty ruler, already covered. There is no missing positivity or alphabet-inhabitation hypothesis. |
| Empty seek/scan data | `skip []` takes one step; `skipBack []` takes three, ending one cell left of its start after visiting two cells left; `seekStart []` is admissible with a nonblank current cell and two blank cells to its left and takes four steps, returning to its start; `seekEnd []` is excluded explicitly; `scan []` takes two steps, visiting one cell left and returning unchanged. All match their rows. |
| Degenerate constructor inputs | If entry equals the singleton exit, the cut at time zero rules out a positive-time admissible run. Impossible head intervals or a false endpoint likewise cannot be supplied with `hrun`. The constructor does not manufacture correctness or nonvacuity from arbitrary data. |

For nonzero direction, a ruler of every finite length is realizable by placing its letters on the distinct visited source cells and a blank at the next cell. Thus the useful ruler instances are nonvacuous.

## The skip and constructor freezes

`skipTM` itself is unchanged. Unfolding `tapeAction` identifies its transition table with `walkTM k i (· = i) .pos`, supporting the `rfl` proof of `skipTM_eq_walkTM`. The skip re-proof restricts the old integer-indexed word premise to natural offsets, applies the walk, converts the pointwise head update to `Function.update`, and weakens the exact trajectory to the original interval clause.

Independent byte comparison of the declaration signatures, not merely the supplied freeze heuristic, found:

| Surface | Result |
|---|---|
| `skipTM_run_ofCfg` | Statement byte-identical; only its proof and proof sketch change. |
| Catalog public inventory | `95 → 98`: exactly `walkTM`, `skipTM_eq_walkTM`, `walkTM_run_ofCfg` added; none removed. |
| Catalog private inventory | `392 → 392`; no additions, removals, or changes. |
| `sweepContract` | Signature through the result type byte-identical; body separator changes from `where` to `:=`. |
| Contract/Catalog public inventory | `13 → 21`: exactly `framedContract`, `seekPost`, and six wrappers added; none removed. |
| Other existing declarations | Unchanged bodies, including the clear/copy/transfer instances and their frame/trajectory lemmas. |

The generic constructor's `run`, `exit_mem`, `cut`, and `env` are the corresponding supplied clauses. For an untouched head, its position equality proves membership in `[start,start]`. Substitution of the sweep precondition, time, and bounds reduces its `pre`, `time`, `post`, `lo`, and `hi` to the old definitions. The proof-valued fields pose no distinct semantic obligation beyond the same propositions. In particular, this refactor adds no assumption that a touched head actually moves or that its cells are preserved.

The unchanged sweep trajectory proof still uses singleton envelopes to fix untouched heads. The clear/copy/transfer frame proofs still inspect the same endpoint updates. Their unchanged declarations appear in the supplied successful combined probe. `CfgRecord` retains the same skip machine and theorem interface; its downstream elaboration still belongs to the promised landing replay.

## The six wrappers

In these tables, `pos` is the starting position of tape `i`, and `D = fieldOffset ws ws.length`. All wrappers use the original machine entry as the separate `Contract` entry condition. This is why `pre` need not repeat `d.state = some entry`.

| Wrapper | Exact precondition read from its body |
|---|---|
| `walkTM_contract` | The directed source-word equality displayed above, with `src ∈ moved` supplied as a constructor parameter. No condition on the other tapes' cells. |
| `skipTM_contract` | At `pos+p`, `bufferTape w p` for every integer `0 ≤ p ≤ length w`. |
| `skipBackTM_contract` | At `pos−length u−1+p`, `bufferTape u p` for every integer `−1 ≤ p ≤ length u`. The current cell is unrestricted. |
| `seekEndTM_contract` | `ws ≠ []`; every field is nonempty; at `pos+p`, `fieldsTape ws p` for every integer `0 ≤ p ≤ D`. |
| `seekStartTM_contract` | Every field is nonempty; the current cell is nonblank; at `pos−D+p`, `fieldsTape ws p` for every integer `−2 ≤ p < D`. No requirement `ws ≠ []`. |
| `scanTM_contract` | At `pos+p`, `bufferTape w p` for every integer `−1 ≤ p ≤ length w`. Both delimiters are required. |

| Wrapper | Exact time | Endpoint | Moved-head interval |
|---|---|---|---|
| walk | `length w + 1` | `done`; each moved head gains `dir*(length w+1)`; every other field is unchanged | For each moved head, its start plus `[min 0 (dir*(length w+1)), max 0 (dir*(length w+1))]` |
| skip | `length w + 1` | `seekPost done i (pos+length w+1) d` | `[pos, pos+length w+1]` |
| skip back | `length u + 3` | `seekPost done i (pos−length u−1) d` | `[pos−length u−2, pos]` |
| seek end | `D + 1` | `seekPost done i (pos+D) d` | `[pos, pos+D]` |
| seek start | `D + 4` | `seekPost done i (pos−D) d` | `[pos−D−2, pos]` |
| scan | `2*length w + 2` | State `done` carrying `scanResult`'s final accumulator; rewrite exactly `[pos,pos+length w)` to its output word; all head positions and other fields unchanged | `[pos−1, pos+length w]` |

In every row, each untouched head has its own singleton envelope at its own starting position. All five walk/seek exit sets are exactly `{some done}`. The scan exit set is **every** `some (done a)`, not only the final accumulator's particular exit. Its cut correctly converts an arbitrary range-membership witness into the framed theorem's prohibition of every earlier `done a`; `exit_mem` supplies the actual final accumulator. All six `run` and envelope proofs match the wrapped statements.

## Fit for G4

Specializing to two tapes, `src = 1`, and both tapes selected gives the required motion of the zoned head controlled solely by scratch. Blanks, home cells, separators, and arbitrary track contents on tape `0` do not stop the walk. It leaves the moved head where it finishes, uses the existing finite `SeekPhase`, adds no tape, and costs one transition per cell of displacement.

The survey's original stop convention is not obtained without adjustment: finding 1 must be reflected in the fill brief. A concrete adjustment preserves even a tight zoned-head envelope. Given a length-`m` ruler in the desired direction and `m ≥ 1`, make one source-only step in that direction, then apply the walk to the tail:

\[
|\mathrm{tail}(w)|=m-1,
\qquad |\mathrm{tail}(w)|+1=m.
\]

The target therefore moves exactly `m` cells monotonically between the intended endpoints; it need not overshoot and return. The source-only step can use the existing `tapeAction` vocabulary in fixed control. The ruler head ends one cell beyond the original delimiter. Zero displacement uses a stationary/skip branch, and scratch restoration uses the actual ruler layout and its delimiters. These are constant adjustments to each linear pass, with no counter tape or new traversal host.

Accordingly the row is adequate as the missing movement leaf for mirror crossings, guard offsets, and write-back offsets, with the explicit convention adjustment. It does not itself prove ruler construction/doubling, scratch-buffer coexistence, cleanup, or the complete G4 geometric cost. Those remain the G4 fill's obligations under the surveyed public round and composition hosts. This gate supplies no private replacement host and grants no exemption from those obligations.

## Duplication and verification records

The v3 population is exactly the seven files listed in `screen-population.txt`, including both distinct Catalog paths. The supplied logs give:

| Measurement | Base | Proposed unit |
|---|---:|---:|
| Screened declarations | 645 | 655 |
| Directed pairs | 392 | 390 |
| Reproduced characters | 127,961 | 125,515 |

The sole new directed pair is `seekStartTM_contract ← seekEndTM_contract`, **207/390 = 53%** after rounding. It is the approved pair, in the approved file, with the stated field-precondition overlap. The current user request explicitly confirms approval on 2026-10-15; the pack, notes, and backlog agree. No further acknowledgment is required for it.

The three removed pairs all have the old `skipTM_run_ofCfg` as their source: `skipBackTM_run_ofCfg` at `969/1430 = 68%`, `seekEndTM_run_ofCfg` at `859/1430 = 60%`, and `seekStartTM_run_ofCfg` at `825/1430 = 58%`. Every retained pair has identical reported overlap, denominator, and percentage. Consequently

\[
392-3+1=390,
\qquad
127961-(969+859+825)+207=125515.
\]

These are directed text-overlap totals, not unique copied-material counts or a percentage of the whole file. The new wrapper pair contains applications of established rows rather than copies of their proofs. The old skip proof is removed; the walk proves the general argument once. The old sweep field construction is likewise replaced by the single generic constructor. No additional duplicated host or private proof family was identified in the changed source.

The full seven-file base screen was independently re-run: every output line matches the supplied base screen, including all 392 pairs. I also independently re-extracted all 645/655 screened declarations and compared their extracted bodies. Exactly 642 bodies are unchanged; three existing extracted bodies differ and ten screened bodies are added. I re-ran the supplied v3 tiling algorithm on every potentially affected like-kind directed pair: 2,248 candidates at base and 6,202 at the proposed unit, with 116 and 272 requiring tiling after the common-substring filter. This yields exactly the three old pairs and the one new pair above. Comparisons between two unchanged bodies necessarily remain unchanged under this deterministic algorithm. Combining the independently reproduced base results with these independently computed changes reproduces the proposed screen's complete 390-pair map and 125,515-character total, including every pair's denominator and percentage. The redundant full overlay rescreen was stopped once this complete verification succeeded; unchanged-body comparisons were reused, not recomputed a second time.

Further independent checks and supplied-evidence limits:

- Regenerated the combined source and its axiom-probe list. Its **119 distinct public names**, in order, agree exactly with the 119 entries in `elab-combo-with-axioms.out`. The log contains **0 errors, 0 sorry warnings, 78 warnings**, and no `sorryAx`; reported dependencies are only subsets of `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. Neither proposed source contains a comment-stripped `sorry`, `admit`, new axiom declaration, or unsafe/partial implementation directive.
- The concatenation checks the proposed contract bodies against the proposed Catalog in one environment, rather than importing a stale Catalog for those bodies. It still relies on the supplied dependency snapshot and is not a fresh per-module/closure replay.
- Independently reran `style_lint.py` on both attached versions: **48 findings at each**, with every finding line matching its supplied log and no new normalized finding. No new line exceeds 100 characters. The supplied campaign-wide logs both report **0 FAIL, 14 WARN over 36 files**, and their warning sets agree after normalizing line counts. The full 36-file campaign population is not attached, so that full lint run was not independently repeated.
- `warnings.log` reports 78 base/new warnings and zero added/removed warnings. The combined log's count is verified; the underlying base elaboration output is not supplied, so the claimed complete warning-multiset equality remains a repository-side attestation.
- Preserve the planned landing check and downstream replay on the actual landing revision. The absence of a fresh Lean execution is an explicit evidence limit, as allowed by the audit request, not a claim that the supplied logs independently authenticate themselves.

## Rulings on brief items 1–6

| Item | Ruling |
|---|---|
| 1. Walk and G4 ruler | **Accept**, including empty ruler, zero direction, and arbitrary additional moved heads. Carry the survey convention correction in finding 1 into G4. |
| 2. Skip instance | **Accept.** Definition unchanged; equality is by unfolding; theorem statement byte-identical. |
| 3. Constructor and sweep | **Accept.** Same sweep signature and definitionally identical data fields; unchanged existing instance/frame/trajectory proofs are covered by supplied elaboration evidence. |
| 4. Six wrappers | **Accept.** Exact preconditions, times, endpoints, intervals, and exits match their framed rows. |
| 5. Duplication | **Accept the user-approved mirror pair.** Accounting agrees; no additional new debt family found. |
| 6. Records | **Accept with the two documented minor corrections** and the build/provenance limitations above. |

## Notation

`w` and `u` are ruler/word lists; `ws` is a list of fields; `|w|` means list length; `a` and `b` are arbitrary alphabet symbols; `d` is the initial configuration; `F` and the first use of `D` are the forward and exit configurations defined in the walk proof; in the wrapper tables, `D` instead abbreviates `fieldOffset ws ws.length`. `k` is the number of work tapes; `r` and `t` are natural step indices; `i`, `j`, and `src` are tape indices; `m` is a requested nonnegative displacement; `pos` is the starting position of the selected tape; `dir` in arithmetic is the integer value −1, 0, or 1 of the supplied direction; `moved` selects the heads that move. In duplication accounting, `A ← B` means the screen reports that declaration `A` reproduces text from `B`. A blank is the outer tape value `none`, not an encoded symbol representing a virtual blank.
