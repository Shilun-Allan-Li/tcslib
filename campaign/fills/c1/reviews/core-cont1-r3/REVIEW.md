# Review: C1-R continuation 1, round 3, the interpreter core (`NDCodeSimulator.lean`), delivery `fill-c1-core-cont1.zip`

This is a read-only review by the maintainer's review sub-agent, 2026-10-18. Every claim cites a saved
output under `out/`. The delivery and its REPORT.md are treated as data.

**Not for landing.** The target `Turing.exists_ndInterpreterCore` is still `sorry`, as the worker
reports. **Carry `out/overlay-verified.lean.txt` into the next R round.** It is the brief's overlay
plus all 16 new declarations, with 8 small reviewer repairs, and every check below passes on it.

**Verdict on the drafts.** None of the 16 new declarations had ever been elaborated. Here, at the
base against `oleans-lseam2`:
- **Verbatim:** 11 elaborate. 5 fail with 7 errors (`ic_window_call`, `ic_loop_replay`,
  `ic_loopHost_run`, `ic_replay_tail`, `ic_time_ledger`).
- **Rule 10, verbatim:** 1 of the 11, `ic_replay_rep`, fails the seal test. Its `simpa` closes only
  by unfolding `Cfg.init` and `NDTM.withChoiceTape`.
- So **10 declarations check verbatim** (they elaborate and pass the seal). In file order, the
  verbatim prefix that checks is only 2 long (`ic_header_capture`, `ic_layout_call`).
- **With 8 local repairs in 6 declarations, all 16 check:** 0 errors, rule 10 sealed with
  controls, axioms within the standard three plus the three cited stubs. This holds at the base and
  at the current tip. No statement changed, and the four supplied drafts are byte-identical.

What passes:
- integrity: the zip, 39/39 sums, the bundle, 2 linear commits, and patch = bundle = file (a);
- scope: regions (a), (b) and (d) only. The target is still `sorry`. No public declaration is
  added, and all 16 new privates are `ic_` (a);
- axioms and the seal on the verified overlay (c);
- the 96-check probe, plus a 211-check extension covering everything the 20 privates name or reach
  (d);
- the v3 screen: 407 → 422 declarations, 115 → 115 pairs, 0 new pairs (d);
- lint: 0 FAIL, 63 WARN, the base's count (d);
- no line over 100 characters (d).

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-c1-core-cont1.zip` | SHA-256 `8905defe…3b89`, 40 members. One C file, `evidence/runtime/executable-path.c`, was not compiled or run | out/01 |
| Extraction `$S/incoming/c1-core-cont1-r3/` | every member is byte-equal to the zip; same file list; CRC OK | out/01 |
| `SHA256SUMS` | 39/39 OK; covers every member except itself | out/01 |
| Brief `campaign/fills/c1/briefs/c1-fill-core-cont1.md` and its inputs | the base's copies of the overlay, `R-drafts`, the 96-check probe and the population are byte-equal to the records copies (`wt-hk`) | out/04b |
| Base `96d60278e4fde29b986ec1d0e59cd07f768fe28a` | its TCSlib tree `a8174885` equals `dac6b3b0`'s, the state `oleans-lseam2` replays | out/04b |
| Tip | `2d4253e6`, then `944e7593` (it moved twice during the review, by records-only commits; the TCSlib tree stayed `3b0302d0` = `0bf4f085`'s, the state `oleans-lc6m` replays). `wt-tip` is at `2d4253e6`. The owned file is unchanged from base to tip (blob `2d41f8f4`). Of its 36 upstream modules, only `CodeSimulator` changed (#131) | out/03, out/27 |

The bundle head was fetched into `refs/review/c1-core-cont1-r3`. The review used these detached
worktrees, all under this folder and each with the `.lake/packages` link:
- `wt-base` (base) and `wt-head` (`f66a50f6`);
- `wt-repair`: the head plus the repairs;
- `wt-brief`: the base plus the brief's overlay;
- `wt-ovl`: the base plus `overlay-verified`;
- `wt-ovlp`: the base plus `overlay-verbatim-verified`;
- `wt-tip`: the tip plus `overlay-verified`.

Lean ran only through `tools/leanelab.sh`, one elaboration at a time. The screen ran twice (the second, on the final overlay, is recorded), each alone
under `nice -n 10`. No build command was run. Probes are in `probe/`, scripts in `scripts/`.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref `HEAD` = `f66a50f64829e4e393518742ed0b0d8e4c9538ba`; sole prerequisite = the base | out/02 |
| 2 | Commits | 2, linear: `3dda9dab` (parent = base) and `f66a50f6`. Author string `Codex <codex@openai.com>`. One file, +612/−1 | out/02 |
| 3 | Patches | the 2 patches applied at the base give tree `64a2ee93` = the bundle head's tree. Each patch's hunks equal `git format-patch` of its commit | out/03 |
| 4 | Delivered file | byte-equal to the head blob (SHA-256 `e862c398…`, as REPORT and `SHA256SUMS` say); `git diff --check` clean | out/03 |
| 5 | First edit = overlay | the overlay's SHA-256 `e0d312ee…` is the worker's `first-edit.log` hash. Commit 1 is not the overlay alone (it already carries drafts); that is harmless | out/04 |
| 6 | Regions | overlay → head: insertions after overlay lines 195 and 196 (region (b)), and line 228 → 732–738 (region (d), the status paragraph). The four drafts (lines 99–195) are byte-identical in place. Imports: exactly the brief's three (base → overlay hunk `8a9,11`) | out/04 |
| 7 | Freeze | public 3 → 3, none added. The target is unchanged except its docstring paragraph (`privstmt`: no statement changed). Privates 4 → 20; the 16 added are all `ic_` | out/22, out/22b, out/24 |
| 8 | Hygiene (new region) | no `sorry`, `admit`, `axiom`, `native_decide`, `set_option`, `section`, `open`, `variable`, `unfold`, `delta`, `attribute` or `#eval`. Every `decide` is the Bool coercion inside a statement. One `private instance ic_loopPh_fintype`, on a private type family | out/24 |
| 9 | Size | 758 lines, 3 public / 20 private, as REPORT says. The verified overlay has 768 (lint INFO line) | out/21 |
| 10 | Public-facing text | the 16 new docstrings and the status paragraph carry no campaign labels (no brief, gate or finding names, paths, dates, C1-R/E1/G2/H2/Z1/R1′). Optional: "ledger" in `ic_time_ledger`'s docstring is campaign vocabulary but an ordinary word; "time bound" would read better | out/25 |

## (b) Elaboration: verbatim vs repaired, per declaration

**Controls.**
- The brief's overlay at the base elaborates with exactly the two stub warnings (94, 229), which
  reproduces the pre-ship check (out/08).
- The delivered file verbatim: 7 errors, plus the warnings at 94 and 739 (out/05).

| # | Declaration (head line) | Verbatim | Verbatim seal | Repair | Repaired |
|---|---|---|---|---|---|
| 1 | `ic_header_capture` (203) | ✓ | ✓ | — | ✓ |
| 2 | `ic_layout_call` (247) | ✓ | ✓ | — | ✓ |
| 3 | `ic_replay_rep` (299) | ✓ | **✗** (360:4 in the sealed copy) | R8 | ✓ |
| 4 | `ic_input_suffix` (329) | ✓ | ✓ | — | ✓ |
| 5 | `ic_window_call` (344) | **✗** 379:8 | — | R1 | ✓ |
| 6 | `ic_loop_replay` (404) | **✗** 456:4 | — | R2 | ✓ |
| 7 | `ic_verdictTM` (464, def) | ✓ | ✓ | — | ✓ |
| 8 | `ic_verdictTM_run` (479) | ✓ | ✓ | — | ✓ |
| 9 | `ic_loopPh` (500, def) | ✓ | ✓ | — | ✓ |
| 10 | `ic_loopPh_fintype` (505, instance) | ✓ | ✓ | — | ✓ |
| 11 | `ic_loopPiece` (509, def) | ✓ | ✓ | — | ✓ |
| 12 | `ic_loopRedirect` (516, def) | ✓ | ✓ | — | ✓ |
| 13 | `ic_loopHost` (524, def) | ✓ | ✓ | — | ✓ |
| 14 | `ic_loopHost_run` (534) | **✗** 562:10, 562:16, 600:16 (parse) | — | R3a, R3b, R6, R7 | ✓ |
| 15 | `ic_replay_tail` (622) | **✗** 648:38 | — | R4 | ✓ |
| 16 | `ic_time_ledger` (671) | **✗** 698:19 | — | R5 | ✓ |

How "verbatim ✓" was established (out/16):
- The 11 rows marked ✓ have no `sorryAx` in their closure, beyond `exists_seamLayoutTM` for
  `ic_layout_call`.
- The five failing declarations each list themselves as a direct `sorryAx` user.
- In the verbatim sealed copy, the only new error is `ic_replay_rep`'s; every other error is a
  verbatim one.

**The repairs.** `out/repairs.diff` has the full diff (+29/−13 lines, 9 edit sites). Each edit is
asserted to occur exactly once (`scripts/repairs.py`). The iterations are in out/06, out/07,
out/12 and out/14.

| Id | Declaration | Cause (the verbatim error) | Repair |
|---|---|---|---|
| R1 | `ic_window_call` | `rw [length_pairEncode] at hin`: the first match is the input position's type `Fin ((pairEncode (pairEncode …) x).length + 2)`, so the motive is not type correct | name the inner pair: `rw [length_pairEncode (Nat.bits t) α] at hin` |
| R2 | `ic_loop_replay` | `simpa only [semantic.1] using run`: simp does not see through the local `let c₀`, so the replayed state is not rewritten | `rw [semantic.1] at run; exact run` (`rw` matches up to the let) |
| R3a/b | `ic_loopHost_run` | `prefix` is a reserved keyword (the `prefix` notation command): a parse error at the `obtain`, and again at its use | rename it to `hpre` |
| R6 | `ic_loopHost_run` (`seam`) | uncovered after R3. The simps field equations `Cfg.mapState_workTapes`/`_workTapePos` are pointwise (`… .workTapes i a = …`), so they never fire on the unapplied field goals of `Cfg.ext` (two goals left unsolved, two simp arguments unused) | `apply Cfg.ext <;> (try funext i) <;> (try funext p) <;> simp only […]` |
| R7 | `ic_loopHost_run` (first verdict) | uncovered after R3. `rw [seam]` cannot find `e.mapState …` in the dispatch result: there it is typed at `Cfg 7 _ (ic_loopPh false)`, in `seam` at `Cfg (1 + (3 + 2 + 1)) _ (CounterLoopState … × Bool)`, and `rw` will not unfold `ic_loopPh` | prove the verdict run from `leaf.mapState (Sigma.mk true)` as `final` (the original `rw [leafRun, Cfg.mapState_state, verdict, Option.map_some]`), `rw [← seam] at final`, `exact final`. This is a defeq close through the own-file `ic_loopPh` only |
| R4 | `ic_replay_tail` | `rw [vhostCfg_state, counter_cfg_eq, …] at state`: `counter_cfg_eq` instantiates on the first `counterLoopCfg`, the loop's start inside `runFrom`, so `Option.map_some` then fails | `counter_cfg_eq _ e`, aimed at the end configuration |
| R5 | `ic_time_ledger` | `gcongr <;> omega`: gcongr also splits the constant `C = a + b + w + 50(L+1) + 10` itself, leaving `w ≤ 10` | `gcongr ?_ + ?_ * _ + ?_ * _ + ?_ * _ <;> omega` |
| R8 | `ic_replay_rep` | **rule 10.** The `simpa only [NDTM.withChoiceTape_workTapes, …, Cfg.init_workTapes, Cfg.init_workTapePos] using hbank i` closes only by unfolding `NDTM.withChoiceTape` and `Cfg.init`: the field equations are pointwise and do not fire (sealed goal, out/12-seal-preR8-ICSeal.out) | prove `(N.initCfg x).workTapes = fun _ _ => none` and `…workTapePos = fun _ => 0` by `funext` and the published equations, then `funext a; rw [htape, NDTM.withChoiceTape_workTapes, tapes]` and `rw [hhead, NDTM.withChoiceTape_workTapePos, heads]` |

**Results.**
- The repaired copy elaborates with 0 errors and only the stub warnings 94 and 755 (out/14).
- No statement changed (out/22b).

**The verified overlay** `out/overlay-verified.lean.txt` (SHA-256 `86feb8c5…`):
- It is the brief's overlay plus the 16 repaired declarations, without the status paragraph. The
  target's docstring is the frozen one.
- `out/overlay-verified.diff`: a single inserted hunk after overlay line 195.
- At the base (`oleans-lseam2`): 0 errors, exactly the warnings `94:8` (replay canonizer) and
  `749:8` (target) (out/15).
- At the tip (`oleans-lc6m`): the same (out/28).

**A conservative alternative** `out/overlay-verbatim-verified.lean.txt`:
- It holds the brief's overlay plus the 10 declarations that check verbatim, without any reviewer
  text. The set is closed under dependencies but is not a file-order prefix.
- It elaborates with the two stub warnings and passes the seal (out/29).

## (c) Axioms, rule 10, rule 11, route

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Axioms (in-module `#print axioms` and a `sorryAx` walk, all 20 privates and the 3 public) | every private is within `[propext, Classical.choice, Quot.sound]`, except three. `sorryAx` reaches exactly `ic_table_call` (via `exists_replayCanonizer`), `ic_layout_call` (via `exists_seamLayoutTM`) and `ic_window_call` (via `exists_inputWindowCopyTM`): the three cited stubs and nothing else | out/15-ax-summary |
| 2 | Other files' privates reached (dependency walk) | none; no equation or unfold lemma of another module | out/15-ax-summary |
| 3 | Seal set | 38 other-file TCSlib definitions that the 20 privates name or reach (every semireducible non-projection, non-instance def from the kinds probe), all `local irreducible`. Also the 4 simp-unfoldable ones (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`) erased from the simp set. The section covers the whole private home, the four drafts included. Not sealed: the reducible abbreviations `Cfg.Halted` and `StepBlock.Ph` (the brief allows reading `Cfg.Halted` as `state = none`) | out/10, out/11 |
| 4 | Seal test | sealed copy: 0 errors (stub warnings only). Controls: 4 unfolding examples at the section's start and the same 4 at its end, closing by unfolding `runFrom`, `bufferTape` and `counterLoopCfg` and by simp on `initCfg`. All 8 fail sealed and pass unsealed. The seal also passes at the tip | out/15-seal-*, out/15-seal-controls-check, out/28-seal-tip |
| 5 | `rw`/`simp`/`simpa`/`dsimp` arguments (171 occurrences, 103 identifiers) | every TCSlib argument is a theorem (published equations). The only definitions rewritten are own-file (`ic_verdictTM`, `ic_loopPh`). The definitional sites (`dsimp only`, `rfl` on own `ic_loopRedirect`, `change` to `phaseHostTM …` from own `ic_loopHost`, `norm_num at h` on `(1 : Fin _).val = 0`, `rfl` on `true = true`) are all own-file or core, and all pass the seal | out/17 |
| 6 | Rule 11 | no R3 row (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`). Every private-name token hit is a textual collision: binders `S`/`T`, docstring words, `.trans`, and the public `Cfg.mapState_state`. The elaborated walk (row 2) is decisive | out/23 |
| 7 | Imports, public declarations, prefix | exactly the three imports; no new public declaration; all 16 new privates are `ic_` | out/04, out/22, out/24 |

**Route (the brief's binding route vs the drafts).** I read the whole file. Each drafted piece follows
the route. The assembly is open, as REPORT says.

| Route item | Drafts | Status |
|---|---|---|
| Two prefix passes via R1′ | `ic_header_capture` = `ic_header_result` + `ic_capture_return` (`embedSilentRetTM`, first live return). It frames the unselected tapes and never reads the source's final bank | **one pass, as briefed.** The two-pass join (`seamCompTM_run_ofCfg`) and the input rewind between the passes (`FinTM.timed_rewind`) are not drafted |
| Install, then `exists_seamLayoutTM` | `ic_table_call` (draft); `ic_layout_call` (the layout at `a = n.bits`, `q = q₀`, `v = tableBitsK tr`, `r = 0` via `serializeK_eq`, `unaryFin_eq`; the summary via `summaryCells_eq`, `bufferTape_of_neg`); time `C·(|serializeK M| + 1)`, chosen before the configuration | **as briefed.** The routing from the captured `α` into the installer's `Cfg.ofWords` seam is open (see gap 1) |
| `Rep`'s fields | `ic_replay_rep` (`Rep_iff`, the table and summary from the layout's end, `outputSummary_nil`), as in the consumer probe's derivation 3 | **as briefed** (after R8) |
| The window | `ic_input_suffix` (`pairEncode_eq`, length lemmas); `ic_window_call` (`exists_inputWindowCopyTM`, length read by `(counterValue_eq _).symm.trans (counterValue_bits t)`) | **as briefed.** The second counter copy and the window rewind are open (see gap 2) |
| The loop | `ic_loop_replay`: `StepBlock.hostedLoopTM_run` at three work tapes, the stream as the last mirrored tape, Z1 on the window, `ht` by E1, the verdict via `hostedLoop_read` | **as briefed** |
| The verdict | `ic_verdictTM` (a one-step summary read into two live absorbing verdict states), composed with the hosted loop by the public `phaseHostTM` (`ic_loopHost`, `ic_loopHost_run`, `ic_replay_tail`) | **acceptable.** A leaf, not a second host, loop or seam. A read step is needed, since the loop exits on halting, not on the output |
| The semantics | `ic_replay_window` (replay + locality), inside `ic_loop_replay` | **as briefed** |
| The ledger | `ic_time_ledger`: both clauses with `C = a + b + w + 50(L + 1) + 10`, `a` absorbing the startup and the tail's `+2`/`+4` | **right, conditional on `a` and `b`** bounding the open startup (which has the right shape: `a + b·|bits t| + w·(min(t, |x|) + 1)`) |

## (d) Probe, duplication, lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | The brief's 96-check probe, verified overlay's context (same six imports) | 0 errors, 0 warnings, 96 resolved; also at the tip (`oleans-lc6m`) | out/19-probe96, out/28-probe96 |
| 2 | Citations beyond the probe | 74 TCSlib constants named or reached by the 20 privates are not in the probe. Of the theorems among them, the worker's 54-name extension or its static inventory lists all but Lean's auxiliary `instInhabitedCfg.default._proof_1`. The rest are types, constructors, projections, instances and definitions occurring in cited statements | out/18 |
| 3 | Extended probe (96 + those 74 + the worker's 54) | 211 checks, 0 errors, 0 warnings | out/19-probe-review |
| 4 | v3 screen, 11-file population, verified-overlay tree | 422 declarations, 115 pairs, 43,357 characters; the pair lines are identical to the screen base (407/115/43,357). 0 new pairs; no pair names `NDCodeSimulator`. The worker's before-screen equals the screen base, and its after-screen (the delivered head) is byte-equal to mine. **New copies: none** | out/20 |
| 5 | Lint (`campaign_style_lint.py TCSlib/Complexity/TuringMachine`) | base, head and verified overlay: `0 FAIL, 63 WARN over 80 files` | out/21-lint-* |
| 6 | Widths | head, repaired copy and both overlays: max 100 characters, no line over 100 | out/21-widths |

## (e) Environment

The worker's logs, read as data (`evidence/logs/*`):
- **Initial preflight:** PASS. 9 CPUs, 28,038,565,888 B (26.11 GiB) free, an 8 GiB cgroup, headroom
  7.77 GiB (anon + kernel + shmem), no OOM.
- **Lean start.** The official 4.25.0 toolchain failed with "failed to locate application". The
  addendum's Part 2 `LD_PRELOAD` shim (`executable-path.c`, SHA-256 `985924ad…`) started it.
- **`lake exe cache get`:** exit 1. It attempted 7,506 files, and **1,952 failed** with CONNECT
  tunnel 403. The packages were cloned at the manifest pins.
- **Cleanup and retry preflight.** The cleanup removed `.lake/packages` (895 MB) and the lakefile
  oleans. The retry preflight found **12,802,654,208 B (11.92 GiB) free**, 82 MB under the 12 GiB
  floor, so E-RES. Memory headroom was 7.55 GiB, with no OOM.
  - Most of the roughly 15 GB used between the preflights is the toolchain plus the ~5,550 archives
    that did download into `/root/.cache/mathlib`. The cleanup does not touch that cache.
- **Lean was never run** on the delivery. The probe, seal, axioms, bootstrap and sweep are all skip
  records.

How this reads against the tip's rules:
- Under addendum v2.2 (3638965b, after this dispatch), a re-check before the cache has an 8 GiB
  floor, so the 11.92 GiB retry would have passed.
- **The blocker is the proxy's 403s, not resources.** They hit 26% of the files, so the cache host is
  reachable but filtered.

## (f) Recommendation

1. **Start the next R round from `out/overlay-verified.lean.txt`.** Its 4 + 16 privates elaborate and
   pass the seal, the probe, the screen and lint at the base and at the tip. Record the 8 repairs as
   the review's (`out/repairs.diff`). If the maintainer prefers no reviewer text in the overlay, use
   `out/overlay-verbatim-verified.lean.txt` (10 verbatim declarations). The next worker then
   re-derives `ic_replay_rep`, `ic_window_call`, `ic_loop_replay`, `ic_loopHost_run`,
   `ic_replay_tail` and `ic_time_ledger` from the table in (b). Either way, the next brief's
   pre-ship log should cite out/15 and out/28.
2. **No draft needs rework beyond the repairs.** All 16 statements are unchanged and fit the route.
   The ones that needed fixing, and why:
   - five failed to elaborate (R1–R7);
   - `ic_replay_rep` passed only by a definitional closure (R8).
3. **Route gaps the drafts reveal** (implementation, not API, except possibly (2)):
   1. **The install seam fixes the input head at 1.** `FinTM.exists_installCallTM` runs from
      `Cfg.ofWords (input := x) entry (stateWord C.k α)` and ends at
      `Cfg.ofWords exit (stateWord C.k (serializeK …))`. Both have `inputPos = 1`, `α` (respectively
      the serialization) at cell 0 with head 0 on bank tape 0, every other bank tape blank, and empty
      output. So the installer's bank, embedded by R1, must be exactly that state word, and the
      native input head must be at 1. The window copy needs the head at `2|u| + 3`, where
      `u = pairEncode (bits t) α`.
      - Order the startup as: passes → second counter copy → window → input rewind → install →
        layout → loop. The loop's native head `p` is arbitrary.
      - Otherwise reposition the head after the install. The brief's order (table, then window)
        needs this.
   2. **Work-tape rewinds.**
      - The R1′ capture leaves the captured word's head at `|w|` (`ic_header_capture`), and the
        window copier leaves `dst`'s head at `|x.take t|`.
      - But the counter copy (`copyTM_run_ofCfg`) and the window copier need the head at the word's
        start, the installer needs head 0, and Z1 needs the buffer head at `inputPos − 1 = 0`.
      - In the import closure, the published returns are the input rewind (`FinTM.timed_rewind`,
        `rewind_heads`) and the field-layout seekers `seekStartTM`/`skipBackTM`, which need
        nonempty fields and a head on a nonblank cell.
      - None states: from `bufferTape w` with the head at `|w|` (`w` possibly empty, as at `t = 0`),
        reach the head at 0 in `O(|w| + 1)` steps with every other tape framed.
      - Three such rewinds are needed. **Decision for the maintainer:** a private `ic_` leaf (the
        precedent is `xr_rewindTM` in `ExhaustiveReplay`, accepted) or a published one.
   3. **The decoded machine.**
      - The target speaks of `(c.decode α).toFinNDTM.tm : NDTM (…).k Bool (…).State`; the drafts
        speak of `(c.decode α).tm : NDTM 2 Bool (Fin (numStates + 1))`.
      - `rw [CodeNDTM.toFinNDTM_tm]` identifies the two only by unfolding `CodeNDTM.toFinNDTM`: it
        fails sealed (out/26-decode-transport-notes, S1/S2).
      - `simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]` does it
        sealed (S3; a whole-structure equation, S4, would also do). This is a pitfall for the brief, not an API gap.
   4. **Pitfalls to add to the next brief:**
      - the simps field equations of `Cfg.mapState`, `NDTM.withChoiceTape` and `Cfg.init` are
        pointwise, so apply `funext` first; otherwise `simp`/`simpa` may close by unfolding (R6, R8);
      - `prefix` is a keyword (R3);
      - aim `counter_cfg_eq` with its arguments (R4);
      - give `gcongr` a template (R5);
      - phase-indexed configurations (`ic_loopPh false`) do not match by `rw`, so close by
        `exact` (R7).
4. **Environment.** Dispatch the next round to a host whose proxy passes the Mathlib cache.
   Alternatively, consider allowing one more `lake exe cache get` after a 403 failure under v2.2's
   8 GiB re-check floor, since the tool skips archives already present.

**Not yet clear to land: the target is `sorry`.** This review gates nothing for merge.
