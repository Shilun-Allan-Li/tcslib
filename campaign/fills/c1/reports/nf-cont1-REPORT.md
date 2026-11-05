# Fill report — NF cont1 (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`): complete

**Status: complete.** The target `Turing.FinNDTM.exists_codeNDTM_accepts_linear` is proved, on
`[propext, Classical.choice, Quot.sound]`; no declaration reaches `sorryAx`. Final commit
`825ee3f583356008c4e1400e991756a3afe41763` on `fill/c1-nf-cont1` (7 commits on the base, as the
patch series and the bundle carry them). Checkpoints reached: **3, 4, 5, 6, 7, 8**, one commit and
one zip each, each delivered at once:

| Checkpoint | Commit | Zip |
|---|---|---|
| 3 — the input's replay, the layout, the return of tape `0` | `15fd6cf7` | `fill-c1-nf-cont1-cp3.zip` |
| 4 — a work tape's replay on tape `1`, the exit invariant, the clear | `b76f4fb7` | `-cp4.zip` |
| 5 — the characterization, `hV`, the verdict on a display | `59737ab6` | `-cp5.zip` |
| 6 — the forward transfer and the ledger | `62890cc4` | `-cp6.zip` |
| 7 — the backward transfer | `d8b264ed` | `-cp7.zip` |
| 8 — the target | `ba46b709` | `-cp8.zip` |
| consolidation after the first after screen (§7) | `825ee3f5` | this zip |

Agent: Claude.

## 1. Base, branch and environment

- **Base** `348781a383f102d971fca153c818026b4f49fbf6` on `lean/c1-nf-partial`. Ancestor check
  (`git merge-base --is-ancestor <base> origin/lean/c1-nf-partial`): **passed**. Branch
  `fill/c1-nf-cont1` created at the base (`git rev-parse HEAD` printed the base). Owned file's blob
  at the base: `e6432b1e6cf6eb33f81bff05eb389b09dd7cb9f0` (**matches**). `git diff --quiet
  5241eb82… HEAD -- '*.lean'` printed **same-Lean**. No rebase, merge or cherry-pick.
- **Brief**: the attached `c1-fill-nf-cont1.md`, SHA-256
  `7853cd44b1f5c6aac7e260a7a6fcca9e1471faae96f1dbd06e4dca273da44c72` (as stated by the user). The
  copy in the repository (`campaign/fills/c1/briefs/c1-fill-nf-cont1.md`, SHA-256 `780719d8…`)
  differs only in carrying the placeholder `@ANCESTOR@` where the attached brief names the base
  hash (three lines). The addendum in the repository is byte-identical to the attached v2.6
  (SHA-256 `9f5bd5e7…`).
- **Preflight** (`evidence/logs/preflight.log`, addendum v2.6 Part 1 item 1): `nproc` **4**;
  cgroup v1 memory limit **14,341,881,856 B**; memory in use `usage_in_bytes − total_cache +
  total_shmem` = 758,661,120 − 708,964,352 + 0 = **49,696,768 B**; headroom **13.31 GiB** (floor
  4 GiB); clone filesystem ext4 (`/dev/vda`), **29.36 GiB free** (floor 12 GiB); scratch directories
  on the same ext4 filesystem (no tmpfs). **PREFLIGHT: PASS.** Re-check after installing the
  toolchain: **26.96 GiB free** (floor 8 GiB).
- **Toolchain**: elan, `leanprover/lean4:v4.25.0` (`Lean (version 4.25.0, … commit cdd38ac5…,
  Release)`). Lean started normally: **Part 2's shim was not needed and not used.**
- **Cache store** (`evidence/logs/cache-store.log`), logged before the first fetch:
  `/root/.cache/mathlib` **did not exist** (0 files, 0 bytes). Every archive was downloaded by this
  session.
- **Roots** (`evidence/logs/mathlib-roots.txt`): **39** Mathlib roots from the order list's 112
  modules (as the brief says).
- **Cache fetch** (`evidence/logs/cache-get.log`), `TAR_OPTIONS=--no-same-owner lake exe cache get
  <39 roots>`, run alone: "Attempting to download **1007** file(s)", all 1007 downloaded, "Decompressing
  **1007** file(s)", "Completed successfully!", exit 0, no failed download, no retry. (The cache
  tool compiled itself first, 20 Lake jobs: outside the one-Lean rule, addendum v2.6.)
- **Manifest check** (`evidence/logs/manifest-check.log`): 11 present packages match the manifest's
  URL and revision; **ABSENT** (not cloned by the narrowed fetch): `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean`; no order-list module imports an absent package. Last line: **MANIFEST
  CHECK: PASS**.
- **Cache checks** (item 3): fetch exit 0; `find .lake/packages -name '*.olean' -size 0` printed
  nothing (0); the probe importing the first root
  (`Mathlib.Algebra.BigOperators.Group.Finset.Basic`) elaborated through
  `scripts/lean_check_tree.sh` (exit 0; `evidence/logs/cache-probe.log`).
- **Bootstrap** (`evidence/logs/bootstrap.log`, per-module table `bootstrap-summary.tsv`: start,
  end, wall time, maximum RSS, exit, sorry count): the whole order list, **112 modules, in its
  order, 0 failures**, 21:44:00–22:05:03 UTC, **1,257.8 s** of module time; peak **3,019,012 KB**
  (`TuringMachine/CodeSimulator`); `NDNormalForm` 5.1 s, 1,977,948 KB. `/usr/bin/time` was
  installed from the distribution's `time` package for the memory measurement.
- **Base sorry set**: the bootstrap's sorry warnings are **19 in 9 modules**, exactly the base list
  (`campaign/fills/c1/logs/c1-fill-nf-cont1-base-sorries.txt`): `Simulation` 1
  (`branchTM_spaceUsed`), `Composition` 3 (`idTM_computes`, `ifEqTM_computes`,
  `condTM_computes_iff`), `Encoding` 1 (`pairDiagTM_computes`), `ClassP/TimeConstructible` 2
  (`lengthBitsTM_computes`, `lengthBitsTM_spaceUsed`), `Build/Wrappers` 2 (`timedCondTM_computes`,
  `timedCondTM_spaceUsed`), `Build/Loop` 5 (`loopHostTM_contracts`, `loopHostTM_decides`,
  `loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes`), `Build/Primitives` 3
  (`polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes`), `ClassNP/NDNormalForm`
  1 (`exists_codeNDTM_accepts_linear`, line 752), `Diagonalization/NTimeDiagonalizer` 1
  (`exists_diagonalizer`). Per-module counts: `evidence/logs/bootstrap-summary.tsv`; the warning
  lines: `evidence/logs/bootstrap-sorries.txt`.
- **Before screen** (`evidence/logs/screen-before.txt`; frozen worktree of the base, `nice -n 10`,
  beside the bootstrap): **byte-identical** to the screen base
  `campaign/fills/c1/logs/c1-fill-nf-cont1-screen-base.txt` (`cmp`): 1,379 declarations, 866 pairs,
  274,994 characters. Wall 20:47, maximum RSS 805,016 KB.
- **Process notes.** The repository's `.claude/CLAUDE.md` describes an editor workflow that runs
  no Lean; the brief requires `scripts/lean_check_tree.sh` for every check, and that is what was
  done, one Lean process at a time (the before screen ran beside the bootstrap, as the brief
  says). No `lake build`, no unfiltered `lake exe cache get`.


## 2. What the fill adds (regions (b)–(d))

Region (b): lines 705–3272 of the owned file, inserted after `nf_sweep_display_pass` and before the
target's docstring. Region (c): the target's body (4 lines for the base's `sorry`). Region (d): the
two status phrases ("(statement; proof incomplete)" in the module docstring, "statement; proof
incomplete" in the target's). Nothing else changed: `git diff` against the base has exactly the
hunks `@@ -30,2 +30 @@` (d), `@@ -705,0 +705,2568 @@` (b), `@@ -707 +3274 @@` (d), `@@ -758 +3325,4 @@`
(c). The 39 first-round privates and the target's statement are byte-identical (freeze check: the
diff's only deleted lines are the base's `sorry` and the two status phrases; `git diff` against
the base, `patches/`).

**The verifier's layout** (the route probe's, renamed `nf_`, docstrings rewritten with tape `0` /
tape `1` for A / B):

| Declaration | Role |
|---|---|
| `nf_Ph` | the phase index (`ctl`, `rep j`, `aFwd j`, `aBack j`, `bFwd j`, `bBack j`, `bClr j`, `park`); `deriving DecidableEq, Fintype` |
| `nf_St` | the state family (scan, leaf, seek, sweep, `Bool` for the park) |
| `nf_stDecEq`, `nf_stFintype` | the named `private instance`s on the fibers, with `@instDecidableEqScanPhase _ inferInstance` / `@instFintypeScanPhase _ inferInstance` for the control sweep |
| `nf_park` | the stationary verdict park (the review's `rvPark`) |
| `nf_M`, `nf_after`, `nf_red`, `nf_V` | the phase machines, the next tape's entry, the redirect table and the verifier `phaseHostTM (nf_M N L) ⟨.ctl, .fwd init⟩ (nf_red N L exit)` (generic over the leaf `L` and its exit reader) |

**The replay leaf:**

| Declaration | Role |
|---|---|
| `nf_LeafSt` | the leaf's states: `read σ` (σ the control sweep's own parser and control), `blk₁`/`blk₂` on the block of tape `1`, `adj₁`/`adj₂` (two head adjustments), `pass`, `rej` |
| `nf_leafEquiv`, `nf_leafStDecEq`, `nf_leafStFintype` | an equivalence with a sum of finite types, and the leaf state's **`private instance`s** through it (each summand's instance given locally: default synthesis does not reach the sum at the default size) |
| `nf_act` | the action of `N`'s table on a completed record's decoded claims (the action `nf_complete` recomputes) |
| `nf_blockDecode` | a two-cell block of tape `1` decoded as `nf_decode` decodes a claim (`01` and blank to blank) |
| `nf_leaf` | **the replay leaf**, one machine parameterized by `j : Option (Fin N.k)`; its docstring names the rows it is not (`scanTM` reads one tape; `StepBlock`'s record reader reads records on `k + 2` tapes). Every action is a `Turing.tapeAction` |
| `nf_leafExit` | the exit reader: `pass ↦ some true`, `rej ↦ some false` |

The leaf reads tape `0` one cell per step through `nf_sweepStep` (the control sweep's parser and
control, so its simulated state is the control fold's by construction). At a record's last bit
it decodes the record through `nf_decode` (MP5) and recomputes `N.tm.tr` (`nf_act`). The input
instance compares the decoded input claim with the native input cell and performs the recomputed
input move (`moveInputPos`, through the action), in the same step that reads the last bit; it
does not return the input head. A work-tape instance then works on tape `1` with tape `0`
stationary: `blk₁` reads the block's first cell and writes the first bit of the new content,
`blk₂` reads the second cell, checks `nf_blockDecode` against the claim, and writes the second
bit; the content is `(a.workTapes j).1.getD claim`, written at **every** record; then the head of
tape `1` moves `+1` or `−1` and `adj₁`, `adj₂` move it `0` or `−1` each, so the simulated move is
two cells. **After the end-flagged record the head move is skipped** (the leaf passes from
`blk₂`, its head on the block's second cell), as pinned.

**Chaining** (authorized transcriptions, renamed, with the strengthening noted):

| Declaration | Role |
|---|---|
| `nf_retag` | the probe's `nfc_retag`, stated over any source state type `S` (it is used after phases of different state types) |
| `nf_tagged_ne_park` | a configuration tagged by a phase other than the park is at no verdict (for the first-verdict clauses) |
| `nf_aNext` | the redirect after the return of tape `0`: `nf_after none` after the input, `⟨.bFwd j, .run⟩` after work tape `j` |
| `nf_aReturn` | the probe's `nfc_aReturn`, **stated once for every replayed tape `j`** (ending at `nf_aNext N L j`), and extended by `c₃.state.isSome` and "at no verdict on the way" (the window's states, from the phase lemma's first conjunct) |
| `nf_bClear` | the review's `rv_bClear` (`NFContClearTail.lean.txt`), extended by the unchanged tape `0`, head `0`, input head and output, `c₅.state.isSome`, and "at no verdict on the way" |
| `nf_entry` | `rv_entry`: the verifier's entry is `streamStartCfg x 0 q s` |
| `nf_tag` | `rv_tag`, for the verifier's state family |
| `nf_inputSymbol_congr` | `rv_inputSymbol_congr`, stated once (**promotion request**) |

**The input's replay:**

| Declaration | Role |
|---|---|
| `nf_prefix_last` | after a record's first `2k + 3` bits the parser is at its last position; the last bit completes the array, and the parser's step there is the completion rule (read off `nf_sweep_prefix` and `nf_sweep_record`) |
| `nf_leaf_prefix` | the leaf reads a record's first bits, one step and one cell of tape `0` each, for every instance |
| `nf_leaf_toLast` | the leaf at a record's last bit, for every instance: no exit for the record's `2k + 4` steps, the parser at its last position, the array complete and the completion rule there (shared by both record lemmas) |
| `nf_leaf_record_in` | one record of the input instance: `2k + 4` steps, no exit before; pass, next record, or reject |
| `nf_vstep` | the decoded virtual step of `N` (the recomputed action applied to a virtual configuration) |
| `nf_ok` | a record's claim on replayed tape `i` is checked: the virtual configuration is live and the claim is its read |
| `nf_vstep_ctl`, `nf_vrun_ctl` | the control fold's state and output summary follow the virtual run |
| `nf_vstep_state` | the control fold's state follows the virtual run, one record at a time (shared by both run lemmas and `nf_vstep_ctl`) |
| `nf_stream_cons` | a stream's cells: the first record's bits, then the rest one record further |
| `nf_all_cons` | every record of `rec :: rs` meets a check along the virtual run iff `rec` does and every record of `rs` does from the virtual step (shared by both run lemmas) |
| `nf_flags_cons` | the end flags of a stream's first record and of its tail (shared by both run lemmas) |
| `nf_leaf_run_in` | **the input instance's run lemma**: over `n ≥ 1` records (only the last end-flagged), an exit at some `T`, none before; it passes iff every record's input claim is checked along the virtual run, and then `T = (2k + 4)n` with only the state, the input head and the head of tape `0` (one cell past the stream) changed |

**Checkpoint 4: a work tape's replay on tape 1, the exit invariant, and the clear:**

| Declaration | Role |
|---|---|
| `nf_blockWrite` | tape `1` with one block rewritten to a content's two-bit code |
| `nf_leaf_block` | one block of a work tape's replay: two writing steps (the second checks `nf_blockDecode` of the block against the claim), then, after an unflagged record, two moves; the head of tape `1` ends at `b + 2 mv` (after the end-flagged record: `pass`, the head on the block's second cell, **no head move**); a failed check rejects |
| `nf_leaf_record_wk` | the read of one record by a work-tape instance: `2k + 4` steps into the block's first state with the claim, the new content `(a.workTapes t).1.getD claim`, the move and the flag; a halted control rejects |
| `nf_blocks` | the block representation: tape `1` holds the replayed tape's cells `[lo, hi]` from `p₀` as two nonblank bits each, blank elsewhere, and the replayed tape is blank outside `[lo, hi]` |
| `nf_blocks_decode`, `nf_blocks_write`, `nf_blocks_support` | a block decodes to its cell's content (visited or not); rewriting the block of a cell within one cell of the interval extends the interval by it; the nonblank cells are exactly the interval's blocks |
| `nf_signType_bound` | a simulated move is at most one cell |
| `nf_leaf_run_wk` | **the work-tape instance's run lemma**: over `n ≥ 1` records, an exit at some `T`, none before; it passes iff every record's claim on tape `t` is checked along the virtual run, and then `T + 2 = (2k + 8)n`, the head of tape `0` one cell past the stream, and **the exit invariant**: tape `1` blank outside a nonempty contiguous nonblank region `[p₀ + 2lo', p₀ + 2hi' + 1]` of at most `hi − lo + 1 + n` blocks, its head on the region (on block `y`'s second cell) |
| `nf_region` | the exit invariant gives the clear's input: from the head at offset `i` into the region, the region is a blank-delimited word `R` (`i < |R|`), and blanking `R`'s cells leaves tape `1` blank everywhere |

With `nf_bClear` (B's three clear phases, chained through the phase host), this is checkpoint 4.
**Every record writes its block**, so the visited region has no hole (an action that writes
nothing writes the old content's code; an unvisited cell under the head becomes the nonblank code
of blank), and the region is exactly the blocks read: if the work tape's head never moves, it is
the one block at the start position.

**Checkpoint 5: the verifier's characterization, `hV`, and its verdict on a display:**

| Declaration | Role |
|---|---|
| `nf_stream_length` | a stream of `n` records has `(2k + 4)n` cells |
| `nf_tapeEntry` | the entry of the phases of work tape `m` (its replay, or the passing verdict for `m = k`); `nf_after N L none` and `nf_after N L (some j)` are it at `0` and `j + 1` |
| `nf_allPass` | every check passes: the control sweep, and every record's claim on every replayed tape `i : Fin (k + 1)` along the decoded virtual run from `N`'s start |
| `nf_V_tail` | the verifier over the work tapes from `m` on (induction on `k − m`): a first verdict at some `T`, accepting iff every claim on every work tape `≥ m` is checked; then an empty output and `T ≤ (k − m)((2(2k + 4) + 12)n + 15)` |
| `nf_allPass_iff` | `nf_allPass` split into the control sweep, the input, and the work tapes |
| `nf_V_char` | **the characterization**: from the stream start, a first verdict `acc` or `rej` at `TQ`, `acc ⇔ nf_allPass`, and then an empty output and `TQ ≤ 4|s| + 10 + k((2(2k + 4) + 12)n + 15)` |
| `nf_split` | a stream that first stops the controller is `n ≥ 1` records, only the last end-flagged (read off `nf_firstStop_records` with `List.ofFn_mul'`) |
| `nf_P` | the trivial setup machine (one state, its own exit) |
| `nf_hV` | **`hV`, as its own lemma**, in the host's terms: for every stream first stopping the controller, well formed or not, the verifier from `guessRunCfg (nf_P.initCfg x) 0 s qentry` reaches `acc` or `rej` at some `TQ` and is at neither before |
| `nf_vrun_of_ok` | checked claims make the decoded virtual run genuine: if every claim of every record before the `r`th is checked, the run after `r` records is `N`'s run under the records' first `r` choice bits (shared by the verdict on a display and the backward transfer) |
| `nf_V_display` | **the verdict on a display**: a branch live before its end that halts at its end with output `[true]` has its display accepted, first verdict `acc`, output `[]`, within the bound |

Why `hV` holds on every first-stopped stream (as the brief explains it): the control sweep runs
on every stream (`nf_sweep_run`); a failed sweep rejects; each replay ends at the blank after `s`
or rejects earlier (`nf_leaf_run_in`, `nf_leaf_run_wk`, which make no content assumption beyond
the record structure that `nf_split` gives); the head of tape `1` moves at most two cells per
record; and the clear runs over the visited region, contiguous, nonblank and holding the head by
the exit invariant (`nf_region`).

**Checkpoint 6: the forward transfer and the ledger:**

| Declaration | Role |
|---|---|
| `nf_C` | the constant, `C = 6W + k(2W + 12) + 21 + 15k` with `W = 2k + 4` (that is `4k² + 47k + 45`) |
| `nf_host` | `M`'s host: `guessCtlRunTM nf_P nf_P.q₀ 0 (0, false) (nf_ctlStep N.k) (nf_ctlStop N.k) false V ⟨ctl, fwd init⟩ ⟨park, true⟩ ⟨park, false⟩` with `V = nf_V N (nf_leaf N) (nf_leafExit N)` |
| `nf_ledger` | `0 + 2|s| + TQ + 11 ≤ C(t + 1)` from `|s| = W t₀`, `t₀ ≤ t` and the characterization's bound |
| `nf_forward` | **the forward transfer**: `N.AcceptsWithin x t →` a word of length exactly `C(t + 1)` halts the host with output `[true]` (the word is the host lemma's: `guessCtlRunTM_accepts_of`; no word is built here) |

**Checkpoint 7: the backward transfer:**

| Declaration | Role |
|---|---|
| `nf_backward` | a stream of records on which every check passes is a genuine accepting run: `nf_allPass N x rs → N.AcceptsWithin x rs.length`, with the records' choice bits as the word (through `nf_vrun_of_ok`); it works over raw records' decoded fields (`nf_decode`), never over `nf_record` images |
| `nf_backward_host` | **the backward transfer**: a word halting the host with output `[true]` gives `∃ t', N.AcceptsWithin x t'`, through `guessCtlRunTM_stream_of_accepts` with `hV` (`nf_hV`), `nf_split`, and the characterization (its first verdict is the host lemma's `TQ`, since both are first verdicts) |

**Checkpoint 8: the target** (region (c)):

```lean
  obtain ⟨M, hM⟩ := nf_pack (nf_host N)
  refine ⟨M, nf_C N.k, fun x t hN => (hM x _).2 (nf_forward N x t hN), fun x t hMt => ?_⟩
  obtain ⟨w, -, hh, ho⟩ := (hM x t).1 hMt
  exact nf_backward_host N x w hh ho
```

`M` is the controller-stopped host (`nf_host`) packaged by `nf_pack`; `C = nf_C N.k`.

**`C`, term by term** (`n = t₀` records, `|s| = W t₀`, `W = 2k + 4`):

| Term | Steps | Bound used |
|---|---|---|
| the trivial setup `TP` | `0` | `0` |
| the guess (the host's `2|s|`) | `2|s|` | `2W t₀` |
| the control sweep and its dispatch | `2|s| + 2 + 1` | |
| the input's replay and its dispatch | `W t₀ + 1` | |
| the return of tape `0` after the input (two redirects included) | `|s| + 6` | the three: `4|s| + 10` |
| per work tape: its replay and dispatch | `(2k + 8)t₀ − 2 + 1` | |
| per work tape: the return of tape `0` | `|s| + 6` | |
| per work tape: the clear of tape `1` (three redirects included) | `(|R| − i + 2) + (|R| + 4) + (2|R| + 3) ≤ 4|R| + 9`, `|R| ≤ 2t₀` | per tape `≤ (2W + 12)t₀ + 15` |
| the host's constant | `11` | `11` |

Total `0 + 2|s| + TQ + 11 ≤ (6W + k(2W + 12))t₀ + 21 + 15k ≤ C(t + 1)` since `t₀ ≤ t`.

The run lemmas are proved by induction over records through `Turing.step_of_tapeAction_move` (the
published one-step lemma of `Turing.tapeAction`, itself proved from `MultiTapeTM.step` and the
`Action.apply` field equations), with no private loop driver.

## 3. Checks at the final commit (`evidence/checks/`, `evidence/seal/`, `evidence/probe/`)

- **Tail** (`tail.log`, `tail-summary.tsv`): `ClassNP/NDNormalForm`, `ClassNP`,
  `Diagonalization/NTimeHierarchy`, `Diagonalization`: all exit 0, **no warning** (no sorry).
- **Final checks 1–2: the final sweep** (§6): the whole order list, 0 errors; `NDNormalForm` no
  sorry warning and no other warning; every other module's sorry warnings exactly the base's.
- **Final check 3: the probe re-run** (`evidence/probe/`): the import probe extended by the
  **320** names the elaborated-constant walk cites beyond it: **908 checks of 751 cited names,
  0 errors** (the 2 deprecation warnings of the base).
- **Axioms** (`axioms-raw.log`, a scratch copy with `#print axioms` for the 65 new declarations and
  the target): the target **`[propext, Classical.choice, Quot.sound]`**; every new declaration
  within `[propext, Classical.choice, Quot.sound]` (none at all for `nf_Ph`, `nf_park`,
  `nf_blockDecode`, `nf_blockWrite`, `nf_blocks`, `nf_blocks_decode`, `nf_P`); **no `sorryAx`**.
- **Rule 10.**
  - Cited outside the file: the elaborated-constant walk of every new constant and the target
    (`walk-raw.log`, `walk-ext.tsv`): **751** external constants, 141 of them TCSlib (by module in
    `rule11.txt`); none is another file's private.
  - **Seal** (`evidence/seal/`): a scratch copy of the module with `attribute [-simp]` on the four
    `@[simp]` definitions and `attribute [local irreducible]` on **231** definitions — the
    review's 223, the six derived phase instances the walk reaches (`instDecidableEq`/`instFintype`
    of `ScanPhase`, `SeekPhase`, `SweepPhase`) and the two host instances the target's packaging
    reaches (`instFintypeGuessRunPhase`, `GuessRunPhase.instFintypeCtlState`) — inserted before the
    first new private: **0 errors**. Every TCSlib definition the walk reaches is sealed, except
    structure projections and `casesOn` recursors (`reached-defs.txt`). **Controls**: one per
    sealed definition, 231 (`#ctl_rfl` delta goals; `#ctl_eqn` equation-lemma controls for the 10
    recursive definitions whose delta goal does not close unsealed; `#ctl_use` usage controls,
    `Finset.univ.card` by `decide`, for the three derived `Fintype` instances whose delta goal
    closes sealed): **unsealed 231 PASS / 0 FAIL, sealed 0 PASS / 231 FAIL** (raw outputs
    `controls-unsealed.log`, `controls-sealed.log`).
  - **Inspection table** (`inspection.md`, 847 rows, all resolved): every `rw`/`simp`/`simpa`/
    `dsimp`/`unfold`/`show`/`change` argument of the diff with its origin. No other-file TCSlib
    definition is an argument. `unfold` and `simp only [d]` name only this file's definitions
    (`nf_V`, `nf_leaf`, `nf_act`, `nf_complete`, `nf_vstep`, `nf_blockDecode`, `nf_blockWrite`,
    `nf_tapeEntry`, `nf_C`, `nf_sweepPass`); `MultiTapeTM.step` and `Action.apply`
    are never unfolded (the leaf's steps are `step_of_tapeAction_move`/`_write` and
    `step_of_some`, the field equations `Action.apply_*`); `N.tm.tr` is applied, never unfolded.
    The rest are published lemmas, core/Mathlib lemmas and local hypotheses; every `show` restates
    a goal in this file's terms or through structure projections of literals.
- **Rule 11** (`rule11.txt`): the diff cites none of the six R3 rows (it cites
  `clearTM_run_ofCfg`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `scanTM_run_ofCfg` through
  `nf_sweep_run`); no other file's private name is reached. New privates are under `nf_`, clear of
  the 39. `deriving` on `nf_Ph` creates the public constants `Turing.FinNDTM.instDecidableEqNf_Ph`
  and `Turing.FinNDTM.instFintypeNf_Ph` (with their auxiliaries): no file of the tree and no branch
  or PR head of the remote has either name, or any of the 65 new names (`git grep -w` over all
  306 refs, `evidence/duplication/name-hits.txt`, empty). The leaf state's instances are
  `private instance`s, as pinned.
- **Lint**: `campaign_style_lint.py TCSlib/Complexity/ClassNP`: **0 FAIL, 18 WARN over 21 files**
  (base 17; the new WARN is the owned file's size, expected); `style_lint.py` on the file: 1
  finding, the file size (3,332 lines > 1,000; expected per the brief). No line over 100
  characters. Every proof over 20 lines has a literal `**Proof sketch.**` (the linter finds none
  missing).
- **File size**: 3,332 lines (base 762); **1 public declaration** (the target), **104 private**
  (39 first-round + **65 new**); no new public declaration.

## 4. The target's axiom walk

`exists_codeNDTM_accepts_linear` depends on `[propext, Classical.choice, Quot.sound]`.

## 5. Escalations, promotion requests

- Escalations: none.
- Process notes: the first after screen (on checkpoint 8's commit) led to a consolidation commit,
  after which the final sweep and the after screen were rerun (§7); the first runs are kept as
  finished, superseded logs. The session's worker process was restarted once, after checkpoint 4 (the
  checkout, the toolchain, the cache and the oleans survived; the kernel build changed). A
  resource re-check was logged (`evidence/logs/restart-check.log`: 13.33 GiB headroom, 26.4 GB
  free, no OOM event) and the work continued.
- Promotion requests (each re-derives another file's private; kept, as the brief directs):
  `nf_inputSymbol_congr` (the input read depends on the input head only, across machines;
  `ExhaustiveReplay`'s private `xr_inputSymbol_congr`), `nf_retag` (a redirected configuration is
  the next phase's tagged start; `SeamLayout`'s private `sl_rewrap`), `nf_tagged_ne_park` (a
  configuration tagged by another phase is at no verdict; `CfgRecord`'s private `record_tag_ne`, a
  generalization).
- `**Implementation.**` paragraph: the route does not depart from the landed text; no new text is
  proposed.

## 6. The final sweep

`evidence/logs/final-sweep.log`, with each module's start, end, wall time, maximum RSS, exit
status and sorry-warning count in `final-sweep-summary.tsv`: the whole order list, **112 modules in
its order, 0 failures**, on the final commit `825ee3f5` (23:31:00–23:50:51 UTC), **1,187.1 s** of
module time; peak **2,934,668 KB** (`TuringMachine/CodeSimulator`); `ClassNP/NDNormalForm` 16.5 s,
2,227,924 KB, **no warning of any kind**.

- **Sorry warnings**: **18 in 8 modules**, exactly the base's 19 minus the target
  (`final-sweep-sorries.txt` against `bootstrap-sorries.txt`: the only difference is the owned
  file's line): `Simulation` 1, `Composition` 3, `Encoding` 1, `ClassP/TimeConstructible` 2,
  `Build/Wrappers` 2, `Build/Loop` 5, `Build/Primitives` 3, `Diagonalization/NTimeDiagonalizer` 1.
- **Every other warning** of the sweep (other modules' linter warnings) is byte-identical to the
  bootstrap's.
- `NTimeHierarchy`, the one consumer of the target (by statement), elaborates unchanged.
- The first final sweep, on checkpoint 8's commit `ba46b709` (23:01–23:23 UTC, 1,309.7 s, 0
  failures, the same sorry set), is kept in `evidence/superseded/`.

## 7. Duplication governance

**Screens** (`evidence/screens/`; `scripts/copy-text-screen-v3.py` on the 21-file population, each on a
frozen worktree of its commit, `nice -n 10`, one at a time, each beside one Lean process):

- **Before** (base `348781a3`, beside the bootstrap): `declarations screened: 1379; copy pairs: 866; reproduced text: 274,994 chars (wall 20:47, 805,016 KB)` — **byte-identical** to the
  screen base.
- **After** (final `825ee3f5`, beside the final sweep): `**declarations screened: 1438; copy pairs: 904; reproduced text: 285,506 chars** (wall 22:29, 812,464 KB): **38 new pairs** (25 cross-file, 13 in-file), none removed; the base's NF-X1 pair (`un_setup` / `nf_setup`) unchanged`.
- **A first after screen** (checkpoint 8's `ba46b709`, beside that commit's final sweep;
  `evidence/screens/superseded/`): `declarations screened: 1439; copy pairs: 918; reproduced text: 288,722 chars: 52 new pairs (the same 25 cross-file, 27 in-file)`. Its 27 in-file pairs led to the consolidation commit
  `825ee3f5` (one lemma for the virtual run's genuineness under checked claims, one for the record
  read up to its last bit, one section with one `simp`-attribute line instead of twelve, whose
  repeated line was counted into the preceding definitions' bodies and paired five unrelated short
  definitions), and the final sweep and the after screen were rerun on it. The first sweep's logs
  are kept (`evidence/superseded/`).

**New cross-file pairs** (after minus before; each with one disposition):

| Pair (screen line) | Disposition |
|---|---|
| `CodeSimulator.lean::canonStageInnerSpec  reproduces  NDNormalForm.lean::nf_retag: 195/322 = 61%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg0  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg1  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg2  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg3  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg4  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg5  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageLeg6  reproduces  NDNormalForm.lean::nf_retag: 239/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::canonStageOuterSpec  reproduces  NDNormalForm.lean::nf_retag: 227/322 = 70%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `CodeSimulator.lean::us_start  reproduces  NDNormalForm.lean::nf_retag: 182/322 = 57%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `ExhaustiveReplay.lean::xr_E_initCfg  reproduces  NDNormalForm.lean::nf_retag: 194/322 = 60%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `ExhaustiveReplay.lean::xr_halt_fixed  reproduces  NDNormalForm.lean::nf_retag: 231/322 = 72%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `ExhaustiveReplay.lean::xr_inputSymbol_congr  reproduces  NDNormalForm.lean::nf_inputSymbol_congr: 255/384 = 66%` | re-derivation of another file's private (`ExhaustiveReplay`'s `xr_inputSymbol_congr`): kept, the authorized `rv_inputSymbol_congr` stated once; **promotion request** |
| `ExhaustiveReplay.lean::xr_phase_step  reproduces  NDNormalForm.lean::nf_retag: 231/322 = 72%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `InputRewind.lean::Cfg.mapState_mapState  reproduces  NDNormalForm.lean::nf_retag: 238/322 = 74%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `NDCodeSimulator.lean::exists_ndInterpreterCore  reproduces  NDNormalForm.lean::nf_retag: 198/322 = 61%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `NDCodeSimulator.lean::ic_loopHost_run  reproduces  NDNormalForm.lean::nf_tagged_ne_park: 80/135 = 59%` | idiom: the state of a tagged configuration through the published `Cfg.mapState_state` and `Sigma` injectivity; no lemma re-derived (`CfgRecord`'s private `record_tag_ne` generalizes `nf_tagged_ne_park`: promotion request) |
| `NDHost.lean::gr_handoff  reproduces  NDNormalForm.lean::nf_retag: 194/322 = 60%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `NDHost.lean::guessCtlRunTM_stop_of_halted  reproduces  NDNormalForm.lean::nf_retag: 175/322 = 54%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `NDNormalForm.lean::nf_entry  reproduces  CodeSimulator.lean::canonStageBuffer_none: 67/84 = 80%` | re-derivation of another file's private (`CodeSimulator`'s two-line `canonStageBuffer_none`, a buffer's blank past its end, inside `nf_entry`, the authorized `rv_entry`): kept; **promotion request** (with the buffer's API) |
| `NDNormalForm.lean::nf_inputSymbol_congr  reproduces  ExhaustiveReplay.lean::xr_inputSymbol_congr: 255/445 = 57%` | re-derivation of another file's private (`ExhaustiveReplay`'s `xr_inputSymbol_congr`): kept, the authorized `rv_inputSymbol_congr` stated once; **promotion request** |
| `NDNormalForm.lean::nf_retag  reproduces  CodeSimulator.lean::us_start: 182/281 = 65%` | idiom: `nf_retag` (the route probe's `nfc_retag`, authorized) compares two configurations field by field through the published `Cfg.mapState_*` equations, as the other declaration does; it states neither's equation (`Cfg.mapState_mapState` composes renamings; `us_start` is `CodeSimulator`'s private) |
| `NDNormalForm.lean::nf_retag  reproduces  InputRewind.lean::Cfg.mapState_mapState: 238/402 = 59%` | idiom: `nf_retag` (the route probe's `nfc_retag`, authorized) compares two configurations field by field through the published `Cfg.mapState_*` equations, as the other declaration does; it states neither's equation (`Cfg.mapState_mapState` composes renamings; `us_start` is `CodeSimulator`'s private) |
| `NTimeHierarchy.lean::un_setup  reproduces  NDNormalForm.lean::nf_retag: 216/322 = 67%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |
| `Seam.lean::phaseHostTM_run  reproduces  NDNormalForm.lean::nf_retag: 221/322 = 69%` | idiom: the other declaration converts configurations field by field through the published `Cfg.ext` and field equations, as `nf_retag` (the route probe's authorized `nfc_retag`) does; no lemma is re-derived |

**New in-file pairs** (each with a one-line justification):

| Pair (screen line) | Justification |
|---|---|
| `NDNormalForm.lean::nf_V_tail  reproduces  NDNormalForm.lean::nf_setup: 154/218 = 71%` | reading `N`'s initial configuration's fields through `NDTM.initCfg_eq` and `Cfg.init_*`, as the first round's `nf_setup` reads the setup's: the published field equations, no lemma re-derived |
| `NDNormalForm.lean::nf_bClear  reproduces  NDNormalForm.lean::nf_aReturn: 1353/2357 = 57%` | the two pinned transcriptions (the probe's `nfc_aReturn`, the review's `rv_bClear`; "keep both"): the same phase-lemma invocation and retagging around different rows on different tapes |
| `NDNormalForm.lean::nf_leafStDecEq  reproduces  NDNormalForm.lean::nf_leafStFintype: 299/375 = 80%` | the leaf state's two private instances (pinned), through one equivalence with the same local summand instances |
| `NDNormalForm.lean::nf_leafStFintype  reproduces  NDNormalForm.lean::nf_leafStDecEq: 299/386 = 77%` | as above |
| `NDNormalForm.lean::nf_leaf_record_in  reproduces  NDNormalForm.lean::nf_leaf_record_wk: 567/929 = 61%` | after `nf_leaf_toLast` took their common read, the two instances' last steps are different actions (an input move vs the block's entry) with the same step-lemma invocation and field conversion |
| `NDNormalForm.lean::nf_leaf_run_wk  reproduces  NDNormalForm.lean::nf_leaf_run_in: 1296/2435 = 53%` | the two instances' inductions over records share their skeleton through `nf_stream_cons`, `nf_all_cons`, `nf_flags_cons` and `nf_vstep_state`; the rest is each instance's own invariant (the input head vs the block representation and the exit invariant) |
| `NDNormalForm.lean::nf_pack  reproduces  NDNormalForm.lean::nf_retag: 162/322 = 50%` | the first round's `nf_pack` and `nf_retag` both compare configurations field by field through the published `Cfg.mapState_*` equations (idiom) |
| `NDNormalForm.lean::nf_stDecEq  reproduces  NDNormalForm.lean::nf_stFintype: 245/318 = 77%` | the phase fibers' two named instances (pinned, the probe's `nfcStDecEq`/`nfcStFintype`): parallel case tables |
| `NDNormalForm.lean::nf_stFintype  reproduces  NDNormalForm.lean::nf_stDecEq: 245/350 = 70%` | as above |
| `NDNormalForm.lean::nf_sweep_run  reproduces  NDNormalForm.lean::nf_tag: 216/402 = 54%` | the first round's `nf_sweep_run` and `nf_tag` (the review's `rv_tag`) both compare stream starts field by field through `streamStartCfg_*` (idiom) |
| `NDNormalForm.lean::nf_tag  reproduces  NDNormalForm.lean::nf_retag: 162/322 = 50%` | two authorized transcriptions comparing configurations field by field through `Cfg.mapState_*` (idiom) |
| `NDNormalForm.lean::nf_vstep_ctl  reproduces  NDNormalForm.lean::nf_vstep_state: 131/172 = 76%` | the control's agreement with the virtual run, state and summary: the summary component needs a second case split on the virtual state; the state component alone (`nf_vstep_state`) serves the run lemmas, which do not track the summary |
| `NDNormalForm.lean::nf_vstep_state  reproduces  NDNormalForm.lean::nf_vstep_ctl: 131/236 = 56%` | as above |

**new copies: none.** No pair re-derives a published lemma; the three re-derivations of other
files' privates (`xr_inputSymbol_congr`, `sl_rewrap`'s and `record_tag_ne`'s statements; and
`canonStageBuffer_none`'s two-line buffer fact inside `nf_entry`) are kept and listed as promotion
requests.

### Semantic duplication: the search per new private

Three searches for every new declaration (`evidence/final/`):
1. **By name**, in the tree and on every branch and PR head of the remote (306 refs: all
   `refs/heads/*` and `refs/pull/*/head`, fetched; a superset of the open PRs, since the GitHub API is
   not enabled for this session): `git grep -w` of each of the 64 names: **no occurrence outside the
   owned file** for any of them.
2. **By statement shape**, the same refs, `git grep -E` of each lemma's characteristic pattern
   (`evidence/duplication/semantic-grep.txt`, with every hit).
3. **By `exact?`**, at the module's imports, for every lemma whose statement mentions no definition
   of this file (`evidence/duplication/NFExactProbe.lean`, `exact-probe.log`: every `exact?` reports that it
   could not close the goal). A lemma whose statement mentions this
   file's definitions (the leaf, its states, the phases, `nf_decode`, the control fold, the virtual
   run, the block representation) cannot be stated by a published declaration, which cannot see
   them; for those the shape search is the semantic search.

| Declaration(s) | Shape searched | Result |
|---|---|---|
| `nf_Ph`, `nf_St`, `nf_stDecEq`, `nf_stFintype`, `nf_park`, `nf_M`, `nf_after`, `nf_red`, `nf_V` | the pinned layout (the route probe's, renamed) | the probe's own layout; no published verifier over these rows |
| `nf_LeafSt`, `nf_leafEquiv`, `nf_leafStDecEq`, `nf_leafStFintype`, `nf_leaf`, `nf_leafExit`, `nf_act`, `nf_blockDecode`, `nf_blockWrite` | readers of fixed-width records checked against another tape; two-bit block codes (`blockDecode`, `blockWrite`, "two-bit block") | none: `scanTM` reads one tape; `StepBlock`'s and `CodeSimulator`'s record readers read `k + 2` tapes; the "two-bit block" hits (`Randomized/Build/PairSplit`, `UnaryMul`, `Build/Catalog`) are parsers of aligned `00`/`11` words, not a replayed tape |
| `nf_retag` | `theorem …retag`; redirected configuration as a tagged start | none public; `SeamLayout`'s **private** `sl_rewrap` states it for its own family: **promotion request** |
| `nf_tagged_ne_park` | `(c.mapState (Sigma.mk i)).state ≠ …` | none public; `CfgRecord`'s **private** `record_tag_ne` is a generalization: **promotion request** |
| `nf_aNext`, `nf_aReturn`, `nf_bClear` | `skipBackTM_run_ofCfg` chains on two tapes | `Build/RecordTable` chains `skipBackTM` inside its own record table (a different composition); the authorized transcriptions of the route probe and the review's `rv_bClear` |
| `nf_entry` | `guessRunCfg … = streamStartCfg` | none; `exact?`: none |
| `nf_tag` | `streamStartCfg … mapState (Sigma.mk …)` | none (the review's `rv_tag`, for this family) |
| `nf_inputSymbol_congr` | `inputSymbol = ….inputSymbol`, `…inputSymbol_congr` | `ExhaustiveReplay`'s **private** `xr_inputSymbol_congr` states it; the other hits are `rfl` facts of particular configurations: **promotion request** (as the brief lists it); `exact?`: none |
| `nf_prefix_last`, `nf_leaf_prefix`, `nf_leaf_record_in`, `nf_leaf_run_in`, `nf_leaf_block`, `nf_leaf_record_wk`, `nf_leaf_run_wk` | run lemmas of this file's leaf | none possible elsewhere (the leaf is this file's); they cite `nf_sweep_prefix`, `nf_sweep_record` and the published one-step lemmas of `tapeAction` |
| `nf_vstep`, `nf_ok`, `nf_vstep_state`, `nf_vstep_ctl`, `nf_vrun_ctl`, `nf_vrun_genuine` | `Fin.cases c.inputSymbol c.workTapeSymbols`; decoded runs | none: the first round's `nf_complete_step` and `nf_sweep_control_prefix` are about the control fold on genuine records; these are about the decoded virtual run on arbitrary records |
| `nf_stream_cons`, `nf_stream_length`, `nf_split`, `nf_all_cons`, `nf_flags_cons` | `flatMap List.ofFn` and its length | none in TCSlib; `exact?`: none `exact?`: none `exact?`: none |
| `nf_blocks`, `nf_blocks_decode`, `nf_blocks_write`, `nf_blocks_support`, `nf_region` | block representations of a tape; a region read off as a buffer | none; `exact?`: none |
| `nf_signType_bound` | `(m : ℤ) ≤ 1` for `SignType` | none in TCSlib; `exact?`: none |
| `nf_tapeEntry`, `nf_allPass`, `nf_allPass_iff`, `nf_V_tail`, `nf_V_char`, `nf_hV`, `nf_V_display` | the verifier's characterization | none possible elsewhere (this file's verifier) |
| `nf_P`, `nf_host`, `nf_C`, `nf_ledger`, `nf_forward`, `nf_backward`, `nf_backward_host` | first halting time (`Nat.find … runWith`, "first halting"); the transfers | `EXP`'s private `enumCont_first_halt` and `SAT`'s, `ExhaustiveReplay`'s, `ConfigCount`'s first-halting arguments are about other runs; `nf_forward` cuts its word with `Nat.find` inline, as no published lemma states the first halting time of an `NDTM` branch; the transfers are the host's acceptance lemmas, cited |

## 8. Checklist

- [x] Preflight numbers, roots (39), cache fetch (1,007 of 1,007; store empty before), the store's
      log, the logs in this zip (`evidence/logs/`), the bootstrap with per-module time and memory,
      the base blob check (§1).
- [x] Nothing outside regions (b)–(d); the 39 privates and the target's statement unchanged (the
      diff's four hunks, §2; it deletes only the base's `sorry` and the two status phrases).
- [x] Checkpoints 3–8, one commit and one zip each; the base hash and the ancestor check (§1, status).
- [x] Every new declaration with its role (§2): the leaf and its run lemmas, the exit invariant (the
      skipped last move), the instances, `V`'s phases and redirects, the hand-built machine's
      docstring naming the rows it is not.
- [x] `hV` as its own lemma (`nf_hV`), and the edge cases: `N.k = 0` (`nf_tapeEntry … 0` is the
      passing verdict and `nf_V_tail` runs zero tapes; `W = 4`); `t₀ = 1` (one record:
      `nf_leaf_run_in`/`_wk`'s base case, `nf_split`); the input head off the input (the claim is
      compared with `Cfg.inputSymbol`, blank there: `nf_inputSymbol_congr`); a work-tape write of a
      blank and an action writing nothing (`(a.workTapes j).1.getD claim`, always written:
      `nf_leaf_block`, `nf_blocks_write`); a work tape whose head never moves (the region is one
      block: `nf_blocks_write` from `[0, −1]`); a halting transition that emits, or two emissions
      (the control sweep's summary, first round, rejects; `nf_V_char`); wrong claims (rejected,
      verdict still reached: `nf_V_char`, `nf_hV`); the code `01` (`nf_decode`, MP5:
      `nf_backward` works over decoded fields).
- [x] `C`, term by term (§2): the guess, the control sweep, each replay and return, the clears, the
      redirects, the host's `+ 11`.
- [x] The base sorry list by name (§1), and the final sweep's (§6).
- [x] Promotion requests and escalations (§5); the `**Implementation.**` paragraph needs no change.
- [x] Rule 10 (§3): the cited declarations from the elaborated-constant walk; the probe re-run (908
      checks of 751 names); the seal with its 231 discriminating controls and both raw outputs; the
      inspection table.
- [x] Rule 11 (§3): no R3 row, no other file's private; the two derived instance names checked.
- [x] Duplication (§7): both screens (and the superseded first after screen), every new pair with a
      disposition or a justification, the semantic search per private, "new copies: none".
- [x] File size, the final sweep, the axiom prints, the lint line (§3, §6).

## 9. What is in this zip

- `REPORT.md`; `source/` (the owned file at `825ee3f5`); `patches/` (`git format-patch` of the 7
  commits on the base); `bundle/` (a bundle of `fill/c1-nf-cont1` whose only prerequisite is the
  base, with `git bundle verify`'s output); `SHA256SUMS`.
- `evidence/logs/`: preflight, restart re-check, cache store, roots, cache fetch, manifest check,
  cache probe, the bootstrap and the final sweep (logs, per-module tables, sorry lists), the
  screens' timing; `evidence/superseded/`: checkpoint 8's final sweep and after screen.
- `evidence/screens/`: the before and after screens' full outputs, and the superseded first after
  screen.
- `evidence/checks/`: the tail, the walk, the axiom prints (`NFAxioms.lean`, `axioms-raw.log`),
  the inspection table, the lint outputs, the rule-11 grep.
- `evidence/seal/`: the sealed module copy, the seal set, the sealed/unsealed control sources and
  their raw outputs.
- `evidence/probe/`: the extended import probe and its output.
- `evidence/duplication/`: the shape search, the name search, the `exact?` probe and its output,
  the screen difference.
- `evidence/runtime/`: the scripts used for the checks (sweep, walk, seal, probe, inspection, zip).
