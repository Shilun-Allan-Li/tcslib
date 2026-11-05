**Verdict: issue after edits.** Do not issue the draft as written. It has no blocker and one major
(F1): the pinned replay leaf no longer says that every record writes its block. Without that, the
visited region on B can have blank holes, the pinned exit invariant fails, and a genuine display
can be rejected. The first round's brief had the sentence; this draft dropped it. There are also
10 minors and 4 notes. `suggested-fix.diff` applies 17 asserted edits that fix F1–F11 and F13–F15.
F12 is a decision for the maintainer (D1, below). Apart from F1, the route is sound against the
published statements:
- the layout, A's return and B's clear chain through `phaseHostTM_run` under the probe's seal and
  under the maximal 223-definition seal (out/09, out/11);
- the pre-ship reproduces exactly.

# Review: the NF cont1 fill brief draft (`c1-fill-nf-cont1.DRAFT.md`, `Turing.FinNDTM.exists_codeNDTM_accepts_linear`, checkpoints 3–8)

This is a read-only review by the maintainer's review sub-agent, done on 2026-11-04.

## Inputs and method

- **The draft.** `campaign/fills/c1/drafts/c1-fill-nf-cont1.DRAFT.md` at `0b8c2f9a52fa4c1bc5832223c2cd441499f03402`:
  - SHA-256 `268d5b266173264adccb46850621b75400a368eb3457f5ace1df52a268147b00`, git blob
    `16411f3b` (out/draft.sha256); the copy is in `orig/`;
  - the records then moved to `299d2d54` (six commits). Only `campaign/duplication-ledger.md`
    changed, in lines unrelated to NF; the draft, its inputs and all Lean are unchanged
    (out/14).
- **The tree.** `wt/` is detached at `5241eb8257bdeb5b5c274145575749dd186ec65f`, the tip of
  `lean/c1-nf-partial`, on GitHub too (`git ls-remote`, out/13):
  - I checked that `reviews/nfc-brief` was absent first, and linked `.lake/packages`;
  - the owned blob is `e6432b1e6cf6eb33f81bff05eb389b09dd7cb9f0`: 762 lines, 1 public and 39
    private declarations (out/12);
  - its TCSlib differs from `711f5444` (#176's merge) only in `NDNormalForm.lean`, and
    `0b8c2f9a`'s TCSlib equals `711f5444`'s (out/13).
- **Lean.** It ran only through `tools/leanelab.sh` against `oleans-leqc3`, one elaboration at a
  time: seven runs (out/00-runs.txt). A probe needing the 39 privates is a copy of the module with
  a tail, elaborated as its own file, as the pre-ship did. There was no build, no cache command and
  no copy-text screen.
- **Probes.** Probe files went only to `wt/rvprobe/`, with copies in `probe/` (`.lean.txt`).
  The one written by hand is `probe/RVClearTail.lean.txt`.
- **Python.** Every script ran as `python3 -I`, from `scripts/`:
  - `order.py`: the order list, the roots and the sorry census from `git show`;
  - `maxseal.py`: the maximal seal;
  - `edits.py`: the 17 asserted draft edits.

  I also ran the two read-only lint scripts at the base.
- **Untouched.** `wt-hk`, `wt-nfp`, `wt-sav` and the main checkout's working tree, index and
  branches. Nothing was committed or pushed.
- **Disclosure.** Early on I ran `git fetch -q origin` in the main checkout (13:14). It rewrote
  `.git/FETCH_HEAD` only. The remote-tracking refs were already at the fetched values: their
  reflogs show only the maintainer's pushes, and no fetch entry. Nothing else changed.
- **Evidence.** Every claim cites `out/`.

## (a) The pre-ship, re-run

| # | Check (draft lines) | Result | Evidence |
|---|---|---|---|
| 1 | The module: exactly the target's sorry warning (123) | exit 0, `752:8` "declaration uses 'sorry'", 2.8 s. Identical to `module-elab.out` | out/01 |
| 2 | The import probe: 588 checks, 0 errors, 2 deprecation warnings (124–125) | 588 `#check`s, exit 0, 0 errors. The two warnings are `#check`s of `Int.ofNat_mul` and `Int.ofNat_nonneg`, at probe lines 277–278. Identical to `import.out` after path normalization | out/05 |
| 3 | The route probe: 0 errors, the target's sorry only; `nfc_retag` on `[propext, Quot.sound]`; `nfc_aReturn` on the standard three, sealed over 10, 4 erased (126–134) | exit 0, the same three lines. Identical to `route.out` after `rvprobe`→`NFProbe` | out/02, out/02-route.normalized.out |
| 4 | Its 10 controls close unsealed and fail sealed (135) | 10 `CONTROL_PASS`, 10 `CONTROL_FAIL`; both identical | out/03, out/04 |
| 5 | Order list: 112 modules, 39 roots (136) | Re-derived from `git show 5241eb82`: the import closure of `NDNormalForm`'s dependents, with the root `TCSlib` excluded. **The same 112 modules in the same order**, and the same 39 roots. The tail is lines 67, 81, 111 and 112 | out/06-order/ |
| 6 | 19 base sorries in 9 modules (136, 437) | My comment-stripped census: the same 19 names in the same 9 modules | out/06-order/sorries-text.txt |
| 7 | Screen base 1,379 / 866 / 274,994, "the first round's after screen exactly" (137–138, 383–386) | Not re-run (excluded). The base file is **byte-identical** to the first round's delivered `screen-after.txt` (SHA-256 `6ed6fece…`). Its one line naming `NDNormalForm` is the `un_setup` pair at 57%. The 842 s and 2.47 GB are as in `screen-base.time` | out/07 |
| 8 | Lint: 0 FAIL, 17 WARN over 21 files; 0 findings on the file (139) | Identical to `lint-base.txt` | out/08 |
| 9 | Line numbers: target 752, `sorry` 758, 762 lines, `nf_sweep_display_pass` 693–704, target docstring 706, NDHost 571, Catalog 1520/12240/12302, Seam 835/898 (69–71, 116–119, 144–160) | all right; `scanTM_run_ofCfg` is at Catalog 12865 | out/12 |
| 10 | Paths named by the draft | all 25 exist at `0b8c2f9a`, NF-X1 included (`campaign/duplication-ledger.md` 791) | out/15 |
| 11 | In flight (72–76) | The open PRs are #181 and #182. Both change only `SpaceComplexity/*`, outside the order list. Their merge order is ruled (records `5fee87f6`); see F10 | out/14, `gh pr view` |

## (b) The route: feasibility from published rows, and the mathematics

**The pinned layout is right and covers every phase.** `nfcRed` (probe 102–132) redirects every
exit:
- `ctl.done` to `rep none` or `park false`;
- `rep j` by `exit` to `aFwd j` or `park false`;
- `aFwd j` to `aBack j`;
- `aBack none` to `nfcAfter N L none`, and `aBack (some j)` to `bFwd j`;
- `bFwd j` → `bBack j` → `bClr j` → `nfcAfter N L (some j)`.

Every other state maps to `none`, which is what each `hguard` needs.
- **`N.k = 0`.** `nfcAfter N L none = if h : 0 < N.k then … else ⟨.park, true⟩` (probe 96) goes
  straight to the verdict, and `rep (some j)` is uninhabited.
- **The verdict.** Park states are entered only by a redirect, and `nfcPark` stays put. So
  `hfirst` follows from the prefix clauses of `phaseHostTM_run`, and the verdict holds at `TQ`.
- **`exit : SL → Option Bool`** is enough: the leaf needs one pass state and one reject state,
  shared by all instances. Its intermediate states must have `exit q = none`, which is
  `hguard`. The probe's `L : Option (Fin N.k) → MultiTapeTM 2 Bool SL` matches "one machine,
  parameterized by the replayed tape".

**A's return.** It fits the leaf, on one condition (F3). `nfc_aReturn` needs
`hpos : c.workTapePos 0 = s.length` and `htape : ∀ p, c.workTapes 0 p = FinTM.bufferTape s p`.
The leaf never writes A, and the control sweep leaves A as `streamStartCfg` (`nf_sweep_run`). The
leaf reads one cell per step moving right, and the flag bit is a record's last bit. So after the
end-flagged record A's head is on cell `|s|`, provided the pass exit does not step past it. A
leaf that "reads the blank and moves on" would end at `|s| + 1`, and `skipBackTM_run_ofCfg` at
`u := s` would no longer apply. The probe states the return for `none` only; `some j` needs the
redirect `⟨.bFwd j, .run⟩` (F3).

**B's clear meets the rows' exact hypotheses: proved sealed (`rv_bClear`, out/09; under all 223
definitions, out/11).** The statement:
- **Hypotheses.** A region `R` on tape `1`, delimited by blanks: `htape : ∀ p, -1 ≤ p →
  p ≤ |R| → c.workTapes 1 (c.workTapePos 1 - i + p) = FinTM.bufferTape R p`, with B's head at
  offset `i ≤ |R|`.
- **Conclusion.** From `bFwd j` at `.run`, the host reaches `c₅.mapState (fun _ => nfcAfter N L
  (some j))` in `(|R| − i + 1 + 1) + (|R| + 3 + 1) + (2|R| + 2 + 1)` steps. There B is blank on
  `[pos − i, pos − i + |R|)` and B's head is at `pos − i`.

How each row's ranges are met:
- **`skipTM_run_ofCfg`** at `w := R.drop i`. Its `hw` range `0 ≤ p ≤ |w|` reads the suffix and
  the right delimiter.
- **`skipBackTM_run_ofCfg`** at `u := R`. Its `hu` range `-1 ≤ p ≤ |u|` reads both delimiters
  from `pos − |u| − 1`, which is the region's start because the head is at `start + |R| + 1`.
- **`clearTM_run_ofCfg`** at `w := R`. Its `-1` and `|w|` blanks are the same delimiters.

What the lemma also shows:
- `i = |R|` is allowed: the clear works from the region's right delimiter;
- `R = []` is allowed: it works on an empty region too.

What the rows' statements rule out: the clear does **not** work from the block left of the region
(B cell `a − 2`, where `a` is the region's first cell). There `skipTM_run_ofCfg` at `w := []` ends
on the left delimiter `a − 1`, and `skipBackTM_run_ofCfg` at `u := R` would need
`(a − 1) − |R| − 1 = a`.

**The exit invariant, and the gap (F1).** The draft's leaf "checks each decoded claim against B's
block, then writes the recomputed write" (draft 213–216). `Action.apply_workTapes` (Simulation 89)
says the cell after a step is `(a.workTapes i).1.getD (c.workTapeSymbols i)`. So the recomputed
write of a no-write action is "nothing", and a literal leaf leaves that visited block blank. Then:
- **The region can have holes.** With "skip the last move", the region is only the written
  cells, which need not be contiguous. The pinned invariant ("the nonempty, contiguous, nonblank
  visited region") is false, and `skipBackTM_run_ofCfg` over the visited set does not apply.
- **Completeness fails.** Clearing only the head's component leaves cells that a later replay
  reads. A concrete `N` with `k = 2` and three steps (out/18):
  - tape 0 writes, skips a write, then writes, so the clear leaves blocks with the code of true;
  - tape 1 then walks left into them and reads `some true` where its genuine claim is blank;
  - the genuine display is rejected, so the forward transfer fails.
- **The first round had the fix.** Its brief said: "The region is never empty: every record writes
  its block" (`c1-fill-nf.md` 238). The draft dropped it.

With that sentence restored, the visited region after `r` records is exactly the blocks of the
positions read so far: contiguous, since the head moves at most one cell per step, and nonempty,
since `t₀ ≥ 1`. Only the last record's move can leave it.
- **A move to the right** lands inside the region or on its right delimiter, which `rv_bClear`
  covers with `i = |R|`.
- **A move to the left** lands inside the region or on the block left of it, two cells outside,
  which nothing covers. The draft's two remedies each fix this:
  - skipping the end-flagged record's move keeps the head on the last read block;
  - initializing the destination block extends the region.
- **When the head never moves**, the region is the one block at B's start (`|R| = 2`, `i = 0`),
  and the clear takes `4|R| − i + 9 = 17` steps.
- **The initialization remedy without per-record writes** keeps the region contiguous, but leaves
  it empty when the head never moves and `N` never writes. The clear still works then (`R = []`),
  but the pinned "nonempty … B's head on a cell of it" is false. Per-record writes remove that
  case too.

**The replay leaf can be written and its run lemma proved as framed.**
- **Its state.** The state type is finite with decidable equality: a record position, the record
  buffer `Fin W → Option Bool`, the simulated state `Option N.State`, one scratch bit, and the two
  exits. Name its instances (MP4).
- **Its steps.** Each one is `MultiTapeTM.step_of_some`, then the own table, then
  `Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` and `Action.apply_workTapes`. The
  reads go through `Cfg.workTapeSymbols_eq`, and the input through `inputSymbolInner`,
  `Cfg.inputSymbol_of_zero` and `Cfg.inputSymbol_of_end`. All of these are in the import probe.
- **Its cost.** A work-tape record costs `W` steps on A, then `O(1)` steps on B with A stationary:
  read two cells, check, write two cells, move `0` or `±2`.
- **Its framing.** The run lemma must be framed over B's start position, because the previous
  clear leaves B's head on its region's first cell. The draft's framing ("B's head position")
  covers this, but "twice the simulated head" does not (folded into F1's edit).

**`hV` holds for every first-stopping stream.** Its ingredients:
- **The control sweep** runs on every `s` (`nf_sweep_run`) and redirects to `park false` unless it
  passes.
- **`nf_firstStop_records`** needs only the first-stop hypotheses, so every stream `V` sees is
  `n ≥ 1` records with only the last flagged. The leaf therefore reaches its pass exit after `n`
  records, or rejects earlier.
- **B's head** moves at most two cells per record.
- **B's clear** applies by `rv_bClear`, given the invariant: so `hV` depends on F1's sentence.
- **Wrong claims** reject, and rejection needs no clear.

**The transfers and the ledger.**
- **Forward.** Cut at the first halting time `t₀ ∈ [1, t]`. `nf_display_firstStop` on `w.take t₀`
  gives exactly `hslive`/`hsstop` of `guessCtlRunTM_accepts_of` (NDHost 1951). Its `hB` is
  `TP + 2 * s.length + TQ + 11 ≤ B`, and `TP = 0`, so the ledger shape `0 + 2|s| + TQ(s) + 11 ≤
  C·(t + 1)` is right.
- **The ledger's terms.** A's return is `|s| + 6` with its two redirects (`nfc_aReturn`:
  `(0 + 1 + 1) + (|s| + 3 + 1)`), so listing "one step per redirect" beside it counts them twice
  (F5). B's clear is `4|R| − i + 9` with `|R| ≤ 2t₀ + 2`.
- **Backward.** It is sound with `nf_decode`'s `01 ↦ blank`, as MP5 requires.
  - Induction on records: if the decoded reads of records `< r` are genuine, so are the recomputed
    actions, hence each replayed tape at `r`; the passed checks then make record `r`'s reads
    genuine.
  - The control fold gives a halted state after `n` records and the summary `some true`, so
    `N.AcceptsWithin x n`.

**Published, private, missing.** Every row and lemma the draft names is public at the base and in
the import probe. The one exception is a probe's file, not a declaration: `rv_tag` is in
`NFReviewVProbe.lean.txt`, not `NFReviewProbe.lean.txt` (F9). The one-step identity hazard has a
one-`rw` answer, `runFrom_succ_eq_step'` at `t := 0` and `runFrom_zero` (F14). The public
`Turing.runFrom_one` (`EmitIterEmbed` 261) is outside the 27-module import closure.

**The route probe shows what the draft says, with one caveat for copying (F7).** The
`deriving DecidableEq, Fintype` on the private `NfcPh` creates **public** constants:
`Turing.FinNDTM.instDecidableEqNfcPh` and `Turing.FinNDTM.instFintypeNfcPh`, with their
`decEq`/`match_N` auxiliaries (out/09, `private=false`). By `workflow.md` §4 these are public
constants, not public declarations, and need a name check. Rule 11 names only `DecidableEq`. The
`nf`/`Nf`/`nfc` names and these instance names are unused in the tree and on #181/#182 (out/10).

## (c) Standards, precedent and the must-pins

**The must-pins are all carried. Under MP5, the per-record write that the exit invariant depends
on is missing (F1).**

| Pin | Draft | Status |
|---|---|---|
| MP1 base and regions | base on `lean/c1-nf-partial` (the user's 2026-11-04 ruling supersedes MP1's "tip after this landing"); (b) after `nf_sweep_display_pass`, (c) line 758, (d) status phrases and the Implementation paragraph proposed in REPORT; the 39 frozen | carried; (d) lines added (F15) |
| MP2 lists re-taken | order 112, base sorries 19 in 9, screen base with NF-X1 | carried; the order list and sorries re-derived, the screen base matched (a5–a7) |
| MP3 four-module tail; measured budgets | "After every proof edit" (440–443); the budget table | carried; tail = order lines 67, 81, 111, 112 |
| MP4 named instances | "Named instances (pinned)" | carried; wording is broader than the probe (F6) |
| MP5 the leaf | shape, `nf_decode`, run lemma framing, exact time, exits, the invariant and its two remedies | carried, **but the per-record write is dropped (F1)**; invariant wording (F2); exit position (F3) |
| MP6 rows, `_ofCfg` only | the route and rule 11 | carried; proved for B's clear (`rv_bClear`) |
| MP7 layout, park, two-phase probe | the route probe | carried; checkpoint order (F4) |
| MP8 transcriptions | `rv_entry`, `rv_tag`, `rv_inputSymbol_congr`, `rv_moveInputPos_le`, plus `rvPark` | carried; `rv_tag`'s file (F9) |
| MP9 `hV`, transfers | binding sections | carried |
| MP10 ledger | "The ledger (pinned shape)" | carried; the redirect double count (F5) |
| MP11 seal | rule 10, `NFSealDefs.txt` (223), the four erasures | carried |

**The rest of the brief.**
- **Rules 10 and 11.** Rule 10 is incorporated "in full" from the first round. Rule 11's prefix
  rule is clear of the 39 names. Its derived-instance sentence needs `Fintype` too (F7).
- **Public-facing docstrings.** The draft lists the campaign labels. Copying the probe would bring
  in its "A's return…"/"B's clear…" docstrings: the first round's F1 flagged "A's head" as
  undefined vocabulary (F8).
- **Checkpoints 3–8 and zip names** (`fill-c1-nf-cont1.zip`, `-cp<N>.zip`, `N` 3–8) are
  consistent with the precedent. `V`'s layout is needed at checkpoint 3, though, because
  `nfc_aReturn` is stated over `nfcV` (F4).
- **The REPORT checklist** lacks the precedent's "ancestor check" and the first round's F9
  resolution, "what ended the work" (F11).
- **Duplication governance.** Population, screen, base and NF-X1 are right (ledger 791). The
  idiom pair needs no re-justification.
- **Environment.** The section matches addendum v2.6:
  - the narrowed cache over 39 roots;
  - the cache tool outside the one-Lean rule;
  - "a process deviation never ends the item";
  - the item-5 bootstrap.
- **Base and branch.** The commands are right for a default clone: `origin/lean/c1-nf-partial`
  exists after it, and the fetch refreshes it. `--is-ancestor` then checks @ANCESTOR@ against the
  branch tip, and the blob check prints `e6432b1e…` at `5241eb82`. But the blob check covers only
  the owned file. If #181 merges into the campaign before the records merge into
  `lean/c1-nf-partial`, the issued base's Lean is no longer 711f5444's (F10).

## (d) Findings

| # | Severity | Where (draft lines) | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **major** | the replay leaf, work-tape instance (213–216); the exit invariant (223–230); edge cases (283–291) | The pinned leaf "writes the recomputed write". By `Action.apply_workTapes`, `(a.apply c).workTapes i = Function.update (c.workTapes i) (c.workTapePos i) ((a.workTapes i).1.getD (c.workTapeSymbols i))`, so a no-write action (`(a.workTapes j).1 = none`) leaves a visited block blank. The region can then have holes, and the pinned invariant ("nonempty, contiguous, nonblank visited region") is false; `skipBackTM_run_ofCfg` over it does not apply. Clearing the head's component leaves cells that a later replay reads. For a 3-step, `k = 2` machine, the genuine display is rejected, so the forward transfer fails. The first round's brief had "every record writes its block" (`c1-fill-nf.md` 238); this draft dropped it. "Twice the simulated head" also omits B's start position, which the previous clear moves | out/18 (the lemma, the counterexample, the quotes); out/09 | Restore it: at every record the leaf writes the block with the post-step content `(a.workTapes j).1.getD old`, as two nonblank bits; B's head is at its start plus twice the simulated head; add the no-write and head-never-moves edge cases (edits F1a, F1b) |
| F2 | minor | the exit invariant (223–230) | "`skipTM_run_ofCfg` started left of the region ends on its first cell, so B's clear would not apply otherwise" and "The head can leave the region only by the last record's move to the left" are not quite right. The clear also applies from the right delimiter (`rv_bClear`, `i = |R|`). From the block left of the region, `skipTM` at `w := []` ends on the left delimiter, not the first cell. And "only … to the left" holds only given F1's per-record writes | out/09, out/11 (`rv_bClear` sealed) | Restate: B blank outside the region; the right delimiter is fine; the left block is not, and why; the head-never-moves case (edit F2) |
| F3 | minor | `nfc_aReturn` (193–194); "Its exits" (217) | `nfc_aReturn` needs `hpos : c.workTapePos 0 = s.length`. The pass exit must leave A's head on cell `|s|`: a leaf that reads the blank and moves on ends at `|s| + 1`, where `skipBackTM_run_ofCfg` at `u := s` fails. The probe proves the return for `none` only, but work tapes redirect to `⟨.bFwd j, .run⟩` | probe 189–264 | Pin the exit position; say to state the return once over the replayed tape (edits F3a, F3b) |
| F4 | minor | checkpoints 3 and 5 (357, 360) | Checkpoint 3 includes "A's return after it", which is stated over `nfcV`, the layout. But the draft places the layout at checkpoint 5 | probe 194–204 | Move the layout (generic over the leaf) to checkpoint 3 (edits F4, F4b) |
| F5 | minor | the ledger (272–278) | "each return of A, `|s| + 6`" already includes its two redirects (`(0 + 1 + 1) + (|s| + 3 + 1)`), and "one step per redirect" counts them again. For B's clear only `O(t₀)` is given. Its exact cost is `4|R| − i + 9` with its three redirects | probe 253; `rv_bClear`'s time | State which redirects each term includes; give the clear's exact cost (edit F5) |
| F6 | minor | "Named instances (pinned)" (198–202) | It pins private instances for the control sweep's `ScanPhase`, the leaf's state, the phase family and `V`'s state. The probe names only the fibers' two (`nfcStDecEq`, `nfcStFintype`, with `ScanPhase (nf_SweepState N)` inside at `.ctl`), and gets `V`'s state by inference (its two `example`s) | probe 52–75, 139–143 | Pin the probe's two and the leaf state's; `V`'s state by inference (edit F6) |
| F7 | minor | rule 11 (350–353) | It says "`deriving DecidableEq` gets a public instance name". The probe's `private inductive NfcPh … deriving DecidableEq, Fintype` creates `Turing.FinNDTM.instDecidableEqNfcPh` and `Turing.FinNDTM.instFintypeNfcPh` (`private=false`), with auxiliaries. Copying the pinned layout reproduces both. `workflow.md` §4 counts them as public constants, not declarations, so `Fintype` is missing from the rule | out/09 (`RV_INST`) | Name both; cite workflow §4; check and report, or write private instances (edit F7) |
| F8 | minor | region (b)'s docstring rule (146–151) | The probe's docstrings say "A's return, first step", "B's clear, first step" and "on B". The first round's review (F1) flagged "A's head" as undefined campaign vocabulary in library text. "Copy the probe's layout" would bring it back | probe 25–37; nf-fill REVIEW F1 | Say A/B are brief names; write tape `0`/tape `1` (edit F8) |
| F9 | minor | inputs (44–46); transcriptions (232–233) | `rv_tag` is in `NFReviewVProbe.lean.txt` (line 46), not `NFReviewProbe.lean.txt` | `grep` of both files | Attribute each transcription to its file (edits F9a, F9b) |
| F10 | minor | branch commands (13–20); "Base" (69–76) | The blob check covers only the owned file. @ANCESTOR@ is a later merge of the campaign records. The records already rule "#181 first, then #182" (`5fee87f6`). If #181 lands on the campaign before that merge, the base's Lean is no longer "711f5444's Lean", and "invisible to it" is false. The change is harmless to the order list (`SpaceComplexity` only), but it is undetected | out/13, out/14 | Add a Lean-identity check against `5241eb82` (edit F10). The maintainer merges the records at a campaign commit whose TCSlib is `711f5444`'s (`0b8c2f9a` and `299d2d54` both qualify), or restates the base |
| F11 | minor | REPORT checklist (470) | It lacks the precedent's "the base hash and the ancestor check", and the first round's F9 resolution ("REPORT states what ended the work") | `eq-fill-query-cont1.md` 690; nf-fill REVIEW F9 | Add both (edit F11) |
| F12 | note (decision D1) | B's clear (188–190, 358–359) | The draft pins the three clear rows but ships no chain for them. `rv_bClear` is that chain: 3 phases through `phaseHostTM_run` and `nfc_retag`, sealed over 10 and over 223 definitions, about 120 lines | out/09, out/11; `probe/RVClearTail.lean.txt` | Optional: add it to the inputs as an authorized transcription (D1) |
| F13 | note | inputs (44–46) | `rv_skeleton` (NFReviewProbe 80) assembles the target from `hfwd`/`hbwd`/`hV`, sealed. It is checkpoint 8's model and is not mentioned | NFReviewProbe 80–119 | Mention it (edit F9a) |
| F14 | note | known hazards (406–407) | The one-step identity needs no lemma: `rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]`. `Turing.runFrom_one` (EmitIterEmbed 261) is outside the imports | Deterministic 210–220; out/12 | Say so (edit F14) |
| F15 | note | region (d) (153–155) | It gives no lines. The status phrases are lines 30–31 and 707 | out/12 | Add them (edit F15) |

## Decisions for the maintainer

1. **D1 (F12).** Ship `rv_bClear` with the inputs, as an authorized transcription for checkpoint
   4 beside `nfc_aReturn`, or leave the chain to the worker. **Recommended: ship it.** It is
   proved under both seals, and it settles the clear's exact hypotheses that F1 and F2 turn on. If
   shipped, add one line to "The route", after the clear's bullet: "The review's `rv_bClear`
   (`NFContClearTail.lean.txt`) chains the three phases through `phaseHostTM_run` from B's head at
   any offset `i ≤ |R|` into a blank-delimited region `R`; keep it, renamed."
2. **D2 (F1/F2), optional.** Leave the remedy for a leftward last move to the worker, as the draft
   does ("Say which in `REPORT.md`"), or pin one. **Recommended: skipping the end-flagged
   record's move.** Given per-record writes, the region is then exactly the read blocks, and the
   clear's `i` is the last read block's offset.
3. **D3 (F10).** Merge the records into `lean/c1-nf-partial` before #181 lands on the campaign,
   or else restate the base's Lean in "Base, line numbers and what lands around you".

## Files

- `REVIEW.md`, this file; `suggested-fix.diff` (`orig/` → `edited/`, 17 asserted edits from
  `scripts/edits.py`; it applies to `orig/` and reproduces `edited/` exactly, out/19);
- `orig/c1-fill-nf-cont1.DRAFT.md` (`268d5b26…`), `edited/c1-fill-nf-cont1.DRAFT.md`;
- `out/`: the raw outputs cited above; `out/00-runs.txt` lists every Lean run;
- `probe/`: the probe sources as `.lean.txt`; `scripts/`: the review's scripts;
- `wt/`: the review worktree, left registered for re-runs. To remove it: unlink
  `wt/.lake/packages`, then `git worktree remove --force`.
