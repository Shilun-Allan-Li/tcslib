# Review: NF cont1, the linear normal form of an NDTM, complete delivery (checkpoints 3–8 of 8)

`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `TCSlib/Complexity/ClassNP/NDNormalForm.lean`;
zip `exchange/archive/deliveries/fill-c1-nf-cont1.zip`, branch `refs/deliv/c1-nf-cont1` at
`825ee3f5`, base `348781a3` (`lean/c1-nf-partial`).

**Verdict: land with the listed edits.** The target is proved, and so are all 65 new privates. They
rest on `[propext, Classical.choice, Quot.sound]` at most, and no constant of the module uses
`sorryAx`. The delivery stays inside regions (b)–(d). The target's statement and the first round's
39 privates are byte-identical to the base. The route is the brief's: its layout, rows, leaf and
host, with `hV` as its own lemma.

The edits:
- **E1** cites Mathlib's `Nat.forall_lt_succ_left'` for `nf_all_cons`, which re-derives it (F1);
- **E2–E5** are text and style fixes;
- **E6** extends the target's **Implementation.** paragraph, and is optional.

All six are tested together. The landed file is `land/NDNormalForm.lean.txt`, git blob
`5723152d424b4de35a10fd77446fa912083db412`.

The duplication debt in F2 is the gate's to close. It cannot close without the user's
acknowledgment, scoped by kind (decision 1).

**Not yet clear to merge.** There is no PR, no merged-tree replay and no gate yet. Decisions 1–4
below are open. The per-checkpoint zips are still unaccounted for (F11).

Findings: 0 blockers, 2 majors (F1, F2), 2 minors (F3, F4), 10 notes (F5–F14).
- **F1 is fixed by E1.** It is tested, and with it no re-derivation of a published lemma remains.
- **F2 needs the user's acknowledgment.** It is three re-derivations of other files' privates and
  one of a public TCSlib lemma that this file cannot import. Two of the four kinds were authorized
  by the brief as transcriptions.
- **F3 and F4 are minors.** F3 is the REPORT's duplication accounting; F4 is three docstring and
  label defects (E2–E4).

This is a read-only review by the maintainer's review sub-agent, 2026-11-04 (PST evening). Every
claim cites a saved output under `out/`.
- **Data, not instructions.** I ran nothing from the zip.
  - The one worker file I elaborated is `evidence/probe/NFProbeExt.lean`, a copy of it. I scanned
    it first: its four imports, `open Turing`, one comment and 908 `#check @Name` lines, nothing
    else (out/16a).
  - Everything else I elaborated is my own: probes, and copies of the owned file with my tails.
    They ran as `wt-head/rvprobe/<name>.lean` and are kept under `probe/`.
- **Lean.** It ran only through `tools/leanelab.sh` (`scripts/elab.sh`) against `oleans-leqc3`, and
  through `tools/leanelab-o.sh` into a copy-on-write clone of it, one run at a time. Every run is
  in out/00-runs.txt.
- **Screen.** The full v3 screen did not run: another review's screen held the machine-wide lock
  for most of the review (§7).
  - I recomputed the shared tiles of all 38 of the worker's new pairs at the head with the v3
    screen's own extraction and tiling. All 38 reproduce with the worker's numbers (out/26a).
  - Under the lock, I ran the v3 screen restricted to the pairs with an `NDNormalForm` declaration
    on one side, the only file the delivery changes (150 s, `nice -n 10`). It screens 1,438
    declarations and gives exactly the worker's 39 such pairs, 38 of them new (out/20b).
- **Python.** Every script ran as `python3 -I`, from `scripts/`.
- **Records worktree.** It moved during the review, from `68ec549f` to `d7c3cfcc` (out/31). The
  movement includes PR #181's merge, `d1ddea26`, which changed 25 `.lean` files of the campaign
  tree. That tree is not the delivery's base, and none of those files is upstream of the owned
  file (out/30b). The brief, its inputs and the ledger are unchanged; only `campaign/backlog.md`
  gained records.
- **Restart.** The maintainer's session restarted mid-review. My queued head screen was lost at
  that point, before it had taken the lock. No finished output was lost.

## Findings

| # | Severity | Where | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| F1 | **major** (failure mode 5: re-derivation of a published lemma) | `nf_all_cons`, head 1642–1657 | `nf_all_cons` re-proves Mathlib's `Nat.forall_lt_succ_left'`, in 6 lines: a statement over the indices of `rec :: rs` iff the head and the shifted tail. `exact?` names the lemma for the generic form (X13), and the lemma alone closes `nf_all_cons`'s statement as a term (`:= Nat.forall_lt_succ_left'`; the module copy elaborates). REPORT §7 says "`exact?`: none" for this row, but its `exact?` probe has no example for `nf_all_cons` (7 examples, out of 65 declarations) | out/22c (X13, X14), out/22d; worker `evidence/duplication/NFExactProbe.lean` | **E1** (tested): `:= Nat.forall_lt_succ_left'`. Nothing then remains to acknowledge |
| F2 | **major** (failure mode 5: debt, human acknowledgment required) | `nf_inputSymbol_congr`, `nf_retag`, `nf_tagged_ne_park`, `nf_stream_length` | Four kinds of fact that other TCSlib declarations already state. None is in the duplication ledger (out/28a). The canonical statements, with the copies found (a candidate enumeration, not an exhaustive one): **(i)** the input read depends on the input head only (`c.inputPos.val = c'.inputPos.val → c.inputSymbol = c'.inputSymbol`): `nf_inputSymbol_congr` is `ExhaustiveReplay`'s private `xr_inputSymbol_congr`, the same statement, and `ZoneRebalance`'s private `zr_inputSymbol_congr` is a third member, which the worker missed. **(ii)** a live configuration redirected to `⟨i, q⟩` is the tagged configuration of phase `i` at `q`: `nf_retag` is a special case of `SeamLayout`'s private `sl_rewrap`, and the same text runs inline in 15 other declarations (screen pairs). **(iii)** a configuration tagged by phase `i` is at no state `v` with `v.1 ≠ i`: `nf_tagged_ne_park` is a special case of `CfgRecord`'s private `record_tag_ne`, and `SeamLayout`'s private `sl_tagged_ne_done` is another member, which the worker missed. **(vi)** a list of equal-length chunks has length count × chunk length: `nf_stream_length` is a special case of the public `Complexity.CfgTableau.length_flatMap_const` (`CircuitComplexity/PSubsetPPolyTableau`), which lies outside the frozen import set, so it cannot be cited. The brief authorized (i) and (ii) as transcriptions with promotion requests. **No public form of (i)–(iii) exists at these imports** (`exact?` X04–X07). In `NDNormalForm` these are 4 of 105 declarations, under one fifth | out/22a, out/22e, out/22f, out/26a, out/27a, out/22c | User acknowledgment by kind (decision 1). Resolution in the 12.2c window: publish `Cfg.inputSymbol_congr` (Configuration), a generic retag and tagged-≠-verdict lemma beside `phaseHostTM_run` (Seam), and move `length_flatMap_const` to a basic list home; then re-point every copy |
| F3 | minor (REPORT accuracy; accounting) | REPORT §7, §5 | (1) "Three searches for every new declaration", but the `exact?` probe covers 7 statements, and the table marks rows "`exact?`: none" that were never probed. (2) It cites `evidence/final/`, which does not exist; `evidence/duplication/` does. (3) "the 64 names" against 65 new declarations. (4) The table names `nf_vrun_genuine`, which the consolidation replaced by `nf_vrun_of_ok`. (5) The promotion families miss `zr_inputSymbol_congr` and `sl_tagged_ne_done`, and the public generalization of `nf_stream_length` is not reported (F2). None of this changes what is delivered | worker NFExactProbe and exact-probe.log; out/25b; out/22a, out/22e, out/22f | Record the corrected accounting in the ledger entry for F2 |
| F4 | minor (public-facing text; docstring accuracy) | head 1549, 1599, 705/3271 | (1) `nf_vstep`'s docstring cites `nf_vstep_genuine`, a name that never existed in any of the seven commits. (2) `nf_vrun_ctl`'s docstring states only the state, but its statement also carries the output summary. (3) The code section is named `Continuation`, the campaign's name for this round, in library code | out/18b, out/19a, out/25b | **E2**, **E3**, **E4** (tested) |
| F5 | note (rule 11; public constants) | `nf_Ph`, `deriving DecidableEq, Fintype` | This creates 76 public constants: `Turing.FinNDTM.instDecidableEqNf_Ph` with `.decEq`, 70 `_proof_N` and a `match_N`, and `instFintypeNf_Ph` with two `match_N`. The module's other 436 constants are private, and its only public declaration is the target. Allowed: the brief's rule 11 permits it once the names are checked, and by `workflow.md` §4 a derived instance of a private type is a public constant, not a public declaration, and needs no finding when the name check finds no clash. **The check:** `git grep -w` over all 457 refs (277 distinct commits) finds the 65 new names and the two instance names only in the owned file at the delivery head. Later in the review the repository had 645 refs; the 12 commits they added contain none of the names (with a positive control on the delivery head). `policy.md` §1 is met: nothing goes to the root namespace | out/09, out/13d, out/13f | None (a pair of private instances would be optional uniformity) |
| F6 | note (rule 10; clean) | the diff | **Walk.** It reaches 141 TCSlib constants, none private. The 37 semireducible definitions among them are reached as terms only. The walk is identical to the worker's 141 (out/15a). **Inspection.** 952 argument rows. Every other-file TCSlib name passed to `rw`/`simp`/`simpa` is a theorem: 49 distinct published equations and laws. The only TCSlib definition named at all is `moveInputPos`, inside `show` terms, where it is restated, not unfolded. `unfold` and `simp only [d]` name only this file's definitions. The 34 unrestricted `simp`/`simpa` calls, run as `simp?`, use only core/Mathlib lemmas, simprocs and local hypotheses (39 suggestions, 64 names). No core or Mathlib definition is passed to `rw`, `simp` or `unfold`. **Seal.** My generator seals 257 definitions: the brief's 223 and every semireducible TCSlib instance in scope (34), the host and phase instances included. With it the module body elaborates with 0 errors. The file's own `attribute [-simp]` erases the four `@[simp]` TCSlib definitions over the whole new section, and the target's 4-line body contains no `simp`. **Controls.** 252 of the 257 definitions have a rfl- or equation-goal control that closes unsealed and fails sealed. The other 5 (four derived `Fintype` instances and `instInhabitedCfg`, whose delta goal closes by structure eta) get source controls: 41 hand-written `rfl`/`decide` goals over 41 definitions, the host and phase instances among them; all 41 close unsealed and fail sealed. The worker's 231-definition seal is a subset of mine and is sound | out/08, out/11, out/12a–g, out/14a–i, out/15a | None |
| F7 | note (duplication: the 38 new pairs) | §7 | Each is an idiom or an in-file parallel; none is a copy at 90% or more. The cross-file pairs are the published field equations (`Cfg.ext` with `Cfg.mapState_*`, `streamStartCfg_*`, `Cfg.init_*`) and the kinds of F2. `nf_entry` ← `canonStageBuffer_none` (80%) is the published `FinTM.bufferTape_eq` plus core `List.getElem?_eq_none`. **One pair touches H's file:** `NTimeHierarchy.lean::un_setup` reproduces `nf_retag`, 216/322 = 67% | out/21a, out/26a, §7 | Decision 3 (H's overlap) |
| F8 | note (row candidates; the 12.2c window) | `nf_entry`, `nf_aReturn`, `nf_region`, `nf_forward` | **(iv)** "a buffer is blank at and past its end" is a two-line private in `CodeSimulator` (`canonStageBuffer_none`) and runs inline three times here. No public form exists (X09); the counterpart `FinTM.bufferTape_of_neg` is public. **The first halting time of a choice word** (FH-1's kind, for `NDTM.runWith`) runs inline in `nf_forward` by `Nat.find`. FH-1's public form `MultiTapeTM.exists_first_halt` is deterministic, and no NDTM form exists (X10). Neither is a re-derivation of a lemma | out/22a, out/22b, out/22c, out/28a | Ledger "row candidates" (optional) |
| F9 | note (style) | 19 places in the new region | 16 double and 3 triple blank lines | out/06 | **E5** (tested) |
| F10 | note (the target's docstring) | head 3273–3318 | The **Implementation.** paragraph (the partial's E3) is accurate, but it does not mention the second work tape's block layout or the constant. That leaves "forward with the explicit constant" without a value. The sketch's "tape A"/"tape B" and "Fill obligations, named:" are base text from before the partial; the deferred cleanup covers them | head 3281–3318 | **E6** (tested; optional, decision 2) |
| F11 | note (process; timeline) | the session | (1) **The checkpoint zips.** REPORT says cp3–cp8 were "one zip each, each delivered at once", but only the final zip arrived; the partial was the same (its F9). The zip records no checkpoint zip and no per-checkpoint tail log, only the final tail's. (2) **A compressed timeline.** Checkpoint 3 (1,050 lines) was committed 12 min 47 s after the bootstrap ended. Checkpoint 5 (730 lines) came 6 min after the worker restart. The consolidation (+114/−165, two new shared lemmas) was committed 6 min 15 s after the first after screen ended, the result that REPORT says led to it. No development-run log is shipped, so the one-Lean rule during development and the tail runs after each edit cannot be verified. (3) **The logs.** What the zip does log is consistent: bootstrap 112/112, 1,257.8 s, 19 sorries; final sweep 112/112, 1,187.1 s, 18 sorries, the target's line the only difference; no overlapping modules. Nothing landed depends on this: Lean checks the content, and my own runs pass | out/02, out/25a, out/25b, out/25c | Decision 4 (ask for the checkpoint zips) |
| F12 | note (history) | the 7 commit messages | The bodies say "Checkpoint N of the linear normal form's continuation" (campaign labels) and end with a `Claude-Session: https://claude.ai/code/session_…` trailer | out/02 | Reword at landing (§11) |
| F13 | note (route letter) | the leaf's run lemmas | They step through the published `step_of_tapeAction_move` and `step_of_tapeAction_write` (Catalog), the one-step lemmas of `Turing.tapeAction`, rather than `MultiTapeTM.step_of_some` and `Action.apply_*`, which the brief names. That is the same argument through a published row lemma, with no private loop driver. The authorized `rv_moveInputPos_le` is unused | out/14i, out/27a | None |
| F14 | note (landing environment) | the campaign tip | #181 merged after the base (`d1ddea26`, Lean `98912ab2`'s; snapshot `oleans-lsm5`). Among its 25 changed `.lean` files, `CodeSimulator` is upstream of `NTimeHierarchy` (a one-line proof dedup) and lies in the screen population; nothing is upstream of `NDNormalForm`. The campaign's `NDNormalForm` is still the pre-partial blob `5150734a` | out/30a, out/30b | Replay from the merged tree's snapshot; re-take the screen at the PR head (§11) |

## 1. Integrity and scope

| Check | Result | Evidence |
|---|---|---|
| Zip | SHA-256 `9dd14763…4184`; 108 members; 90/90 sums OK, no unlisted file, no link | out/01 |
| Bundle | `verify` okay; sole prerequisite `348781a3`; one ref, `fill/c1-nf-cont1` = `825ee3f5` = `refs/deliv/c1-nf-cont1` | out/01 |
| Commits | seven, linear on the base, author "Claude (fill agent)", no merge; owned file only, +2574 −4 | out/01, out/02 |
| Blobs | base `e6432b1e` (762 lines), head `d767cc72` (3,332 lines) = the zip's source; the base's Lean equals `5241eb82`'s | out/01, out/06 |
| Regions | four hunks: `@@ -30,2 +30 @@` (d), `@@ -705,0 +705,2568 @@` (b), `@@ -707 +3274 @@` (d), `@@ -758 +3325,4 @@` (c). The only deleted lines are the base's `sorry` and the two status phrases | out/04 |
| Freeze | public 1 → 1, none added or removed; private 39 → 104, **"private changed: []"**; the target's statement unchanged, its body the only authorized change; `stmtcheck`: every base code line in order, except the `sorry` | out/05 |
| Imports | the base's four, none added | out/04 |
| Admissions | in the added code (comments stripped): no `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `opaque` or `set_option`. The hits are the section's `attribute [-simp]` on the four `@[simp]` TCSlib definitions (a hardening), `deriving DecidableEq, Fintype` on `nf_Ph`, and four `private instance`s | out/06 |
| Widths | widest line 100; none over 100 | out/06 |

## 2. Elaboration and axioms

- **The head file.** Against `oleans-leqc3`: exit 0, no message of any kind, so no sorry warning and
  no other warning (out/03).
- **Axioms.** A copy with my tail prints all 66 declarations (out/08, out/10):
  - **the target:** `[propext, Classical.choice, Quot.sound]`;
  - **the 65 new privates:** 30 on those three, 26 on `[propext, Quot.sound]`, 1 on `[propext]`,
    8 on none;
  - **the census** of the module's 513 constants: none is outside the standard three, and none
    uses `sorryAx` directly ("OUTSIDE_STD []", "DIRECT_SORRY []").
- **Downstream, compiled into the clone.** The import graph gives exactly four modules, the root
  excluded (out/23a). The clone matches the head's tree, since the head's Lean differs from
  `711f5444`'s only in `NDNormalForm` (out/23b).
  - **The runs:** `ClassNP/NDNormalForm`, the `ClassNP` facade, `Diagonalization/NTimeHierarchy`
    and the `Diagonalization` facade all exit 0 with no warning (out/24).
  - **Against the base sorry list:** `NDNormalForm`'s one entry is gone, and none of the four
    modules has any sorry warning. `NTimeDiagonalizer`'s `exists_diagonalizer` remains in the base
    set and outside this closure.
  - **The headline:** in the clone the target is on the standard three, while `exists_diagonalizer`,
    `Complexity.ntime_hierarchy` and `NTIME_linear_ssubset_square` carry `sorryAx`. That is
    consistent with E-D's target still being sorried at this base (out/24e).

## 3. Brief conformance

**Must-pins MP1–MP11** (the partial's review, §6):

| Pin | Delivery | Status |
|---|---|---|
| MP1 base, regions, freeze | base `348781a3` on `lean/c1-nf-partial`; (b)–(d) only; 39 privates and the statement byte-identical | met (§1) |
| MP2 lists | bootstrap sorries 19 in 9, exactly the base list; before screen byte-identical to the screen base | met (out/25c; worker `cmp`, out/21a) |
| MP3 tail after each checkpoint | the final tail is logged (4 modules, 29.3 s); the per-checkpoint tails are not shipped | unverifiable (F11) |
| MP4 named instances | `nf_stDecEq`/`nf_stFintype`, private, with `@instDecidableEqScanPhase _ inferInstance` and `@instFintypeScanPhase _ inferInstance` at `.ctl`; the leaf's state through `nf_leafEquiv`, private; `V`'s state by inference (the two `example`s); no `synthInstance` option | met |
| MP5 the leaf | one machine `nf_leaf N j`, `j : Option (Fin N.k)`; every claim through `nf_decode`, every block through `nf_blockDecode`, which maps `01` and blank to blank as `nf_decode` does; tape `0` one cell per step through the control sweep's own `nf_sweepStep`; tape `0` stationary on tape-`1` steps; `nf_act` recomputes `N.tm.tr`; the input instance compares with the native input cell and moves by the action's `inputTape`. Its docstring names `Turing.scanTM` (one tape) and `StepBlock`'s record reader (`k + 2` tapes), and says what was missing | met |
| MP5 run lemmas | `nf_leaf_run_in`: exact time `(2k+4)n`. `nf_leaf_run_wk`: `T + 2 = (2k+8)n`. Both are framed over tape `0`'s head, tape `1`'s start `p₀`, an arbitrary interval and the input head, by induction over records with the virtual run `(rs.take r).foldl nf_vstep` | met |
| MP5 exit invariant | tape `1`'s nonblank cells are exactly `[p₀ + 2lo', p₀ + 2hi' + 1]`, with `lo' ≤ y ≤ hi'` and the head on block `y`'s second cell; `nf_region` reads off the clear's word and offset | met |
| MP6 rows | tape `0`'s return: `skipTM` at `w := []`, then `skipBackTM` at `u := s`. Tape `1`'s clear: `skipTM` at `R.drop i`, `skipBackTM` at `R`, `clearTM_run_ofCfg` at `R`. `_ofCfg` forms only; no R3 row is reached | met (out/15a) |
| MP7 layout | `nf_Ph`, `nf_St`, the instances, `nf_park`, `nf_M`, `nf_after`, `nf_red` and `nf_V` are the route probe's, identical up to renaming and whitespace | met (out/27a) |
| MP8 transcriptions | see below | met |
| MP9 `hV` and the transfers | `nf_hV` is its own lemma, over every first-stopping stream; the backward transfer works over decoded fields, through `nf_split` (`nf_firstStop_records` and `List.ofFn_mul'`), `nf_sweep_records` and `nf_vrun_of_ok`; the forward transfer cuts at the first halting time | met |
| MP10 ledger | `nf_ledger`: `0 + 2|s| + TQ + 11 ≤ nf_C k · (t + 1)` from `|s| = (2k+4)t₀` and `t₀ ≤ t` | met |
| MP11 seal | 231 definitions (the 223 and 8 instances) with 231 controls and 4 erasures | met; mine is a superset (F6) |

**Every record writes its block, and the leaf skips the last record's head move.** Both hold
(head 941–974):
- **The writes.** The `blk₁` step writes `some n.isSome` and the `blk₂` step writes
  `some (n.getD false)`. Here `n = (a.workTapes t).1.getD claim`, so an action that writes nothing
  rewrites the old content. Both bits are nonblank symbols, so `none` is coded `00` and is never
  blank.
- **The skip.** With the end flag set, `blk₂` moves `0` and enters `pass`, with the head on the
  block's second cell. Otherwise the moves are `+1` then `0, 0`; `−1` then `0, 0`; or `−1` then
  `−1, −1`: two cells per simulated move.
- **The pinned exit position.** At the flag bit, tape `0` moves right onto cell `|s|`, and the host
  redirects there.

**Hosts.** `nf_host N` is
`guessCtlRunTM nf_P nf_P.q₀ 0 (0, false) (nf_ctlStep N.k) (nf_ctlStop N.k) false V ⟨ctl, fwd init⟩
⟨park, true⟩ ⟨park, false⟩`, packaged by `nf_pack`.
- **The acceptance lemmas.** It cites `guessCtlRunTM_accepts_of` and
  `guessCtlRunTM_stream_of_accepts`. It never composes `phaseHostND`, and never writes a host state
  (out/15a).
- **The setup.** `nf_P` is a one-state machine started at its own exit, so `TP = 0` (`nf_setup`). No
  published stationary row exists to cite instead, for `nf_P` or for `nf_park`.

**The authorized transcriptions** are faithful, and the extensions are sound (out/27a). Lean proves
each extension.
- **Identical up to renaming:** the layout, `nf_entry` (`rv_entry`) and `nf_inputSymbol_congr`
  (`rv_inputSymbol_congr`).
- **Generalized:**
  - `nf_park` is `rvPark`, reflowed;
  - `nf_retag` takes any source state type `S` instead of `nf_St N SL i₀`;
  - `nf_tag` takes any phase `i` instead of `rvPh A false`.
- **Strengthened:**
  - `nf_aReturn` is stated for every replayed tape `j`, ending at `nf_aNext N L j`. It adds
    `c₃.state.isSome` and "at no verdict on the way", from `phaseHostTM_run`'s prefix clause. Its
    rows, arguments and `|s| + 6` are the probe's.
  - `nf_bClear` adds the unchanged tape `0`, its head, the input head and the output, plus
    `c₅.state.isSome` and the no-verdict clause. Its rows, arguments and time are `rv_bClear`'s.

**The constant.** `nf_C k = 6W + k(2W + 12) + 21 + 15k` with `W = 2k + 4`, that is
`4k² + 47k + 45`. It depends on `N.k` only. I checked REPORT §2's term-by-term account against
`nf_V_char`, `nf_V_tail` and `nf_ledger`:
- **Up to the input's return:** the control sweep and its dispatch take `2|s| + 3`; the input's
  replay and its dispatch, `|s| + 1`; the return, `|s| + 6`. In total `4|s| + 10`, which is
  `nf_V_char`'s first term.
- **Per work tape:** the replay and its dispatch take `(2k+8)n − 1`; the return, `(2k+4)n + 6`; the
  clear, `4|R| − i + 9 ≤ 8n + 9`, since `|R| ≤ 2n` by `hsz` with `hi − lo = −1`. That is at most
  `(4k + 20)n + 14 ≤ (2W + 12)n + 15`, which is `nf_V_tail`'s factor.
- **The total:** with the host's `2|s| + 11`, it is `(6W + k(2W+12))t₀ + 21 + 15k ≤ C(t + 1)`. The
  arithmetic is `nf_ledger`'s `e1`–`e4`. The account is correct.

**Edge cases** (REPORT §8):
- `N.k = 0`: `nf_after N L none` and `nf_tapeEntry … 0` are the passing park, and `nf_V_tail` runs
  with `d = 0`.
- `t₀ = 1`: the `nil` tails of both run lemmas.
- An input head off the input: the leaf compares with the native `Cfg.inputSymbol`, blank there.
- A blank write, and an action that writes nothing: the block is always written, as two nonblank
  cells.
- A head that never moves: `nf_blocks_write` from `[0, −1]` gives one block.
- Emitting transitions: the first round's summary.
- Wrong claims: rejected, and the first verdict still exists (`nf_V_char`).
- The code `01`: decoded as blank in both readers.

All hold as stated.

## 4. The mathematics: statements, sketches, non-vacuity

- **The target's statement is unchanged and proved.** Its forward clause rules out an `M` that
  rejects everything, and its backward clause rules out one that accepts everything. So the proof
  cannot have chosen a degenerate `M`.
- **Every hypothesis of the chain is discharged inside the chain.**
  - The run lemmas' interval hypotheses are met at each work tape's start: `lo = 0`, `hi = −1`,
    tape `1` blank.
  - `nf_V_char`'s `rs ≠ []` and its flags come from `nf_split`, in the backward transfer, and from
    the display, in the forward one.
  - `nf_hV`'s hypotheses are the host's `hV` obligation exactly: it is passed as
    `fun s hl hs => nf_hV N x s hl hs`.
- **I compared every new docstring with its statement** (out/18c).
  - **They match, except F4's two.**
  - **Imprecise wording, no edit:** `nf_leaf_prefix` "reads a record's bits" covers its first
    `2k + 3` bits, and `nf_leaf_toLast` takes the last. "One cell past the stream" in
    `nf_leaf_run_in`/`_wk` means cell `|s|`, the blank after the stream, as pinned.
  - **The non-public module docstring stays accurate:** "This module isolates the normal-form
    statement and its supporting construction"; "No new definitions".

## 5. Rule 10

**The walk** (out/08, out/15a).
- **Its size.** It reaches 948 external constants: 141 in TCSlib (13 constructors, 58 definitions,
  10 inductives, 60 theorems) and the rest in core, Mathlib and my tail. None of the TCSlib ones is
  private, and none is an R3 row.
- **The definitions.** Of the 58, 37 are semireducible: `Action.apply`, `Cfg.init`,
  `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`, `CodeNDTM.toFinNDTM`,
  `FinNDTM.AcceptsWithin`, `FinTM.bufferTape`, `GuessRunPhase.CtlState` and its `Fintype`
  instance, `MultiTapeTM.initCfg`, `runFrom`, `step`, `NDTM.initCfg`, `runWith`, `stepWith`,
  `StepBlock.outputSummary`, `summaryEmit`, `clearTM`, `guessCtlRunTM`, `guessRunCfg`, the six
  Scan/Seek/Sweep phase instances, `instFintypeGuessRunPhase`, `moveInputPos`, `phaseHostTM`,
  `scanFold`, `scanKeep`, `scanTM`, `skipBackTM`, `skipTM`, `streamStartCfg` and `tapeAction`. The
  rest are reducible projections and three `casesOn`.
- **The probe.** The worker's extended probe, copied and scanned, has 908 checks, 0 errors and the
  two known deprecation warnings. It checks all 141 TCSlib constants of the walk (out/16b).

**The tactic arguments** (out/14a–i).
- **Over the diff:** 952 argument rows, with 1,580 identifier occurrences, each resolved by Lean in
  the module's namespace:
  - 944 are local hypotheses or variables;
  - 173 occurrences are TCSlib theorems: 49 distinct published equations and laws (out/14i), from
    `Cfg.mapState_*`, `Cfg.init_*`, `streamStartCfg_*` and `guessRunCfg_*` to
    `MultiTapeTM.runFrom_add`, `step_of_tapeAction_move` and `phaseHostTM_run_le`;
  - 86 are own-file definitions, in `unfold`/`simp only`/`rw`. Their unfold targets are only
    `nf_C`, `nf_V`, `nf_act`, `nf_blockDecode`, `nf_blockWrite`, `nf_sweepPass` and
    `nf_tapeEntry`.
- **Mis-resolutions.** The few "definition" hits are local names that resolve to globals (`rec`,
  `k`, `read`) or proof terms inside arguments (`rfl`, `decide`, `absurd`).
- **No `delta` and no `change`.** `MultiTapeTM.step` and `Action.apply` are never unfolded, and
  `N.tm.tr` is only applied.
- **The unrestricted simps.** All 34 calls, made `simp?`, use only core and Mathlib theorems,
  6 simprocs and 4 local hypotheses (out/14d).

**The seal** (out/11, out/12a–g). My generator (`scripts/mkseal.py`) takes every semireducible TCSlib
definition in the environment except projections, matchers, auxiliary recursors, other files'
privates and compiler auxiliaries.
- **The set.** That is 257 definitions: the brief's 223 and 34 instances. It is a superset of
  every definition the walk reaches.
- **Where.** It is inserted before the first new declaration, so it covers the whole new region
  and the target's body. The file's own section-wide `attribute [-simp]` covers the four `@[simp]`
  TCSlib definitions.
- **The body:** 0 errors, no message.
- **The meta controls.** For each sealed `D`, `rfl` at `@D = D's value` and at `D`'s first
  equation, run by an elaborator command.
  - **Delta:** 247 close unsealed, 5 sealed; 242 discriminate.
  - **Equation:** 256 close unsealed, 5 sealed; 251 discriminate.
  - **Coverage:** 252 of 257 definitions have a discriminating control.
- **The 5 without one:** `instFintypeGuessRunPhase`, `instFintypeInputRewindPhase`,
  `instFintypeSeekPhase`, `instFintypeSweepPhase` and `instInhabitedCfg`. Each closes sealed by
  structure eta.
- **The source controls.** 41 hand-written `rfl`/`decide` goals, each on its own sealed definition:
  the 5 above, the other phase instances, `GuessRunPhase.CtlState` and its `Fintype` instance, and
  30 core definitions from `bufferTape` to `guessCtlRunTM` and `AcceptsWithin`. All 41 close
  unsealed and all 41 fail sealed, with 0 errors before the tail (out/12f).
- **So every one of the 257 definitions has a working control.**

## 6. Rule 11

- **No other file's private is reached or restated under another name.** The walk reaches none
  (out/15a). Three privates do restate facts that other files state privately; they are F2's
  kinds (i)–(iii), disclosed by the worker for (i) and (ii).
- **Names.** All new names are `nf_`, and clear of the 39 first-round names. The name check is in
  F5 (out/13d).
- **The rows.** No R3 row is reached; the `_ofCfg` forms only.

## 7. Duplication

**The screens.**
- **Before.** The worker's before screen is byte-identical to the screen base (worker `cmp`; out/21a
  recomputes the difference against the base).
- **After.** `pairdiff` of the worker's after screen against the base: 904 pairs at the head, 866
  before, **38 new, 0 removed** (out/21a).
- **Tiles.** All 38 recomputed at the head with the screen's own tiling (`scripts/tiles.py`), each
  with the worker's numbers (out/26a).
- **The restricted run.** A new pair must involve `NDNormalForm`, the only changed file. So I ran
  the v3 screen restricted to pairs with an `NDNormalForm` declaration on one side, under the
  screen lock (`scripts/screen-nf-pairs.py`, the repository's script with one asserted line
  added).
  - **Its declarations:** 1,438 screened, the worker's count.
  - **Its pairs:** 39 with `NDNormalForm`, **identical to the worker's after screen's 39**. Against
    the screen base, 38 are new and 0 removed. The new pairs reproduce 10,512 characters, which is
    exactly the worker's total difference, 285,506 − 274,994 (out/20-screen-nf.txt, out/20b).
  - **So the worker's after screen is confirmed** for every pair this delivery can add.

**The 38 pairs and their dispositions** (shared tiles in out/26a):

| Pair(s) | Shared text | Disposition |
|---|---|---|
| 15 declarations of other files reproduce `nf_retag`, 54–74%: `canonStageLeg0`–`6`, `canonStageOuterSpec`, `canonStageInnerSpec`, `us_start`, `xr_phase_step`, `xr_halt_fixed`, `xr_E_initCfg`, `exists_ndInterpreterCore`, `gr_handoff`, `guessCtlRunTM_stop_of_halted`, `phaseHostTM_run`, `Cfg.mapState_mapState`, `un_setup` | `Cfg.ext` with the five published `Cfg.mapState_*` equations | idiom; the kind is F2 (ii). No published lemma states `nf_retag`: `Cfg.mapState_mapState` composes renamings, and X06 finds nothing |
| `nf_retag` reproduces `us_start` (65%) and `Cfg.mapState_mapState` (59%) | the same equations | idiom; neither statement is re-derived |
| `xr_inputSymbol_congr` ↔ `nf_inputSymbol_congr` (66% / 57%) | `inputSymbol_of_zero/_of_end`, `inputSymbolInner` | the same statement as `ExhaustiveReplay`'s private: F2 (i), kept, a promotion request |
| `ic_loopHost_run` reproduces `nf_tagged_ne_park` (59%) | `Cfg.mapState_state` and a case split on the state | idiom; the kind is F2 (iii) |
| `nf_entry` reproduces `canonStageBuffer_none` (80%) | `rw [FinTM.bufferTape_eq, if_pos (by omega)]` and `List.getElem?_eq_none (by omega)` | idiom of a published equation and a core lemma; a row candidate (F8) |
| `nf_V_tail` reproduces `nf_setup` (71%) | `Cfg.init_*`, `MultiTapeTM.runFrom_zero`, `absurd hu (Nat.not_lt_zero u)` | idiom, the same as NF-X1, in-file |
| `nf_sweep_run` reproduces `nf_tag` (54%); `nf_tag` and `nf_pack` reproduce `nf_retag` (50%) | the `streamStartCfg_*` and `Cfg.mapState_*` equations | idiom, in-file |
| `nf_leafStDecEq` ↔ `nf_leafStFintype` (80% / 77%); `nf_stDecEq` ↔ `nf_stFintype` (77% / 70%) | parallel instance bodies (the pinned named instances) | in-file parallel, accepted |
| `nf_vstep_ctl` ↔ `nf_vstep_state` (76% / 56%) | `nf_vstep_ctl` repeats `nf_vstep_state`'s case split (100 characters) for the summary component | in-file; optional factoring |
| `nf_leaf_record_in` reproduces `nf_leaf_record_wk` (61%); `nf_leaf_run_wk` reproduces `nf_leaf_run_in` (53%); `nf_bClear` reproduces `nf_aReturn` (57%) | step-lemma invocations, the induction skeleton and the phase-chaining skeleton | in-file; the two chains are the pinned transcriptions ("keep both") |

**Semantic search by kind.** These are candidates enumerated and inspected, not an exhaustive search
(out/22a–f):
- **By `exact?`.** 14 generic forms of the new privates (`probe/NFExact.lean`): stream lengths,
  `SignType` bounds, input-read congruence, retagging, the tagged-≠-verdict fact, a fold
  invariant, a buffer past its end, the first halting of a choice word, the record split, the
  stream's cells, and the cons-index shift.
  - **One hit: the cons-index shift,** `Nat.forall_lt_succ_left'` (F1).
  - The other 13 fail.
- **By `git grep` over the tree.**
  - **Input-read congruence:** `xr_` and `zr_` congruences.
  - **Retagging and tags:** `sl_rewrap`, `record_tag_ne`, `sl_tagged_ne_done`, `Contract/Seam`'s
    `mapState_const_inl`, the public `Cfg.mapState_mapState`.
  - **List lengths:** `length_flatMap_const` (public, CircuitComplexity).
  - **First halting:** FH-1 and `MultiTapeTM.exists_first_halt`.
  - **The entry:** `guessRunCfg_clean`, a generalization of `nf_entry` that needs a capture tape
    outside the selection, which a two-tape host cannot supply, so it does not apply.
- **Run composition.** It goes through the published `runFrom_add`, `runWith_append` and
  `runWith_of_halt`.
- **Tape-update facts.** They use Mathlib's `Function.update_*`; the block facts are this file's
  own representation.

**The worker's promotion requests.**
- `nf_inputSymbol_congr`: valid, a family of three (F2 (i)).
- `nf_retag`: valid; a generic form beside `phaseHostTM_run` would serve the 15 inline sites
  (F2 (ii)).
- `nf_tagged_ne_park`: valid, a family of three (F2 (iii)).
- `canonStageBuffer_none`: better filed as a row candidate. The landed text is an idiom of
  `FinTM.bufferTape_eq`, and the missing row is public `FinTM.bufferTape_of_length_le` beside
  `bufferTape_of_neg` (F8).

**One fifth.** No file crosses it.
- **`NDNormalForm`:** 105 declarations, of which F2's four are counted (3.8%). NF-X1 is an
  excluded idiom.
- **No other file changes.**
- **The rule's trigger.** "Copies to a file that already received copies" does not fire:
  `NDNormalForm` had no counted copy.

**For the ledger:**
- F2's entry, by kind, with the canonical statements above and the 12.2c resolution;
- F8's row candidates;
- F7's `un_setup` pair, an idiom.

**New copies at 90% or more: none.**

## 8. Docstrings and policy

- **Coverage.** All 65 new declarations have a docstring. All 17 proofs over 20 lines carry a
  literal `**Proof sketch.**`, and 9 shorter ones do too. The three other bodies over 20 lines
  (`nf_red`, `nf_leafEquiv`, `nf_leaf`) are definitions' tables, not proofs (out/18a).
- **Public-facing text** (out/19a).
  - **Clean:** no checkpoint number, MP label, gate or finding label, date, `audits/` path, "brief",
    "review", "pinned", "authorized", "transcription", "route probe" or "published" in the new
    text. Tapes are "tape `0`" and "tape `1`" throughout.
  - **Defects:** F4's three (E2–E4).
  - **"The ledger"** in `nf_ledger`'s docstring is plain English for the time budget.
- **Statements, not labels.** The one-line docstrings describe their declarations (for example
  `nf_signType_bound`: "A simulated move is at most one cell"). No bare label.
- **The module docstring.** "Main results" now reads without the status phrase, and stays
  accurate.
- **The target's docstring.** The **Implementation.** paragraph exists and is accurate, so a new
  one is not needed; E6 completes it (F10).
- **Hand-built machines.** `nf_leaf` names the rows it is not. `nf_P` and `nf_park` are one-state
  stationary machines; no published stationary row exists (grep, §3).

## 9. Lint

| Run | Base | Head | Landed |
|---|---|---|---|
| `campaign_style_lint.py TCSlib/Complexity/ClassNP` | 0 FAIL, 17 WARN over 21 files | 0 FAIL, 18 WARN; the new WARN is `NDNormalForm`'s size, 3,332 lines | 0 FAIL, 18 WARN; 3,309 lines |
| `style_lint.py NDNormalForm.lean` | 0 findings | 1: the file size | 1: the file size |

The size findings are expected by the brief, and the memory rule says file size is not a driver
(out/17a, out/17b, out/29h, out/29i).

## 10. Process and timeline

The timeline (out/02, out/25a, out/25c, the worker's logs):
- **Setup:** base commit 21:37:44Z; preflight 21:40:47; cache 21:41:53–21:43:14 (1,007 files).
- **Bootstrap** 21:44:00–22:05:03 (112 modules, 1,257.8 s, peak 3,019,012 KB), with the before
  screen beside it (21:44:12–22:04:59).
- **Commits:** checkpoint 3 at 22:17:50 (+1,050), checkpoint 4 at 22:36:17 (+662/−31), the worker
  restart and its re-check at 22:44:40, checkpoint 5 at 22:50:34 (+730), checkpoint 6 at 22:54:13,
  checkpoint 7 at 22:58:06, checkpoint 8 at 23:01:30.
- **The first sweep and after screen:** the sweep 23:01:44–23:23:39, the screen 23:01:52–23:24:27,
  both superseded.
- **The consolidation** at 23:30:42 (+114/−165). The final sweep ran 23:31:00–23:50:51 (1,187.1 s,
  18 sorries), the after screen 23:31:00–23:53:28, and the tail 23:51:10–23:51:40.

What is consistent and what is not:
- **The logs.** REPORT's numbers match its logs. No two logged modules overlap. The final sweep
  differs from the bootstrap only in the target's sorry line.
- **The pace.** It is implausibly fast for what was shipped, and the claimed checkpoint zips are
  missing (F11). The consolidation itself does what REPORT says: one section with one
  `attribute [-simp]` line instead of twelve, `nf_vrun_genuine` replaced by `nf_vrun_of_ok`, and
  `nf_leaf_toLast` added (out/25b).
- **What REPORT does state:** the restart after checkpoint 4, its re-check (13.33 GiB headroom, no
  OOM), and the superseded first sweep and after screen. All four are present.
- **`evidence/final/`** does not exist (F3).

## 11. Landing

**Recommended: a maintainer PR into `complexity/arora-barak-ch3-4`, with a fill gate (light).**

- **Branch.** Start from `lean/c1-nf-partial` at `348781a3`, the delivery's base, which is also
  `origin/lean/c1-nf-partial` (out/30a).
  - **The delivery.** `git am -3` the seven patches, which preserves the worker's authorship
    (`workflow.md` §4).
  - **Rewording.** Reword each subject, and drop "Checkpoint N of the linear normal form's
    continuation" and the `Claude-Session:` trailer from each body (F12):
    1. `15fd6cf7`: "Build the normal form's verifier layout and replay leaf; prove the input's
       replay";
    2. `b76f4fb7`: "Prove the normal form's work-tape replay, its exit invariant and the clear";
    3. `59737ab6`: "Prove the normal form verifier's characterization and its verdict on
       displays";
    4. `62890cc4`: "Prove the normal form's forward transfer and its time ledger";
    5. `d8b264ed`: "Prove the normal form's backward transfer";
    6. `ba46b709`: "Prove the linear-overhead coded normal form";
    7. `825ee3f5`: "Share the normal form's record-read and genuine-run lemmas".
  - **The landing commit.** Add one maintainer commit, for example "Cite Nat.forall_lt_succ_left'
    in the normal form; docstring fixes", with `out/29a-landing-edits.diff`.
  - **The base.** The PR's base is the campaign branch itself, not a stacked branch. Its diff
    against the campaign tip is `NDNormalForm` only: the campaign still has the pre-partial blob
    `5150734a`, and the PR carries the partial's commits.
- **The landing edits** (`scripts/landing_edits.py`, every edit asserted; out/29a). The landed
  file is `land/NDNormalForm.lean.txt`: git blob `5723152d424b4de35a10fd77446fa912083db412`,
  SHA-256 `3da2779c…3b43`, 3,309 lines.
  - **E1.** `nf_all_cons := Nat.forall_lt_succ_left'` (F1).
  - **E2.** `nf_vstep`'s docstring cites `nf_vrun_of_ok`.
  - **E3.** `nf_vrun_ctl`'s docstring: "state and output summary".
  - **E4.** `section Continuation` / `end Continuation` become an anonymous `section` / `end`.
  - **E5.** The 19 blank-line runs collapse to single blank lines.
  - **E6** (optional). The **Implementation.** paragraph gains three things: the block layout on
    the second work tape, rewritten at every record, with the last record's head move skipped; the
    returns and the erasure between sweeps; and
    `C = 6W + k(2W + 12) + 21 + 15k` with `W = 2k + 4`.
- **The edits are tested** against `oleans-leqc3`:
  - **Elaboration.** The module elaborates with 0 errors and no message (out/29b).
  - **Axioms.** 66 printed, all within the standard three, the target unchanged. `nf_all_cons` drops
    to `[propext, Quot.sound]`. Still "OUTSIDE_STD []" and "DIRECT_SORRY []" (out/29c, out/29e).
  - **The seal.** The 257-definition seal elaborates the body with 0 errors (out/29d).
  - **The freeze.** No statement changed. The body or docstring changes only in the target
    (docstring), `nf_all_cons`, `nf_vrun_ctl` and `nf_vstep`. The 39 privates are unchanged
    against the base (out/29f).
  - **The code.** Comment-stripped, it is the head's except the section line and `nf_all_cons`'s
    proof (out/29g).
  - **Lint and width.** Lint 0 FAIL / 18 WARN; widest line 100.
  - **The downstream.** Compiled into the clone, the 4 modules all exit 0 with no warning
    (out/29j).
  - **The screen.** E1 shortens `nf_all_cons`, which is in no pair, so no pair can be added.
- **The replay.** It is the owned file's downstream closure in the merged tree, in order, never
  with the root (out/23a):
  1. `TCSlib/Complexity/ClassNP/NDNormalForm`;
  2. `TCSlib/Complexity/ClassNP`;
  3. `TCSlib/Complexity/Diagonalization/NTimeHierarchy`;
  4. `TCSlib/Complexity/Diagonalization`.

  **Where it chains from.** `oleans-lsm5`, the snapshot of #181's merge (`d1ddea26`, Lean
  `98912ab2`'s), or `oleans-larm2` if #182 merges first. If E-D merges first, use the snapshot its
  merged-tree replay leaves; never compose snapshots.

  **Expected:**
  - 0 errors, and no sorry warning in the four modules;
  - `NTimeHierarchy`'s headline is admission-free only once E-D's `exists_diagonalizer` is also
    landed (out/24e).
- **The screen at the PR head.** Re-take the v3 screen on the 21-file population at the merged
  tree: `CodeSimulator`, which is in the population, changed on the campaign after the base (F14).
- **Clear to merge** when five things hold:
  - the PR is based on the campaign branch;
  - decision 1 is taken;
  - decisions 2–4 are taken or waived;
  - the replay above passes;
  - the gate records 0 blockers and 0 open majors (F1 closed by E1, F2 by the user's
    acknowledgment).

**What the gate's pack should ask.**
- **Attach:** `TEMPLATE.md`, `policy.md`, `workflow.md`, the brief and addendum v2.6, the
  delivery's REPORT and evidence, this review with `out/` and `probe/`, the landing diff, and the
  ledger entry for F2.
- **Ask:**
  - the correctness and non-vacuity of the 65 privates' statements, and the fitness of `hV` and
    the transfers (§3–4);
  - rule 10 (the seal and its 293 controls) and rule 11 (F5);
  - the pair dispositions and the by-kind debt scope (F2, F7);
  - the public text with E2–E6;
  - the replay;
  - the findings as a downloadable `nf-cont1-fill-findings.md`.

## Decisions for the user

1. **The debt, F2, by kind.** Acknowledge as one ledger family, scoped by kind across TCSlib, every
   re-derivation of:
   - (i) the input read depending on the input head only;
   - (ii) a redirected live configuration being the next phase's tagged start;
   - (iii) a configuration tagged by one phase never being a verdict of another;
   - (vi) the length of a list of equal-length chunks.

   Resolution in the 12.2c window, as the maintainer's dedup: publish the three in
   `Configuration`/`Seam`, move `length_flatMap_const` to a basic list home, and re-point the
   copies. **Recommended.** (i) and (ii) were authorized by the brief as transcriptions with
   promotion requests. All four are small (4 of 105 declarations).
2. **E6.** Land the extended **Implementation.** paragraph, with the block layout and the explicit
   constant, or keep the partial's text. **Recommended: land it.** The docstring promises "the
   explicit constant", and the constant is stated nowhere public.
3. **H's overlap.** H's population contains `NDNormalForm`. Re-take H's screen base at the landing
   tree, which gains the 65 privates and the pair `un_setup` ← `nf_retag` (67%, an idiom), per the
   ruling "NF's final landing re-takes H's overlap".
4. **The checkpoint zips** (F11). Ask whether `fill-c1-nf-cont1-cp3.zip` to `-cp8.zip` exist in the
   worker session's `deliveries/` folder, as REPORT says. Or accept their absence: the final zip
   carries everything, and the content is independently verified.

## Files

- `REVIEW.md` (this file) and `NOT-COPIED.md`.
- `out/`: the cited outputs; `out/00-runs.txt` lists every Lean run.
- `probe/`: my probes and generated copies.
- `scripts/`: my scripts, among them `landing_edits.py`, `mkseal.py`, `mk_audit.py`, `tacargs.py`,
  `transcmp.py`, `tiles.py` (copied from the partial's review) and `screen-nf-pairs.py`.
- `land/NDNormalForm.lean.txt`: the tested landed file.
- The worktrees `wt-head` and `wt-base` and the clone `oleans-clone` are removed at the end.
