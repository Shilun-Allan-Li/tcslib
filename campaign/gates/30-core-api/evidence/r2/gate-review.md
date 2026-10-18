# Review of the external gate audit of PR #116 (the core specification API)

The auditor returned FAIL, 0/2/3/0. **All five findings are true at `d5255232`, and I accept
all five at the auditor's severities.** I tested a repair. It adds five theorems and edits
docstrings only; no statement or definition changes, and nothing in Hydroxyi's files.
- **Finding 1** needs no exception. A generic machine-model lemma lets U2-S restart `cleanTM`
  without reading or unfolding his `cleanTM`. His own `cleanTM_run` proof uses the same device
  (Clean.lean:325–326).
- **Finding 2** is one `Iff.rfl` beside the definition.
- **Finding 3** is confirmed. Both consumers that changed after `d5255232` (#114's
  `StepBlockForward`, #115's `ZoneRebalance`) went into the bundle in their pre-merge versions.
- **Findings 4 and 5** are text and record fixes. Finite.lean's "vendored files unmodified" note
  also goes stale with this PR.

| # | Auditor | Verdict | One line |
|---|---|---|---|
| 1 | major | **ACCEPT (major)**, fix R1 | No public statement reads `cleanTM`'s initial state, and CleanSweep is Hydroxyi's. Fix: generic `runFrom_with_q₀`/`initCfg_with_q₀` in campaign-owned `Finite.lean`, and the U2-S brief builds `{ cleanTM … with q₀ := .init q₀ }`. |
| 2 | major | **ACCEPT (major)**, fix R2 | `FinTM.ComputesFunInTime` (Finite.lean:256) has no characterization; `prefixCanon_complete` needs one built. Fix: `computesFunInTime_iff` beside the definition. |
| 3 | minor | **ACCEPT (minor)**, fix R3 (records) | The bundle took every `TCSlib/` file from `d5255232`. `StepBlockForward` and `ZoneRebalance` differ from the tip. |
| 4 | minor | **ACCEPT (minor)**, fix R4 (records) | `serializeK_eq` is missing from `axioms.log`. Measured: `[propext, Quot.sound]`. |
| 5 | minor | **ACCEPT (minor)**, fix R5 | The two vendoring headers say "mathematical content unchanged". Replacement inventories are in the patch. |

## Inputs checked

- **Audit text:** `audits/core-api-findings.md` (untracked), read as data.
- **PR head:** `origin/lean/core-api` = `d5255232d8ff15dcb21cf8caeaf961f69453bf13`, on `62fa2330` (Lean `c2897d7f`).
- **Campaign tip at review:** `4308b1135934d61efeb923caf05784874ad58d36`, which includes #113, #114, #115 and the #112 gate records.
- **Bundle:** `infra_local/gate-dispatches/30-core-api-gate/core-api-bundle.md`.
  - SHA-256 `fc8219a6…78e5`, as commissioned.
  - 63 sections; the auditor's count is right.
  - Rebuilding with `vtools/mkbundle-mixed.py … --verify` against `BUNDLE-FILES.txt` gives `verified 63 segments`. The rebuild runs `git show` only.
- **Evidence:** extracted with `git archive e2301305` into `review/core-api-gate/ev/`.
- **Worktree:** `review/core-api-gate/wt-pr`, detached at `d5255232` and reset after testing.
- **Snapshot:** `oleans-lf3p`, which is exactly the PR's base Lean (`c2897d7f`). Every repaired file elaborated against it with no complaint.

## Finding 1 — `cleanTM`'s initial state (ACCEPT, major)

**Ownership.** `SpaceComplexity/Machines/CleanSweep.lean` is Hydroxyi's: its header says
`Authors: Hydroxyi`, and its only commit is his (`f70c57c2`, 2026-10-06). `Machines/Clean.lean`
is his too. So the auditor's fix, "publish `(cleanTM M q).q₀ = .init q` beside `cleanTM`", would
edit his file and is not available.

**True at `d5255232`.**
- `cleanTM M q₀` (CleanSweep.lean:80) is a `where` structure with `q₀ := .init q₀`.
- No public statement in Clean or CleanSweep mentions `(cleanTM …).q₀` or `initCfg`. The only
  occurrences are inside `cleanTM_run`'s proof.
- `cleanTM_run` (Clean.lean:314) starts from the explicit `Cfg.init (.init q) V`, for any `q₁`.
- The U2-S draft's step 1 wraps `cleanTM E.canonizer.tm` as a `FinTM`, so it starts at
  `initCfg = Cfg.init (cleanTM …).q₀ α` (`initCfg_eq`). Connecting that to `cleanTM_run` needs
  the unpublished field. The pitfall line 351, "initial configuration is `Cfg.init (.init q₀) α`",
  is exactly that unpublished fact.
- **A bridge lemma `(cleanTM M q).q₀ = .init q` cannot be proved from his public API without
  unfolding `cleanTM`.**
- The same gap holds for any composite the worker builds as the target's `R` (phase host, seams,
  `embedSilentRetTM`), since the target is stated from `R.initCfg`. No `q₀` equation exists for
  those hosts either (checked `Build/Seam`, `Build/Embed`, `Contract/Seam`). This is the
  auditor's "also inventory" point.

**Fix R1: one generic lemma pair, no exception needed.** Restart the machine instead of reading its start state.
- `{ tm with q₀ := q }` has `tm`'s transition table.
- Its runs are `tm`'s, and its initial configuration is `Cfg.init q x`.
- Both facts hold by `rfl`, mention no definition of Hydroxyi's, and work for any machine: `cleanTM`, a phase host, a seam composite.
- The lemmas go in **`TuringMachine/Finite.lean`** (campaign-owned, Seyoon), in its "Raw-layer" `MultiTapeTM` section. That section exists to keep run lemmas out of the vendored files; the lemmas follow `exists_first_halt`.

```lean
/-- **A new initial state changes no run** (the core specification API, user 2026-10-16; its
gate, finding 1): the machine `{ tm with q₀ := q }` has `tm`'s transition table, so from every
configuration it takes `tm`'s run, `({ tm with q₀ := q }).runFrom cfg t = tm.runFrom cfg t`.
A consumer restarts a machine whose initial state it does not read (for example
`Complexity.LogProg.cleanTM`) at a state of its choice, without unfolding the machine. -/
theorem runFrom_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).runFrom cfg t = tm.runFrom cfg t :=
  rfl

/-- **The initial configuration at a new initial state** (the core specification API; its
gate, finding 1): `({ tm with q₀ := q }).initCfg x = Cfg.init q x`. -/
theorem initCfg_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State) (x : List Symbol) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).initCfg x = Cfg.init q x :=
  rfl
```

**Tested.**
- In the repaired `Finite.lean`: 0 errors. Axioms: `runFrom_with_q₀` `[propext, Quot.sound]`;
  `initCfg_with_q₀` `[propext]`.
- The consumer probe `ReviewScratch/CleanRestartProbe.lean` (`out/…CleanRestartProbe.lean.out`)
  imports only `Machines.Clean`, with the two lemmas restated by `rfl` as stand-ins. It proves
  that the restarted cleaned machine halts with `M`'s output from its own `initCfg`, by
  `cleanTM_run` alone: 0 errors, 0 warnings, and `cleanTM` is never unfolded.

**Brief text for U2-S:**
- Step 1: "`F' := ⟨_, _, { cleanTM E.canonizer.tm E.canonizer.tm.q₀ with q₀ := .init E.canonizer.tm.q₀ }, _, _⟩`".
- Pitfall 351: "its initial configuration is `Cfg.init (.init q₀) α` by `MultiTapeTM.initCfg_with_q₀`, and its runs are `cleanTM`'s by `MultiTapeTM.runFrom_with_q₀`".
- Add both names to U2-S's probe.
- If the target's `R` is a host composite, the same device gives `R.initCfg` without the host's `q₀` field.

**If the user prefers literally `F' := cleanTM …`:** the only remaining fact is
`(cleanTM M q).q₀ = .init q`, provable only by `rfl` through his definition. That needs an
exception, either in his file or as a campaign-file `rfl` bridge. Recommendation: not needed.

## Finding 2 — `FinTM.ComputesFunInTime` (ACCEPT, major)

**True at `d5255232`.**
- `def ComputesFunInTime (M) (f) (T) : Prop := ∀ input, M.ComputesInTime input (f input) (T input.length)` (Finite.lean:256).
- Its public lemmas are `ComputesFunInTime.computes` (elimination to `Computes`) and `computesInTime_iff` (for the inner `ComputesInTime`).
- There is no characterization or general introduction. My scan of every public theorem concluding in `ComputesFunInTime` found only machine-specific constructors: `computesFunInTime_comp`, `_const`, `_id`, the `Primitives`/`Catalog` rows, and others.
- U2-S must construct `F'.ComputesFunInTime …` (draft step 1), the hypothesis of `prefixCanon_complete`. The tip lint's check 8 also lists `Finite.lean: Computes, ComputesFunInTime, ComputesFunInTimeVia`.

**Fix R2.** Beside the definition:

```lean
/-- **Computing a function in time, input by input** (the core specification API, user
2026-10-16; its gate, finding 2): `M` computes `f` in time `T` exactly when, on every input
`x`, it halts within `T |x|` steps with `f x` on its output tape,
`M.ComputesFunInTime f T ↔ ∀ x, M.ComputesInTime x (f x) (T |x|)`. With
`Turing.FinTM.computesInTime_iff` this reads a function computation off the runs. -/
theorem computesFunInTime_iff (M : FinTM Symbol) (f : List Symbol → List Symbol)
    (T : ℕ → ℕ) :
    M.ComputesFunInTime f T ↔ ∀ input, M.ComputesInTime input (f input) (T input.length) :=
  Iff.rfl
```

**Optional (`repair-optional.patch`).** `computesFunInTimeVia_iff` and `computes_iff`, the same
shape, so check 8 reports nothing for `Finite.lean`. No drafted route needs them.

**Tested.** 0 errors; all three axioms `[propext, Classical.choice, Quot.sound]`. Check 8 for
`Finite.lean` goes from 3 names to none, and the file adds none.

## Finding 3 — the consumer snapshots (ACCEPT, minor)

Confirmed. `mkbundle-mixed.py` takes every `TCSlib/` path from the Lean revision (`d5255232`), so
the consumer files are pre-merge. Blob comparison (bundled = `d5255232`, against tip `4308b113`):

| Bundled consumer | Bundled | Tip | Status |
|---|---|---|---|
| `Build/StepBlockForward.lean` | `c2437da1` (132 lines; the target `sorry`) | `60e29249` (555 lines; #114, proved; cites `MultiTapeTM.visitedByTapeHead_add_subset` in its proof, line 525) | **differs** |
| `Build/ZoneRebalance.lean` | `7ba68d5c` (331 lines, 0 privates) | `9deb85fb` (571 lines; #115's 18 `zr_` helpers) | **differs** |
| `UniversalK.lean`, `Build/InputDevice.lean`, `UniversalStartup.lean`, `Build/WindowRun.lean`, `SpaceComplexity/Machines/Clean.lean` | — | — | identical |

Of the PR's own ten files, `CodeSimulator.lean` is bundled without #113's changes; the tip
changed it by 415 lines since the PR's base. The other nine are unchanged on the tip since the base.

A trial merge of `d5255232` with the tip (`git merge-tree --write-tree`, in a scratch repo with
alternates) is clean. Tree `3af90f78`; the merged `CodeSimulator` has both `serializeK_eq` and
cont5's decider.

**Fix R3 (records).**
- Merge the tip into `lean/core-api`, as planned.
- Rebuild the bundle's Lean sections from the merged head, so the consumers are #114's and #115's landed versions.
- Or relabel the current files as baseline snapshots.
- The ~320-module replay of the merged head is the check that `StepBlockForward`'s proof resolves the moved lemma. The name is unchanged: `Turing.MultiTapeTM.visitedByTapeHead_add_subset`, now `Deterministic.lean:312`.

## Finding 4 — `serializeK_eq` absent from `axioms.log` (ACCEPT, minor)

- True: `axioms.log` has 46 prints and none for `serializeK_eq` (CodeSimulator.lean:111, `rfl`).
- Measured on `d5255232`'s `CodeSimulator.lean` plus a print, against `oleans-lf3p` (`out/ReviewScratch_CodeSimAx.lean.out`): `'Turing.serializeK_eq' depends on axioms: [propext, Quot.sound]`.

**Fix R4 (records).** Append that line to `audits/evidence/core-api/logs/axioms.log`. The
attestation then holds as written. Add R1's and R2's five prints with the repair:
- `runFrom_with_q₀` `[propext, Quot.sound]`;
- `initCfg_with_q₀` `[propext]`;
- the three iffs `[propext, Classical.choice, Quot.sound]`.

## Finding 5 — the vendoring headers (ACCEPT, minor)

True, under `policy.md` §2, "Vendored code": a summary of local modifications.

**Configuration.lean**, lines 14–15, current text:

```
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
```

The PR adds `Cfg.init_*` (generated), `Cfg.inputSymbol_of_zero`/`_of_end` and
`Cfg.workTapeSymbols_eq`. The September port also re-proved five lemmas (`83c4fd33`), and that
was never listed either.

**Deterministic.lean**, lines 21–25, ends "The remaining mathematical content is unchanged." The
PR adds `initCfg_eq` and `mem_visitedByTapeHead_iff` and moves in the two split lemmas. The
campaign's `timed_input_bound` (D6, `19bd38f4`, 2026-10-05) was already unlisted.

**Fix R5** (header text only; `repair-required.patch`).

Configuration:
```
* added the repository-standard `set_option` header;
* re-proved `moveInputPos_leftBoundary`, `moveInputPos_rightBoundary`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_pos_of_ne_right` and `inputSymbolInner` for our
  mathlib pin (`dite_eq_left`/`dite_eq_right` are absent there), statements unchanged
  (2026-09-16);
* added lemmas that are not upstream, the specification API (user, 2026-10-16): the fields of
  `Cfg.init` (`Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`, generated
  by `simps` without the `simp` attribute), `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`
  and `Cfg.workTapeSymbols_eq`.
The upstream definitions and theorems are otherwise unchanged.
```

Deterministic:
```
  `NSPACE`); comments only, no code change (2026-10-08);
* added `timed_input_bound`, promoted from the campaign (D6, 2026-10-05);
* added lemmas that are not upstream, the specification API (user, 2026-10-16):
  `initCfg_eq` and `mem_visitedByTapeHead_iff`, and the split lemmas
  `visitedByTapeHead_add_subset`, `visitedByTapeHead_step_subset`, moved here from
  `Build/StepBlock` with their statements and proofs (design note O9).
The upstream definitions and theorems are otherwise unchanged.
```

**Follow-on, same fix.** Finite.lean says its raw-layer lemmas are kept apart "to keep the
vendored files unmodified" (line 60) and "byte-comparable with upstream" (line 90). Both become
false with this PR. The patch rewords both to "close to upstream", noting that the API's
equations sit beside their definitions.

**Caveat.** The inventories follow each file's git history, taking the initial import
`d3b0bb92` as upstream plus the listed changes. A diff against cslib `a374775` would confirm.

## Repair list

Patches against `d5255232`:
- `review/core-api-gate/repair-required.patch` (SHA-256 `c5c21d18da5fa1b9e2e0179589f0e5a6b1dc34b3a1c35db1c7edfce3df581d17`): R1, R2, R5.
- `repair-optional.patch` (`1bf473227ecae7e73501dbdf661030f650066497bf1376561eeaa1c3ed1ff753`): the two optional iffs, applied on top.

Both `git apply` cleanly. The edits come from `review/scripts/core_api_repair.py`, with every replacement asserted; the staged copies are in `review/core-api-gate/edit/`.

| Fix | File | Change |
|---|---|---|
| R1 | `TuringMachine/Finite.lean` (campaign-owned) | `MultiTapeTM.runFrom_with_q₀`, `MultiTapeTM.initCfg_with_q₀` after `exists_first_halt`; Main-results bullet |
| R2 | `TuringMachine/Finite.lean` | `FinTM.computesFunInTime_iff` beside `ComputesFunInTime`; Main-results bullet |
| R2 (optional) | `TuringMachine/Finite.lean` | `FinTM.computesFunInTimeVia_iff`, `FinTM.computes_iff` beside their definitions |
| R5 | `Configuration.lean`, `Deterministic.lean`, `Finite.lean` | the vendoring headers and Finite's two convention sentences (text only) |
| R3, R4 | records (`audits/evidence/core-api/`, the bundle) | rebuild the consumer sections after the merge; append the axiom prints |
| U2-S brief | `u2s-fill-startup.DRAFT.md` | step 1 and pitfall 351 as above; probe gains the five names |

**Tests** (against `oleans-lf3p`; `out/`):

| Check | Result |
|---|---|
| Elaboration of `Finite` | repaired 0 errors, 2 warnings; base 2 warnings; `warndiff`: 0 new |
| Elaboration of `Configuration` | 3 warnings, as the PR head (evidence: 3) |
| Elaboration of `Deterministic` | 0 warnings |
| Freeze (`privstmt`/`declfreeze`, orig → all) | `STATEMENT CHANGED: []` in all three files; no body change; public added only in `Finite` (the 5 theorems) |
| Lint (tip script, check 8, `TuringMachine`) | 71 → 70 WARN, 0 FAIL: Finite's check-8 line disappears, nothing new. PR's own lint script: 0 FAIL, 23 WARN, unchanged |
| Copy-text screen (`Finite`, `Deterministic`, `Configuration`) | 50 declarations and 10 pairs before and after, 0 new; the five new bodies are under the screen's 60-character floor |

**Do the repairs change any statement or definition?** No. They add five theorems (two of them
optional) and edit text: three module headers, two Finite comment lines and Main-results bullets.

**After applying:**
- Merge the tip, as the PR needs anyway; the merge is clean.
- Rebuild the bundle's Lean sections and append the axiom prints.
- Update the U2-S draft.
- Run the planned ~320-module replay of the merged head.
- A round-2 check covers findings 1 and 2.
