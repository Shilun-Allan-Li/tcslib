# Review of the external gate audit of PR #112 (the specification API)

**Summary.**
- The auditor's result is FAIL, with 0 blockers, 2 majors, 2 minors and 1 note.
- All five findings are true at `28824c36`.
- My severities: 1 major (finding 1), 3 minors (findings 2, 3, 4), 1 note (finding 5, now resolved).
- Finding 2 is downgraded. A published route already reads the mapped sweeps' cells at every admissible start; the probe for it elaborates.
- The repair adds declarations only: 3 hand-written theorems and 15 generated equations (40 with the optional part). It edits 3 docstrings and the module-docstring lists. No statement or definition body changes.
- The repair is tested:
  - all six repaired files elaborate with 0 errors and the base warning counts;
  - the copy-text screen gives 714 declarations, 350 pairs, 0 new;
  - lint is 0 FAIL, with the WARN sets unchanged.

  It is in two patches: `repair-required.patch` and `repair-optional.patch`.
- After the repair, a new 85-module replay is needed, and a short round-2 check of the repair diff.

| # | Auditor | Verdict | One line |
|---|---|---|---|
| 1 | major | **ACCEPT (major)**, fix R1 | `ReturnContract.release`, `RoundContract.release` and `Contract.ofSegment` have no field equations. G4's binding iteration hosts cannot be applied without unfolding; there is no other route. |
| 2 | major | **ACCEPT-DOWNGRADE → minor**, fix R2 | `sweepMapWrite` has no equation. G4 can still read the endpoint cells at admissible starts through the contract's `run` field and the public framed theorem, so this is an ergonomic gap, not a block. |
| 3 | minor | **ACCEPT (minor)**, fix R3 | WindowClock's appendix still grants the superseded 2026-10-15 unfolding permission. |
| 4 | minor | **ACCEPT (minor)**, fix R4 | The two docstrings are bare labels under `policy.md` §2, "Statement prose". |
| 5 | note | **ACCEPT (note), resolved** | `replay-lapi.log` was run at exactly `28824c36`: 89/89 modules, 0 failed. Repairs need a new replay. |

## Inputs checked

- The audit text `audits/spec-api-findings.md` (untracked) was read as data.
- PR head `origin/lean/spec-api` = `28824c36f0501a6bfb01231531bebee4e88ff3df`.
  - Campaign tip `origin/complexity/arora-barak-ch3-4` = `5eff414667df629ffe88e633a2053f93deca2904` (the #113 merge).
  - `5eff4146` is not a git ancestor of `28824c36`; the merge commit is newer. Its Lean content is contained, though: `git diff 5eff4146 28824c36 -- '*.lean'` lists exactly the six API files, +107/−2.
  - The cont5 commits `15eae7a7`, `a8856abe` and `e2089d70` are in the PR head.
- The bundle `infra_local/gate-dispatches/29-spec-api-gate/spec-api-bundle.md` has SHA-256 `91f96cf5…19dca1`, as commissioned.
- Review worktree: `review/spec-api-gate/wt-pr` (detached at `28824c36`). Snapshot: `oleans-lapi`.
- The evidence and pack were extracted with `git archive` from the campaign branch into `review/spec-api-gate/ev/`.

## Finding 1 — the iteration adapters' fields (ACCEPT, major)

**True at `28824c36`.** All three declarations are structure-valued defs written with `where`.
The data fields are terms; the proof fields are tactic blocks. This is the same shape as
`Contract.seq` and `Contract.trans`, which #112 already handles. None has field equations, and
the positivity lemmas (`ReturnContract.release_positive`, `RoundContract.release_positive`)
state only `Positive`.

| Declaration | File:line | Type | Data fields | Proof fields |
|---|---|---|---|---|
| `Turing.ReturnContract.release` | `Build/Contract/Seam.lean:554` | `Contract (seamReleaseTM M anchor) (Sum.inl ()) {some (Sum.inr anchor)} ι x` | `pre i d := C.pre i (d.mapState fun _ => anchor)`; `time`, `lo`, `hi` likewise; `post i d := (C.post i (d.mapState …)).mapState Sum.inr` | `run`, `exit_mem`, `cut`, `env` |
| `Turing.RoundContract.release` | `Build/Contract/Seam.lean:606` | `Contract (seamReleaseTM M anchor) (Sum.inl ()) (Option.map Sum.inr '' insert (some anchor) escape) ι x` | as above, over `R` | `run`, `exit_mem`, `cut`, `env` |
| `Turing.Contract.ofSegment` | `Build/Contract/Basic.lean:584` | `Contract M entry exits ι x` | `pre := pre`, `time := time`, `post := post`, `lo := lo`, `hi := hi` | `run`, `exit_mem`, `cut`, `env` (from `seg`) |

**G4 reads them.**
- G4's brief (`briefs/s13d-fill-g4.md:156–158`, binding hosts) prescribes `Turing.Round.iterate`, or `RoundContract` "released into a contract by `Turing.RoundContract.release`".
- `Round.iterate`'s docstring (`Contract/Basic.lean:725–728`) routes the iterated segment to a contract through `Turing.Contract.ofSegment`.
- G4's delivery review lists "the release adapters" in the ruling's scope (`audits/evidence/s13d-g4-fill/delivery-review.md:195`).
- Without `pre` and `time` equations, a consumer cannot discharge `R.release.pre i d` or compute the composite time without unfolding the def.
- Unlike finding 2, I found no alternative published route.

**Severity.** Major is right in function. The pack makes E1 coverage the gate's main question (Q4), and the answer for G4's binding iteration hosts is "not covered". TEMPLATE's wording ("materially misleading") fits loosely: the PR is presented as the ruling's discharge of G4's E1.

**Fix R1, tested.** In `Build/Contract/Seam.lean`, after `RoundContract.release` (before `/-! ## Joint trajectories …` at line 646):

```lean
/-! The specification API (user, 2026-10-16; its gate, finding 1): the two release adapters'
data fields as equations, generated by `simps` without the `simp` attribute, so that consumers
never unfold the definitions. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  ReturnContract.release RoundContract.release
```

In `Build/Contract/Basic.lean`, inside `namespace Contract`, right after `ofSegment` (its body ends at line 598):

```lean
/-! The specification API (user, 2026-10-16; its gate, finding 1): the segment bridge's data
fields as equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] ofSegment
```

Both modules' "Main results" lists gain a bullet for the new equations (in the patch).

The result is 15 new equations:
- `Turing.ReturnContract.release_{pre,time,post,lo,hi}`;
- `Turing.RoundContract.release_{pre,time,post,lo,hi}`;
- `Turing.Contract.ofSegment_{pre,time,post,lo,hi}`.

`simps` works on all three exactly as in #112. The attribute must sit in the defining module, as NOTES.md records.

Printed forms, all faithful:
- `C.release.pre i d = C.pre i (Cfg.mapState (fun x => anchor) d)`;
- `R.release.post i d = Cfg.mapState Sum.inr (R.post i (Cfg.mapState (fun x => anchor) d))`;
- `(Contract.ofSegment pre time post lo hi seg exit_mem).pre a a_1 = pre a a_1`.

Evidence:
- `out/ApiSeam.out` and `out/ApiBasic.out`: in-module probes, 0 errors, 0 warnings, all names printed;
- the full repaired files: `out/rep/ReviewScratch_Rep{Seam,Basic}.lean.out`, 0 errors, 0 warnings.

For the auditor's "consumer probes": add the 15 names to `probes/Contract_{Seam,Basic}.checks.lean.txt`, as for the 85.

## Finding 2 — `sweepMapWrite` (ACCEPT-DOWNGRADE to minor)

**True at `28824c36`.** The definition is at `Build/Contract/Catalog.lean:234`:

```lean
def sweepMapWrite {S : Type} {x : List Γ} {Δ : Type} (extract : Γ → Δ) (merge : Option Γ → Δ → Γ)
    (w : List Γ) (d : Cfg k Γ S x) (j : Fin k) (q : ℤ) : Option Γ :=
  (FinTM.bufferTape w (q - d.workTapePos j)).map fun γ => merge (d.workTapes j q) (extract γ)
```

- It is a plain `Option`-valued def, not a structure, so `simps` does not apply; a hand-written `rfl` lemma is needed.
- `copyMapTM_contract_post` and `transferMapTM_contract_post` end in `sweepPost .done dst (sweepMapWrite extract merge) w d`.
- `sweepPost_workTapes` exposes `v w d j q`, which here is `sweepMapWrite …`. Nothing publishes its value.

**Does G4 read it? Yes, and only G4.**
- G4's route builds its column moves and constant halves with `copyMapTM_contract`/`transferMapTM_contract`:
  - `merge := zoneSlotSet t` and `extract := zoneSlotOf t`;
  - the constant merges `inr (fun _ => some none)` / `inr (fun _ => none)`.
  - These are `briefs/s13d-fill-g4.md:163–164`, 197–201 and 245–247.
- The F3-cont1 and U2-S drafts use `copyMapTM_run_ofCfg`, the framed theorem in `Build/Catalog.lean:1230`. It states the destination cells inline, so it does not involve `sweepMapWrite`.
- The cont6 and F5 drafts do not use mapped copies.

**Why I downgrade to minor.**
- At every admissible start, the only place a composition reads an endpoint, the published API already recovers the cells. Rewrite `post w d` backwards with the contract's own `run` field, then use `copyMapTM_contract_time` and `copyMapTM_contract_pre`, and apply the public `copyMapTM_run_ofCfg` (`transferMapTM_run_ofCfg` for the transfer). No definition is unfolded.
- My probe `ReviewScratch/ApiRunRoute.lean` (imports only `Build.Contract.Catalog`; `out/ApiRunRoute.out`) proves `(copyMapTM_contract …).post w d = { d with state := …, workTapes := fun j q => if j = dst ∧ … then (FinTM.bufferTape w (q - pos)).map … else d.workTapes j q }` from `hd`/`hp` this way: exit 0, 0 errors, 0 warnings.
- So nothing is blocked or misleading; the endpoint interface is merely roundabout. That is a completeness defect, which is minor.
- The fix is still worth landing, because it is one line.

**Fix R2, tested.** In `Build/Contract/Catalog.lean`, right after `sweepMapWrite`:

```lean
/-- **The values a mapped sweep writes** (the specification API, user 2026-10-16; its gate,
finding 2): at cell `q` of tape `j`, whose head is at `pos`, the merge of the cell's original
content with the extract of the source word's symbol at offset `q - pos`, and blank where the
buffered word has no symbol. -/
theorem sweepMapWrite_apply {S : Type} {x : List Γ} {Δ : Type} (extract : Γ → Δ)
    (merge : Option Γ → Δ → Γ) (w : List Γ) (d : Cfg k Γ S x) (j : Fin k) (q : ℤ) :
    sweepMapWrite extract merge w d j q =
      (FinTM.bufferTape w (q - d.workTapePos j)).map
        fun γ => merge (d.workTapes j q) (extract γ) :=
  rfl
```

Two recommended destination-cell lemmas go at the end of the file, after the `simps!` lines whose `_post` equations they use. Their full text with docstrings and proof sketches is in the patch:
- `copyMapTM_contract_post_workTapes` — the cell is `if j = dst ∧ pos ≤ q < pos + |w| then (bufferTape w (q - pos)).map (merge (d.workTapes j q) ∘ extract) else d.workTapes j q`. Proof: `rw [copyMapTM_contract_post, sweepPost_workTapes, sweepMapWrite_apply]`.
- `transferMapTM_contract_post_workTapes` — the `src` residue `(bufferTape w (q - pos)).bind rest` first, then the `dst` merge, else unchanged. Proof: `simp only [transferMapTM_contract_post, sweepPost_workTapes, sweepPost_workTapePos, sweepMapWrite_apply]`.

Results (`out/rep/ReviewScratch_RepCatalog.lean.out`):
- 0 errors, 0 warnings;
- axioms: `sweepMapWrite_apply` none; the two cell lemmas `[propext, Classical.choice, Quot.sound]`.

Two consumer checks pass using only published equations (`ReviewScratch/ApiCatalog.lean`):
- a constant merge writes `some c` on the whole destination interval (via `FinTM.bufferTape_nat` and `List.getElem?_eq_getElem`);
- cells outside the interval are kept.

The `zoneSlotOf`/`zoneSlotSet` instances are zone-layer definitions, which the coordinator scoped out (#116). The cell lemmas above are what those instances will rewrite with.

## Finding 3 — WindowClock's appendix (ACCEPT, minor)

**True at `28824c36`.** `WindowClock.lean` is unchanged since #111: blob `47962f5c` at `2e4f414c`, `5eff4146` and `28824c36`.

Current text, lines 272–275:

```
The numerical helpers take the record-length formula and the position-width bound as
explicit hypotheses. The specification-level definitions `RecordAt`, `recordLength` and
`posWidth` may be unfolded in this module (user ruling on the delivery's escalation E1,
2026-10-15), which discharges them and gives the field cells from a `RecordAt` hypothesis.
```

**Fix R3.** Replace lines 273–275, keeping the line count, so the F3-cont1 draft's line references (region (c) 269–278, statement 280–309) stay valid:

```
explicit hypotheses. The specification API discharges them (`Turing.recordLength_eq`,
`Turing.record_pos_lt`) and reads a `RecordAt` hypothesis's cells (`Turing.recordAt_iff`): the
user's ruling on E1 (2026-10-16), superseding the 2026-10-15 permission to unfold.
```

- The edit is docstring-only.
- WindowClock is already in #112's 89-module replay closure (`down-lapi.txt` line 74), so including the file in #112 adds no replay work.
- Repaired WindowClock elaborates with 0 errors and its 1 sorry warning (base: 1).
- The F3-cont1 draft already states the 2026-10-16 ruling (lines 71–74, 260–269) and owns this paragraph (region (c)). Deferring the edit to cont1 is the alternative, but the library text would contradict the ruling until then.

## Finding 4 — two bare-label docstrings (ACCEPT, minor)

**True at `28824c36`.** `policy.md` §2, "Statement prose", says: "A bare label … is not a statement."

Current text:
- `Build/CfgRecord.lean:367–368`: "**Reading a record** (the specification API, user 2026-10-16): `Turing.RecordAt` as an equivalence, so that consumers read the cells of a record without unfolding the definition."
- `Build/RecordTable.lean:157–158`: "**The record length's formula** (the specification API, user 2026-10-16), so that consumers never unfold `Turing.recordLength`."

**Fix R4** (the patch's text):

```lean
/-- **Reading a record** (the specification API, user 2026-10-16): `RecordAt d r fs` holds
exactly when, at every offset `p` with `-1 ≤ p ≤ |joinFields fs|`, the cell of tape `r` at its
head plus `p` holds `fieldsTape fs p`: the layout's cells, with blank delimiters at offsets `-1`
and `|joinFields fs|`. Cells outside that interval are unconstrained. -/
```

```lean
/-- **The record length's formula** (the specification API, user 2026-10-16):
`recordLength k n s = k (2s + 1) + posWidth n + k + 4`, that is, `k` tape fields of `2s + 1`
cells, `posWidth n` position digits, the state and tag cells, and `k + 2` separators. -/
```

- The new text adds 2 lines in CfgRecord and 1 in RecordTable. Later line numbers in those files shift; the drafts' measurement placeholders are taken after the base lands anyway.
- Both files elaborate as at the base: CfgRecord 0 warnings; RecordTable 4 sorry warnings.

## Finding 5 — the replay (ACCEPT as note; resolved)

- `$S/fills/replay/replay-lapi.log` begins `# replay-lapi at 28824c36: … (89 modules)` and ends `# modules=89 failed=0`.
- Its script `replay-lapi.sh` refuses to run unless the worktree `wt-api` is at `origin/lean/spec-api` with no local changes. `wt-api` is at `28824c36` (commit 00:50:10); the log was written at 00:59:24.
- The 89 listed modules equal the evidence's `replay-order.txt`.
- The base snapshot was `oleans-lc5p`, #113's replay at `e2089d70`: 9/9, 0 failed.
- So downstream verification at `28824c36` is complete. It postdates the bundle (00:51:22), which is why the auditor saw no log.
- **After the repairs, a new replay is required.** graph2 over the six repaired files gives an 85-module closure (`review/spec-api-gate/graph/replay-order.txt`), all within the 89. The 4 not needed are `Build/Catalog`, `Build/NDHost`, `Build/Scan`, `Build/StepBlock`, since `Build/Catalog` is not touched.

## The auditor's numeric claims

| Claim | Check | Result |
|---|---|---|
| 52 distinct sections | `^## ===== … =====$` headers in the bundle | 52, no duplicates; README says 52 |
| 85 generated equations (5 + 15 + 65) | `#check` lines in `probes/*.checks.lean.txt` and `@Turing.` entries in `logs/generated-*.txt` | Basic 5, Seam 15, Catalog 65; 85 distinct. Catalog is 13 definitions × 5 |
| Reversing the patch reproduces the six base blobs | `git apply -R spec-api.patch` at `28824c36`, `git hash-object` | all six equal the blobs at `5eff4146` and `c2897d7f` |
| Screen 711 → 712, 350 pairs, 116,080 characters | `logs/screen-{base,head}.txt`; pairdiff; my own sum | 711/350/116,080 → 712/350/116,080; 0 new, 0 gone; the reproduced counts sum to 116,080 in both |
| Sole newly screened declaration is `fieldsTape_of_length_le` | the screen's own extraction rule (body after `:=`, at least 60 characters) on the ten hand-written lemmas | only `fieldsTape_of_length_le` (107) newly qualifies; `record_pos_lt` (62) was already screened as a private; the other eight are 3–35 |

No discrepancy.

## The five "additional interfaces"

All five are structure-valued `where` defs with data fields `pre time post lo hi` and proof
fields. `simps (config := { isSimp := false }) pre time post lo hi` works on each: tested
in-module, 25 equations, 0 errors, faithful printed forms (`out/ApiBasic.out`).

| Declaration | File:line | Result type | Read by a drafted route? |
|---|---|---|---|
| `Turing.Contract.mapState` | `Build/Contract/Basic.lean:1123` | `Contract N (emb entry) (Option.map emb '' X) ι x` | no |
| `Turing.Contract.lockstep` | `Build/Contract/Basic.lean:1252` | `Contract N entry' X' (ι × Cfg k Γ S x) x'` | no. F5 (`b6-fill-rulerdevice.DRAFT.md:127–132`) uses the `Lockstep` structure and `Lockstep.runFrom`/`.cut`/`.locate`, which are theorems; the structure's fields are proofs, already exposed |
| `Turing.RoundContract.returning` | `Build/Contract/Basic.lean:783` | `ReturnContract M anchor ι x` | no |
| `Turing.RoundContract.escaping` | `Build/Contract/Basic.lean:803` | `Contract M anchor escape ι x` | no |
| `Turing.ReturnContract.toRound` | `Build/Contract/Basic.lean:823` | `RoundContract M anchor ∅ ι x` | no |

How each draft reads the contract layer:
- **F3-cont1** (`audits/evidence/drafts/b6-fill-configclock-cont1.DRAFT.md`): uses `_run_ofCfg` rows, the phase host and seams; it names no contract combinator. Its "every row contract's field equations" is background.
- **U2-S** (`u2s-fill-startup.DRAFT.md`): uses `_run_ofCfg` and `<row>_contract_*`, and none of the five.
- **cont6** (`b5a-fill-canon-cont6.DRAFT.md`): uses the `phaseHostTM` adapter and the counter loop; there is no contract layer.
- **G4-cont**: not drafted (README: it waits for the zone-layer ruling). Its binding brief names `Round.iterate` and `RoundContract.release` (finding 1) and none of the five.

**Optional fix R1b** (`repair-optional.patch`, on top of the required one): the same attribute
for all five. It adds 25 equations and no statement change.
- The `mapState` line is placed with `Contract.lockstep`'s, after that definition, not right
  after `mapState`.
- The first placement attached the attribute text to `mapState`'s screen body. That pushed a
  pre-existing near-half overlap to a new pair, `Seam.lean::branch reproduces
  Basic.lean::mapState: 482/948 = 51%` (`out/screen/screen-required+optional.txt`).
- After relocation the screen is clean. The patch's comment says why; drop the parenthetical if
  you prefer library text without it.

Taking R1b now is cheap, since `Contract/Basic` is edited and replayed anyway. No draft needs it.

**Related, not a finding.** `Turing.Round` and `Turing.Segment` (`Contract/Basic.lean:652`, `:400`) are Prop-valued defs without iff lemmas.
- G4's `Round.iterate` → `Contract.ofSegment` route needs neither unfolded. Rounds come from `RoundContract.round` or `Round.of_cut`, and the segment is passed whole to `ofSegment`.
- A G4 continuation that builds a round with a non-trivial head relation outside those constructors would need a `Round` introduction lemma. Check this at G4-cont's pre-ship.

## Repair list (apply directly)

The patches, made against `28824c36`, are:
- `review/spec-api-gate/repair-required.patch` (SHA-256 `24d6361a58c5d756a89fe85cd9e5fcd27b898fc81b0fd3f4f6eec919a0ef6482`): R1–R4;
- `review/spec-api-gate/repair-optional.patch` (`7653836f70316ef08bcf10fb0d61967a3fc890b18b1cd46db34009693028692c`): R1b, applies after the required patch.

Both `git apply` cleanly. The edits are generated by `review/scripts/spec_api_repair.py`, every replacement asserted. The staged before/after copies are in `review/spec-api-gate/edit/{orig,req,all}`.

| Fix | File | Change |
|---|---|---|
| R1 | `Build/Contract/Seam.lean` | `attribute [simps (config := { isSimp := false }) pre time post lo hi] ReturnContract.release RoundContract.release`, after `RoundContract.release`; a Main-results bullet |
| R1 | `Build/Contract/Basic.lean` | `attribute [simps (config := { isSimp := false }) pre time post lo hi] ofSegment`, after `ofSegment` (inside `namespace Contract`); a Main-results bullet |
| R2 | `Build/Contract/Catalog.lean` | `theorem sweepMapWrite_apply … := rfl` after `sweepMapWrite`; `copyMapTM_contract_post_workTapes` and `transferMapTM_contract_post_workTapes` at the end (after the `simps!` lines); a Main-results bullet |
| R3 | `SpaceComplexity/WindowClock.lean` | lines 273–275 replaced (docstring only, same line count) |
| R4 | `Build/CfgRecord.lean`, `Build/RecordTable.lean` | the two docstrings replaced (statements and proofs unchanged) |
| R1b (optional) | `Build/Contract/Basic.lean` | `… returning escaping` before `end RoundContract`; `… ReturnContract.toRound` after it; `… Contract.mapState Contract.lockstep` after `Contract.lockstep`; a Main-results bullet |

**Tested with the repairs in place** (scratch worktree, reset afterwards):
- **Elaboration** against `oleans-lapi`: Seam, Basic and Contract/Catalog give 0 errors and 0 warnings. CfgRecord 0 warnings, RecordTable 4 sorry warnings, WindowClock 1 sorry warning, all as at the base.
- **Generated names:** all 15 + 25 resolve; the 3 theorems resolve.
- **Freeze** (`declfreeze.py`/`privstmt.py`, `orig` → `all`):
  - `STATEMENT CHANGED: []` in all six files;
  - no declaration removed;
  - public added only in `Contract/Catalog` (the 3 theorems);
  - "body/docstring-only" changes only for `recordAt_iff`, `recordLength_eq` and `exists_configWindowRunnerTM`, all three docstring-only, by R3/R4.

  The generated equations are new declarations; the freeze tool does not list them.
- **Lint:** `TuringMachine/Build` 0 FAIL, 14 WARN over 36 files; `SpaceComplexity` 0 FAIL, 4 WARN over 107 files; every added line at most 100 characters.
- **Copy-text screen** of #112's six-file population:
  - required only: 714 declarations, 350 pairs, 116,080 characters, 0 new;
  - required + optional: the same (`out/screen/screen-{required,all}.txt`).

  The +2 declarations are the two cell lemmas; `sweepMapWrite_apply`'s body is under the floor.

**Do the repairs change any statement or definition?** No. They add declarations: 3 theorems,
15 generated equations, and 25 more with R1b. They edit 3 docstrings (findings 3 and 4 require
it) and the module-docstring "Main results" lists. No existing statement, definition body or
proof changes.

**After applying:**
- Replay the 85-module list.
- Extend `probes/*.checks.lean.txt` with the new names, so 85 becomes 100, or 125 with R1b.
- Record `replay-lapi.log` (finding 5).
- Send the repair diff for a round-2 check: finding 1 is the one remaining major.
