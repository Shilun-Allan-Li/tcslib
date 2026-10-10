# Zone fill batch ZF-A — partial delivery

**18/20 targets filled, with 22/24 original `sorry` terms removed.** All pure targets are complete. The two uniform shift-machine existence rows remain byte-identical admissions. No new admissions, axioms, public declarations, imports, or weakened statements were introduced. This is not a zero-sorry batch and does not close the fill gate.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Requested branch: `complexity/arora-barak-ch3-4`.
Working branch: `fill/zone-f1-A`.
Recorded base: `3e5dd8c7504725750720629a7be08855b89d4e87`.
Final commit: `1f2c014729f7087b4fcf9245b12b65fde1610774`.
The owned source at the recorded base is byte-identical to the source at the brief's issued base `8f13d74ecba8e73a3642d605f462774092d7ef8a`. No rebase, push, or PR was performed.

Read in full: `briefs/zone-f1-batchA.md`, the three `zone-infra` findings files, and `audits/zone-infra-resolutions.md`, followed by repository policy/workflow. The attachment and repository brief agree. The round-3 inventory is used: four definitions with eight capacity holes, plus sixteen theorem holes.

## Target disposition

All names below are in namespace `Turing`.

| Target | Status |
|---|---|
| `zoneShiftIn` | Both capacity fields proved |
| `zoneShiftOut` | Both capacity fields proved |
| `zoneMoveRight` | Both capacity fields proved |
| `zoneMoveLeft` | Both capacity fields proved |
| `zoneIndex_eq_iff` | Proved |
| `zoneTape_empty` | Proved |
| `zoneTape_blank_outside` | Proved |
| `zoneTape_homeWrite` | Proved |
| `zoneSide_shiftInW` | Proved |
| `zoneSide_shiftOutW` | Proved |
| `zoneShiftInW_full_donor` | Proved |
| `zoneSide_moveRight` | Proved |
| `zoneCascade_cost_le` | Proved |
| `zoneSide_cascadeRight` | Proved |
| `zoneCascadeRight_lengths` | Proved |
| `zoneCascadeRight_zero` | Proved |
| `zoneCascadeRight_blocked` | Proved |
| `MultiTapeTM.spaceUsedByTape_le_card_Icc` | Proved |
| `FinTM.exists_zoneShiftInTM` | Unchanged `sorry`; escalation below |
| `FinTM.exists_zoneShiftOutTM` | Unchanged `sorry`; escalation below |

## Binding proof routes

Capacity proofs follow the audited prefix/suffix and pushed-cell inequalities. The index proof uses `Nat.log2_eq_iff` at the positive argument `s / 2 + 1`, then the even-endpoint division arithmetic. The extent proof excludes both home cells and maps an outside physical cell to a slot at or beyond `zoneBase ℓ`, whose index fails the level guard.

The list proofs expose adjacent words in the increasing-level concatenation and apply `take_append_drop`; the move proof exposes level zero and applies the nonempty-list tail/append identity. The cost proof establishes the stronger inequality `sum + 16 ≤ 16 * 2^j` by induction, using the library's `Nat.lt_two_pow_self` for the audited elementary power bound.

The cascade proofs package the auditor's descending/move/ascending induction recursively:

```lean
zoneCascadeRight (j + 1) z =
  zoneStepPair (j + 1) (zoneCascadeRight j (zoneStepPair (j + 1) z))
```

This equality is proved by unfolding the actual two folds. It does not alter the schedule. For the word theorem the first outer pair produces a nonempty right prefix and a half-full left receiver at level `j`; the smaller cascade fires its central move, and both outer pairs preserve concatenations. The weaker room hypothesis is retained, and length restoration is not used.

For the lengths theorem the first outer pair leaves level `j` at `(2^j, 2^j)` in right/left lengths; the smaller cascade leaves that level at `(0, 2 * 2^j)`, leaving level `j+1` untouched. The final outer pair therefore fires. The top donor has another `2^j` cells and the second top push uses precisely the stronger room hypothesis. The final lengths combine two transfers of `2^j`. The blocked proof retains the full left family on descent, blocks the central move, and uses concatenation invariance on ascent, with no premise on right data.

The interval-cardinality export is finite-image containment followed by `Finset.card_le_card` and `Int.card_Icc`.

## Machine-row escalation and continuation

The supplied file imports only `TCSlib.Complexity.TuringMachine.Simulation`. Its complete repository import closure is recorded in `import-closure.log`; it contains none of `Build/Embed`, `Build/Seam`, or `Build/Catalog`. Consequently the §12 exports mandated by the brief are not in the environment of either machine-row proof.

The brief restricts edits to the twenty proof bodies and private helpers. I preserved that restriction and the existing imports. This scope issue must be resolved before a continuation can assemble these rows by the required citations. It is **not a counterexample to either mathematical statement**, and granting imports alone does not supply their missing implementation. No machine witness or phase proof is claimed in this delivery.

Requested prerequisite for the continuation: authorize the precise imports of the §12 construction modules in `Zone.lean` (at least `Build/Embed`, `Build/Seam`, and `Build/Catalog`), or provide an explicitly sanctioned shared import path. Then implement the inward row first, with the outward row last. Required obligations remain:

1. Uniform unary-level navigation with the anchored binary-countdown geometric ledger; no level baked into finite control.
2. Bounded guard tests, pair-preserving staging, and word-window rewrites, including identity branches and arbitrary outer tape contents.
3. Scratch cleanup to `bufferTape (List.replicate i true)`, both heads at zero, preserved input position, empty output, and the first-halt cut.
4. Data-head interval containment and the separate scratch-space bound, then one common coefficient for time and scratch.

The reviewed public §12 facilities for that implementation are:

| Phase/obligation | Public exports to consume |
|---|---|
| Transfer/copy staging and cleanup | `transferTM_run`, `transferTM_spaceUsedByTape`, `copyTM_run`, `clearTM_run`, `clearTM_spaceUsedByTape` in `Build/Catalog` |
| Returning embedding and trajectory transport | `embedEmitRetTM_run`, `embedEmitRetTM_visitedByTapeHead` in `Build/Embed`; the silent counterpart additionally requires a separate capture tape |
| General-configuration sequencing | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg` in `Build/Seam` |
| Release to genuine halt | `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead` in `Build/Seam` |

These are a continuation map, **not citations consumed by a completed machine proof**. In particular, the catalog's canonical word-run contracts do not automatically establish framed, displaced runs on a two-sided zoned tape. The continuation must explicitly connect the window invariants to the available general-configuration/embedding contracts; it must not copy catalog private proofs or assert a missing adapter without proof.

## New declarations and duplication ledger

**New copies: none.** Nine new private lemmas, no private definitions or machine controllers, no sorried private helpers. No existing proved family was copied. Optional public exports: **none**. Public docstrings, attribution, imports, and computational definitions are unchanged; no sketch appendices were added to public declarations.

| New private declaration | Exact role |
|---|---|
| `zoneSide_succ` | Separate level zero from the higher-level concatenation |
| `zoneSide_adjacent` | Two adjacent replacements with equal combined word preserve the concatenation, when every other word agrees |
| `zoneShiftInW_capacity` | An inward shift preserves all family capacity inequalities |
| `zoneShiftOutW_capacity` | An outward shift preserves all family capacity inequalities |
| `zoneStepPair_side` | A shift pair preserves each represented half-word |
| `zoneStepPair_frame` | A shift pair leaves both words at every index different from its two affected indices unchanged |
| `zoneStepPair_active` | Four exact prefix/suffix equations for an enabled successor-level pair |
| `zoneCascadeRight_succ` | Peel off the outer pair in each of the two folds |
| `zoneCascadeRight_frame` | The cascade leaves both words at every level above its index unchanged |

The source has 38 public and 9 private explicit declarations. The 1,083-line file triggers one size warning; retaining these private proofs in the owned file is required by this batch's ownership and statement-freeze rules. Splitting/promoting helpers is deferred to the maintainer's shared-file window. The other size warnings (`Catalog`, `Loop`, `Primitives`) are unchanged baseline files.

## Verification and integration

`axioms.log` contains all twenty requested prints. The eighteen completed targets use subsets of `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. Exactly the two retained machine rows print `sorryAx`.

`freeze.log` verifies the unchanged ordered 38-declaration public inventory, all public theorem signatures, all non-proof definition fields, and imports. Only `TCSlib/Complexity/TuringMachine/Build/Zone.lean` is changed in the commit series. `Zone.lean` at the ZIP root is the full source for that repository path.

Style command:

```text
python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build
style_lint: 0 FAIL, 4 WARN over 9 files
```

The ZIP contains an incremental git bundle whose prerequisite is the recorded base; the two format patches apply in numeric order. `integration.log` records successful bundle verification and clean application of both patches to a detached worktree at that base, reproducing the delivered source byte-for-byte. `environment.md` documents the pinned toolchain, successful cache bootstrap, and host compatibility setup.


Final verification completed successfully:

```text
Bootstrap: 73 distinct repository modules freshly checked, zero errors.
Zone: fresh Zone.olean; exit 0; 0 errors; exactly 2 retained machine-row sorry warnings.
Facade: fresh TuringMachine.olean; exit 0; 0 errors.
Axioms: 20/20 prints; all 18 completed targets free of sorryAx.
Lint: 0 FAIL, 4 WARN over 9 files.
Freeze: 38 public declarations unchanged; 9 new private proved lemmas.
Integration: both patches apply cleanly; reconstructed source matches the delivered source.
```

The bootstrap's seven unchanged admission warnings are in `AlphabetReduction` (one), `SingleTape` (two), `CounterProgRun` (one), `NDCodes` (one), `QBF` (one), and `QBFEncoding` (one). They are distinct from the two unfinished Zone rows and are outside this batch's ownership. No zero-sorry claim is made for the whole repository or for this partial Zone file.
