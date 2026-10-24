# Megafill C: the drafting report (drafting agent, 2026-10-24)

The deliverable of `campaign/fills/megafill/drafts/megafill-C-drafting-brief.md` (SHA-256
`496ac104360334eef9dd83b4293088decda0b376fc897466fb4f15231fca0cc3`, verified against the attached
copy and the repository copy at the drafting base; the brief's commit
`1133762f39ea344b56e40d0c6e9af98eaf915bb0` is an ancestor of the base). Three new fill briefs, their
pre-ships, the megafill C cover, and this report. **Nothing under `TCSlib/` changed**; every Lean
check ran through `scripts/lean_check_tree.sh`, one Lean process at a time, on copies of the probes
under the clone's ignored `.lake/probes/`; no `lake build`, and the cache was fetched for the union
of the items' Mathlib roots only.

**The drafting base:** `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532`, the campaign tip
when drafting started (its TCSlib tree equals `6e761018`'s: G4 cont4's recorded pre-ship holds
here). Every line number and measurement in the drafts is this tree's.

**The branch:** `drafts/megafill-c`, from the drafting base; it adds files under `campaign/` only.

Items are numbered as in the drafting brief's §3 (G4 1, C1 2, B5a 3, U2 4); the cover's queue
order differs (C1, B5a, U2, G4: Q-M1, under "The cover" below).

## The environment (addendum v2.5, Part 1; shared by the three pre-ships)

Logs: `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/logs/`.

| Step | Result | Log |
|---|---|---|
| Preflight | 4 CPUs; cgroup v1 with no effective memory limit, so the headroom is `MemAvailable`: 16,365,686,784 B = 15.24 GiB (floor 4); the clone's filesystem ext4 (not memory-backed), 31,664,181,248 B = 29.49 GiB free (floor 12) | `preflight.log` |
| Toolchain | elan, then `leanprover/lean4:v4.25.0` (`lean --version` in the log); Lean started normally (Part 2 not needed) | `toolchain.log` |
| Re-check | 27.08 GiB free after the toolchain (floor 8) | `recheck.log` |
| Cache store | `/root/.cache/mathlib` absent before the fetch: 0 archives | `cache-store.log` |
| Roots | 41: the union of the three new order lists (C1 and B5a 119 modules each, the same set; U2 96, a subset); G4's 96 add none | `mathlib-roots.txt` |
| Narrowed fetch | `TAR_OPTIONS=--no-same-owner lake exe cache get <41 roots>`: exit 0; attempted and downloaded 1,023, decompressed 1,023, no failure | `cache-get.log`, `cache-get.time` |
| Manifest | 11 packages present, each matching the manifest's URL and revision; 4 absent (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`), imported by no module of the lists: PASS | `manifest-check.log` |
| Cache check | no empty olean among 1,032; a probe importing the first root elaborated (exit 0) | `cache-check.log` |
| Bootstrap | the 119-module union in topological order: 119/119 exit 0, 0 errors, 31 sorry warnings (agreeing module by module with the base sorry set); 879 s of Lean time; peak 2,993,964 KiB (`Build/CfgRecord`); per-module time and memory logged | `bootstrap.log`, `bootstrap-order.txt` |

The host has no `/usr/bin/time`; per-module memory is the children's peak RSS from `getrusage`
(a small wrapper, the `MEM` lines). Lint (`campaign_style_lint.py TCSlib/Complexity/TuringMachine`)
at the base: 0 FAIL, 68 WARN over 83 files.

## Item 1: G4 continuation 4 (drafted earlier; not rewritten)

`campaign/fills/s13d/drafts/s13d-fill-g4-cont4.DRAFT.md`, pre-ship re-run at `6e761018`
(`drafts/s13d-fill-g4-cont4/preship-6e761018/`). **TCSlib is unchanged from `6e761018` to the
drafting base** (`git diff 6e761018 HEAD -- TCSlib` is empty), and `fillinputs.py` at the base
reproduces its order list (96 modules) and base sorries (27) exactly. Issue-time items left:
@ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩ (at drafting #156 and #135), ⟨SNAPSHOT⟩, ⟨SORRIES⟩ (27, unchanged),
⟨SCREEN⟩ (846 declarations, 477 pairs, unchanged), the banner (item 4 in the cover's order) and
its budget (the rest). It already carries addendum v2.5 and the 2026-10-23 rule-10 scope bullet.

## Item 2: C1, the replay canonizer

**Target:** `Turing.exists_replayCanonizer` (`NDCodeSimulator.lean:96`). Draft:
`campaign/fills/c1/drafts/c1-fill-replaycanon.DRAFT.md`; pre-ship:
`campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f/`.

**The route in five lines.**
1. A private primitive recursive `rc_g` with `rc_g M.serialize = serializeK M.tm.replayTM`: keep
   the header (`pairDecode`, `codeReadUnary`, the kept prefix by `codePrimPrefix`).
2. Find the `true` table (`codeSkipRepeat (codeSkipActionK 2 n) (27 (n + 1))`), then `27 (n + 1)`
   lockstep rounds peeling one record off each table, emitting `w(rF) ++ w(rF) ++ w(rT)`.
3. `w r = r.take 10 ++ [false, false, true, false] ++ r.drop 10`: the choice tape's field inserted
   after the input move and the two work fields (`rc_widen_record`, from `actionBitsK_eq`).
4. Correctness from the published layouts (`tableBitsK_eq`, `workReadsK_succ`, `NDTM.replayTM_tr`,
   `NDTM.fixChoice_tr`, `serialize_eq_tableBitsK`, `codeSkipActionK_append`); `Primrec` from
   `MathlibBridge`'s building blocks (no `Primrec.list_take` at this pin: `codePrimPrefix`).
5. Compile by `codePrim_machine`, monotonize the bound by a running maximum, compose with the
   scheme's canonizer by `computesFunInTime_comp`.

**The maintainer's findings, verified.** All five hold: `canonizer_computes` is the structure
field as stated; `codePrim_machine`'s `T` is arbitrary; `ComputesInTime.mono` with
`computesFunInTime_iff` weakens to `fun n => (Finset.range (n + 1)).sup T` (the route probe proves
the monotonicity by `Finset.sup_mono`); `computesFunInTime_comp` needs `Monotone T₂`; every layout
and the bridge are published, with field equations (`replayTM_tr`, `fixChoice_tr` pointwise).

**Pre-ship (all at the drafting base).**

| Check | Result |
|---|---|
| Owned file | exactly the target's sorry warning |
| Order list, roots, base sorries | 119 modules, 41 roots, 31 sorried declarations in 15 modules |
| Import probe | standalone import of the owned module: 102 checks of 102 names, 0 errors, 0 warnings; the route's machine lemmas on the standard three axioms |
| Route probe | sealed over 14 TCSlib definitions: the composition with `g` abstract, the choice field, the record widening, the read order, both tables' layouts, the widening's `Primrec` proof: 0 diagnostics |
| Seal controls | 15 goals: all close unsealed, all fail sealed, each at its own goal |
| Definitions probe | the recommended `rc_` definitions elaborate; **by evaluation** (`#eval`; not a proof), `rc_g` reproduces the replay serialization on two concrete machines (732 → 1,407 and 1,545 → 2,949 bits) |
| Screen base | 16 files: 541 declarations, 173 pairs, 86,076 characters; no pair on the owned file |
| Lint | `TuringMachine` 0 FAIL, 68 WARN over 83 files |

**Dependencies.** `NDCodeSimulator` imports `CodeSimulator` (B5a's file): C1 cites only its
unchanged `serializeK` and `serializeK_eq`, not B5a's target. Downstream, C1 completes the core
(#151) and the universal NDTM (#154), whose only admission is this target. **Proved modulo:
none.** No import needed.

**Open questions:** none blocking. One sketch refinement, stated in the brief: a record is widened
at bit level, not decoded (the two are equal by `rc_widen_record`; only the bit form is primitive
recursive with the published blocks); the target's docstring may get an `**Implementation.**`
paragraph at integration.

**Size and budget:** about 350–550 new lines (definitions 40; record-level lemmas 120, in the
probe; the split and rounds 150; the header 60; `Primrec` 120; the composition 25). **3 hours.**

## Item 3: B5a, the uniform simulator

**Target:** `Turing.MachineFormat.exists_uniformSimulator` (`CodeSimulator.lean:8656`). Draft:
`campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`; pre-ship:
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-77f1eb4f/`.

**The route in five lines.**
1. The interpreter core's startup, deterministic: two header passes (`prefixCanonTM` with the pair
   extractors, captured by `embedSilentRetTM`), input rewinds by `Turing.inputRewindTM`, the
   counter copied.
2. The window `x.take t` by `exists_inputWindowCopyTM`; bounded acceptance on the window is on `x`
   by locality (`MultiTapeTM.toNDTM_runWith` with `NDTM.runWith_initCfg_take`).
3. The polynomial canonizer through `FinTM.exists_installCallTM` (uniform, polynomial:
   `b5a_install`), then `exists_seamLayoutTM` onto the table and summary tapes.
4. The landed hosted verdict `h1HostedVerdict_accepts` on the window (`b5a_window_verdict`),
   embedded by R1; the startup is silent, so the output is `[answer]`.
5. A uniform ledger: every phase `≤ c · N^e` with `N = |α| + |x| + t + 1`, using
   `|tableBitsK| ≤ max |α| |F.serialize F.fallback|` (`b5a_table_le`) and `|bits t| ≤ t`.

**Pre-ship (on the overlay, `CodeSimulator` with five new imports).**

| Check | Result |
|---|---|
| Overlay | exactly the target's sorry warning (overlay line 8661); no import cycle; the five downstream modules that gain names share no declaration name with the gained modules |
| Order list, roots, base sorries | 119 modules (the base set, `CodeSimulator` now after its new imports; computed by `fillinputs-overlay.py`, `fillinputs.py` reading the overlay for that one module), 41 roots, 31 sorries in 15 modules |
| Import probe | 109 checks of 109 names, 0 errors, 0 warnings; the eight composed rows on the standard three (the input rewind on two) |
| Route probe | sealed over 12 TCSlib definitions: `b5a_install`, `b5a_locality`, `b5a_accepts_take`, `b5a_verdict`, `b5a_table_le`: 0 diagnostics |
| Verdict probe | in-module (appended to the overlay), sealed over 4 more: `b5a_window_verdict`, `h1HostedVerdict_accepts` on the window deciding acceptance on `x`: the target's warning only |
| Seal controls | 16 goals: all close unsealed, all fail sealed |
| Screen base | 54 files: 2,756 declarations, 3,005 pairs, 973,130 characters; on the owned file 58 in-file pairs (4 at 90% or more, CC7-1) and 41 cross-file; 87 minutes |
| Lint | `TuringMachine` 0 FAIL, 68 WARN over 83 files |

**Dependencies.** `CodeSimulator` is upstream of C1's and U2's files; neither cites this target.
B5a cites no other item. **Proved modulo: none** (every composed row is admission-free). Complete,
it removes the last admission of targets 3–8 and `Complexity.baker_gill_solovay` from this file.

**Open questions.**
- **Q-B1 (blocking; the user's ruling): the startup kit.** B5a's phases 1–3 are, mathematically,
  `NDCodeSimulator`'s private `ic_header_result`, `ic_capture_return`, `ic_header_capture`,
  `ic_input_suffix`, `ic_seam_step`, `ic_install_phase`, `ic_window_call` and `ic_layout_call`
  (and, for the header pass, UN's `un_canon_halt`/`un_step` and U2-S's `ss_capturedPrefix_run`
  family). `CodeSimulator` cannot import `NDCodeSimulator` (it is upstream), and rule 11 forbids
  another file's privates, so a fill on the published rows alone **re-proves them**: the fourth
  private header capture, and cross-file pairs with `NDCodeSimulator` that the brief's "no new
  cross-file pair" forbids. `policy.md` ("do not write a third private variant") and the IR-1
  precedent (the input rewind: "an API PR first") point one way.
  - **(A, recommended) An API PR first: harvest the kit** into a new small module below
    `CodeSimulator`, e.g. `TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean`
    (importing `UniversalStartup`, `Build/Embed`, `Build/Seam`, `Build/Loop`, `Build/InputWindow`,
    `Build/SeamLayout`), with exactly the current private statements under public names:
    `Turing.prefixCanon_pairExtract_halt` (`ic_header_result`),
    `Turing.embedSilentRetTM_firstReturn` (`ic_capture_return`), `Turing.headerCapture_run`
    (`ic_header_capture`), `Turing.seamCompTM_step` (`ic_seam_step`; not in `Build/Seam` while #156
    is open there), `Turing.installCall_releasePhase` (`ic_install_phase`),
    `Turing.exists_windowCall` (`ic_window_call`), and `Turing.exists_layoutCall`
    (`ic_layout_call`, restated over `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`, since
    `serializeK` lives in `CodeSimulator`; consumers rewrite by `serializeK_eq`). For the suffix
    drop (`ic_input_suffix`) cite or move the public `Complexity.Codec.pe_drop`
    (`SpaceComplexity/Codec/Parse`), which has the same statement (PathWalk's private
    `drop_pairEncode` is a third copy). `NDCodeSimulator` re-points in the same PR (the #153
    precedent); UN's and U2-S's members in the dedup window. Then B5a's brief keeps its ⟨Q-B1: A⟩
    paragraphs and its import list gains the new module.
  - **(B) Issue as drafted**, B5a writing the kit's analogues privately (`us_`), with the
    resulting cross-file pairs pre-disclosed and ledgered by the ruling, and the harvest later.
  The draft carries both outcomes as marked paragraphs (⟨Q-B1: A⟩, ⟨Q-B1: B⟩); keep one at issue.
- **Q-B2 (note): five new imports** into `CodeSimulator` (`UniversalStartup`, `Build/Rewind`,
  `Build/SeamLayout`, `Build/InputWindow`, `Nondeterministic`), authorized as region (a), as R's
  four were. The checks above found no cycle and no name clash; the fill's final sweep is the
  authority. `Nondeterministic` is only for the locality bridge; a public deterministic locality
  lemma beside `MultiTapeTM.toNDTM_runWith` would serve the next consumer (promotion candidate).
- **Q-B3 (note): two refinements of the frozen sketch**, stated in the brief: the buffer holds the
  window `x.take t` (the published row that places a suffix window; locality makes it enough), and
  the clock and verdict are the landed `h1HostedVerdict_accepts`. The docstring's fill appendices
  then describe an earlier state: the maintainer's status rewrite at integration.

**Size and budget:** under (A) about 800–1,200 new lines (the startup's assembly, the window and
locality, the install and layout embedding, the loop's entry, the ledger); under (B) about
1,400–1,900 (plus the kit's analogues; the core added 1,651 lines in one 4-hour round). **5
hours**; a partial at checkpoints 3–4 is plausible.

## Item 4: U2, the `k`-tape universal machine

**Targets:** `Turing.exists_selfUniversalK` (`UniversalK.lean:1716`) and `Turing.universalK`
(1754). Draft: `campaign/fills/u2s/drafts/u2s-fill-universal.DRAFT.md`; pre-ship:
`campaign/fills/u2s/drafts/u2s-fill-universal/preship-77f1eb4f/`.

**One brief or two (decided, as the drafting brief asked):** **one brief, two phases**, U2-U then
U2-E. `universalK` does **not** follow from `exists_selfUniversalK`: U2-U runs the coded machine on
its own input `pairEncode α w` through the native device, U2-E on the suffix `x` of
`pairEncode α x` through H5's ruler host, with another machine and another time. They share the
startup (`exists_selfStartupTMK`, which is uniform in the suffix, so it serves both layouts) and
the seam into H2-F, which phase 2 reuses; one brief keeps that seam one private lemma.

**The route in five lines.**
1. U2-U: the startup, then H2-F's loop embedded by R1 on the first `k + 2` tapes; at the startup's
   exit the embedded part is `forwardLoopCfg entry M (M.initCfg z)` (`u2_encode_init_*`).
2. U2-U's ledgers: `Lockstep.runFrom` to the first halt, `cost ≤ 50 (|table| + 1) + C_L`, per-code
   `C`; space by `spaceUsed_eq_sum` and the embedding's and seam's visited sets; converse by
   `Lockstep.cut`.
3. U2-E: the startup on `pairEncode α x`, then the one authorized leaf, the header-ruler scan
   (`true^ℓ`, `ℓ = 2|α| + 2`), and its rewind by `rewindTM_run_ofCfg`.
4. U2-E: H5's `exists_rulerHostTM` over H2-F's `L`, started at
   `rulerHostCfg ℓ hz (… inj q false) (forwardLoopCfg entry M (M.initCfg x)) rt rp`
   (`u2_ruler_fields`; tag `false`).
5. U2-E's ledger `C_R (ℓ + 1)` per step of `L`, no `|x|` term; converse by the host's cut and the
   lockstep's.

**Pre-ship (on the overlay, `UniversalK` with `Build/Rewind`).**

| Check | Result |
|---|---|
| Overlay | exactly the two targets' sorry warnings (overlay 1717, 1755); no cycle; `SelfUniversal` (the one module gaining names) shares none with `Build/Rewind` |
| Order list, roots, base sorries | 96 modules (the base set), 40 roots, 27 sorries in 12 modules |
| Import probe | 77 checks of 77 names, 0 errors, 0 warnings; startup, H2-F, H5, `Lockstep.runFrom`, rewind on the standard three |
| Route probe | sealed over 8 TCSlib definitions, **with the proposed API's equations as `rfl` stand-ins**: `u2_encode_init_tapes`, `u2_encode_init_fields`, `u2_encode_halt`, `u2_ruler_fields`: 0 diagnostics |
| Seal controls | 8 goals: all close unsealed, all fail sealed; the `forwardLoopCfg` and `rulerHostCfg` controls are the API gap |
| Screen base | 20 files: 1,039 declarations, 785 pairs, 213,552 characters; on the owned file 13 in-file pairs (none at 90% or more) and one cross-file (56%); 10 minutes |
| Lint | `TuringMachine` 0 FAIL, 68 WARN over 83 files; check 8 lists `forwardLoopCfg`, `RulerAt` and `rulerHostCfg` |

**Dependencies.** `UniversalK` is downstream of `CodeSimulator` (through `Codes2Tape`) and cites
nothing of it. **Proved modulo: none.** Complete, U2-U also makes `Turing.exists_selfUniversal`
(its `k = 1` case, `SelfUniversal`) admission-free.

**Open questions.**
- **Q-U1 (blocking): "API PR first": the field equations of two public definitions.** Both
  phases' seams read `Turing.StepBlock.forwardLoopCfg` (`Build/StepBlockForward`) and phase 2 reads
  `Turing.rulerHostCfg` (`Build/InputDevice`); neither has any published lemma (lint check 8), so
  rule 10 leaves no route. The PR: beside each definition,
  `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]`,
  generating (statements as the route probe's stand-ins, pointwise):
  - `Turing.StepBlock.forwardLoopCfg_state : (forwardLoopCfg entry M c).state =
    c.state.map fun _ => entry`, `_inputPos : … = c.inputPos`, `_workTapes : ….workTapes i =
    Fin.addCases c.workTapes (fun j => if j = 0 then FinTM.bufferTape (tableBitsK M.tr) else
    StepBlock.summaryCells none ((c.state.map unaryFin).getD [])) i`, `_workTapePos : … =
    Fin.addCases c.workTapePos (fun _ => 0) i`, `_output : … = c.output`;
  - `Turing.rulerHostCfg_state : (rulerHostCfg ℓ hz q c rt rp).state = q`, `_inputPos` (the `Fin`
    `⟨ℓ + c.inputPos.val, _⟩`; consumers read `.val`), `_workTapes : … i = Fin.lastCases rt
    c.workTapes i`, `_workTapePos : … i = Fin.lastCases rp c.workTapePos i`, `_output : … =
    c.output`.
  Optionally `RulerAt_iff` (check 8 lists `RulerAt` too; U2's route does not read it). An API gate;
  replay the downstream closures of the two modules. **Recommendation: do it before issue**
  (small, mechanical, and the route probe shows it suffices); then re-run U2's pre-ship against it.
- **Q-U2 (note): the header-ruler leaf.** No public row writes a ruler of the header's length; the
  brief authorizes one private leaf (a finite-state pair scan) for U2-E, as briefs authorize
  leaves. `Complexity.space_universal`'s startup (`SpaceComplexity/Hierarchy`) needs the same scan
  for a three-part header; **recommendation:** keep it private now, as a promotion candidate,
  and publish it when `space_universal` is briefed (its second consumer), not before.

**Size and budget:** U2-U about 500–800 new lines; U2-E about 600–900 (the leaf about 150).
**4 hours**; a partial (U2-U complete, U2-E at 2.1–2.2) is the likely outcome.

## The cover

`campaign/fills/megafill/drafts/megafill-C.DRAFT.md`: four items, Codex, addendum v2.5, one
preflight, one cache for the union (41 roots, 119 modules), a re-bootstrap per item, a zip per
item, megafill A's lessons (shared logs in every zip, per-module memory, "seal not run" and "seal
without failing controls" as checklist failures, `Simulation`/`Build/InputRewind` for an input
rewind). **The proposed order** (Q-M1, the maintainer's call): **C1 (3 h), B5a (5 h), U2 (4 h), G4
(the rest)**: the small, fully probed item first so that an early end still delivers it; the most
valuable and largest item second; U2's two checkpointed phases third; G4, a long checkpoint chain
whose rounds have each ended partial, last. Items whose prerequisite (Q-B1, Q-U1) is not in the
shared base are dropped at issue, and the queue renumbered.

- **Q-M2 (the maintainer's call): B5a's screen time and its budget.** On the drafting host one
  run of B5a's 54-file screen took **87 minutes** (C1's 13, U2's 10, under `nice -n 10`, about
  100 MB resident), so its before and after runs cost about three hours of a 5-hour budget. The
  brief has the before run started in the background right after the first edit, beside the one
  Lean process (the addendum limits Lean processes and screens to one each, not their sum), which
  hides most of it; the after run cannot be hidden. **Recommendation:** the cover counts B5a's
  budget up to the start of its after run, and the next item's branch is created only after that
  run ends (the screen reads the working tree); otherwise raise B5a's budget to 6 hours.

## Records

- **Hashes:** every commit and blob hash in these files was inserted by `git rev-parse`
  (placeholders resolved by a script that checks each object with `git cat-file -t`); no hash was
  typed by hand.
- **Copy-hazard searches:** the tree and both open PR heads (#156 `lean/phasehost-last`, #135
  `complexity/arora-barak-ch7`, fetched read-only) for each route's would-be copies (each
  pre-ship README).
- **For the dedup window (note, outside megafill C):** `Complexity.Codec.pe_drop` (public) has the
  statement of `NDCodeSimulator`'s private `ic_input_suffix` and `Logspace/PathWalk`'s private
  `drop_pairEncode`; a home beside `pairEncode_eq` in `Encoding` would serve all three.

## Not complete

Nothing: every deliverable of the drafting brief's §9 is on the branch.

## Files (all new, under `campaign/`)

78 files.

- `campaign/fills/b5a/drafts/` (1): `b5a-fill-unisim.DRAFT.md`
- `campaign/fills/b5a/drafts/b5a-fill-unisim/preship-77f1eb4f/` (22): `B5aUSImportProbe.lean.txt`,
  `B5aUSImportProbe.out`, `B5aUSRouteProbe.lean.txt`, `B5aUSRouteProbe.out`,
  `B5aUSSealControl.lean.txt`, `B5aUSSealControl.out`, `B5aUSVerdictProbe.append.lean.txt`,
  `B5aUSVerdictProbe.assembled.sha256`, `B5aUSVerdictProbe.out`, `CodeSimulatorOverlay.lean.txt`,
  `README.md`, `base-sorries.txt`, `elab-CodeSimulator.out`, `elab-CodeSimulatorOverlay.out`,
  `fillinputs-overlay.py`, `lint-turingmachine.txt`, `order.txt`, `roots.txt`, `screen-base.status`,
  `screen-base.stderr`, `screen-base.txt`, `screen-population.txt`
- `campaign/fills/c1/drafts/` (1): `c1-fill-replaycanon.DRAFT.md`
- `campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f/` (18): `C1RCDefsProbe.lean.txt`,
  `C1RCDefsProbe.out`, `C1RCImportProbe.lean.txt`, `C1RCImportProbe.out`, `C1RCRouteProbe.lean.txt`,
  `C1RCRouteProbe.out`, `C1RCSealControl.lean.txt`, `C1RCSealControl.out`, `README.md`,
  `base-sorries.txt`, `elab-NDCodeSimulator.out`, `lint-turingmachine.txt`, `order.txt`,
  `roots.txt`, `screen-base.status`, `screen-base.stderr`, `screen-base.txt`,
  `screen-population.txt`
- `campaign/fills/megafill/drafts/` (2): `megafill-C-DRAFTING-REPORT.md`, `megafill-C.DRAFT.md`
- `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/` (1): `README.md`
- `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/logs/` (11): `bootstrap-order.txt`,
  `bootstrap.log`, `cache-check.log`, `cache-get.log`, `cache-get.time`, `cache-store.log`,
  `manifest-check.log`, `mathlib-roots.txt`, `preflight.log`, `recheck.log`, `toolchain.log`
- `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/tools/` (2): `runmem.py`,
  `subst_hashes.py`
- `campaign/fills/u2s/drafts/` (1): `u2s-fill-universal.DRAFT.md`
- `campaign/fills/u2s/drafts/u2s-fill-universal/preship-77f1eb4f/` (19): `README.md`,
  `U2UEImportProbe.lean.txt`, `U2UEImportProbe.out`, `U2UERouteProbe.lean.txt`,
  `U2UERouteProbe.out`, `U2UESealControl.lean.txt`, `U2UESealControl.out`,
  `UniversalKOverlay.lean.txt`, `base-sorries.txt`, `elab-UniversalK.out`,
  `elab-UniversalKOverlay.out`, `fillinputs-overlay.py`, `lint-turingmachine.txt`, `order.txt`,
  `roots.txt`, `screen-base.status`, `screen-base.stderr`, `screen-base.txt`,
  `screen-population.txt`
