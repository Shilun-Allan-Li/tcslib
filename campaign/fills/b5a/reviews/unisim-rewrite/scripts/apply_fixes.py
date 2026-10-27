# apply_fixes.py <orig-root> <edited-root>: the review's edits, each old string asserted to occur
# exactly once. Paths are relative to the repository root.
import os, sys, shutil

ORIG, EDIT = sys.argv[1], sys.argv[2]
DRAFT = 'campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md'
IMPORT = 'campaign/fills/b5a/drafts/b5a-fill-unisim/preship-9d0af8cb/B5aUSImportProbe.lean.txt'
CLASH = 'campaign/fills/b5a/drafts/b5a-fill-unisim/preship-9d0af8cb/ImportClashProbe.lean.txt'

EDITS = {DRAFT: [
# F2a (comment): the start probe was dropped; the verdict block is inside the junction probe
("""probes, the route, start, verdict and junction probes with their controls, the lists, the
screen base and the lint base. **Measured (2026-10-27) on #169's merged head `9d0af8cb`** (`oleans-laplusm`;""",
 """probes, the route and junction probes (the verdict block in the latter) with their controls,
the lists, the screen base and the lint base. **Measured (2026-10-27) on #169's merged head
`9d0af8cb`** (`oleans-laplusm`;"""),
# F2a: the inputs list
("""    probe, the route, start, verdict and junction probes with their seal controls, and the
    screen population; the""",
 """    probe, the route probe and the junction probe (your overlaid file with the verdict and
    junction blocks after the target) with their two seal controls, and the screen population;
    the"""),
# F2b: the import probe's prints
("""probe's eight axiom prints). **A complete delivery has no `sorryAx` in your target**, and then""",
 """probe's 29 axiom prints: 27 within the standard three, 2 with none). **A complete delivery has
no `sorryAx` in your target**, and then"""),
# F2c + F3: the junction probe's file, and copying needs docstrings
("""- **the junction probe** (`B5aJunctionProbe.append.lean.txt`): the tape map, the junction, the
  start and the run, proved in your file's overlay. Its proofs, and the other pre-ship probes',
  may be copied into your home as `us_` privates.""",
 """- **the junction probe** (`B5aJunctionProbe.lean.txt`, your overlaid file with two blocks after
  the target): the tape map, the junction, the start and the run. Its proofs, and the other
  pre-ship probes', may be copied into your home as `us_` privates; at the home (inside
  `StepBlockClients`, `open StepBlock` in force) they elaborate unchanged. **Copied, each needs
  region (d)'s docstring:** the route probe's lemmas (but `b5a_table_le`) and the verdict
  block's have none, `b5a_install`'s 22-line proof needs a `**Proof sketch.**`, and `b5a_run`'s
  docstring names the probe's `b5a_verdict` (write `us_verdict`). The route probe's
  `b5a_locality` and the verdict block's `b5a_locality'` are one lemma: copy it once, as
  `us_locality`."""),
("""- **The junction probe** (`B5aJunctionProbe.append.lean.txt`, appended to the overlay, after the
  verdict probe's block `b5a_window_verdict`; sealed over 20 definitions): only the target's
  sorry warning; every lemma within the standard three:""",
 """- **The junction probe** (`B5aJunctionProbe.lean.txt`: the overlay with two blocks after the
  target, the verdict block `b5a_window_verdict`, sealed over 11 definitions, then the junction
  block, sealed over 20): only the target's sorry warning; every lemma within the standard
  three:"""),
# F4: promotion candidates
("""  (`us_locality`; a candidate beside `MultiTapeTM.toNDTM_runWith`), and the tape-map lemma
  `us_bank` (generic in `k`).""",
 """  (`us_locality`; a candidate beside `MultiTapeTM.toNDTM_runWith`), the tape-map lemma
  `us_bank` (generic in `k`), and the restart identity `us_start` (a restarted composite starts
  at the relabelled blank start; `UniversalK`'s private `uk_init_mapState` is a second variant)."""),
# F5: route step 1, the installer's names and the cost
("""   - `us_install` (the route probe's `b5a_install`; copy it): one module `C` with `entry`,
     `exit`, constants `a`, `d₀` and `0 < C.k`, uniform in the code;
   - **the startup at `p = F.k`**: `exists_interpreterStartup (fun α => F.numStates (F.decode α))
     (fun α => F.machine (F.decode α)) C entry exit cost hk (fun x α => by rw [← serializeK_eq];
     exact inst x α) F.k`, as gate 79's consumer probe does (`b5aP_startup`,""",
 """   - `us_install` (the route probe's `b5a_install`; copy it): one module `C` with states
     `entryI`, `exitI`, constants `a`, `d₀` and `0 < C.k`, uniform in the code;
   - **the startup at `p = F.k`**: `exists_interpreterStartup (fun α => F.numStates (F.decode α))
     (fun α => F.machine (F.decode α)) C entryI exitI cost hk (fun x α => by
     rw [← serializeK_eq]; exact inst x α) F.k`, with `cost := fun α => a * ((α.length + 1) ^ d₀ +
     α.length + max α.length (F.serialize F.fallback).length + 1)` (`us_install`'s bound), as
     gate 79's consumer probe does (`b5aP_startup`,"""),
# F6: route step 3, the let and the copy list
("""   `done` and the threshold fields (destructure the conclusion's `let` by `dsimp only`). Then
   `us_run` (the junction probe's `b5a_run`; copy it with `us_junction`, `us_tail`, `us_start`
   and `us_window_verdict`): `S` halts from `S.tm.initCfg z` at `T₁ + 1 + T₂` with output""",
 """   `done` and the threshold fields (`obtain` destructures the conclusion through its `let`, as
   gate 79's consumer probe does). Then `us_run` (the junction probe's `b5a_run`; copy it with
   `us_junction`, `us_tail`, `us_start`, `us_window_verdict` and `us_locality`): `S` halts from
   `S.tm.initCfg z` at `T₁ + 1 + T₂` with output"""),
# F6: route step 4, names and the closed form
("""     `|tableBitsK M.tr| ≤ max |α| L₀` (`b5a_table_le`): `O(N^2)`;
   - so `T₁ + 1 + T₂ ≤ c · N^e` with `c`, `e` depending on `F` only. Take `d ≥ c` and `d ≥ e`,
     and close with `ComputesInTime.mono`.""",
 """     `|tableBitsK M.tr| ≤ max |α| L₀` (`us_table_le`, the route probe's `b5a_table_le`):
     `O(N^2)`;
   - so `T₁ + 1 + T₂ ≤ c · N^e` with `c`, `e` depending on `F` only. Take `d ≥ c` and `d ≥ e`
     (`c · N^e ≤ d · N^d`, as `N ≥ 1`); `us_verdict` applies `ComputesInTime.mono`. One closed
     form that works: `e = d₀ + 2`, `c = a (L₀ + 4) + A (L₀ + 3) + 3B + 50 L₀ + 110` and
     `d = c + e`; every term is at most a constant times `N^e`, as `|α| + 1 ≤ N`, `N ≤ N^e`,
     `N · N ≤ N^e`, `1 ≤ N^e` and `max |α| L₀ ≤ |α| + L₀`."""),
# F2e: the H1 harvest gate's guidance
("""- **The H1 harvest gate** (`campaign/gates/20-h1-harvest-statements/`): cite the hosted loop and
  its reading lemma as stated.""",
 """- **The H1 harvest gate** (`campaign/gates/20-h1-harvest-statements/`): the hosted loop and its
  reading lemma are cited, as stated, inside `h1HostedVerdict_accepts`; you cite that."""),
# F2f: the cited-infrastructure summary
("""restart; the model's run algebra and field equations. In your file you also cite the canonizer,""",
 """restart; the model's run algebra and field equations. Its sections marked "context only" (the
startup's phases, the kit's and the phase host's rows, H1's step reader, host and clock) list
what the cited contracts compose: never cite them. In your file you also cite the canonizer,"""),
# F7: rule 10's reading list
("""file's definition reduces counts as unfolding. Read `vhostCfg` and `counterLoopCfg` only
      through their field equations and `counter_cfg_eq`; `embedEmitCfg` through its field equations
      and `embedEmitCfg_eq`; `Cfg.init` and `Cfg.mapState` through theirs; `Cfg.ofWords` and
      `stateWord` through theirs; `serializeK` through `serializeK_eq`; `MultiTapeTM.toNDTM` through
      `toNDTM_runWith` and `toNDTM_initCfg`; `StepBlock.Rep` through `StepBlock.Rep_iff`.""",
 """file's definition reduces counts as unfolding. Read `vhostCfg` only through its field
      equations and `counterLoopCfg` through `counter_cfg_eq`; `embedEmitCfg` through its field
      equations and `embedEmitCfg_eq`; `Cfg.init` and `Cfg.mapState` through theirs; `Cfg.ofWords`
      and `stateWord` through theirs; `serializeK` through `serializeK_eq`; `MultiTapeTM.toNDTM`
      through `toNDTM_runWith` and `toNDTM_initCfg`; `MultiTapeTM.initCfg` through `initCfg_eq`
      and `initCfg_with_q₀`; `StepBlock.Rep` through `StepBlock.Rep_iff`, and `tableTape`,
      `summaryTape`, `outputSummary` through `tableTape_eq`, `summaryTape_eq`, `outputSummary_nil`;
      `FinTM.ComputesInTime` through `computesInTime_iff` and `ComputesInTime.mono`; the seam and
      the embedding through `seamCompTM_runFrom_right` and `embedEmitTM_runFrom`."""),
("""      leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.""",
 """      leaf defined in your own file."""),
("""        other-file TCSlib definition your new proofs mention (start from the union of the pre-ship
        probes' seals and extend by every one you reach), and `attribute [-simp]` on the `@[simp]`""",
 """        other-file TCSlib definition your new proofs mention (start from the union of the pre-ship
        probes' seals, 28 definitions: `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`,
        `MultiTapeTM.ComputesInTimeAndSpace`, `Cfg.ofWords`, `stateWord`, `MultiTapeTM.toNDTM`,
        `NDTM.runWith`, `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `NDTM.initCfg`,
        `CodeFormat.decode`, `vhostCfg`, `counterLoopCfg`, `FinTM.bufferTape`, `tableBitsK`,
        `Cfg.init`, `Cfg.mapState`, `embedEmitCfg`, `embedEmitTM`, `seamCompTM`,
        `StepBlock.summaryCells`, `StepBlock.Rep`, `StepBlock.tableTape`, `StepBlock.summaryTape`,
        `StepBlock.exit`, `StepBlock.outputSummary`, `unaryFin`, `pairEncode`; their controls are
        the two seal-control files'; extend by every one you reach), and `attribute [-simp]` on
        the `@[simp]`"""),
# F2d: the population's description
("""  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  route's new imports (`Build/InputRewind`, `Build/Rewind`, `Build/InputWindow`,
  `Build/SeamLayout`, `BufferWords`, `Nondeterministic`), the two model files whose lemmas the
  route reads (`Configuration`, `StateRenaming`), the kit's module, and the remaining""",
 """  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  six modules of the earlier six-import route (`Build/InputRewind`, `Build/Rewind`,
  `Build/InputWindow`, `Build/SeamLayout`, `BufferWords`, `Nondeterministic`; all in your two
  imports' closure), the two model files whose lemmas the route reads (`Configuration`,
  `StateRenaming`), the startup's module (`Build/InterpreterStartup`), and the remaining"""),
# F4: hazards
("""  - the start identity: `UniversalK`'s `ss_captureInitial` and `ExhaustiveReplay`'s `xr_E_initCfg`
    (the `initCfg_with_q₀` idiom);""",
 """  - the start identity and the run after a seam into an embedding: `UniversalK`'s
    `ss_captureInitial`, `uk_init_mapState` and `uk_loop_run`, `ExhaustiveReplay`'s
    `xr_E_initCfg` and `NTimeHierarchy`'s `un_setup` (its start) (the `initCfg_with_q₀` and
    `seamCompTM_runFrom_right` idioms);"""),
("""    pairs; the junction probe's lemmas pair with them at 54–64%: disclose, do not factor; at 90%
    or more stop and escalate).""",
 """    pairs; the junction probe's lemmas pair with them at 54–64%, measured against `CfgRecord`,
    `SeamLayout` and `InputRewind` ⟨and against the whole population, at issue⟩: disclose, do not
    factor; at 90% or more stop and escalate)."""),
# F2g: the REPORT checklist
("""- [ ] Every new declaration with its role; the tapes chosen for each phase; the status paragraph,""",
 """- [ ] Every new declaration with its role; the tape map `g` (`us_bank` on the startup's roles);
      the status paragraph,"""),
("""- [ ] The ledger, phase by phase, and the final `d`.""",
 """- [ ] The ledger (the startup, the dispatch step, the verdict) and the final `d`."""),
# F6: the let pitfall
("""- **The startup's conclusion ends in a `let`** (`let c := U.runFrom … T`): destructure it after
  `dsimp only at h`, and keep the start configuration's type ascription
  (`Cfg K Bool Q (pairEncode (pairEncode (Nat.bits t) α) x)`), or the input is not found.""",
 """- **The startup's conclusion ends in a `let`** (`let c := U.runFrom … T`): `obtain` destructures
  through it (gate 79's consumer probe). If you restate the start, keep the start configuration's
  type ascription (`Cfg K Bool Q (pairEncode (pairEncode (Nat.bits t) α) x)`), or the input is
  not found. The passive clause comes out as `tapes₀ (ιP i)`, which is `fun _ => none` up to
  beta: pass it to `us_run` as it is."""),
],
IMPORT: [
("""A standalone import of the owned module and of the two imports the brief authorizes; every
public declaration the route cites must resolve. -/""",
 """A standalone import of the owned module and of the two imports the brief authorizes; every
public declaration the route cites must resolve. The sections marked "context only" list the rows
that the cited contracts (the startup, H1's verdict) compose: the route does not cite them. -/"""),
("""-- the header passes\n""", """-- context only (the startup's phases): the header passes\n"""),
("""-- the rewinds and the counter copy\n""",
 """-- context only (the startup's phases): the rewinds and the counter copy\n"""),
("""-- the window, and input locality for a deterministic machine\n""",
 """-- the window (context only: the startup's), and input locality for a deterministic machine\n"""),
("""-- the install and the layout\n""",
 """-- the install call (cited by `us_install`), and the layout (context only: the startup's)\n"""),
("""-- at issue (after #162): the startup kit's eight lemmas, the phase host's four, and the
-- route's step reader, virtual host and clock""",
 """-- context only: the startup kit's eight lemmas and the phase host's four (the startup's own
-- citations), and the step reader, virtual host and clock (cited inside H1's landed lemmas)"""),
],
CLASH: [
("""/-! Review probe (Q-B2): the five new imports together with every module downstream of""",
 """/-! Review probe (Q-B2): the two imports together with every module downstream of"""),
],
}

for rel, edits in EDITS.items():
    src = open(os.path.join(ORIG, rel), encoding='utf-8').read()
    for old, new in edits:
        n = src.count(old)
        assert n == 1, (rel, n, old[:80])
        src = src.replace(old, new)
    out = os.path.join(EDIT, rel)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, 'w', encoding='utf-8').write(src)
    print(rel, len(edits), 'edits')
