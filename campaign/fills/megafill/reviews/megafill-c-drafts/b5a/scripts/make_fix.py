"""Apply the review's text fixes to the B5a draft (every replacement asserted: exactly one hit)."""
import sys
src, dst = sys.argv[1], sys.argv[2]
t = open(src, encoding='utf-8').read()
E = []
def rep(old, new):
    n = t.count(old)
    assert n == 1, (n, old[:80])
    E.append((old, new))
def apply():
    global t
    for old, new in E:
        assert t.count(old) == 1, old[:80]
        t = t.replace(old, new)

# F2 / out/17: the issue base
rep('''below are the two outcomes; keep one at issue. Other issue-time items: @ANCESTOR@, ⟨BASE⟩,
⟨IN-FLIGHT⟩, the megafill banner, and re-running the pre-ship at the issue commit. -->''',
'''below are the two outcomes; keep one at issue. Other issue-time items: @ANCESTOR@, ⟨BASE⟩,
⟨IN-FLIGHT⟩, the megafill banner, and re-running the pre-ship at the issue commit.
**Issue base (review, 2026-10-24):** after #156 (whose round-2 head `0e5f210b` edits this file's
`canonEmitVerdict`, 4593–4603) and the follow-up phase-host API PR (user, 2026-10-24; it edits
`canonEmitVerdict` again), and, under ⟨Q-B1: A⟩, the startup kit's API PR. Regenerate the overlay
and every line number, count, blob and screen figure there; the numbers below are the drafting
base's. -->''')

# F1: the kit, published (names)
rep('''  - ⟨Q-B1: A⟩ **the startup kit, published** (⟨its PR⟩): the header passes, the returning
    capture, the seam step, the install phase, the window call and the layout call, harvested
    from `NDCodeSimulator`'s privates into ⟨its module⟩;''',
'''  - ⟨Q-B1: A⟩ **the startup kit, published** (⟨its PR⟩, ⟨its module⟩): `Turing.seamCompTM_step`,
    `Turing.prefixCanon_pairExtract_halt`, `Turing.embedSilentRetTM_firstReturn`,
    `Turing.headerCapture_run`, `Turing.exists_windowCall`, `Turing.installCall_releasePhase`,
    `Turing.exists_layoutCall` (stated over `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`)
    and `Turing.embedSilentCfg_initCfg`, harvested from `NDCodeSimulator`'s startup privates and
    `UniversalK`'s `ss_captureInitial`;
  - **the phase host's last phase** (PR #156, gate 69) and its start-state and redirect-branch
    equations (the follow-up API PR): `Turing.phaseHostTM_tr_of_red_none`,
    `Turing.phaseHostTM_run_le`, ⟨the follow-up's two equations⟩. Both PRs edit your file's
    `canonEmitVerdict` (not yours);''')

# F2: in flight
rep('''- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #156,
  `Build/Seam`'s last-phase lemmas `phaseHostTM_tr_of_red_none` and `phaseHostTM_run_le`, gate 69
  pending: **not citable**; #135, chapter 7 onto `main`); on their own branches in this session,
  the other megafill items, among them **C1** (`NDCodeSimulator`, downstream of your file) and
  **U2** (`UniversalK`, downstream of your file). Cite nothing they add.''',
'''- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #135,
  chapter 7 onto `main`; #156 and the follow-up phase-host API PR are in your base, above); on
  their own branches in this session, the other megafill items, among them **C1**
  (`NDCodeSimulator`, downstream of your file) and **U2** (`UniversalK`, downstream of your file).
  Cite nothing they add.''')

# F7: frozen-text line ranges
rep('''**The statement and the docstring's statement and sketch, frozen verbatim** (lines 8554–8580 and
8656–8664; the fill appendices 8582–8654 and the `-/` at 8655 are frozen byte for byte too):''',
'''**The statement and the docstring's statement and sketch, frozen verbatim** (lines 8554–8582 and
8656–8664; the fill appendices 8584–8653 and the `-/` alone on 8655 are frozen byte for byte too):''')

# pre-ship: probe extension and seal
rep('''- **The import probe** (`B5aUSImportProbe.lean.txt`, a standalone import of your module and the
  five, **109 checks of 109 names**, and eight axiom prints): 0 errors, 0 warnings. Every row the
  route composes is on the standard three axioms (the input rewind on two). **Re-run it after
  your delivery**, extended by every further name you cite.''',
'''- **The import probe** (`B5aUSImportProbe.lean.txt`, a standalone import of your module and the
  five, **109 checks of 109 names**, and eight axiom prints): 0 errors, 0 warnings. Every row the
  route composes is on the standard three axioms (the input rewind on two). The review's
  extension (137 names: the start's `MultiTapeTM.initCfg_with_q₀` and `runFrom_with_q₀`, the
  `Cfg.init` fields, `stateWord_eq`, `seamReleaseTM_runFrom_pos`, R1's frame and field
  equations, and the definitions the route names) is the probe at issue ⟨Q-B1: A⟩ (with the
  kit's eight names). **Re-run it after your delivery**, extended by every further name you cite.''')
rep('''  clauses) and `b5a_table_le` (`|tableBitsK| ≤ max |α| |F.serialize F.fallback|`).''',
'''  clauses) and `b5a_table_le` (`|tableBitsK| ≤ max |α| |F.serialize F.fallback|`). The review
  re-ran all five as `us_` privates at your home (region (b)), also sealing `tableBitsK`,
  `pairEncode` and `unaryFin`, which `b5a_table_le` touches: still clean.''')

# F7: region (d)
rep('''- **(d) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its closing ` -/` (line 8655). It is public-facing library text: what''',
'''- **(d) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its `-/` (alone on 8655). It is public-facing library text: what''')
rep('''- [ ] Every new declaration with its role; the tapes chosen for each phase; the status paragraph,
      if a partial.''',
'''- [ ] Every new declaration with its role; the tapes chosen for each phase; the status paragraph,
      if a partial; for a complete delivery, a proposed `**Implementation.**` paragraph for the
      target's docstring (public-facing; the maintainer edits it in at integration).''')

# F6: hosts
rep('''- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamCompTM_runFrom_left`/`_right`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`), the phase host (`phaseHostTM`, `phaseHostTM_run`), R1 and R1′
  embeddings (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq` for the emitting verdict;
  `embedSilentTM`, `embedSilentRetTM`, `embedSilentRetTM_run` for the silent phases).''',
'''- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamCompTM_runFrom_left`/`_right`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`, `seamReleaseTM_runFrom_pos`; ⟨Q-B1: A⟩ `seamCompTM_step`), R1 and
  R1′ embeddings (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq` for the emitting
  verdict; `embedSilentTM`, `embedSilentRetTM`, `embedSilentRetTM_run` for the silent phases).
- **The phase host** is not needed: seams join every phase. If you host a phase in
  `phaseHostTM`, read it only through `phaseHostTM_run`, `phaseHostTM_run_le`,
  `phaseHostTM_tr_of_red_none` and the follow-up API PR's two equations.''')
rep('''  `FinTM.exists_installCallTM`; the layout `exists_seamLayoutTM`. **Never write a private input
  rewind** (IR-1 is being retired; `Turing.inputRewindTM` is the published one).''',
'''  `FinTM.exists_installCallTM`; the layout `exists_seamLayoutTM`. **Never write a private input
  rewind** (IR-1 is being retired; `Turing.inputRewindTM` is the published one). ⟨Q-B1: A⟩ Through
  the published kit: `headerCapture_run` (both passes), `exists_windowCall`,
  `installCall_releasePhase`, `exists_layoutCall`, `embedSilentCfg_initCfg`: cite them, never
  re-prove them.''')

# F3: the start
rep('''0. **The first edit**: the five imports (region (a)).''',
'''0. **The first edit**: the five imports (region (a)).
   **The start.** `S.tm` is your seam composite `W` restarted at its first phase's initial
   state (`{ W with q₀ := q }`, `q` the nested `Sum.inl` of the first pass's `q₀`), read only
   through `MultiTapeTM.initCfg_with_q₀` and `MultiTapeTM.runFrom_with_q₀`: no lemma publishes
   `seamCompTM`'s or `embedSilentRetTM`'s `q₀`, so never read them by `rfl`, `show` or `simp`.
   `Cfg.init` at the nested state is the first phase's transported start by ⟨Q-B1: A⟩
   `embedSilentCfg_initCfg` ⟨Q-B1: B⟩ a `us_` copy of `UniversalK`'s `ss_captureInitial` (a
   pre-disclosed pair), and a relabelling of `Cfg.init` from the `Cfg.init_*` and
   `Cfg.mapState_*` field equations (U2-S's `ss_capture_run` is the pattern).''')

# F1: route steps 2-3
rep('''   - **the window** by `exists_inputWindowCopyTM` from the suffix: `x.take t` on a blank tape,
     the counter consumed, cost `C · (min t |x| + 1) + 2 |bits t|`;''',
'''   - **the window** by `exists_inputWindowCopyTM` from the suffix (⟨Q-B1: A⟩ through
     `exists_windowCall`): `x.take t` on a blank tape, the counter consumed, cost
     `C · (min t |x| + 1) + 2 |bits t|`;''')
rep('''     tape and the rest blank, which is exactly `Cfg.ofWords … (stateWord C.k α)`, behind
     `seamReleaseTM` for the positive first return (the core's install phase is the pattern);''',
'''     tape and the rest blank, which is exactly `Cfg.ofWords … (stateWord C.k α)`, behind
     `seamReleaseTM` for the positive first return (⟨Q-B1: A⟩ `installCall_releasePhase`
     ⟨Q-B1: B⟩ the core's install phase is the pattern);''')
rep('''   - **the layout** by `exists_seamLayoutTM` (`src` the installed tape, three distinct tapes):
     the table tape `FinTM.bufferTape (tableBitsK M.tr)`, the summary tape''',
'''   - **the layout** by `exists_seamLayoutTM` (⟨Q-B1: A⟩ through `exists_layoutCall`, its source
     word rewritten by `simp only [← serializeK_eq]`; `src` the installed tape, three distinct
     tapes): the table tape `FinTM.bufferTape (tableBitsK M.tr)`, the summary tape''')

# F10: do not copy
rep('''install call, whose bound is polynomial (`b5a_install`). **Do not copy** `NDCodeSimulator`'s
privates, `UniversalK`'s `ss_` startup or `Diagonalization/NTimeHierarchy`'s `un_` setup.''',
'''install call, whose bound is polynomial (`b5a_install`). **Do not copy** `UniversalK`'s `ss_`
startup or `Diagonalization/NTimeHierarchy`'s `un_` setup; ⟨Q-B1: A⟩ nor `NDCodeSimulator`'s
privates (they are the published kit) ⟨Q-B1: B⟩ re-prove the eight startup facts as `us_`
privates, their pairs pre-disclosed (Duplication).''')

# gate 46 path
rep('''- **The seam layout's gate** (46): its time is chosen before the configuration; cite it as
  stated.''',
'''- **The seam layout's gate** (gate 46: `campaign/gates/43-seam-layout-statements/`, round 2):
  its time is chosen before the configuration; cite it as stated.''')

# F4/F11/F12: population, screen, hazards
rep('''- **The population** is 54 files
  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  route's new imports (`Build/InputRewind`, `Build/Rewind`, `Build/InputWindow`,
  `Build/SeamLayout`, `BufferWords`, `Nondeterministic`), and the remaining hazards:
  `Diagonalization/NTimeHierarchy` (UN's setup), `UniversalK` (U2-S's startup) and''',
'''- **The population** is 56 files (⟨Q-B1: A⟩ 57)
  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  route's new imports (`Build/InputRewind`, `Build/Rewind`, `Build/InputWindow`,
  `Build/SeamLayout`, `BufferWords`, `Nondeterministic`), the two model files whose lemmas the
  route reads (`Configuration`, `StateRenaming`), ⟨Q-B1: A⟩ the kit's module, and the remaining
  hazards: `Diagonalization/NTimeHierarchy` (UN's setup), `UniversalK` (U2-S's startup) and''')
rep('''- **The screen is long:** start the before run in the background right after your first edit (it
  may run beside the one Lean process, never beside another screen), and the after run as soon as
  the owned file is final.''',
'''- **The screen is long:** start the before run in the background right after your first edit (it
  may run beside the one Lean process, never beside another screen), and the after run as soon as
  the owned file is final. Run each on a frozen copy of its commit (`git worktree add <dir> HEAD`,
  the screen's root `<dir>`), so that later edits cannot race its reads. Expect the after run to
  be longer than the before run: your target's body, `sorry` at the base and so not screened,
  becomes one of the largest screened declarations.''')
rep('''- **Known hazards** (a proof reproducing one at 90% or more must be factored):''',
'''- **Known hazards** (a proof reproducing one at 90% or more must be factored if both sides are
  yours; if the other side is another file's, stop on that item and escalate):''')
rep('''  - UN's setup (`un_step`, `un_step'`, `un_canon_halt`, `un_setup`) and U2-S's startup
    (`ss_capturedPrefix_run`, `ss_capture_run`, `ss_serialized_layout`), the other header passes;''',
'''  - UN's setup (`un_step`, which is `ic_seam_step`'s statement, `un_step'`, `un_canon_halt`,
    `un_setup`) and U2-S's startup (`ss_capturedPrefix_run`, `ss_capture_run`,
    `ss_serialized_layout`), the other header passes;
  - the start identity: `UniversalK`'s `ss_captureInitial` and `ExhaustiveReplay`'s `xr_E_initCfg`
    (the `initCfg_with_q₀` idiom);
  - **the core's startup assembly** (`exists_ndInterpreterCore`'s body, lines 924–1990 at the
    drafting base): your target's body will be compared with it. ⟨D-3: the user's ruling⟩ A pair
    below 90% is pre-disclosed: list it with its shared fragments; at 90% or more stop and
    escalate;''')

# F9: pitfalls
rep('''- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.''',
'''- **`S` starts from `S.tm.initCfg`**, unlike the core's explicit start: see the route's start
  (`initCfg_with_q₀`, `runFrom_with_q₀`); the composite's `q₀` has no other published equation.
- **H1's proofs predate rule 10**: `h1HostedVerdict_effect` passes `MultiTapeTM.initCfg`,
  `Cfg.init`, `FinTM.VirtualTag`, `Action.apply` and `vhostCfg` to `simp` and unfolds
  `MultiTapeTM.step` (8499–8528). Cite it; do not imitate its proof text.
- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.''')

# F14: axiom prints, lint
rep('''- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for the target, every new
  private (in an in-module probe), `exists_polyCanonizer`, targets 3–8 and
  `Complexity.baker_gill_solovay`. For a complete delivery none has `sorryAx` from your file.''',
'''- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for the target, every new
  private (in an in-module probe), `exists_polyCanonizer`, targets 3–8 and
  `Complexity.baker_gill_solovay`. At the base the target is the only admission of targets 3–8
  and Baker–Gill–Solovay (the review's admission walk), so for a complete delivery all of them
  print within the standard three.''')
rep('''  and `TCSlib/Complexity/Diagonalization`, 0 FAIL. Add no line over 100 characters and no Lean
  linter warning in your region.''',
'''  and `TCSlib/Complexity/Diagonalization` (base: 0 FAIL, 2 WARN over 5 files), 0 FAIL. Add no
  line over 100 characters and no Lean linter warning in your region.''')

# the B outcome's pre-disclosure covers the start identity too
rep('''- **No new cross-file pair** with an owned-file declaration on one side ⟨Q-B1: B⟩ **except the
  startup pieces' pairs with `NDCodeSimulator`, pre-disclosed by the user's ruling Q-B1**: list
  each with its shared text; at 90% or more it is a copy, ledgered under the ruling.''',
'''- **No new cross-file pair** with an owned-file declaration on one side ⟨Q-B1: B⟩ **except the
  startup pieces' pairs with `NDCodeSimulator` and the start identity's with `UniversalK`,
  pre-disclosed by the user's ruling Q-B1**: list each with its shared text; at 90% or more it is
  a copy, ledgered under the ruling.''')

apply()
open(dst, 'w', encoding='utf-8').write(t)
print('edits', len(E))
