# External audit pack — the phase host's field equations (PR #159, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, the machine library (`machine-library-design.md`
§12.8, the phase host).
- **Why:** gate 69 (#156, merged) published the phase host's table off the redirects
  (`Turing.phaseHostTM_tr_of_red_none`) and its last-phase run lemma. Its round-1 seal sweep
  (`campaign/gates/69-phasehost-last-api/evidence/round1-fix/phasehost-reads-inventory.md`, with
  `sweep/` and `residue.txt`) found 12 older proofs in seven other files that still read
  `Turing.phaseHostTM` through its definition: its start state, its redirect branch's dispatch,
  single table reads, and `NDHost`'s `phaseHostND_fixChoice`. Rule 10 forbids that in another
  file. **The user ruled (2026-10-24): a follow-up API PR** publishing a start-state and a
  redirect-branch equation beside `phaseHostTM`, and re-pointing the 12 reads, with its own gate
  and replay.
- **The head:** `lean/phasehost-fields` at `5e881c42`, two commits on the campaign branch at
  `21d53053` (after #156): `ef3440ee`, the two equations in `Build/Seam` with one header sentence;
  `5e881c42`, the re-points (`evidence/phasehost-fields.patch`). This bundle's Lean files are from
  `5e881c42`, and its records from the records commit that the dispatch prompt names.

| File | Change |
|---|---|
| `TuringMachine/Build/Seam` | **`Turing.phaseHostTM_q₀`**: `(phaseHostTM M q0 red).q₀ = q0`, by `rfl` (the definition is this file's); **`Turing.phaseHostTM_tr_of_red_some`**: for `red i s = some q'`, `(phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ⟨0, fun _ => (none, 0), none, some q'⟩`, by `simp only [phaseHostTM, hs]`; the header names them |
| `SpaceComplexity/Inclusions` | `b2b_setup_capture`: `hinit` through `MultiTapeTM.initCfg_eq` and `phaseHostTM_q₀`; the goal is rewritten by `hinit` before its two parts, so the start is no longer matched by definition |
| `TuringMachine/Build/NDHost` | `phaseHostND_fixChoice` (public; statement unchanged): from `rfl` to a proof by its two fields, through `NDTM.fixChoice_q₀`/`_tr`, `phaseHostTM_q₀` and the two table equations, and structure eta |
| `TuringMachine/Build/OracleSim` | `oracleHost_initial`: the host's start state through `phaseHostTM_q₀` before its `change` |
| `TuringMachine/Build/StepBlock` | `seekTM_request` (the redirect's dispatch; the skipper's start state through `phaseHostTM_q₀` in the `simp` set, where `phaseHostTM` was), `seekTM_observe` (two router reads), `seekTM_stateStep` (`phaseHostTM_tr_of_red_none` in the `simp` set, where `phaseHostTM` was), `roundTM_lookup` (the seek host's start state), `roundTM_canonical` (the entry's dispatch) |
| `TuringMachine/Build/StepBlockForward` | `fl_hosted_leaf` (the leaf's table), `fl_return` (the return anchor's dispatch) |
| `TuringMachine/Build/WindowRun` | `wl_stop_fixed`: the stop phase's table through `phaseHostTM_tr_of_red_none` in its `simp only`, where `phaseHostTM` was |
| `TuringMachine/CodeSimulator` | `canonEmitVerdict`: the host's start state through `phaseHostTM_q₀` before its `change` |

## Brief for the auditor

1. **Faithfulness.** Is `phaseHostTM_q₀` the host's start state, and is `phaseHostTM_tr_of_red_some`
   exactly the host's action at a redirected state (stationary input head, no work-tape write or
   move, no output, successor `q'`)? Are the docstrings exact readings? Together with
   `phaseHostTM_tr_of_red_none`, do they determine the host completely (the
   `phaseHostND_fixChoice` proof is the test)?
2. **The re-points.** Is each of the 12 reads of the inventory now through a published equation,
   with its statement unchanged and its uses downstream unaffected? Is any read of the inventory
   missed, or any new one introduced?
3. **Rule 10.** Every changed file elaborates with `attribute [local irreducible] Turing.phaseHostTM`
   after its imports, with 0 errors (`evidence/fields/*Sealed.out`); the same seal at the base found
   the inventory's errors; the control (`PHFSealControl`) closes unsealed and fails sealed. No
   `simp`/`rw`/`unfold` outside `Build/Seam` names `phaseHostTM` (`evidence/residue.txt`).
   **Scope, disclosed:** the PR removes the reads of `phaseHostTM` only. The changed proofs still
   close older steps through other files' definitions (`Cfg.mapState`, `Cfg.init`,
   `Action.mapState`, `MultiTapeTM.step`, `inputMoveAction`, `tapeAction`, by `rfl` or in `simp`
   sets), as before; that older debt is outside the ruling. Is anything newly introduced?
4. **The stand-in method.** No olean snapshot has the new `Seam` yet, so each changed file was
   checked as a copy with the two new lemmas' exact text inserted after its imports
   (`evidence/fields/mkstandin.py`; the copies' lines are the source's plus 18, or 20 sealed).
   `Seam` itself elaborates with the two lemmas, its five older unused-variable warnings only.
   Is that a faithful check of the head? The replay compiles the real tree.
5. **Duplication.** The ten-file screen (`Seam`, the seven changed files, `Contract/Basic` and
   `InputDevice`) at the base and the head: does any new or gone pair, or any private
   restatement of the new equations, exist (`evidence/screen-*`, `pairdiff-*`)?
6. **No collateral change:** per file, the freeze (`evidence/freeze/`): public 24 → 26 in `Seam`
   (the two added) and unchanged elsewhere; private counts unchanged; only the 12 named bodies
   changed; no statement changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lphl2`, the campaign's tree after #156): `Seam` at the head
  with its five older warnings; the seven files' stand-in copies with their base diagnostics only
  (none, except `OracleSim`'s one linter warning and `CodeSimulator`'s sorry warning), plain and
  sealed (`evidence/fields/`).
- **Axioms** (each stand-in copy and each base file with `#print axioms` for its public theorems,
  lemmas and definitions appended, `mkax.py`): per name identical at the base and the head except
  `Turing.NDTM.phaseHostND_fixChoice`, from no axioms (`rfl`) to `[propext, Quot.sound]` (`funext`
  and `simp`), within the standard three; `phaseHostTM_q₀` on none, `phaseHostTM_tr_of_red_some` on
  `[propext]`; no new `sorryAx` (`evidence/axioms/`).
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 83 files; `SpaceComplexity` 0 FAIL, 81 WARN over
  107 files, both as at the base; no added line over 100 characters.
- **Screen** (v3, the ten files): at the base `21d53053`, 594 declarations, 140 pairs, 75,942
  characters; at the head, 595, 140 and 75,942; no pair new or gone (`evidence/pairdiff-head.txt`).
- **Replay:** `replay-lphf.sh`: the eight changed files' downstream closure (88 modules,
  `down-lphf.txt`, the same set as #156's first replay) at `5e881c42`, chained from `oleans-lphl2`.
  **Pending:** as for gates 64–70, this gate is dispatched before the replay; the PR is clear to
  merge only when both have passed. If #158 (F3's landing, `WindowClock`, inside this closure)
  merges first, the campaign is merged in and `WindowClock`'s closure replays on the merged tree.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/71-phasehost-fields-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `phasehost-fields-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
