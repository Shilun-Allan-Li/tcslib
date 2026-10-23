# External audit pack — the input rewind as a machine (PR #153, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the timed universal NDTM behind the
nondeterministic time hierarchy, [AB09, Theorem 3.2]).
- **Why:** megafill A's UN continuation 1 (`Diagonalization/NTimeHierarchy`) wrote its own input
  rewind, `un_inRewTM` with `un_inRew_run`, and a relabeling collapse, `un_mapState_comp`. Its
  review (`campaign/fills/c1/reviews/universal-cont1/REVIEW.md`, F3) found two new cross-file
  pairs, which the UN brief forbids: with `ClassNP/ExhaustiveReplay`'s `xr_inRewindTM` (61% and
  59%) and with its `xr_E_initCfg` (54%). The ledger records the whole family as IR-1
  (`campaign/duplication-ledger.md`). **The user ruled (2026-10-22): an API PR first**, with a
  public input rewind that has an exact time and a first-visit cut, and a `mapState` collapse.
  UN's landing re-points to them. **Its home (user, 2026-10-22): a new small module,
  `Build/InputRewind`.**
- **Found while building it:** `Build/NDHost`'s private `guessRun_mapState_mapState` had exactly
  the new lemma's statement, and its proof unfolded `Cfg.mapState` (`StateRenaming`'s
  definition). **The user ruled (2026-10-22): re-point it in this PR.**
- **The head:** `lean/input-rewind-api` at ⟨HEAD⟩: the commit `ac5ce7bc` on the campaign branch
  at `86523ba5`, then ⟨MERGE: a merge of the campaign branch after #149⟩. Its Lean diff from the
  merge-base is exactly the three files below (`evidence/input-rewind-api.patch`). This bundle's
  records are from a later records commit (stated in the bundle's README).

| File | Change |
|---|---|
| `TuringMachine/Build/InputRewind` (new, 200 lines) | `Turing.InputRewindPhase` (`start`, `scan`, `done`); `Turing.inputRewindTM k`; **`Turing.inputRewindTM_run`**: from `d` with `d.state = some .start` and `1 ≤ d.inputPos.val`, `runFrom d (p + 1) = {d with state := some .done, inputPos := 1}`, `∀ t < p + 1, state ≠ some .done`, and `∀ t ≤ p + 1` the work tapes, work heads and output are `d`'s (`p = d.inputPos.val`); **`Turing.inputRewindTM_step_done`**: the park is a fixed point of `step`; **`Turing.Cfg.mapState_mapState`**: `(c.mapState f).mapState g = c.mapState (g ∘ f)` |
| `TuringMachine/Build/NDHost` | the private `guessRun_mapState_mapState` removed; its three `rw` sites (in `guessRunTM_runWith_handoff`) rewrite with `Cfg.mapState_mapState`; the new import |
| `TuringMachine` (facade) | the new import and its `## Contents` entry |

- **Evidence:** `evidence/`:
  - `input-rewind-api.patch`, `pr-body.md`;
  - against `oleans-lu2sc1` (no snapshot holds the base tree; see the replay below):
    `elab-InputRewind.out` (the module, empty); `InputRewindAx.lean.txt`/`.out` (the module with
    `#print axioms`); `NDHostCat.lean.txt` with `elab-NDHostCat.out` (empty). No snapshot has an
    olean for the new import, so this file holds the new module's text and then NDHost's, with
    their imports merged;
  - **the seal:** `InputRewindSeal.lean.txt`/`.out`. These are primed copies of the module's text
    with `MultiTapeTM.step`, `MultiTapeTM.runFrom`, `FinTM.controlAction`, `moveInputPos`,
    `Cfg.inputSymbol`, `Cfg.mapState` and `Action.apply` locally irreducible, plus 7 `rfl`
    controls, sealed and unsealed. `InputRewindSealSimp.lean.txt`/`.out` is the same with the two
    `@[simp]` definitions among them (`Action.apply`, `Cfg.init`) also erased from the simp set;
  - **the consumer probe:** `InputRewindConsumer.lean.txt`/`.out` and its sealed form
    `InputRewindConsumerSealed.lean.txt`/`.out`. They restate UN's `un_mapState_comp` and UN's
    phase-8 run (`hs8`, in its exact form over UN's phase-7 endpoint) and prove both from the
    public API alone;
  - `freeze-NDHost.txt`, `freeze-TuringMachine.txt`; `lint-build.txt`;
  - the v3 screen: `screen-population.txt` and `screen-population-base.txt`, `screen-head.txt` and
    `screen-base.txt`, the `.status` files, and `screen-pairdiff.txt`;
  - the replay's script, list (`down-lirapi.txt`), log and static check.
- **The bundle** also contains the three files at the head; `Simulation` (`FinTM.controlAction`,
  `FinTM.rewind_scan`); `StateRenaming` (`Cfg.mapState` and its field equations); `Configuration`;
  `Build/Rewind` (the work-tape rewind it is modelled on); the IR-1 members, namely
  `ClassNP/ExhaustiveReplay`, UN's delivered `NTimeHierarchy`, and #151's `NDCodeSimulator`
  (`ic_rewindLeafTM`, `ic_rewind_leaf_run`); and UN's review.

## Brief for the auditor

1. **Faithfulness.** Is `inputRewindTM` the machine the docstrings describe, and is
   `inputRewindTM_run` true and stated with the right quantifiers? Check the exact time `p + 1`;
   the cut (every `t < p + 1`); the endpoint `{d with state := some .done, inputPos := 1}`; and
   the fixed fields at every `t ≤ p + 1`. Check the boundary cases: the empty input; `p = 1`;
   the head on the right blank, `p = |x| + 1`; and `k = 0`. The hypothesis `1 ≤ p` is needed: at
   `p = 0` the first left step stays at `0`, and the park is reached at `p + 2`. Is it stated
   where a consumer can discharge it? Are the docstrings exact readings?
2. **Sufficiency.** The consumer probe proves UN's two uses in their exact forms from the public
   API. R continuation 2's `ic_rewind_leaf_run` (#151) is the same statement as
   `inputRewindTM_run`'s first two clauses over `Fin 3`, with `0`, `1` and `2` for `start`,
   `scan` and `done`. Would a consumer need a different form: another entry state, an embedded
   or framed version, or the fixed fields stated as one configuration equality?
3. **Rule 10 in the API proofs.** The proofs read other files' definitions only through
   published equations: `MultiTapeTM.step_of_some`, `runFrom_zero`, `runFrom_succ_eq_step'`,
   `FinTM.controlAction_apply`, the `moveInputPos` and `inputSymbol` lemmas, and
   `Cfg.mapState`'s field equations. Does the seal cover every other-file definition they could
   reach? Do its controls show it is effective? Inspect every `rw`, `simp` and `simpa` argument
   and every `show`.
4. **NDHost.** Is the re-point exact: the private gone; only the three `rw` sites changed (the
   `; rfl` after each kept); nothing else in the file changed; the new import acyclic? NDHost's
   other 11 simp-argument unfoldings of `Cfg.mapState` predate this PR and are in the backlog:
   should any of them be required here?
5. **Placement and naming.** The module follows `Build/Rewind`: names in `Turing`, with no `FinTM`
   prefix. `Cfg.mapState_mapState` sits in the new module rather than beside `Cfg.mapState` in
   `StateRenaming`: placing it there would replay `StateRenaming`'s whole downstream closure (the
   user's ruling chose the small module). Is either choice a problem for discoverability or for
   the library's conventions?
6. **Duplication.** The v3 screen covers the two modules, the files they cite, `Build/Rewind`
   and the IR-1 files on this tree. Its 3 new pairs are all with `ExhaustiveReplay`'s IR-1 members (`xr_inRewindTM`
   82% and 73%, `xr_E_initCfg` 54%); the ledger assigns those to the user's dedup window. No pair
   disappears. UN's, R's and U2-S's copies are on other branches and are re-pointed by their
   landings or in the dedup window, as the ledger records. Is that disposition adequate for an
   API PR?
7. **No collateral change:** five new public declarations at source, plus two public constants
   (the derived `DecidableEq` and `Fintype` instances of `InputRewindPhase`; counted separately, as
   `workflow.md` §4 says), and no `@[simp]`; NDHost 25 → 25 public and
   8 → 7 private; the facade's import and entry only.

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms** (against `oleans-lu2sc1`): `Build/InputRewind` no output; the
  three theorems on `[propext, Quot.sound]`. NDHost re-pointed, checked as one file after the new
  module's text: no output.
- **Seal:** the primed proofs elaborate under the seal. The 7 controls fail sealed and close
  unsealed. The result is the same with `Action.apply` and `Cfg.init` also erased from the simp
  set (`InputRewindSeal*.out`: exactly the 7 sealed controls' errors).
- **Consumer probe:** both restatements close, unsealed and sealed (with the simp erasure), on
  `[propext, Quot.sound]`.
- **Freeze:** NDHost 25 → 25 public, 8 → 7 private (`guessRun_mapState_mapState` removed), one
  authorized body change (`guessRunTM_runWith_handoff`); facade 0 → 0 declarations.
- **Lint:** `TuringMachine/Build` 0 FAIL, 33 WARN over 40 files (none on the new module; NDHost's
  two warnings predate it); no line over 100 characters.
- **Screen (v3):** 253 → 257 declarations, 164 → 167 pairs; 3 new, 0 gone
  (`evidence/screen-pairdiff.txt`).
- **Replay:** `replay-lirapi.sh`: the downstream closure of the PR's files (5 modules:
  `Build/InputRewind`, `Build/NDHost`, `Diagonalization/NTimeHierarchy`, the `Diagonalization`
  and `TuringMachine` facades) at ⟨HEAD⟩, chained from ⟨SNAPSHOT: #149's merged-tree snapshot⟩.
  ⟨REPLAY RESULT⟩ (`evidence/replay-lirapi.*`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/65-input-rewind-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `input-rewind-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
