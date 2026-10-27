"""Apply the cont1 brief review's edits to a copy of the draft (every replacement asserted to
occur exactly once). Usage: apply_fixes.py <draft-in> <draft-out>."""
import sys

src, dst = sys.argv[1], sys.argv[2]
t = open(src, encoding='utf-8').read()

E = []  # (finding, old, new)

# F12: the single-fill line (Part 3 does not apply, except items 5 and 7, restated below)
E.append(("F12",
"""# Ch3–4 fill campaign — E-Q cont1, the stage query's main machine (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer.lean`)

""",
"""# Ch3–4 fill campaign — E-Q cont1, the stage query's main machine (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer.lean`)

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

"""))

# F3: twelve imports, not nine
E.append(("F3",
"""- **There is no overlay.** The file already has its nine imports; your first edit is a proof edit.""",
"""- **There is no overlay.** The file already has its twelve imports (lines 6–17: the original
  three, the first round's eight and `Build/WordTests`); your first edit is a proof edit."""))

# F1: the frozen statement's lines and its landed body
E.append(("F1",
"""The statement and its docstring are **frozen verbatim** (lines 248–273: the docstring 248–269;
the statement):

```lean
theorem exists_queryTM {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (G : FinTM Bool) (C : ℕ), G.ComputesFunInTime (query f g) fun n => C * (g n + 1) := by
  sorry
```
""",
"""The statement and its docstring are **frozen verbatim** (lines 376–404: the docstring 376–401,
its last paragraph 399–401 being region (d); the statement 402–404). The body is checkpoint 1's
`suffices` (405–410):

```lean
theorem exists_queryTM {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (G : FinTM Bool) (C : ℕ), G.ComputesFunInTime (query f g) fun n => C * (g n + 1) := by
  suffices hmain : ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (fun x => query f g (List.replicate x.length true))
        (fun n => A * (g n + 1)) by
    obtain ⟨M, A, hM⟩ := hmain
    exact qy_query_of_main hg hM
  sorry
```
"""))

# F15: n ≤ g n is still needed inside hmain
E.append(("F15",
"""so the input call on the native input serves non-unary words too; `n ≤ g n` is already
absorbed by `qy_query_of_main`.""",
"""so the input call on the native input serves non-unary words too. `qy_query_of_main` absorbs
the guard's and the empty branch's `n + 1`; `M₁`'s own linear phases still need `n ≤ g n` inside
`hmain` (checkpoint 7)."""))

# F7: the import probe extended (216 names)
E.append(("F7",
"""- **The import probe** (`EQImportProbe.lean.txt`, **182 checks of 182 names**: megafill D's
  76 after dropping the virtual-input host's five, the route's 43 more, `timeConstructible_iff`
  and `Round.iterate_seq`, and 61 for the release adapter, the input seek, the scan, fold and
  emitter rows, `BufferWords` and the layout equations): 0 errors, 0 warnings. **Re-run it after
  your delivery**, extended by every further name you cite.""",
"""- **The import probe** (`EQImportProbe.lean.txt`, **216 checks of 216 names**: megafill D's
  76 after dropping the virtual-input host's five, the route's 43 more, `timeConstructible_iff`
  and `Round.iterate_seq`, 61 for the release adapter, the input seek, the scan, fold and
  emitter rows, `BufferWords` and the layout equations, and 34 for the linear word tests, the R1
  transports' field equations, the clock layout's remaining fields and `wordPatch_append`, the
  machine model's step and action equations, the emit-mode call and the round cut): 0 errors,
  0 warnings. **Re-run it after your delivery**, extended by every further name you cite."""))

# F17 (note): all sixteen route lemmas are axiom-printed
E.append(("F17",
"""- **The route probe** (`EQRouteProbe.lean.txt`, 16 lemmas, 14 of them axiom-printed, and the""",
"""- **The route probe** (`EQRouteProbe.lean.txt`, 16 lemmas, each axiom-printed, and the"""))

# F18: the cont1 review's probe as an input
E.append(("F18",
"""  Their duplication probe (`EQReviewDupProbe.lean.txt`): 3 of 4 "could not close"; the fourth,
  doubling twice, is Mathlib's `List.flatMap_assoc` (cite it).
""",
"""  Their duplication probe (`EQReviewDupProbe.lean.txt`): 3 of 4 "could not close"; the fourth,
  doubling twice, is Mathlib's `List.flatMap_assoc` (cite it).
- **The cont1 review's route lemmas** (`EQC1ReviewProbe.lean.txt`, one seal over 20 definitions:
  the 12 above, `clockCfg`, `wordPatch`, `FinTM.bufferTape` and your file's `query`, `budget`,
  `stageCode`, `stage`, `ladder`; their 8 further controls in `EQC1ReviewSealControl.lean.txt`,
  each failing sealed): 0 diagnostics, 33 axiom prints within the standard three. It re-proves
  both probes' lemmas together (without `qy_guard`) and adds:
  - `qy_timeout_cert`: a timeout of the all-ones counter forces `n < f a`;
  - `qy_clocked_call`: the clocked, released install call's two outcomes (finish at the call's
    endpoint, right-tagged, the counter patched by a word of width `m`; or a silent `timeout r`),
    from the published clauses of the clock, the release adapter and the call;
  - `qy_rounds_spec`, `qy_stage_of_run`: the stop rule along the ladder and its converse;
  - `qyCut`, `qy_cut_spec`, `qyMachineDecide`, `qy_machineDecide_eq`, `qy_top_budget`: the
    machine's decision (binary compare, unary compare, cutoff product, power-of-two fold) is
    `qyDecide`, and at the top the cut square is the budget;
  - `qy_poly_log_le`, `qy_loop_ledger`, `qy_main_bound`: the loop within
    `(10 A₁ + 9 A₂)(n + 1)` and the absorption into `g n + 1`;
  - `qy_writer_word`: the emission order of `query_eq`'s word.

  They may be copied into your home as `qy_` privates, with public-facing docstrings (not
  `qy_flatten_replicate`). Their duplication probe (`EQC1ReviewDupProbe.lean.txt`): 4 of 5
  "could not close"; the fifth, the expansion's block `(replicate d [true]).flatten`, is
  `List.flatten_replicate_singleton` (cite it).
"""))

# F1: (a) no import; the home; the frozen line ranges
E.append(("F3",
"""- **(a) no import.** The nine are in the file (the first round's eight and `Build/WordTests`); add
  none.""",
"""- **(a) no import.** The file's twelve imports (lines 6–17) stay as they are; add none."""))
E.append(("F1",
"""one declaration is fine). Frozen: the module header (lines 14–69: the maintainer updates its
status at integration), every definition and law, the target's statement and docstring before
(d), **`exists_diagonalizer` and its docstring (E-D's region, 275 to the end)**, and every other
file.""",
"""one declaration is fine). Frozen: the module header (lines 23–78: the maintainer updates its
status at integration), every definition and law, the target's statement and docstring before
(d), **`exists_diagonalizer` and its docstring (E-D's region, 412 to the end)**, and every other
file."""))

# F2: the clock's joint form, not the Bool instance
E.append(("F2",
"""- **The clock:** `Turing.exists_stepClockTMVia` (or its `Bool` instance `exists_stepClockTM`).
  **Never write a second clock, counter or countdown.**""",
"""- **The clock:** `Turing.exists_stepClockTMVia` at `e := Function.Embedding.refl Bool`
  (`Function.Embedding.coe_refl` and `List.map_id` read `w.map e` as `w`; `qy_clocked_call`).
  **Not its `Bool` instance `exists_stepClockTM`:** it leaves the counter tape after either exit
  arbitrary (`∃ ct'`) and drops the frame clause, so the next round's counter precondition
  (blank at `cp - 1` and `cp + m`) cannot be re-established. The joint form's
  `wordPatch ct cp (w'.map e)` with `|w'| = m` keeps every other cell (`wordPatch_of_not_mem`).
  **Never write a second clock, counter or countdown.**"""))

E.append(("F9",
"""- **The guard split:** `FinTM.computesFunInTime_cond` with `computesFunInTime_const []`.""",
"""- **The guard split** (landed: `qy_query_of_main`): `FinTM.computesFunInTime_cond` with
  `computesFunInTime_const []`."""))

# F9: L1 is landed
E.append(("F9",
"""  - **L1, the guard decider**: `x ↦ [decide (x = replicate |x| true ∧ 3 ≤ |x|)]`, linear time,
    composed from the framed input fold `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`) and a
    verdict emission over `Turing.emitAction` (`FinTM.emit_halts`), or from the function-level
    rows (`computesFunInTime_incFixed` with `incFixed_eq_none_iff_replicate`,
    `computesFunInTime_ifEq`, `computesFunInTime_cond`): not a hand-written scan of the input.""",
"""  - **L1, the guard decider, is landed** (`qy_guard_decider`, from the published word tests
    `computesFunInTime_allTrue` and `computesFunInTime_decideEq`): write no second guard
    decider."""))

# F11: the leaves' loops iterate by the published round iteration
E.append(("F11",
"""  L2 and L3 say in their docstrings why `compareTM_contract` (equality, at `compareStop`) and
  `walkTM_run_ofCfg` (the lockstep ruler) do not serve. **Any further leaf is an escalation.**""",
"""  L2 and L3 say in their docstrings why `compareTM_contract` (equality, at `compareStop`) and
  `walkTM_run_ofCfg` (the lockstep ruler) do not serve. A leaf that repeats a row (L3's product,
  L5's search) iterates by the published round iteration (`Round.iterate_seq`, or the counter
  loop `counterLoopTMVia`/`expandTM` where the count is a counter), never by a private loop
  driver (`policy.md`, review checklist item 8). **Any further leaf is an escalation.**"""))

# F15: checkpoint 7 is hmain
E.append(("F15",
"""**`M₁` and the target** (checkpoint 7). Assemble `M₁` by seams and the phase host, halting after the
writer, and silent before it. Its time is `≤ A' (g n + 1)`. Then `computesFunInTime_cond` and
`qy_guard` give the target, with `C` read off the conditional's bound
`c (T₀ n + max (T₁ n) (T₂ n) + 1)` and `n ≤ g n`.""",
"""**`M₁` and `hmain`** (checkpoint 7). Assemble `M₁` by seams and the phase host, halting after the
writer, and silent before it. Its time is at most `B₁ (n + 1) + B₂ (g n + 1)`, which is at most
`(B₁ + B₂)(g n + 1)` by `n ≤ g n` (from `hg` through `timeConstructible_iff`; `qy_main_bound`):
that is `hmain` with `A = B₁ + B₂`. The landed `suffices` then closes the target
(`qy_query_of_main` supplies the conditional and its constant)."""))

# F9: gate guidance's leaf list
E.append(("F9",
"""promotion requests. This brief's leaves (L1–L3, L5, L6) and the scan folds are those rows, in
  unary where the note says so.""",
"""promotion requests. This brief's leaves (L1, landed; L2, L3, L5, L6) and the scan folds are
  those rows, in unary where the note says so."""))

# F7: the cited infrastructure line
E.append(("F7",
"""The probe's 182 names: the target and the stages' laws; A1's reading and the function-level API;""",
"""The probe's 216 names: the target and the stages' laws; A1's reading and the function-level API
(the linear word tests among them);"""))
E.append(("F7",
"""the layout equations and the contract layer; `BufferWords`; `Nat.bits`, `Nat.log` and
`Nat.unpair` facts.""",
"""the layout equations (R1's transports and the clock's `wordPatch` among them) and the contract
layer; the machine model's step and action equations; `BufferWords`; `Nat.bits`, `Nat.log` and
`Nat.unpair` facts."""))

# F3, F9: ground rules 6, 7, 8
E.append(("F3", """6. **Imports.** Exactly the nine in region (a).""",
"""6. **Imports.** Exactly the file's twelve (region (a)); add none."""))
E.append(("F9", """   `Build/Loop`'s call machinery (`callTM`, `emCall_*`). L1–L6 are allowed.""",
"""   `Build/Loop`'s call machinery (`callTM`, `emCall_*`). L2, L3, L5 and L6 are allowed (L1 is
   landed; L4 is the scan fold)."""))
E.append(("F1", """   and private declaration counts (base: 361 lines; 22 public, 0 private).""",
"""   and private declaration counts (base: 498 lines; 22 public, 3 private)."""))

# F10: rule 10's readings, the seal list, own leaves, derived instances
E.append(("F10",
"""      - The clock's layout: through `clockCfg_*`.""",
"""      - The clock's layout: through `clockCfg_*`; its patched counter `wordPatch` through
        `wordPatch_of_mem`, `wordPatch_of_not_mem` and `wordPatch_append`.
      - R1's transports `embedEmitCfg`/`embedSilentCfg`: through their `_state`, `_inputPos` and
        `_output` equations, `_selected_tape`/`_selected_pos`, `_unselected`,
        `embedSilentCfg_cap` and `embedEmitCfg_eq`."""))
E.append(("F10",
"""      leaf defined in your own file (L1–L6).""",
"""      leaf defined in your own file (L2, L3, L5, L6), and prefer `MultiTapeTM.step_of_some` and
      the `Action.apply_*` field equations there too; the inspection table lists each such
      unfolding as an own leaf's, not as a finding."""))
E.append(("F10",
"""        `stateWord`, `clockCfg`, `counterLoopCfg`, `expandTM`, `copyMapTM`, `seamCompTM`,
        `embedEmitTM`, `embedSilentTM`, `pairEncode`, `seamReleaseTM`, `phaseHostTM`,
        `Cfg.mapState`, `Cfg.Stopped`, `embedEmitCfg`, `FinTM.bufferTape`, `scanTM`, `inputFoldTM`,
        `writeAdvTM`, `clearTM`, `rewindTM`, `dbl`.""",
"""        `stateWord`, `clockCfg`, `wordPatch`, `counterLoopCfg`, `expandTM`, `copyMapTM`,
        `seamCompTM`, `embedEmitTM`, `embedSilentTM`, `pairEncode`, `seamReleaseTM`, `phaseHostTM`,
        `Cfg.mapState`, `Cfg.Stopped`, `embedEmitCfg`, `embedSilentCfg`, `FinTM.bufferTape`,
        `scanTM`, `inputFoldTM`, `writeAdvTM`, `clearTM`,
        `rewindTM`, `dbl`."""))
E.append(("F10",
"""    definitions, as `QyStep`, `qyDecide`; unused in the tree at the drafting base).""",
"""    definitions, as `QyStep`, `qyDecide`; used in the tree only by your file's three landed
    privates). A `private inductive` with `deriving DecidableEq` (as `QyStep`) gets a public
    instance name (`instDecidableEqQyStep`): check that no file or open PR has it and report it
    (`workflow.md` §4, counting public names), or write the instance as a `private instance`."""))

# F13: the population covers the machine model's files
E.append(("F13",
"""- **The population** is 30 files
  (`campaign/fills/eq/inputs/eq-fill-query-cont1/screen-population.txt`):""",
"""- **The population** is 32 files
  (`campaign/fills/eq/inputs/eq-fill-query-cont1/screen-population.txt`):"""))
E.append(("F13",
"""    `Encoding`, `StateRenaming`, `BufferWords`, `ClassP/TimeConstructible`, and `Build/WordTests`
    (the guard's rows);""",
"""    `Encoding`, `StateRenaming`, `BufferWords`, `ClassP/TimeConstructible`, `Build/WordTests`
    (the guard's rows), and the machine model's `Configuration` and `Deterministic` (the step and
    action equations your leaves' run lemmas cite);"""))
E.append(("F13",
"""- **The base** is `campaign/fills/eq/logs/eq-fill-query-cont1-screen-base.txt`: **1,735
  declarations, 2,152 pairs, 757,579 characters** (MEASURED at your base; about 19 minutes under
  `nice -n 10`, peak memory 2.0 GB).""",
"""- **The base** is `campaign/fills/eq/logs/eq-fill-query-cont1-screen-base.txt`: **⟨N⟩
  declarations, ⟨P⟩ pairs, ⟨C⟩ characters** (MEASURED at your base; about ⟨T⟩ minutes under
  `nice -n 10` on the maintainer's host, peak memory ⟨M⟩ GB)."""))

# F6: the idiom example is now a published lemma
E.append(("F6",
"""  - **idiom**: the shared text is a public row's invocation and the standard conversion around it
    (for example `FinTM.computesFunInTime_ifEq w [true] [false]` with `convert … using 1;
    funext x; by_cases hx : x = w <;> simp …`), and no lemma, public or private, is re-derived.
    Justify it in one line and go on;""",
"""  - **idiom**: the shared text is a public row's invocation and the standard conversion around it
    (for example the `Cfg.mapState_mapState` field equations around a seam), and no lemma, public
    or private, is re-derived. Justify it in one line and go on. **Since #171 the
    `[decide (x = w)]` conversion of `computesFunInTime_ifEq` is the published
    `Turing.FinTM.computesFunInTime_decideEq`** (the unarity test is
    `computesFunInTime_allTrue`): writing it again is a re-derivation of a published lemma, not an
    idiom;"""))

# F9: hazards against L2, L3, L6
E.append(("F9",
"""  - `Build/Catalog`'s scans and `f2_` privates, against L1–L4: cite a framed row wherever one
    exists;""",
"""  - `Build/Catalog`'s scans and `f2_` privates, against L2, L3, L6 and the scan folds: cite a
    framed row wherever one exists;"""))

# F14: quote summaries, ship outputs as files; finished logs in cp zips
E.append(("F14",
"""- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).""",
"""- List every new in-file pair with a one-line justification. Quote each screen's summary line and
  its new pairs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair), and
  ship both full outputs as files (`screens/`)."""))
E.append(("F14",
"""  (`N` the checkpoint's number, 2 to 7) with the same contents as of that commit (the final sweep
  may be your module's check only). Deliver the latest if the session ends early.""",
"""  (`N` the checkpoint's number, 2 to 7) with the same contents as of that commit (the final sweep
  may be your module's check only; every log in it is a finished run, or is marked partial).
  Deliver the latest if the session ends early."""))

# F8: the budget on a Claude host
E.append(("F8",
"""  tail re-check about 5 s. Reserve about 25 minutes for the finishing sequence (the final sweep
  with the after screen beside it, then the REPORT and the zip), and use the rest for proofs.""",
"""  tail re-check about 5 s. Reserve about 25 minutes for the finishing sequence (the final sweep
  with the after screen beside it, then the REPORT and the zip), and use the rest for proofs.
  These are a 9-CPU host's figures. The last Claude fill host (4 CPUs, 2026-10-24) ran 2–3×
  slower: a 96-module bootstrap in 22 minutes, and a screen of 847 declarations in 12 minutes
  (about 5 on the maintainer's host). If yours is like it, expect about 20 minutes for the
  bootstrap and 45 for each screen, and reserve about an hour for the finishing sequence."""))

# F5: exists_uniformSimulator is proved (#170)
E.append(("F5",
"""`ntime_hierarchy` (`NTimeHierarchy`), `exists_uniformSimulator` (`CodeSimulator`, B5a),
`exists_codeNDTM_accepts_linear` (`ClassNP/NDNormalForm`), and the older function-level and""",
"""`ntime_hierarchy` (`NTimeHierarchy`), `exists_codeNDTM_accepts_linear`
(`ClassNP/NDNormalForm`), and the older function-level and"""))

# F9, F15: the REPORT checklist
E.append(("F9",
"""      rung, `L`, `h`, the seek's, the scratch); each leaf (L1–L3, L5, L6) and its run, and each""",
"""      rung, `L`, `h`, the seek's, the scratch); each leaf (L2, L3, L5, L6) and its run, and each"""))
E.append(("F15",
"""- [ ] `C`, term by term: the guard, the setup, the loop's ledger (passed rounds, the arithmetic
      term, the last round), the stage code, the budget field, the writer.""",
"""- [ ] `hmain`'s `A`, term by term: the setup, the loop's ledger (passed rounds, the arithmetic
      term, the last round), the seek, the stage code, the budget field, the writer; and the
      target's `C` as `qy_query_of_main` forms it from `A`."""))

# F16 (note): checkpoint 3 before M₁ exists
E.append(("F16",
"""**One round at the rung `ℓ < n`, `a = ℓ + 1`** (checkpoint 3; state it as a `Turing.Round` at the
locator's anchor, with three escapes: interior, top, timeout).""",
"""**One round at the rung `ℓ < n`, `a = ℓ + 1`** (checkpoint 3; state it as a `Turing.Round` at the
locator's anchor, with three escapes: interior, top, timeout). Build the locator as its own
machine (a phase host over the round's phases, the anchor a dispatch state), so that the round is
stated before `M₁` exists; at checkpoint 7 the locator is one phase of `M₁`."""))

# F18: the inputs line names the cont1 review's probes
E.append(("F18",
"""    route probe with its seal controls, the semantic-duplication probe, the review's route lemmas
    with their controls and duplication probe, and the screen population; the order list""",
"""    route probe with its seal controls, the semantic-duplication probe, the review's route lemmas
    with their controls and duplication probe, the cont1 review's route lemmas with their controls
    and duplication probe (`EQC1Review*.lean.txt`), and the screen population; the order list"""))

for tag, old, new in E:
    n = t.count(old)
    assert n == 1, (tag, n, old[:80])
    t = t.replace(old, new)
open(dst, 'w', encoding='utf-8').write(t)
print(len(E), "replacements applied")
