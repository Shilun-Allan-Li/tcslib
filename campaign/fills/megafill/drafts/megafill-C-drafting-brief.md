# Drafting brief: megafill C's fill briefs (for a drafting agent; maintainer, 2026-10-23)

You draft **three fill briefs and the megafill C cover brief**, with each brief's pre-ship
measurements. Fill agents (Codex) will later work from what you write, so precision matters more
than prose. **You write no library Lean**: nothing under `TCSlib/` changes. Probe files are
`.lean.txt` records under `campaign/`.

## 1. Repository, branch, delivery

- Clone `https://github.com/Shilun-Allan-Li/tcslib`; the campaign branch is
  **`complexity/arora-barak-ch3-4`** (never `main`). Record its tip when you start (`git rev-parse`;
  never type a hash by hand): that tip is your **drafting base**, and every line number and
  measurement in your drafts is that tree's.
- Work on a new branch **`drafts/megafill-c`** from that tip. Commit only files under
  `campaign/`. **Push that branch; do not push to the campaign branch and do not open a PR.** If
  you cannot push, deliver `megafill-c-drafts.zip`: a git bundle of the branch (its only
  prerequisite the drafting base) and a copy of every file you added.
- Assert every scripted edit (an un-asserted replace once shipped a stale record). Reflow Markdown
  to 100 columns with `devtools/seyoon/mdreflow.py`.

## 2. Read first

- `policy.md`, `workflow.md` (§4, the fill campaign: zips, partials, the one-fifth duplication
  rule, counting public names), `campaign/standards/TEMPLATE.md` (audit severities),
  `campaign/standards/fill-environment-addendum.md` (**v2.5**; it governs your own Lean setup
  too).
- `campaign/backlog.md`, the entries dated 2026-10-22 and 2026-10-23 (the latest rulings and
  their reasons), and `campaign/duplication-ledger.md`, families IR-1 and CC7-1.
- **Model briefs** (copy their structure, ground rules and checklists; they are the house style):
  - C1: `campaign/fills/c1/briefs/c1-fill-core-cont2.md`, the same owned file as your C1 item,
    and `c1-fill-universal-cont1.md`;
  - B5a: `campaign/fills/b5a/briefs/b5a-fill-canon-cont7.md`, the same owned file as your B5a item;
  - U2: `campaign/fills/u2s/briefs/u2s-fill-startup-cont1.md`, the same owned file as your U2 item;
  - the two newest drafts, which carry the 2026-10-23 rule-10 scope bullet:
    `campaign/fills/b6/briefs/b6-fill-configclock-cont2.md` (issued) and
    `campaign/fills/s13d/drafts/s13d-fill-g4-cont4.DRAFT.md`;
  - cover briefs: `campaign/fills/megafill/briefs/megafill-A.md` and `megafill-B.md`.
- Each model's review and gate show what auditors check and what went wrong:
  `campaign/fills/<item>/reviews/` and `campaign/gates/` (gates 63–68 are the most recent).

## 3. Megafill C (the user's rulings of 2026-10-23)

Four items, **Codex-facing** (megafills go to Codex because of cost):

| # | Item | Target(s) | Owned file | Status |
|---|---|---|---|---|
| 1 | G4 continuation 4 | `Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM` | `TuringMachine/Build/ZoneRebalance.lean` | **drafted**; its pre-ship re-run at `6e761018` is recorded (`drafts/s13d-fill-g4-cont4/preship-6e761018/`). Only issue-time placeholders remain. Do not rewrite it; fit it into the cover |
| 2 | C1, the replay canonizer | `Turing.exists_replayCanonizer` | `TuringMachine/NDCodeSimulator.lean` | **new brief** |
| 3 | B5a, the uniform simulator | `Turing.MachineFormat.exists_uniformSimulator` | `TuringMachine/CodeSimulator.lean` | **new brief** |
| 4 | U2, the `k`-tape universal machine | `Turing.exists_selfUniversalK`, `Turing.universalK` | `TuringMachine/UniversalK.lean` | **new brief** |

All four fills start from one shared base and run on separate branches. Their landings serialize
later, which is the maintainer's concern. Check and record how the items depend on each other:
`NDCodeSimulator` imports `CodeSimulator`, and an item may cite another item's target only as its
(sorried) statement. A result proved that way is "proved modulo" that target, which is
acceptable if the brief says so explicitly.

## 4. The items

**Item 2, C1's replay canonizer** (maintainer's findings; verify them). The stub's docstring
already gives the route, and every piece of it is published:
- `EffectiveNDMachineCode.canonizer_computes` (a structure field, `NDCodes.lean`):
  `canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime`;
- `Turing.codePrim_machine` (`MathlibBridge.lean`): a `Primrec` string function is computed by
  some `FinTM` in some time `T`. `T` is arbitrary and not monotone;
- `Turing.FinTM.ComputesInTime.mono`, with `Turing.FinTM.computesFunInTime_iff`: time weakening.
  Use it to make the compiled machine's bound monotone (`fun n => (Finset.range (n + 1)).sup T`);
- `Turing.FinTM.computesFunInTime_comp` (`Composition.lean`): composition. It needs
  `Monotone T₂`;
- the layouts: `Turing.serializeK` (`CodeSimulator`), `Turing.NDTM.replayTM` (`ChoiceReplay`),
  `Turing.tableBitsK` and `Turing.workReadsK` (`Build/StepBlock`), `Turing.actionBitsK` and
  `Turing.codeSkipActionK` (`CodeFormat`), and the proved bridge
  `Turing.CodeNDTM.serialize_eq_tableBitsK` (`NDCodeSimulator`).

The fill's real work is a `Primrec` list function `g` with
`g M.serialize = serializeK M.tm.replayTM` for every `M : CodeNDTM`. It copies the header,
splits the two tables into records, and re-emits them in the replay table's order with the
three-tape field layout. Specify `g`'s definition shape, the record-level lemmas it needs, and
how its `Primrec` proof decomposes (Mathlib's list combinators). Then probe that each cited
lemma exists in the form the route uses: §5's import probe, plus a sealed route probe of the
composition step with `g` left abstract.

**Item 3, B5a's uniform simulator.** Read the stub (`CodeSimulator.lean`, `exists_uniformSimulator`,
about line 8656 at `6e761018`), the module's status text (about line 46), and the backlog entries
that mention it (search `exists_uniformSimulator`; also `exists_uniformSimulator_of_timed`, the
H2 statement probe). The canonizer (`exists_polyCanonizer`) is now proved, and the uniform
simulator is the module's last admitted stub, behind targets 3–8 and `baker_gill_solovay`.
Design the route from published declarations only, or record the missing API (§6).

**Item 4, U2's `k`-tape universal machine.** Read `UniversalK.lean`: its status text (about line
29), `exists_selfUniversalK` (about line 1716) and `universalK` (about line 1754). The startup
`Turing.exists_selfStartupTMK` is proved (#147), and so is the seam layout (#145). Read U2-S's
landing record (`campaign/gates/63-u2s-startup-cont1-fill/`) for what the startup provides.
Decide, and state, whether one brief covers both stubs or `universalK` follows from
`exists_selfUniversalK`.

## 5. What every new brief contains (as in the models)

- The repository section with `@ANCESTOR@` placeholders, filled at issue. Leave `⟨BASE⟩`,
  `⟨IN-FLIGHT⟩` and the megafill banner as placeholders too.
- The target's statement and docstring **frozen verbatim**. The owned file and its regions (the
  home, the target's body, the status paragraph), with line numbers at your base.
- The route, naming every public declaration cited. **Rule 10** (no unfolding, and no
  definitional closure through another file's definition), with the scope bullet of 2026-10-23
  (it binds TCSlib's own definitions; core and Mathlib definitions may reduce in
  `rfl`/`decide`/`show` but are never passed to `simp`/`rw`/`unfold`). **Rule 11** (no R3 rows,
  no other file's privates). No new public declarations.
- Checkpoints that are landable partials, and a budget.
- **Duplication.** The v3 screen (`scripts/copy-text-screen-v3.py`) and its population: the owned
  file, every file the route cites, and every file with a known copy hazard (search the tree and
  every open PR branch for private copies of what the route would prove; IR-1 is the precedent).
  No new cross-file pair. In-file pairs at or above 90% must be justified.
- Proof sketches for every proof over 20 lines; public-facing docstrings (no campaign labels,
  paths or dates in Lean text).
- Environment: addendum v2.5; the cache for the item's Mathlib roots only; never `lake build`;
  `scripts/lean_check_tree.sh` for every check; the order list and the base sorry set.
- The checklist, which adds these lessons from megafill A (the backlog's "for the next cover
  brief"):
  - the shared environment logs go in every item zip;
  - memory is logged per module;
  - "seal not run" is a checklist failure, and so is a seal without `rfl` controls that fail
    sealed and close unsealed;
  - for any item that writes an input rewind, `Simulation` and `Build/InputRewind` are in the
    screen population (or the item cites `Turing.inputRewindTM` instead).

## 6. Pre-ship (per new brief, at your drafting base)

Set up Lean exactly as the addendum's Part 1 says, once, for the union of your items' roots. Then,
for each brief:
1. the owned file elaborates with exactly its base sorry warnings;
2. **the import probe** (`#check @` every public declaration the brief cites, a standalone
   import of the owned file's imports or of the owned file): 0 errors;
3. **a sealed route probe** for the route's key steps: their premises from public lemmas, under
   `attribute [local irreducible]` on every other-file definition they touch (and
   `attribute [-simp]` on any `@[simp]` definition among them), with `rfl` controls that fail
   sealed and close unsealed;
4. the order list, roots and base sorries:
   `python3 -I devtools/seyoon/fillinputs.py <repo> <base> <owned module path without .lean> <outdir>`;
5. the screen base (one screen at a time, under `nice -n 10`);
6. lint: `python3 -I scripts/campaign_style_lint.py <subtree>`.

Record each run in `campaign/fills/<item>/drafts/<brief>/preship-<short base>/`, with a README
table like `campaign/fills/b6/drafts/b6-fill-configclock-cont2/preship-906a9d7b/README.md`.
Drafts go in `campaign/fills/<item>/drafts/<brief>.DRAFT.md`, named like the models (C1:
`c1-fill-replaycanon`; B5a: `b5a-fill-unisim`; U2: `u2s-fill-universal`).

## 7. The cover brief

Write `campaign/fills/megafill/drafts/megafill-C.DRAFT.md`, modelled on `megafill-B.md`:
- the queue order, with a reason;
- the shared base and the shared preflight, toolchain, clone and cache, done once;
- per item, re-bootstrap the order list and create the item's branch from the shared base;
- per-item budgets and checkpoint zips;
- the environment addendum v2.5, with the lessons above;
- the agent: Codex.

## 8. Do not decide; report

Make no design decision that the models do not settle: a new public declaration, a change to a
frozen statement, a route that needs an unpublished lemma, or an item split. Record each in your
report with a recommendation. A missing lemma is an **"API PR first"** escalation: name the exact
statement and its home. Never type a hash by hand (`git rev-parse`; `git cat-file -t` to check).

## 9. Deliverables

- The branch `drafts/megafill-c`, pushed, holding:
  - the three new `.DRAFT.md` briefs;
  - their pre-ship folders and probe files;
  - the cover draft;
  - **`campaign/fills/megafill/drafts/megafill-C-DRAFTING-REPORT.md`**: the drafting base (full
    hash); per item, the target, the route in five lines, the probe and pre-ship results, the
    item dependencies, the open questions with recommendations, and a size and budget estimate;
    and the list of files.
- If you stop early (environment or time), deliver what is complete, and say what is not, in the
  report.
