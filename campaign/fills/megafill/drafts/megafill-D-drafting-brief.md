# Drafting brief: megafill D, a second fill track (for a drafting agent; maintainer, 2026-10-24)

The campaign's current fills wait on a chain of small API PRs (megafill C's B5a and U2 need #160,
the startup kit and #161 first). **The user ruled (2026-10-24): open a second fill track** on
targets that touch none of the in-flight work, so proofs progress while those PRs are audited. You
**triage the candidates, then draft fill briefs for the ready ones and the megafill D cover**, with
each brief's pre-ship. Fill agents (Codex) will work from what you write, so precision matters more
than prose. **You write no library Lean**: nothing under `TCSlib/` changes. Probe files are
`.lean.txt` records under `campaign/`.

## 1. Repository, branch, delivery

- Clone `https://github.com/Shilun-Allan-Li/tcslib`; the campaign branch is
  **`complexity/arora-barak-ch3-4`** (never `main`). Record its tip when you start (`git rev-parse`;
  never type a hash by hand): that tip is your **drafting base**; every line number and measurement
  in your drafts is that tree's.
- Work on a new branch **`drafts/megafill-d`** from that tip. Commit only files under `campaign/`.
  Push the branch; you may open a PR into the campaign branch with `campaign/` files only (the user
  merges it). Never push to the campaign branch itself. If you cannot push, deliver
  `megafill-d-drafts.zip`: a git bundle of the branch (its only prerequisite the drafting base) and
  a copy of every file you added.
- Assert every scripted edit. Reflow Markdown to 100 columns (`devtools/seyoon/mdreflow.py` for list
  items; wrap paragraphs by hand).

## 2. Read first

- `policy.md`, `workflow.md` (§4: zips, partials, the one-fifth duplication rule, counting public
  names), `campaign/standards/TEMPLATE.md`, `campaign/standards/fill-environment-addendum.md`
  (**v2.5**; it governs your own Lean setup too).
- The plan `campaign/design/plans/AroraBarakChapters3-4Plan.md` and **`campaign/backlog.md`** in
  full for each candidate: the backlog records which items are active, **paused, retired or moved to
  another route** by the user's rulings (for example MIG-23 pauses `Build/RecordTable`'s four rows;
  Savitch and PSPACE moved to the §15 program route; RD-3 restated `space_universal`). A ruling
  outranks a file's `sorry`.
- `campaign/duplication-ledger.md`.
- **Model briefs** (copy their structure, ground rules and checklists):
  `campaign/fills/b6/briefs/b6-fill-configclock-cont2.md` (issued 2026-10-23, delivered complete),
  `campaign/fills/s13d/briefs/s13d-fill-g4-cont4.md` (issued 2026-10-24, a single fill),
  `campaign/fills/c1/briefs/c1-fill-universal-cont1.md`; covers
  `campaign/fills/megafill/briefs/megafill-A.md`, `megafill-B.md`, and megafill C's draft
  `campaign/fills/megafill/drafts/megafill-C.DRAFT.md` with its reviews
  (`campaign/fills/megafill/reviews/megafill-c-drafts/`).
- **The recent gates and what failed:** `campaign/gates/69-*` to `73-*`. Two of them failed round 1
  on **semantic duplication**: a new private re-deriving a lemma that was already published
  (gate 69: six prefix arguments re-deriving `Turing.phaseHostTM_run_le`; gate 72: a private
  `(workReadsK 2).length = 9`, the `k = 2` case of `Turing.StepBlock.length_workReadsK`). The text
  screen misses this. §5 makes it a required check.

## 3. Candidates and the triage

The sorried declarations at the drafting base outside the in-flight work include (compute the
current list yourself with `devtools/seyoon/fillinputs.py` on each facade; this list is the
maintainer's, from the tree after #159):

| Area | File (sorried declarations) |
|---|---|
| The time hierarchy's diagonalizer (C1-E: the fills E-Q and E-D) | `Diagonalization/NTimeDiagonalizer` (`exists_queryTM`, `exists_diagonalizer`) |
| The linear-overhead normal form (NF) | `ClassNP/NDNormalForm` (`exists_codeNDTM_accepts_linear`) |
| The space hierarchy (B6, F6 and after) | `SpaceComplexity/Hierarchy` (`space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP`) |
| Savitch | `SpaceComplexity/Savitch` (`spaceConstructible_poly`, `savitch`) |
| The RAM simulation | `RAMSimulation/Classes` (9), `RAMSimulation/Simulation` (2), `RAMSimulation/WordSize` (3), `Programs/WordRAM/Extended` (18) |
| TQBF and the formula kit | `ClassPSPACE/TQBF` (21), `FormulaKit/Emit` (10), `FormulaKit/Gate` (10) |
| MIG-1 stage S's specifications | `Build/Loop` (5), `Build/Primitives` (3), `Build/Wrappers` (2), `Composition` (3), `Encoding` (1), `Simulation` (1), `ClassP/TimeConstructible` (2) |
| `Build/RecordTable`'s four rows | paused by MIG-23 (exclude unless the backlog says otherwise) |

**Excluded (in flight or owned by running fills):** `NDCodeSimulator`,
`Diagonalization/NTimeHierarchy` (including `ntime_hierarchy`), `Build/InterpreterStartup` (new),
`Deterministic`, `Build/StepBlockForward`, `Build/InputDevice` (the open PRs #160, #161 and the
prepared startup kit); `CodeSimulator`, `UniversalK` (megafill C); `Build/ZoneRebalance` (G4 cont4,
running). Cite nothing these PRs add; a route that needs one of them is "blocked on #N", not ready.

**For every candidate, record in the report:**
1. its status under the plan and the backlog (active, paused, retired, moved), citing the entry;
2. whether its statement is frozen (a statement gate passed), and where;
3. its route, in at most five lines, from the target's own sketch and the backlog;
4. whether every declaration the route needs is **published at the drafting base** (an import
   probe: `#check @` each), and what is missing (an exact statement and a proposed home: an
   "API PR first" item);
5. dependencies on other candidates or on in-flight work;
6. a size estimate, and a verdict: **ready**, **blocked** (on what), or **not a fill** (why).

Then rank the ready ones and **draft briefs for up to four of them** (prefer independent owned
files, and items whose completion removes admissions others wait on). Do not draft a brief for a
blocked or excluded item; describe what would unblock it.

## 4. Do not decide; report

Make no design decision that the plan and the backlog do not settle: a new public declaration, a
change to a frozen statement, a route needing an unpublished lemma, an item split, reviving a paused
item. Record each with a recommendation.

## 5. What every brief contains (as in the models)

- The repository section with `@ANCESTOR@` placeholders, filled at issue; `⟨BASE⟩`, `⟨IN-FLIGHT⟩`
  and the megafill banner as placeholders.
- The target's statement and docstring **frozen verbatim**; the owned file and its regions, with
  line numbers at your base.
- The route, naming every public declaration cited. **Rule 10** with the 2026-10-23 scope bullet (it
  binds TCSlib's own definitions; core and Mathlib definitions may reduce in `rfl`/`decide`/`show`
  but are never passed to `simp`/`rw`/`unfold`). **Rule 11** (no R3 rows, no other file's privates).
  No new public declarations.
- **Semantic duplication (new, required):** for every private lemma the route proposes, search for
  a published declaration that already states it or a generalization of it (the tree and every open
  PR branch: name and statement greps, and in the pre-ship an `exact?` or `apply?` probe on the
  proposed statement); list the hits in the brief and prescribe citing them. The brief tells the
  fill: "cite proved material; never re-prove it", and the fill's REPORT lists, for each new
  private, the search made.
- The v3 copy-text screen and its population (the owned file, every file the route cites, every
  known copy hazard); no new cross-file pair; in-file pairs at 90% or more justified. **Run every
  screen on a dedicated worktree that nothing edits during the run.**
- Landable checkpoints and a budget; proof sketches for proofs over 20 lines; public-facing
  docstrings (no campaign labels, paths or dates in Lean text).
- Environment: addendum v2.5; the cache for the item's Mathlib roots only; never `lake build`;
  `scripts/lean_check_tree.sh` for every check; the order list and the base sorry set.
- The checklist with megafill A's lessons (the backlog's "for the next cover brief"): shared
  environment logs in every item zip; memory logged per module; "seal not run" and "seal without
  `rfl` controls that fail sealed and close unsealed" are checklist failures (one control per sealed
  definition).

## 6. Pre-ship (per drafted brief, at your drafting base)

Set up Lean once, for the union of your items' Mathlib roots (the addendum's Part 1). Then per
brief:
1. the owned file elaborates with exactly its base sorry warnings;
2. **the import probe**: `#check @` every public declaration the brief cites; 0 errors;
3. **a sealed route probe** for the route's key steps, under `attribute [local irreducible]` on
   every other-file definition they touch (and `attribute [-simp]` on any `@[simp]` one), with one
   `rfl` control per sealed definition that fails sealed and closes unsealed;
4. **the semantic duplication probe** (§5): the proposed privates' statements against published
   declarations;
5. the order list, roots and base sorries: `python3 -I devtools/seyoon/fillinputs.py <repo> <base>
   <owned module path without .lean> <outdir>`;
6. the screen base (one screen at a time, `nice -n 10`, on a dedicated worktree);
7. lint: `python3 -I scripts/campaign_style_lint.py <subtree>`.

Record each run in `campaign/fills/<item>/drafts/<brief>/preship-<short base>/` with a README table
like `campaign/fills/s13d/drafts/s13d-fill-g4-cont4/preship-21d53053/README.md`. Drafts go in
`campaign/fills/<item>/drafts/<brief>.DRAFT.md`, named like the models.

## 7. The cover brief

`campaign/fills/megafill/drafts/megafill-D.DRAFT.md`, modelled on `megafill-B.md` and megafill C's
draft with its reviews' fixes: the queue order with a reason; the shared base, preflight, toolchain,
clone and cache done once; per item, its order list re-bootstrapped and its branch from the shared
base; per-item budgets and checkpoint zips; addendum v2.5 with the lessons above; the agent: Codex.

## 8. Deliverables

- The branch `drafts/megafill-d`, pushed (or a PR), holding the drafted briefs, their pre-ship
  folders and probe files, the cover draft, and
  **`campaign/fills/megafill/drafts/megafill-D-DRAFTING-REPORT.md`**: the drafting base (full hash);
  the triage table for every candidate (§3's six points); per drafted item, the target, the route
  in five lines, the probe, duplication and pre-ship results, its dependencies, the open questions
  with recommendations, and a size and budget estimate; the list of files.
- If you stop early, deliver what is complete and say what is not.
