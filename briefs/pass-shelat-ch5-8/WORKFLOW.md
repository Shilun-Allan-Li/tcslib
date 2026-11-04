# How the Arora–Barak ch. 3–4 campaign is run, and what carries over to Pass–shelat ch. 5–8

A brief handover, written 2026-11-04 by the campaign's maintainer agent, so that a new session can
run the ch. 5–8 line the same way. The campaign itself lives on branch
`complexity/arora-barak-ch3-4`; its full records are in `campaign/` there (`campaign/README.md`).

## Roles

- **The user** (Seyoon Ragavan):
  - takes the rulings, asked as explicit multiple-choice questions with a recommended option;
  - dispatches fill briefs and audit packs to external agents (Codex or Claude, in separate chats);
  - merges PRs, runs the long replays locally, and drops what comes back into `exchange/inbox/`.
- **The maintainer** (a Claude Code session):
  - designs routes (design notes);
  - writes briefs with executed pre-ship checks;
  - writes the maintainer Lean (API and landing PRs) and the gate packs, bundles and replay
    scripts;
  - reviews every delivery and every audit, through a review sub-agent;
  - keeps the records: the backlog, the duplication ledger, and each gate's resolutions.
- **Fill workers:** external agents given one brief and one owned file or region. They deliver
  zips, not PRs.
- **Auditors:** external agents given one bundle. They deliver a findings file.

## Where things live

| What | Where |
|---|---|
| Standards | `policy.md`, `workflow.md` (repository root); `campaign/standards/TEMPLATE.md` (gate format, severity guide) and `fill-environment-addendum.md` (the fill host's rules: preflight, Mathlib cache for the brief's roots only, one Lean process at a time, never `lake build`) on the campaign branch |
| Records | campaign branch, `campaign/`: `gates/<NN>-<slug>/` (pack, findings, resolutions, evidence), `fills/<group>/` (briefs, inputs, orders, logs, drafts, reviews), `items/` (design notes), `backlog.md`, `duplication-ledger.md`, `MOVED.md` |
| Maintainer tools | `devtools/seyoon/` on the campaign branch (its README lists each). Among them: `leanelab.sh` (throttled single-file elaboration), `declfreeze.py`, `fillinputs.py` (order lists, roots, base sorries), `mkreplay.py`/`mkdownmulti.py` (replay scripts), `mkbundle-mixed.py`/`verifybundle.py`/`stage.sh` (gate bundles), `pairdiff.py` |
| Screens and lint | `scripts/copy-text-screen-v3.py` (campaign branch), `scripts/campaign_style_lint.py`, `scripts/style_lint.py`, `scripts/lean_check_tree.sh` |
| The hand-off folder | `exchange/` in the main checkout, **git-ignored**, local only (below) |

## The exchange folder (`exchange/`)

| Folder | Holds |
|---|---|
| `outbox/gates/<NN>-<slug>-gate/` | a gate ready to dispatch: the bundle to attach, `BUNDLE-FILES.txt` (section order), `SHA256SUMS`, a `README.md` |
| `outbox/fills/` | fill dispatch files: the issued brief with its `@ANCESTOR@` filled in, and the current environment addendum (attached with every fill) |
| `inbox/` | what comes back: delivery zips and findings files; the user drops downloads here |
| `archive/gates/`, `archive/fills/` | dispatched gate folders and fill files (moved when the user says "dispatched") |
| `archive/deliveries/`, `archive/findings-drops/` | processed zips and findings files (moved once committed to the records) |

The maintainer stages in `outbox/` and **pastes the prompt in chat**, in a fenced block (no
`PROMPT.txt` files). The prompt names:
- the absolute path of the file to attach, its SHA-256 and section count;
- every commit by its full 40-character hash, taken from `git rev-parse` and never typed by hand;
- the deliverable's file name: auditors deliver `<name>-findings.md`; fills deliver
  `fill-<item>.zip` and checkpoint zips.

## A fill's lifecycle

1. **Route note** (`campaign/items/…`): the mathematics, which published rows and hosts carry
   each step, and the decisions for the user.
2. **Brief draft plus pre-ship.** Every claim the brief makes is checked by running Lean at the
   issue tree:
   - **probes:**
     - an import probe of every cited name;
     - a route probe that discharges each prescribed step's premises, sealed (below), with
       controls;
     - a duplication probe (`exact?` on each planned lemma);
   - **build inputs:**
     - the order list, its Mathlib roots and the base sorry set (`fillinputs.py`);
     - the screen base and the lint base.
3. **Brief review** by a review sub-agent. Its verdict is "issue as is", "issue after edits" or
   "do not issue", with a suggested diff. Blockers are ruled by the user.
4. **Issue and dispatch.** The brief is committed to the records, and its commit becomes
   `@ANCESTOR@`. The dispatch copy goes to `outbox/fills/`, and the prompt goes in chat.
5. **Delivery** to `inbox/`, with checkpoint zips along the way. Intake checks:
   - `SHA256SUMS`;
   - `git bundle verify` (the only prerequisite is the base);
   - the patches equal `git format-patch` of the bundled branch;
   - the source in the zip equals the bundle's head.
6. **Delivery review** by a review sub-agent. It covers:
   - integrity and scope, and the statement freeze;
   - elaboration and axioms;
   - rule 10 under its own seal;
   - duplication;
   - docstrings and policy;
   - landing edits, and continuation must-pins for a partial.
7. **Landing:** a maintainer PR (reworded commit subjects, tested landing edits), its fill gate
   and its replay. A partial either lands with a continuation brief or travels on a branch with
   its continuation (NF did the latter).

## Gates and replays

- **Gates.** Every Lean change gets a gate: statement gates before fills, fill gates and API gates.
  - **The pack** (`pack.md`) states what changed, the brief for the auditor, the attestations to
    verify, and the findings format.
  - **The evidence**, whichever applies:
    - patches, the freeze, the elaboration chain;
    - the rule-10 seals with controls, the axioms, the constant census;
    - an all-branch search for copies of new public names;
    - lint, screens, and the replay script.
  - **The bundle** concatenates every file the auditor needs: the standards included, and the
    Lean from the PR head plus the records from a campaign commit. It is verified against
    `git archive` exports.
  - **Findings** are committed verbatim, each with a resolution (true and fixed, recorded, or
    rebutted). A gate closes at 0 blockers and 0 majors; otherwise a round 2 follows (`pack-r2.md`).
- **Replays.** A PR's downstream closure is recompiled module by module, with
  `scripts/lean_check_tree.sh`, into a copy of an olean snapshot. A static check compares the
  sorry counts with the source.
  - When several PRs merged since the last common snapshot, the replay covers the union of their
    closures (a merged-tree replay); snapshots are never composed.
  - The root module `TCSlib` is never in a replay list.
- **"Clear to merge"** is said, as a bold line of its own, only when:
  - the gate is closed;
  - the replay has passed on the current head;
  - the PR's base is the campaign branch (not a stacked branch).

  Otherwise: "**Not yet clear to merge** — why". Likewise "**Ready to dispatch**" and
  "**Ready to run**".
- **What goes through a PR:** only commits that change `.lean` files go through a PR the user
  merges. Records (Markdown, evidence, logs) are pushed directly to the campaign branch.

## Standing rules (the ones that bite)

- **Lean runs only through `leanelab.sh`:** at most two elaborations machine-wide, `lean -j4` under
  `nice -n 10`, against an olean snapshot.
  - Never `lake build`, and never an unfiltered `lake exe cache get`.
  - Copy-text screens run one at a time, under a lock.
  - For a pre-replay check of a chain of changed files, compile them with `lean -o` into a
    copy-on-write clone of the snapshot (`cp -cR`).
- **Rule 10 (no unfolding):** proofs read another file's TCSlib definitions only through published
  equations. This applies to the maintainer's own API proofs too.
  - Self-check: a seal (`attribute [local irreducible]` on every such definition, plus
    `attribute [-simp]` on the `@[simp]` ones), with controls that close unsealed and fail
    sealed. Then inspect every `rw`/`simp` argument.
  - Core and Mathlib definitions may reduce in `rfl`, `decide` or `show`, but are never passed to
    `simp`, `rw` or `unfold`.
  - Consequence for design: an API that must look inside an author's definitions goes beside
    them, in their file.
- **Rule 11 (MIG-1 compatibility):**
  - cite none of the six R3 rows (use the framed `_ofCfg` forms);
  - cite no private declaration of another file;
  - keep new privates under the brief's prefix.
- **Duplication:** one proof per shared argument.
  - The copy-text screen runs before and after a change.
  - A semantic search covers each new lemma (by name, statement and `exact?`) across every
    branch.
  - Accepted debt goes into `campaign/duplication-ledger.md`.
- **Public-facing Lean text:** no campaign labels, gate or finding numbers, dates or `campaign/`
  paths in docstrings; provenance goes in reports. Every proof over 20 lines carries a
  `**Proof sketch.**`. Attribution follows `policy.md`.
- **File size alone is never a reason to split or delay.**
- **Scripted edits:** every one asserts that its match is unique. Python runs as `python3 -I`.
- **Sub-agents** are for reviewing incoming deliveries and audits only. The maintainer does
  everything else directly, and keeps working while a review runs.
- **Fill agents (soft rule):** Codex for a first attempt; Claude for a slow-progress single fill.
  Ask the agent as its own question.

## Continuity and overnight routines

- **Work continuously:** after each item, go to the next queued one. Stop only to wait on jobs the
  user runs, or for a ruling.
- **Before the user sleeps:**
  - list the replays and dispatches ready to start, so they run overnight;
  - ask every decision you can foresee needing, as conditional rulings.
- **While the user sleeps:**
  - keep going with reviews, pre-ships, drafting, records and local preparation;
  - stop at a design decision, and leave a clear note of where you stopped;
  - do not push PR branches unless pre-authorized.
- **The scratchpad is temporary.** On this machine `/private/tmp` loses files untouched for about
  three days (nightly, about 03:00). Worktrees, snapshots and tools there need an access-time
  `touch` before a gap, and checking after. Everything that matters is committed and pushed.
- **The backlog** (`campaign/backlog.md`) records each workstream's state, rulings and next step,
  so any session can resume from it.

## What changes for the Pass–shelat ch. 5–8 line

- **The base is this branch,** not the campaign branch. Records for ch. 5–8 live here, under
  `briefs/pass-shelat-ch5-8/` and `PassShelatChapter5-8Plan.md`, until a records layout is
  chosen. The campaign's `campaign/` folder and `devtools/seyoon/` are not on this branch; read
  them from `origin/complexity/arora-barak-ch3-4`.
- **The ch. 2–4 layer is Frederick Dehmel's.** It was built by a different process:
  - shell `lake build` by agreement (his plan's D1);
  - internal adversarial audits;
  - multi-agent runs.

  Its files are not edited from the ch. 5–8 line; see the plan's coordination points.
- **No olean snapshot of this branch's tree exists.** The first replay builds one: the Mathlib
  cache for the roots, then `scripts/lean_check_tree.sh` module by module. The branch's head must
  build first (`SPINE-DESIGN.md` §S1).
- **Gates:** one external statement gate for ch. 5–8 after the statement phase, then a fill gate
  per landing, in the format above.

## Picking up from here

1. Read `README.md` in this folder, then `PassShelatChapter5-8Plan.md`, `SPINE-DESIGN.md` and the
   inventory.
2. Get the user's rulings on decisions D-1…D-7 (`SPINE-DESIGN.md`).
3. Start P0 (Shamir, extractor basics), which needs nothing from ch. 2–4, while S1 (a building
   base, the interface agreement with the ch. 2–4 owner) is arranged.
