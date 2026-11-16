# Stage 2 fills: common instructions (read first)

You are one of three parallel workers on the Arora–Barak chapters 3–4 closeout of TCSlib
(Lean 4). Stage 2 is medium structural deduplication: retire private copies of facts onto
public lemmas, publishing a small approved lemma where none exists. The maintainer integrates
the three fills into one PR and one Codex gate.

## Base

- Branch `closeout/stage1` at **`ceece3a04a3d8896f7dcc216c252ccfed057784a`** (stage 1, PR #349, under audit). Start your work
  from that commit.
- If stage 1 changes before it merges, the maintainer rebases your patch. Do not track it
  yourself.
- Your patch must touch only the files your brief lists. Your file set is disjoint from the
  other two fills'.

## Rules

1. Read `policy.md`, `workflow.md`, `campaign/maintainer/WORKFLOW.md` and
   `campaign/closeout/STAGES.md`.
2. **Rule 10.** A proof you change or add may read another file's definition only through that
   file's published equations or lemmas.
   - Not allowed: `simp [Def]`, `unfold Def` or `rw [Def]` on another file's definition;
     generated `Def.eq_1`/`eq_def`; `rfl`, `change`, `show` or `decide` that unfolds it.
   - Allowed: same-file definitions, structure-update projections (`{c with f := v}.g`),
     and published equations (for example `Cfg.mapState_state`, `Cfg.ofWords_workTapes`,
     `Action.apply_workTapes`).
   - If a proof you touch already reads a definition illegally, repair it with published
     equations. If no equation exists, stop and report.
3. **Statements.** Keep every existing public declaration's statement byte-identical. Add new
   public declarations only where your brief lists them as approved, each with:
   - a docstring;
   - an `[AB09, …]` reference where the mathematics is from the book;
   - a `**Proof sketch.**` paragraph for any proof longer than a few lines.

   No campaign labels (gate numbers, item codes) in Lean docstrings.
4. **Building.** Never run `lake build` or an unfiltered `lake exe cache get`. Elaborate
   module by module with the repository's wrappers (`scripts/lean_check_tree.sh` or
   `devtools/seyoon/leanelab.sh`). Run at most three Lean processes at once.
5. **Stop rule.** If an item turns out not to be a citation-style retirement, stop that item and
   report it instead of building a large new construction. Examples: the copies state different
   facts; retiring them needs a new machine; the net line count grows by more than about 20 for
   the item.

## Deliverable

1. A branch `closeout/stage2-fill-<A|B|C>` (or a patch file) on top of `ceece3a04a3d8896f7dcc216c252ccfed057784a`, in one or more
   commits.
2. A short report, `stage2-fill-<A|B|C>-report.md`, covering:
   - per item: what changed, the declarations deleted and added, and the net Lean lines;
   - items stopped under the stop rule, and why;
   - any rule-10 repair you made to an existing proof;
   - the modules you elaborated, with 0 errors.

The maintainer then runs the merged-tree replay, rule-10 seals and controls, sweeps and the copy
screen over all three fills together.
