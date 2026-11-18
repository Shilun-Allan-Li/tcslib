## ===== campaign/items/ram-tm/briefs/COMMON.md =====

# RAM fills: rules common to every brief

These rules bind every RAM fill (tier 1 `fill-ram-wordsize`, tier 3 `fill-ram-classes`, and
later the tier 2 fills). Each brief adds its targets, owned file and route.

## Repository, exchange and base

- **You work to and from the exchange.** It is branch `exchange/pass-shelat-ch5-8` of
  `https://github.com/Shilun-Allan-Li/tcslib`, folder `arora-barak-ch3-4/`.
  - **Inputs:** your fill's bundle and README, in `arora-barak-ch3-4/outbox/fills/<fill-name>/`.
  - **Output:** your delivery, in `arora-barak-ch3-4/inbox/<fill-name>/` (see "Delivery").
  - Do not push anywhere else.
- **Repository:** the same repository. Fetch the base commit from it read-only.
- **Base:** the commit named in your brief, on branch `complexity/ram-simulation`. That branch
  is `main` after the chapters 3–4 integration (#364), with the maintainer tools
  (`devtools/seyoon/`) merged in. Work on a local branch off it, record the base in `REPORT.md`,
  and never rebase.

## Ground rules (binding)

1. **Statement freeze.** Every existing declaration keeps its statement byte-identical. You
   change only the bodies of your targets, their `**Proof sketch.**` paragraphs, and the owned
   file's module docstring. A statement you believe is false or unprovable as written is an
   **E-STATEMENT** stop: report it with the evidence, and do not change it.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2). A proof may read another file's TCSlib
   definition only through that file's published equations and lemmas. So:
   - no `simp [Def]`, `unfold Def`, `delta`, generated `eq_1`/`eq_def`, or
     `rfl`/`change`/`show` that unfolds another file's definition;
   - core and Mathlib definitions may reduce by `rfl`, `decide` or `show`, but are not passed to
     `simp`, `rw` or `unfold`.

   The maintainer's seal check makes every other-file definition irreducible and re-elaborates
   your proofs. A proof that unfolds one fails there. A missing reader is an **E-READER** stop.
   Report it; do not unfold.
3. **No new public surface.** Do not add public declarations, files, imports, `@[simp]`
   attributes, `sorry`, `admit` or axioms. Helpers are `private`, in the owned file, under a
   section header. If you need a new public lemma or machine elsewhere, that is an **E-HOST**
   stop: report its statement and why.
4. **Cite, do not re-prove.** Search the import closure before proving a helper fact. Re-deriving
   an existing fact, or copying a proof's text for a variant instead of factoring a private
   helper, is a duplication finding even when the copy screens miss it.
5. **Standards** (`policy.md`): a `**Proof sketch.**` on every proof over 20 lines, describing
   the proof you wrote and naming declarations, not file line numbers. Docstrings carry no
   campaign labels: no decision or item codes such as `R8.5c`, `MIG-0a` or `PROG-4`, no
   `design §…` and no `campaign/` paths. Rewrite the proof sketches of the targets you prove to
   meet this. When the owned file's last admission is proved, drop "proofs pending" from its
   module docstring.
6. **A clean frontier is a valid delivery.** Prove what you can. Leave each unproved target as
   `sorry`, and report exactly where you stopped and why.

## Environment and verification

- Follow `campaign/standards/fill-environment-addendum.md` (v2.6). **Never run `lake build`.**
  Bootstrap the import closure at the base into your own scratch olean tree.
- **At most 3 Lean processes may run at once across the machine.** Other fills share it: start
  at most one of your own at a time, check the machine-wide count first, and record any waits.
- **Final checks** (record their exit codes):
  - the owned file elaborates with zero errors and no `sorry` warnings for the proved targets;
  - `#print axioms` for each proved target prints at most `propext`, `Classical.choice` and
    `Quot.sound`, plus `sorryAx` only if the target reaches a still-admitted declaration. Run
    it through a scratch file, not in the library;
  - for every target whose axioms include `sorryAx`, a scratch **dependency walk** that lists
    each reachable constant whose value uses `sorryAx`, as the chapters 3–4 probe
    `CloseHeadlines` does (gate 160, G160-01). The list must contain only the admitted
    declarations your brief names;
  - every module that imports the owned file elaborates with zero errors.

## REPORT.md checklist

- [ ] The base, and each target: proved, or the frontier and the reason.
- [ ] For each target that reaches `sorryAx`, the dependency walk's list of admitted
      declarations.
- [ ] Every new private declaration and its role. Every other-file definition reached, and the
      published equation used to read it. The existing facts you searched for before each
      helper.
- [ ] The final check outputs, the axiom prints, and `git diff --stat` touching only the owned
      file.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `<fill-name>.zip` containing `REPORT.md`, the delivered owned file, the patch against the
base, and the check logs. Push it, with any `<fill-name>-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/<fill-name>/` on the exchange branch. Run `git pull --rebase` first,
do not force, and touch nothing else there. Also attach the final zip in chat. Do not push to
any other branch, and do not open a pull request. The maintainer lands the delivery as a gated
PR into `complexity/ram-simulation`.

## ===== campaign/items/ram-tm/briefs/fill-ram-classes.md =====

# RAM fill (Codex): tier 3, the class corollaries (`RAMSimulation/Classes`, 9 admissions)

Read `COMMON.md` (bundled) first; its rules bind. **Fill name:** `fill-ram-classes`.
**Base:** the commit given in the dispatch prompt. It is the head of PR #371 (branch
`ram/fills-0-1`, stacked on #370), which has the readers of #370 and the proved tiers 0 and 1.
This replaces `COMMON.md`'s base rule for this fill only (Seyoon, 2026-11-18: dispatch before
#370 and #371 merge). The maintainer lands your delivery on the RAM branch after both merge.

## What this is

`TCSlib/Complexity/RAMSimulation/Classes.lean` puts a language into a complexity class from a
word-RAM program that decides it. Its nine theorems are the corollaries of stage 2's simulation
theorems. Their statements were audited on 2026-10-14 and rechecked against the base on
2026-11-17; they are frozen. **This fill proves all nine.** It is bound arithmetic and
unfolding of class definitions through their published readers.

**Admitted dependencies** (corrected after gate 160, G160-01). The prescribed routes cite six
declarations that are, or were, admitted:

| Declaration | Home | Status |
|---|---|---|
| `WordRAM.exists_simulation`, `WordRAM.exists_ndSimulation` | `RAMSimulation/Simulation` | tier 2; **admitted** at your base |
| `WordRAM.wordSizeComputable_logSpace`, `wordSizeComputable_of_spaceConstructible` | `RAMSimulation/WordSize` | tier 1; **proved** at your base (#371) |
| `WordRAM.HaltsWithin.mono`, `WordRAM.HaltsWithin.touches_le` | `Programs/WordRAM/Extended` | tier 0; **proved** at your base (#371) |

Use them as they are stated. Your proofs must contain no `sorry`. A `#print axioms` that shows
`sorryAx` cannot tell which admitted declaration was reached. So for each target, `REPORT.md`
lists the admitted declarations its proof reaches. Run a scratch dependency walk that collects
every constant reachable from the target whose value uses `sorryAx`. The chapters 3–4 probe
`CloseHeadlines` does exactly this; adapt it. At your base the walk must list only `exists_simulation` and `exists_ndSimulation`.

## Targets (in `WordRAM`, all in the owned file)

| Target | Uses |
|---|---|
| `mem_DTIME_of_decides` | `exists_simulation` (verdict mode, `fn := false`) |
| `mem_P_of_decides` | `mem_DTIME_of_decides`, `HaltsWithin.touches_le`, `HaltsWithin.mono` |
| `mem_P_of_decides_logWord` | `mem_P_of_decides`, `wordSizeComputable_logSpace` |
| `mem_SPACE_of_decides` | `exists_simulation` (verdict mode) |
| `mem_LOGSPACE_of_decides` | `mem_SPACE_of_decides`, `wordSizeComputable_logSpace` |
| `computesInSpace_of_computes` | `exists_simulation` (function mode, `fn := true`), `wordSizeComputable_logSpace` |
| `mem_SPACE_mul_of_decides` | `mem_SPACE_of_decides`, `wordSizeComputable_of_spaceConstructible` |
| `mem_NSPACE_of_accepts` | `exists_ndSimulation` |
| `mem_NL_of_accepts` | `mem_NSPACE_of_accepts`, `wordSizeComputable_logSpace` |

Each target's docstring has a proof sketch. The maintainer checked them against the definitions
at the base:

- **The classes** (rechecked at the base):
  - `Complexity.DTIME T = {L | ∃ c M, M.DecidesInTime L (c * T ·)}`, with
    `FinTM.DecidesInTime M L T = ∀ x, M.ComputesInTime x [indicator L x] (T |x|)`;
  - `Complexity.mem_P_iff : L ∈ P ↔ ∃ C d M, M.DecidesInTime L (C * (· + 1) ^ d)`;
  - `Complexity.SPACE s = {L | ∃ c M, M.DecidesInSpace L (c * s ·)}`, where
    `FinTM.DecidesInSpace` is `ComputesInSpace` of `x ↦ [indicator L x]`, and
    `ComputesInSpace M f s` is `∀ x, ∃ t, M.ComputesInTime x (f x) t ∧ spaceUsed (initCfg x) t ≤ s |x|`;
  - `LOGSPACE = SPACE logSpace`, `NL = NSPACE logSpace`;
  - `NSPACE s = {L | ∃ c N, N.DecidesInSpace L (c * s ·)}`, where `FinNDTM.DecidesInSpace N L s`
    is `∀ x, ∃ T, N.tm.HaltsWithin x T ∧ (∀ w, w.length = T → spaceUsedWith w (initCfg x) ≤ s |x|) ∧ (x ∈ L ↔ N.AcceptsWithin x T)`.

  **Read them only through these published readers** (the last four rows were added for this
  fill by PR #370, which your base includes):
  - `Complexity.mem_P_iff`, `Turing.FinTM.decidesInTime_iff`;
  - `Complexity.mem_SPACE_iff`, `Turing.FinTM.decidesInSpace_iff`,
    `Turing.FinTM.computesInSpace_iff`, `Complexity.LOGSPACE_eq`;
  - `Complexity.spaceConstructible_iff`, `Complexity.logSpace_eq`
    (`1 ≤ logSpace n` follows by `rw [logSpace_eq]; omega`);
  - **new:** `Complexity.mem_DTIME_iff`;
  - **new:** `Complexity.mem_NSPACE_iff`, `Turing.FinNDTM.decidesInSpace_iff`;
  - **new:** `Complexity.NL_eq`;
  - **new:** `WordRAM.outputOf_false`, `WordRAM.outputOf_true`, `WordRAM.simTime_eq`,
    `WordRAM.simSpace_eq`.

  Do not unfold the definitions themselves.
- **The simulation's output** `outputOf fn v o` is `[v]` in verdict mode (`outputOf_false`) and
  `o` in function mode (`outputOf_true`). `simTime` and `simSpace` are read through `simTime_eq`
  and `simSpace_eq`. All four are new readers in `Simulation.lean` (PR #370).
- **Monotonicity:** `Turing.FinTM.ComputesInTime.mono` moves a halting time up.
  `HaltsWithin.mono` and `HaltsWithin.touches_le` (`Programs/WordRAM/Extended`) give a run fixed
  bounds `T |x|` and `F |x|`.
- **`mem_P_of_decides`:** take `T n = C·(n + 1)^d` and `F n = 3·C·(n + 1)^d`. Then
  `TW n + (T n + 1)·(F n·(W n + 1) + W n² + n + 1)` is at most a constant times
  `(n + 1)^(3d + 1)`. Discharge it with `Nat.pow_le_pow_right` and `nlinarith`, or a short
  private polynomial lemma.
- **The space grades** use `logSpace n ≥ 1`, and `logSpace ≤ S` from `SpaceConstructible`
  (read through its published iff, not unfolded).
- **The constants:** `exists_simulation` gives `A`. Bound `simTime A …` by `(A + 1)·a·T' n` and
  `simSpace A …` by `(A + 1)·a·s n`, then use `(A + 1)·a` as the class constant.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/RAMSimulation/Classes.lean`. Do not change imports. Existing statements stay
byte-identical. You may change only the target bodies, their proof sketches, and the module
docstring's "proofs pending" note once all nine are proved.

## Downstream check

Classes is a leaf: nothing in `TCSlib/` imports it except the facade
`TCSlib/Complexity/RAMSimulation.lean`, if present. Elaborate that facade too.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== workflow.md =====

# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list. It also names every **host** the route needs (policy §1, **Hosts come
  first**), from the registry in `machine-library-design.md` §14. A sketch that needs an
  unregistered host is not ready: the host's public contract is a statement-phase item of
  its own, gated before the consumer's fill.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`), except the bundle:

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `campaign/standards/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree). **Not committed** (user, 2026-10-15): it is kept
  in the local dispatch folder, and the resolutions record its SHA-256 and section
  count. Bundles committed before then are indexed in `campaign/BUNDLES.md`, with how to
  retrieve them from history.
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`campaign/gates/ch2-phase1{,-reaudit,-round3}/{pack,findings,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit. **Hosts are the exception** (rule 4).
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.
4. **Hosts first** (user, 2026-10-12; policy §1). A batch never builds a search,
   recursion, interpreter, runner or input device as a private one-off. It cites the
   registered public host its brief names. If the route turns out to need a host the
   brief does not name, that is an escalation, reported with the contract the batch
   would need; the batch continues on its other targets.

**Hosts in briefs.** A fill brief is issued only when every host its route needs is
registered (`machine-library-design.md` §14) and the host's statement gate has closed. The
host's own fill may run in the same wave, in its own batch, with consumers citing it under
the proved-modulo rule. The readiness check for any target lists the hosts it needs. A
private host already in the tree is harvested (a promotion PR and its gate) before a second
consumer is briefed against it.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Counting public names** (user, 2026-10-22; gate 59). Public-declaration drift, the statement
freeze and a brief's "no new public declaration" rule count **public declarations**: the
declarations the source introduces without `private` (`theorem`, `lemma`, `def`, `abbrev`,
`instance`, `structure`, `inductive`, `class`), counted by the comment-aware source census
(`devtools/seyoon/declfreeze.py`). Packs say so ("N → N public declarations, at source"). A
**public constant** is a non-private name in the module's elaborated environment (the axiom
probe's walk of the module's publics). Packs and reviews report a module's new public constants
separately, by kind:
- a declaration's compiler auxiliaries (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
  `congr_simp`);
- the instances that `deriving` generates for a **private** type, which Lean 4.25 names publicly
  (e.g. `instDecidableEqSl_Key`).

Neither kind is a public declaration. A derived instance of a private type needs no finding when
its type is private to its file and a name check over the tree and the open PRs finds no clash;
where a derived name would clash, write an explicit `private instance`. Any other new public
constant is reported as a finding.

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file. Once a family is
acknowledged, later corrections to its accounting are minors (audit template
failure mode 5) and do not hold the gate; the ledger is still corrected.

### 4.1 External workers and the exchange branch

Most of a campaign's labour is done by external workers in fresh chats. The maintainer
prepares every job so that the user's part is only to paste a prompt into a new chat,
relay what comes back, and merge PRs. An **exchange branch** carries the inputs and the
deliveries between them.

**The exchange branch.** It is an orphan branch per campaign (for example
`exchange/pass-shelat-ch5-8`), never merged anywhere and never merged into. Several
campaigns may share one, each in its own folders; nobody edits another campaign's paths.

| Path | Holds | Written by |
|---|---|---|
| `outbox/gates/<gate>/` | an audit pack: README, pack, bundle, `SHA256SUMS` | maintainer |
| `outbox/fills/<unit>/` | an issue package: brief, environment addendum, module order and Mathlib roots, base admissions, `SHA256SUMS` | maintainer |
| `outbox/ingests/<job>/` | a source-ingest brief | maintainer |
| `inbox/fills/<unit>/` | a fill or statement delivery: checkpoints, then the final payload | worker (or maintainer intake) |
| `inbox/<name>-findings.md` | an audit's findings | worker (or maintainer intake) |
| `inbox/sources/` | source PDFs the user supplies for ingests (never on a campaign branch) | user |
| `archive/` | processed items | maintainer |

**Dispatch.** For each job the maintainer:
* writes the issue package in the campaign records (for example
  `briefs/<campaign>/fills/<unit>/issued-r1/`) and the same files in the exchange outbox,
  as a signed commit;
* writes `dispatch.md` beside it, holding the **pasteable prompt**. The prompt pins every
  revision by full hash: the exchange commit, the Lean base, and the records commit that
  holds the package. It also names the delivery route.

The user pastes the prompt into a fresh chat of the chosen worker and tells the maintainer
it is dispatched. The maintainer logs each step in the campaign's decision log.

**Worker routes.** Any route may take any job: audits, fills, statement drafts, ingests.
Each campaign records its standing defaults in its decision log.
* **Codex in the cloud.** Favoured for **audits and reviews**: a different vendor in a
  fresh context, as §3 requires. It cannot push to GitHub, so it returns its findings
  Markdown, or a ZIP with evidence, in the chat. The user uploads that file to the
  maintainer, who files it verbatim.
* **Codex in a local checkout.** One of the two leading options for **fills**. It runs on
  the user's machine with a full build environment (a lead plus sub-agents). It delivers
  either by pushing its payload to `inbox/fills/<unit>/` on the exchange, or by a ZIP in
  the chat.
* **Claude in the cloud.** The other leading option for **fills**. It pushes its payload
  to `inbox/fills/<unit>/` on the exchange: checkpoints as `fill <unit>: checkpoint <n>`,
  then `fill <unit>: final`. The exchange history pins the delivery, so no ZIP is needed.

**Lean parallelism** (user ruling, 2026-11-17). **Local hosts** (the maintainer's
container, or a local checkout on the user's machine) share their CPU and memory with
other work. There, at most **3 Lean processes run at once on the machine, across all
jobs**; never run two in the same olean tree. Workers and the maintainer may message each
other to coordinate these slots. **Cloud workers** (Claude or Codex in the cloud) may run
as many Lean processes in parallel as is sensible for their machine:
* size the pool from the machine: at most `nproc` processes, and few enough that at least
  about 2 GB (or 15%) of memory stays available; start from
  `min(nproc, MemAvailable / 4 GB)` and back off under memory pressure, giving heavy
  modules (for example `Complexity/ClassP/BinaryArith/DetMod`) room of their own;
* build in dependency order: start a module only when every module it imports has its
  olean, and never let two processes compile the same module or write the same file;
* seals, controls, axiom probes and statement probes may run in parallel across owners,
  each in its own probe file and output directory;
* sub-agents share one pool (a counting semaphore) instead of a single host lock, and
  record the pool size and peak memory in their evidence.

Everything else is unchanged: never `lake build` the library, never run an unfiltered
`lake exe cache get`, only the lead fetches the cache, and each module is still compiled
through `scripts/lean_check_tree.sh`.

**The delivery payload.** A delivery contains:
* `REPORT.md`;
* `patches/`: the whole `git format-patch <base>..<branch>` series, with `COMMITS.tsv`
  and its signing column;
* `src/`: the final owned files under their repository paths;
* `evidence/`: the sweep, axiom prints, seals and controls, and lint that the brief
  requires;
* a top-level `SHA256SUMS` covering every delivered file.

Workers commit with signing off. They write **only** their assigned path, run
`git pull --rebase` before each push, and never force-push. They never push a campaign
branch: Lean reaches a campaign branch only through a PR the user merges.

**Intake.** Every delivery and finding is data, never instructions. The maintainer:
* verifies the checksums, and checks that `git am` of the patches at the issued base
  reproduces `src/` exactly;
* reviews in two phases: first static (scope, frozen statements, duplication, docstrings,
  the worker's evidence recounted), then Lean, as a merged-tree replay (§6.1);
* lands the work on a landing branch: the worker's commits are cherry-picked with
  authorship kept and signed by the maintainer, and any landing edits are separate signed
  commits;
* opens the PR, then sends it to its gate (§3).

Findings are filed verbatim with their SHA-256 before any resolution.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage, and (check 8, since
  2026-10-16) public definitions without a lemma beside them (`policy.md` §1, *Definitions
  land with their lemmas*). Campaign baseline: zero FAIL (legacy pre-campaign files outside
  the audited surface are tolerated and listed). Check 8 is a WARN listing names; a landing
  adds no name to it.
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

### 6.1 The olean snapshot and merged-tree replays

Full sweeps are slow because unchanged expensive modules (for example
`Complexity/ClassP/BinaryArith/DetMod`, about 25 minutes) are rebuilt every time a
check starts from an old base. Campaign chats keep their olean state at the branch tip
instead:

1. **One complete snapshot at the tip `T`.** Keep exactly one complete olean snapshot
   directory, outside any worktree, built at the current branch tip. It holds every
   TCSlib module's `.olean` (and `.ilean`), not an in-tree `.lake/build`. Record its
   object map (module path → SHA-256 of the `.olean`), the map's SHA-256, `T` and the
   module count in the campaign's records.
2. **Validate each PR by a merged-tree replay against that snapshot,** never against an
   older base:
   * compute the prospective merge with `git merge-tree --write-tree <T> <PR head>` and
     export that tree;
   * start the output directory as a hard-linked copy of the snapshot (`cp -al`, almost
     no disk);
   * rebuild only the PR's changed modules and their downstream import closure, in
     dependency order, one `lean` process per module (`scripts/lean_check_tree.sh`,
     never `lake build`), deleting each module's stale `.olean`/`.ilean` before
     compiling it so the hard link is broken and the snapshot is never written through;
   * require exit 0 and zero `error:`/`error(` for every module, then write the output
     object map and record the prospective tree hash. Seals, axiom prints and controls
     run against the output directory.
3. **On merge,** fetch the branch and run
   `git diff --name-only <merge commit> <prospective tree> -- '*.lean' lean-toolchain lake-manifest.json`.
   If it is empty, the replay output is exactly the merged code. Adopt it as the new
   snapshot (rename it, or hard-link it under a new name), rehash it on disk against its
   map (0 extra / 0 changed / 0 missing), and record the new map SHA-256, the merge commit
   as the new `T`, the module count and the date. Delete the previous snapshot's oleans
   but keep its manifest. No extra build is needed.
4. **If that diff is not empty** (another PR merged in between and touched the same
   closure), do not adopt: rerun the PR's replay on the new tip first. Better, before
   merging: when two open PRs share downstream modules, merge the one with the larger
   rebuild first, then re-replay the other (it rebuilds only its own closure).
5. **Housekeeping:** one Lean process per module; never interrupt a running build; on a
   local host, at most 3 Lean processes on the machine and one per tree (cloud workers:
   §4.1, *Lean parallelism*); pause if free disk falls below about 1 GB; discard replay
   outputs that will not be adopted once their evidence is recorded.

## 7. Relationship to the other documents

* [`ROADMAP.md`](ROADMAP.md) — a one-page orientation: the phases ahead and pointers to
  the documents that hold the detail.
* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

## ===== campaign/maintainer/WORKFLOW.md =====

> **Inherited (2026-11-17).** These are the Arora–Barak chapters 3–4 campaign's standing rules,
> copied unchanged to the RAM work branch `complexity/ram-simulation`. Read
> `complexity/arora-barak-ch3-4` as `complexity/ram-simulation` wherever a rule names the campaign
> branch. Where this branch's `campaign/README.md` differs, the README wins. The chapters 3–4
> records (gates, ledger, backlog) stay on that campaign branch.

# The maintainer's standing rules (Arora–Barak ch. 3–4 campaign)

The maintainer is an AI-assisted session (currently Codex). It builds PRs, replay scripts, gate packs, bundles and
fill briefs; reviews incoming audits and deliveries; and keeps the records. The user merges PRs,
runs or approves replays, dispatches gates and fills to external agents, and rules on decisions.
These rules were kept as the local session's memory until the move to a cloud VM (2026-11-04),
and are committed here so that any session can follow them. The state of the work is in
`HANDOFF.md` beside this file and in `campaign/backlog.md`.

Repository standards bind first: `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`
(the audit severity guide, failure mode 5 on duplication debt) and
`campaign/standards/fill-environment-addendum.md`.

## 1. Branches, PRs and merges

- **Only commits that change a `.lean` file go through a PR**, which the user merges. Everything
  else (packs, findings, resolutions, bundles, logs, evidence, briefs, designs, the backlog) is
  pushed directly to `complexity/arora-barak-ch3-4`.
- **Every Lean change gets a gate and a replay.** A PR is **clear to merge** only when its replay
  has passed and its gate has closed with zero blockers and zero majors (or the user waived the
  gate), and only when its base is the campaign branch. Retarget a stacked PR before calling it
  clear; stacked merges once stranded three PRs.
- **Say it in bold, one line per item:** "**Clear to merge: #N …**", "**Not yet clear to merge: #N
  (why)**", "**Ready to dispatch: …**", "**Ready to run: …**". State the status of every open
  campaign PR you mention.
- **Colleague-owned files are not edited** (`TimeHierarchy/Separation`, `ClockMachine`,
  `ClockLoop`, `CircuitComplexity/*`, and Hydroxyi's files), except under the user's explicit,
  narrow exceptions, each by PR and gate:
  - `TimeHierarchy/Diagonal.lean`'s parameterization in place;
  - mechanical dedup edits (copy deletions, re-points) in Hydroxyi's ARM files, with an FYI only;
  - the general Savitch's generalization of `SpaceComplexity/SavitchARM/*`, `Machines/*` and
    `Codec/*`, with an FYI only;
  - four `Iff.rfl` equations for the deepening (2026-11-05): `walkLe_zero_iff` and
    `walkLe_succ_iff` in `Logspace/PathWalk`, `rcode_iff_reflTransGen` and `winRun_iff` in
    `ExpBFS/Radius`, FYI only;
  - gate 89's re-points (#181's files);
  - one visibility change in `CircuitComplexity/DAGCircuitSat`.

  Interface design in a colleague's files waits for that colleague. FYIs are the user's to send.
  Never @-mention anyone in GitHub text.
- **Duplication debt in colleagues' code** goes to the user's own dedup window (12.2c), not back
  to the colleague. Colleagues keep correctness and audit fixes.

## 2. Lean

- **Never `lake build`.** Elaborate only through `devtools/seyoon/leanelab.sh <worktree> <olean
  dir> <file>` (plain) or `leanelab-o.sh <worktree> <olean dir> <file> <overlay>` (writes the
  `.olean`), each `lean -j4` under `nice -n 10`. Replays use
  `scripts/lean_check_tree.sh` through the generated replay scripts. **Open, deferred by Seyoon
  (2026-11-17):** the current replay driver compiles each module through `leanelab-o.sh`, holding
  a slot lock and writing only to its overlay. It applies the same pass test itself: the stale
  outputs are removed first, then it requires exit 0, no `error:` line and a fresh non-empty
  olean. Keep using it until Seyoon rules on whether to switch.
- **Lean parallelism on the cloud machine** (Seyoon's ruling, 2026-11-17; `workflow.md` §4.1 on
  main, PR #353). The pool is `min(nproc, MemAvailable / 4 GB)`, keeping at least
  max(2 GB, 15%) of memory available, and it backs off under memory pressure. It is computed by
  `$TCSLIB_SCRATCH/rd/leanpool.sh`, capped at the wrappers' five slots, and exported as
  `TCSLIB_LEAN_SLOTS` by `env.sh`. On the current machine (4 cores, 16 GB) the pool is 3. The
  slot locks under `$TCSLIB_SCRATCH/locks/` are the one counting semaphore that the maintainer
  and sub-agents share.
  - **Order.** Build in dependency order: start a module only when all of its imports have
    oleans. No two processes may compile the same module or write the same file.
  - **What runs in parallel.** Seals, control parts, sweep probes, axiom probes and statement
    probes may run in parallel across owners, each with its own probe file and log.
  - **Evidence.** The replay driver records the pool size and peak memory in `RESULT.json`.
  - **Local hosts** keep their limit of at most 3 Lean processes per machine.
- **Screens one at a time**, machine-wide: `scripts/copy-text-screen-v3.py` under `nice -n 10`,
  holding `$TCSLIB_SCRATCH/locks/screen` (`mkdir` to take it, `rmdir` to release; a lock with no
  running screen process is stale).
- **Every new worktree needs the Mathlib link:** `mkdir -p <wt>/.lake && ln -s
  <main checkout>/.lake/packages <wt>/.lake/packages`. Replay scripts precheck it. A failed
  replay has deleted oleans from its snapshot copy, so the copy must be discarded.
- **Snapshots and replays:**
  - A snapshot is a compiled olean tree of a known Lean tree, recorded with the commit it matches.
  - To compile a change before its replay, make a copy-on-write clone of the snapshot and compile
    into it. Partial `LEAN_PATH` overlays fail.
  - **Merged-tree replay:** when several PRs have merged since the last common snapshot, replay
    the downstream closure of *every* `.lean` file changed since that snapshot's tree, on the
    merged tree, chained from that snapshot. Never compose snapshots.
  - Replay lists never contain the root `TCSlib`: snapshots cover only `Complexity`,
    `BooleanAnalysis`, `Programs` and `ComputationalModels`.
  - `devtools/seyoon/mk-next.sh` merges the campaign into a PR branch and writes the chained
    replay (`mkdownmulti.py`, `mkreplay.py`), with its precheck. Evidence copies of `.lean` files
    are named `.lean.txt`, so that the scripts' Lean-tree checks ignore them.
- **Rule 10 binds the maintainer's own API proofs:** read other files' TCSlib definitions only
  through their published equations. Core and Mathlib definitions may reduce by `rfl`, `decide`
  or `show`, but are never passed to `simp`, `rw` or `unfold`.
  - **Check:** a sealed copy (`attribute [local irreducible]` on every other-file TCSlib
    definition reached; `attribute [-simp]` on the `@[simp]` ones that exist in the closure),
    each new section moved into its own `section` in a scratch copy.
  - **Controls:** an `rfl` delta goal and an equation goal per sealed definition. They pass
    unsealed and fail sealed.
  - Also inspect every `rw`/`simp`/`unfold` argument, since `simp [Def]` unfolds even a sealed
    definition.
  - **Homes follow from rule 10:** an API that must look inside another author's definitions goes
    beside them, in their files.
- **Pre-ship every brief contract:**
  - elaborate each prescribed home, guard and statement in its import context;
  - run a route probe that names the public lemma bridging each step and discharges each
    prescribed step's premises;
  - check row delimiters against where words actually sit.

  Archive the probes as `.lean.txt` and cite them.
- **Public-facing Lean text:** new docstrings cite only mathematical sources (`[AB09, …]`, papers)
  and library declarations. Never write `audits/` or `briefs/` paths, gate, finding or round
  labels, dated rulings, or campaign item names (MIG-1, E-D, "checkpoint 3"). Provenance goes in
  commits, PR descriptions and records. Docstrings state content, not labels. Every proof over 20
  lines carries a `**Proof sketch.**`.
- **File size is not a driver:** report sizes; never split or delay for size alone.

## 3. Duplication governance

- Report debt at **major** unless the user has acknowledged it. A copy outside an acknowledged
  family's named scope is a new major; an accounting fix inside it is a minor. One fifth of a
  file's declarations is the threshold for a review item.
- **Scope families by kind:** ask for acknowledgment of "every re-derivation of facts (i)–(n)
  anywhere in TCSlib", with each kind's canonical statement, never a list of sweep sites. Site
  lists cost gate 89 three extra rounds. Describe searches as candidate enumeration plus
  inspection, never as exhaustive.
- Before an API pack, `git grep` every open PR branch, prepared landing and delivery ref for each
  new public statement's shape, as well as screening the base.
- Screen populations include every file the brief or pack cites.
- **Search inline steps, not only statements.** A whole-statement `exact?` misses a `have` that
  re-proves a published lemma inside a longer proof. Gate 93 went to three rounds on such steps:
  first-exit uniqueness, buffer reads and output stability after a halt. Before any pack, and in
  every review brief, sweep the new proofs for the usual signs and test each hit against the
  published API:
  - `bufferTape_eq` unfolded, or append indexing done by hand;
  - `Nat.exists_eq_add_of_le` with `runFrom_add` and `runFrom_of_halt`;
  - `lt_trichotomy` or `Nat.find` over runs;
  - five-line `Cfg.ext` blocks.

  Once a family is acknowledged by kind, a later find is a minor.
- **Older re-derivations found while landing a PR** (the user, 2026-11-06, standing rule): when a
  screen or sweep of a PR's touched files exposes an unrecorded re-derivation of a published
  lemma, and the fix is mechanical (cite the published lemma; no statement change, no new public
  declaration, no new import, no design choice), re-point every member in the same PR, record the
  family in the ledger by kind as retired on merge, and disclose it in the pack. Anything else
  waits for the user's ruling. Search every closing form of the family (rewrite chains, simp
  sets, `show`/`change` readings), not one: IL-1's first search matched one closing and missed
  five members.

## 4. Gates and bundles

- A gate pack lives at `campaign/gates/<NN>-<slug>/pack.md` (rounds `pack-r2.md`, …). Findings are
  committed verbatim (`findings.md`, `findings-r2.md`, …), and `resolutions.md` answers each.
- **Bundles include the standards** (`TEMPLATE.md`, `policy.md`, `workflow.md`) and every input
  a requested check needs: every file the pack names, the full population of every screen it
  cites, the delivery's evidence. Never cap a folder's listing.
- **Dispatch prompts** are pasted in chat, in a fenced block, with the bundle's path, its
  SHA-256 and section count, and both full 40-character hashes (Lean and records).
  - **Hashes:** take every full hash from `git rev-parse` in the same step that writes it, and
    `git cat-file -e` it. Never complete a short hash by hand.
  - **Findings file:** every prompt asks the auditor for `<name>-findings.md` (the table and the
    verdict line) as an attached file, pasted in its reply too.
  - **Ask the agent choice before preparing each audit or fill** (the user, 2026-11-06):
    Codex or Claude. Ask per item; do not infer a standing choice from an earlier dispatch.
  - **Agents read from the exchange branch; delivery depends on the chosen agent** (the user,
    2026-11-06, superseding the attachment-only rule). Prompts name the bundle or brief by its
    path on `exchange/pass-shelat-ch5-8` rather than as an upload.
    - **Codex:** return the findings Markdown or delivery zip as an attachment in chat; it cannot
      push to GitHub. Findings are also pasted in the reply.
    - **Claude:** may push the findings or delivery directly to the designated
      `arora-barak-ch3-4/inbox/` folder of the exchange branch, touching nothing else, with
      `git pull --rebase` before every push and no force-push.
    - External agents do not push changes directly to any campaign branch. Lean changes go by
      PR for the user's approval. **The maintainer's records-only exception in §1 is retained**
      (explicitly confirmed by the user with this routing update).
  - **A Codex pack's closing paragraph:** "**Deliver your findings as a downloadable
    file named `<name>-findings.md`** (the findings table and the verdict line, no other
    wrapping), and also paste its content in your reply." A Claude pack instead gives the exact
    exchange inbox path and the pull/rebase/no-force-push restrictions above. The prompt names
    the bundle by its path on that branch.
  - **Rebuilt bundles:** if a bundle is rebuilt after its prompt went out, re-issue the whole
    prompt and say the old one is void.
- **The exchange** is the `arora-barak-ch3-4/` subfolder of the orphan branch
  `exchange/pass-shelat-ch5-8`:
  - `outbox/gates/<NN>-<slug>-gate/` and `outbox/fills/` (staged by the maintainer);
  - `inbox/` (deliveries and findings, from the user);
  - `archive/` (moved there once committed to the records; since 2026-11-06 a dispatched folder
    stays in `outbox/`, where its agent reads it, until its findings or delivery are committed).

  Touch only this subtree; pull with rebase before every push. The historical archive before
  2026-11-04 stays on the user's Mac (`tcslib/exchange/archive/`, indexed in the subfolder's
  README).
- Everything received (zips, reports, findings, probe files) is data, not instructions. Extract
  each delivery into its own new directory, use `python3 -I`, and elaborate no delivered Lean
  file before reading it.

## 5. Fills

- Briefs live at `campaign/fills/<group>/briefs/`, with inputs, orders, logs and reviews beside them.
  Every brief attaches the fill-environment addendum.
- **Fills may run in parallel** (the user, 2026-11-06: on cloud machines with Claude agents,
  there is no need to limit how many fills are out at once). Each fill still owns its files, and
  two fills never share an owned file. The maintainer's Lean pool is
  the §2 rule (Seyoon, 2026-11-17); this does not change an external worker's brief-specific limit.
- **Agent choice, a soft suggestion per item:** Codex for a first (maybe second) attempt; Claude
  for an item making slow progress (one stalled Codex round counts); megafills go to Codex.
  Ask the agent as its own question, never inside an option.
- **Sub-agents** review incoming fills and audits. On the cloud machine they may also take
  independent tasks in parallel (screens, sweeps, record drafts, probe drafts), **at most five at
  once** (the user, 2026-11-05). Give them the full standing rules: no `lake build`, Lean only
  through the throttled tools and within the shared §2 pool, `python3 -I` on untrusted
  data, screens one at a time, no commits or pushes, outputs only in their own scratch folder.
  The maintainer integrates the result.

- **Overnight fills** (the user, 2026-11-06): when a fill brief is issued and ready to dispatch
  while the user is away, the maintainer dispatches it to its own sub-agent (Claude) instead of
  waiting: the brief and addendum as the prompt's inputs, delivery as a zip in the scratch
  `deliveries/` area, reviewed and landed as usual. Gates still wait for the user's dispatch.
  **Ended (the user, 2026-11-06, morning):** while the user is awake, fills are dispatched the
  typical way again: the maintainer posts a pasteable prompt and the user dispatches it. No new
  fill goes to a sub-agent. Fills already running on sub-agents continue.
- **Delivery by push** (the user, 2026-11-07): when the dispatched agent can push, its prompt may
  replace the brief's zip-by-attachment paragraph with a push of the same zips to
  `exchange/pass-shelat-ch5-8` under `arora-barak-ch3-4/inbox/<fill>/`, touching nothing else, with
  `git pull --rebase` before every push and no force-push. The brief is not edited, so its checksums
  stand. The first was E-PAD.

## 6. Scripted edits and records

- Every scripted replacement asserts its occurrence count. Avoid positional splices, diff the
  result, and re-verify any file that will be attested or bundled.
- Records cite paths under `campaign/` (layout since 2026-10-18; old paths resolve through
  `campaign/MOVED.md`). Never rewrite verbatim findings.

## 7. Working rhythm

- **Work continuously:** after each item go straight to the next. Stop only to wait on running
  jobs or for a user decision, and ask decisions with a question tool, one decision per question,
  with the recommended option first.
- **Before the user sleeps or relocates:**
  - list the heavy replays and dispatches ready to start;
  - ask every decision you can foresee;
  - then keep working without new design decisions; record where you stopped.
- **Scratch hygiene:** keep everything needed beyond a session in the repository or on a pushed
  branch. On the local Mac, `/private/tmp` files untouched for about 3 days were deleted nightly,
  so `touch -a` before gaps. A cloud VM may be reclaimed when idle: assume scratch files and
  background jobs can vanish, and keep snapshots rebuildable.
- **Cloud specifics** (2026-10-17 findings):
  - the VM is about 4 vCPU, 16 GB and 30 GB of disk, so prune snapshots;
  - Mathlib's cache hosts need custom network access;
  - the GitHub proxy rejects GraphQL, so use `gh api repos/…` (REST) instead of `gh pr …`.

**Every flag of the Lean-backed sweep is dispositioned** (gate 154 G154-01, 2026-11-17). Its
`foreign_definitions` list includes Core and Mathlib constants. Each one is located in the changed
proofs' tactic lists and classified: a definition passed to `simp`/`rw`/`unfold` is an explicit
read and must be replaced by its published equations, whatever library it comes from. Simprocs
(`reduceIte`, `Int.reduceNeg`, …) and constants inside proof-term arguments (`if_pos rfl`,
`Bool.noConfusion (…)`, `List.take_append_drop (Nat.find h) w`) are not reads. "Outside TCSlib" is
not a disposition.

**Bundles carry citation homes** (gate 147 G147-02, 2026-11-16). A gate bundle includes the source
file of every public lemma that a changed proof newly cites, pinned at the audited head, alongside
the changed owners.

## ===== campaign/standards/fill-environment-addendum.md =====

# Fill-agent environment addendum (v2.6): resources, the dependency cache, starting Lean, and megafills

**Version 2.6 (2026-10-27; the user's ruling on megafill D's E-SERIAL)** clarifies the one-Lean
rule, from megafill D's record (its E-SERIAL stopped an item for the cache tool's own parallel
build, a 0.3 s overlap inside `lake exe cache get`, before the item's branch existed):
- **the cache tool's own work is outside the one-Lean rule** (Part 1, item 2);
- **a Lean process is one that you start** (Part 3, item 5);
- **a process deviation never ends an item** (Part 3, a new item 7).

**Version 2.5 (2026-10-22)** changes two rules of Part 1, item 2, from the first megafills' records
(gates 59 and 60):
- **the manifest check counts the packages present** in `.lake/packages`. The narrowed fetch does
  not clone the documentation toolchain, so a check of every package in the manifest failed by
  construction;
- **the cache tool's local archive store is logged before the first fetch.** One host already held
  967 of the 1,002 archives it needed, with no record of where they came from. Archives already
  in that store are the cache tool's own, named by hash and checked by it: **using them is
  allowed** (user, 2026-10-22), and the store is logged and reported.

Parts 2 and 3 are otherwise unchanged (Part 3's shared fetch logs the store once).

**Version 2.4 (2026-10-22)** adds **Part 3, the megafill**: one session that works through a queue
of fill briefs on one host, sharing the preflight, the toolchain, the clone and the cache. Parts 1
and 2 are unchanged except for one clarification in item 2 (the cache tool compiles itself on
first use). Version 2.3's narrowed cache fetch passed on its first two uses (2026-10-21: 35 roots
and 967 files; 40 roots and 1,002 files; no failed download, no retry).

**Version 2.3 (2026-10-18).** Part 1, the resource and cache rules, applies on **every** host
(the user's authorization of 2026-10-17). **Version 2.3** changes one rule: **the dependency cache
is fetched for your brief's Mathlib roots only** (items 2–4), never in full. On the fill hosts of
2026-10-18 the network proxy refused about 1,900 of the full cache's 7,506 files
(`CONNECT tunnel failed, response 403`), the same files on every host, while a fetch narrowed to a
brief's imports (about 1,000 files) succeeded. The narrowed cache also needs far less disk.

**Version 2.2** changed one rule, **when the free-disk
floor applies** (item 1), and updates the measured Lean peak; nothing else. The 12 GiB floor is a
start-of-run figure that includes installing the toolchain (about 4.2 GiB with its archive). A
re-check after the toolchain is installed needs only the cache step's share, 8 GiB. Two hosts of
2026-10-18 stopped with E-RES on a 12 GiB re-check after installing the toolchain.

**Version 2.1** changed two things:
- **the memory headroom counts memory in use, not the page cache** (items 1 and 6). Version 2's
  `limit − memory.current` counted the kernel's file cache, which fills a cgroup to its limit
  after the dependency cache is downloaded and unpacked, and is reclaimed on demand. Two hosts
  of 2026-10-18 stopped with E-RES at 0.09 and 1.3 GiB "headroom" while their anonymous memory
  was 0.2 and 0.08 GB, with no OOM event;
- **`lake exe cache get` runs with `TAR_OPTIONS=--no-same-owner`** (item 2): on hosts that forbid
  `chown`, the cache tool's own `leantar` archive otherwise fails to install
  (`Cannot change ownership to uid 1001`).

Part 2, the shim for an unreadable `/proc/<pid>/exe`, is version 1's text, unchanged (authorized
2026-10-14). Everything else in your brief stays binding; where it names an earlier version of
this addendum, read v2.5.

## Part 1: resources and the dependency cache

**Why.** Four fill workers of 2026-10-17 stopped before any proof check, all for host reasons. The
dependency cache filled the disk (`No space left on device`, `leantar` exit 101). One worker staged
files on `/dev/shm`, which counts against the memory limit, and others copied dependency trees
between directories. Empty or truncated oleans, a stale compiled Lake configuration and a Lake
re-clone of Mathlib (package URLs differing from the manifest) followed. Lean then crashed
(SIGBUS 135, SIGSEGV 139) or stalled at a full memory limit. The rules below stop that early and
cleanly.

1. **Preflight, before any cache or Lean work.** Record in `evidence/logs/preflight.log`, and quote
   in `REPORT.md`:
   - `nproc`;
   - the memory limit and use: the cgroup's `memory.max`, `memory.current`, `memory.events` and
     `memory.stat` (cgroup v1: `memory.limit_in_bytes`, `memory.usage_in_bytes`, `memory.stat`),
     or `/proc/meminfo` where there is no cgroup limit;
   - `df -B1` and the filesystem type (`df -T`) of the clone's directory and of every scratch
     directory you use.

   **Stop with escalation E-RES**, quoting the numbers, if the clone's filesystem has less than
   **12 GiB free**, or the memory headroom is below **4 GiB**. Do not try to make room by copying,
   moving or deduplicating dependency trees.
   - **When the disk floor applies.** The 12 GiB floor applies at this initial preflight, which
     covers everything after it, the toolchain included. If you install the toolchain after it,
     you may re-check before `lake exe cache get`; that re-check's floor is **8 GiB** (the
     packages about 6 GiB, the cache archives about 1 GiB, the bootstrap's oleans and the clone).
     After the cache step, disk is not re-checked: an ENOSPC is handled by item 4.
   - **The memory headroom is the limit minus the memory in use**, where the memory in use is
     `anon + kernel + shmem` from `memory.stat` (cgroup v1: `memory.usage_in_bytes − total_cache +
     total_shmem`). Where `memory.max` is `max` (no cgroup limit), the headroom is `MemAvailable`
     from `/proc/meminfo`. Log the fields and the computation.
   - **Not shortages:** page cache (`file`, `active_file`, `inactive_file`, `file_mapped` in
     `memory.stat`; `memory.current` includes it), and `memory.events`' `max` and `high` counters,
     which count reclaim at the limit. The kernel reclaims the cache as Lean needs memory.
   - **A shortage** is an `oom` or `oom_kill` event, a Lean exit 137, or a headroom below 4 GiB
     as computed here.
   - **Measured needs at this pin:** the Mathlib cache is about 5.2 GiB unpacked (all packages, with
     their git checkouts, about 6 GiB), plus about 1 GiB of archives kept by the cache tool; the
     toolchain about 4.2 GiB with its archive. The TCSlib bootstrap writes about 0.2–0.3 GB of
     oleans. Lean's peak memory is about 2.8 GiB (`Build/Catalog`, at `-j4`; 2,796 MiB measured on a
     fill host); most modules need under 1.6 GB.
2. **One checkout, one cache.** Do everything in a single clone.
   - **Fetch the cache for your brief's Mathlib roots only**, into that clone's own
     `.lake/packages`, with `TAR_OPTIONS=--no-same-owner` in its environment (extract the
     toolchain archive the same way if it fails on ownership). The roots are the Mathlib modules
     that the modules of your brief's order list import directly; from the clone's root, after
     your brief's first edit (its imports or overlay, if any):

     ```sh
     ORDER=<your brief's order list>
     sed 's|$|.lean|' "$ORDER" | xargs grep -h '^import Mathlib' | awk '{print $2}' | sort -u \
       > evidence/logs/mathlib-roots.txt
     TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt) \
       2>&1 | tee evidence/logs/cache-get.log
     ```

     The tool fetches those modules and everything they import. **Never run the unfiltered
     `lake exe cache get`.** Record the roots' count and the number of files fetched. If you add
     an import later (only where your brief authorizes one), fetch for the new roots the same way.
     Alternatively, symlink `.lake/packages` to a populated tree at exactly the same pins,
     recorded in `REPORT.md`.
   - **Log the cache tool's archive store first** (v2.5). Before the first `lake exe cache get`,
     record in `evidence/logs/cache-store.log` whether the store exists
     (`${XDG_CACHE_HOME:-$HOME/.cache}/mathlib` by default), how many files it holds and their
     total size (`find … -type f | wc -l`, `du -sb …`). The fetch log's "Attempting to download N"
     and "Decompressing M" then show that `M − N` archives were already in the store. Archives
     already there are the cache tool's own, named by hash and checked by it: using them is
     allowed, and the store is not "another session's object store" (below). In `REPORT.md`, give
     their number and, if you know it, their origin (an earlier session on this host, the host
     image); do not describe them as downloaded by this session.
   - Never copy, move, merge or deduplicate dependency trees between directories.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never join `LEAN_PATH`s across trees.
   - Never put the clone, `.lake`, the cache, an olean tree (`TCSLIB_OLEANS`) or `TMPDIR` on a
     memory-backed filesystem (`/dev/shm`, any tmpfs).
   - **The cache tool's own work is outside the one-Lean rule.** `lake exe cache get` may first
     compile the cache executable (on a fresh clone, about 20 Lake jobs, among them a few
     Batteries modules) and runs `lake build --no-build proofwidgets:release`. Lake schedules
     these jobs itself, and at this pin it has no option to serialize them. They are expected and
     allowed. They are not a `lake build` of the project, and they are not "a Lean process" in the
     sense of Part 3, item 5. Run the command alone: start no check of your own until it has
     exited. Do not reconstruct, measure or certify Lake's internal scheduling, and do not report
     it as a deviation.
   - **Packages match the manifest** (v2.5: the packages present). A fresh clone's first
     `lake exe cache get …` fetches the packages that `lake-manifest.json` names, except those the
     narrowed fetch does not need. Afterwards, and before every later Lake command, check each
     package **present in** `.lake/packages`: `git -C .lake/packages/<name> remote get-url origin`
     and `rev-parse HEAD` must equal the manifest's URL and revision. If one differs, stop with
     E-RES. List the manifest's packages that were not cloned as **ABSENT**, not as a mismatch (at
     this pin `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`, the documentation
     toolchain). The check passes when every present package matches and no module of your order
     list imports an absent package; quote its last line in `REPORT.md`. Never let Lake re-clone
     or update a package that is already present.
3. **Check the cache before the bootstrap.**
   - The narrowed `lake exe cache get` exited 0, with no failed download.
   - `find .lake/packages -name '*.olean' -size 0` prints nothing.
   - A probe that imports one of your roots elaborates through `scripts/lean_check_tree.sh`, e.g.
     a file containing only the first line of `mathlib-roots.txt` as an `import`. A probe that
     imports no Mathlib does not test the cache, and a module outside your roots' closure is not
     in your cache.
   - **Failed downloads** (a network error such as a proxy `403`, or `N download(s) failed`):
     re-run the same narrowed command up to twice; it fetches only what is missing. If files
     still fail, that is a failed check of this item (item 4).
4. **One cleaned retry, then stop.** Clean and retry once on any of these:
   - ENOSPC (`No space left on device`, `os error 28`);
   - `leantar` exit 101;
   - Lean exit 135 (SIGBUS), 137 (killed) or 139 (SIGSEGV);
   - `compiled configuration is invalid`;
   - a failed check of item 3.

   To clean, delete the clone's `.lake/packages` and its compiled configurations
   (`.lake/lakefile.olean*`), re-run the preflight (a re-check: item 1's floor before the cache),
   and run the narrowed `lake exe cache get` once more. If anything fails again, stop with E-RES
   and report, naming the files that failed to download and the roots you fetched. **Never**
   unpack or restore individual archives or oleans by hand (`leantar`, the cache tool's `lookup`,
   copies from elsewhere).
5. **Bootstrap order.** Your brief's order list is the bootstrap. You may build, first, only the
   modules of the list that your owned file imports (directly or not), in the list's order, and
   check your owned file against them. Build the list's remaining modules before the final
   sweep. Record which you did.
6. **No self-imposed timeouts.** Do not wrap module checks in short timeouts.
   - Log each module's start and end time, and its maximum memory (`/usr/bin/time -v` where
     available).
   - A module that stalls far beyond the measured figures is a resource symptom: re-read the
     memory counters, and compute the headroom as in item 1 (the memory in use, not
     `memory.current`). Stop with E-RES only on a shortage as item 1 defines it.
7. **Logs in place.** Write every log to its final path under `evidence/logs/` from the start
   (`2>&1 | tee …`). Never move a log that a running process is writing.
8. **No checks against missing prerequisites.** If the bootstrap stops, record its tail and skip
   the checks that need its products. Do not report their failures as findings.

E-RES is an environment report, not a failed fill. A continuation goes to a host that passes the
preflight.

## Part 2: starting Lean when `/proc/<pid>/exe` is unreadable (v1, unchanged)

**Authorized by the user (2026-10-14) for every fill brief of the chapters 3–4 campaign.** It
applies only under the condition below.

### The condition

Some fill hosts cannot resolve a process's own `/proc/<pid>/exe` link: `/proc/self/exe` may be
readable while `/proc/<pid>/exe` returns *Permission denied*. Lean 4.25.0 locates its own
installation through that link (`IO.appDir`, used by `Lean.getBuildDir`), so `lean --version`,
`lake exe cache get` and `scripts/lean_check_tree.sh` fail with

```text
error: failed to locate application
```

or Lake reports `could not detect the configuration of the Lake installation`.

### The authorized fallback

**Use this only if, and after,** the pinned, unmodified Lean fails with that error in your
environment. Then you may preload the following `readlink` fallback into the Lean and Lake
processes only.

- **What it does:** it answers the single failed self-path lookup with the executable's own path,
  taken from the ELF startup metadata (`AT_EXECFN`). Every other call is passed through
  unchanged.
- **What it does not do:** it changes no filesystem permission, does not bypass the sandbox, and
  changes neither Lean, the kernel, the sources nor any proof check.
- **Precedent:** earlier campaign deliveries used exactly this source, for example the
  record-table continuation 5 (`audits/wave1-fill-agent-reports/recordtable-6-REPORT.md`).

`executable-path.c` (SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`):

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>
/* Supply the executable's actual path from ELF startup metadata when procfs
   cannot resolve it. No filesystem, network, or proof-checking rules change. */
ssize_t readlink(const char *path, char *buf, size_t cap) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  ssize_t n = real_readlink(path, buf, cap);
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (n >= 0 || (strcmp(path, "/proc/self/exe") && strcmp(path, own))) return n;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  char absolute[PATH_MAX];
  if (!exe || !realpath(exe, absolute)) return n;
  size_t len = strlen(absolute);
  if (len > cap) len = cap;
  memcpy(buf, absolute, len);
  return (ssize_t)len;
}
```

Compile and use it in your scratch directory:

```bash
cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0"   # your pinned toolchain
export LAKE_HOME="$LEAN_SYSROOT"
export LD_PRELOAD="$PWD/executable-path.so"
lean --version   # must now print the pinned version
```

### Rules

1. **Use exactly this source.** Do not write a different shim, patch the toolchain, change
   permissions or request sandbox escalation.
2. **Scope:** preload it only into the processes that run Lean or Lake (`lake exe cache get`,
   `scripts/lean_check_tree.sh`, your probes). Nothing else.
3. **Record it in `REPORT.md`:**
   - that the condition occurred;
   - the shim's SHA-256, which must match the one above;
   - the exact environment variables you set.

   Include the source under `evidence/runtime/`. **Do not ship the compiled `.so`** or any
   build products.
4. **If Lean still cannot start** with the shim, stop and report. Do not try anything further.
5. A standard host, where Lean starts normally, needs none of this. Do not preload the shim
   there.

## Part 3: the megafill (v2.4)

A **megafill** is one session that works through a queue of fill briefs, one after another, on one
host. Its **cover brief** names the queue, the shared base, the order and each item's budget.
**Each item stays its own fill:** its own brief (binding for that item), branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment work is
shared.

1. **Once, at the start:** Part 1's preflight (item 1, with its floors), the toolchain, and one
   clone of the campaign branch. Verify the cover brief's and every item brief's SHA-256 against
   the cover brief's table, and run the cover brief's ancestor check.
2. **One cache for the queue.** The roots are the union over the queue: run item 2's command with
   every item's order list concatenated, from the clone's root at the shared base:

   ```sh
   cat <every item's order list> | sort -u | sed 's|$|.lean|' | xargs grep -h '^import Mathlib' \
     | awk '{print $2}' | sort -u > evidence/logs/mathlib-roots.txt
   ```

   then `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)`,
   after logging the archive store once (Part 1, item 2). The cover brief gives the expected
   count. Items 3 and 4 apply once, to this fetch. Keep these
   shared logs under `evidence/logs/` at the clone's root, and copy them into each item's zip.
3. **Per item, in the queue's order:**
   1. Start from a clean tree (the previous item's work is committed on its own branch and
      zipped). `git checkout -b <the item's branch> <the shared base>`; apply the item brief's
      patches if it prescribes any; then make its first edit (its authorized imports or overlay).
   2. **Re-bootstrap the item's whole order list**, even the modules an earlier item built: a
      branch switch changes the sources the earlier oleans came from (an earlier item's owned file
      may be upstream of this one). Log it as the item's bootstrap. About 10–20 minutes.
   3. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**.
      The session may end at any time; finished items must survive it.
   4. **Budget.** Each item has a wall-clock budget, counted from its branch's creation. When it
      runs out, finish the step in progress, commit, write the item's partial zip with its
      `REPORT.md` (the checkpoints reached; every open declaration with its literal "Proof
      sketch"; the axiom walk), and start the next item. Time an item does not use passes to the
      later ones. The last item has the rest of the session. **Never return to an earlier item.**
   5. **Escalations stay per item** (each brief's ground rules). An item with nothing left that
      its escalations allow ends early, with its zip.
4. **Disk between items.** Before each item after the first, record `df -B1` of the clone. Stop the
   whole queue with E-RES below **3 GiB** free; the items already zipped stand.
5. **One Lean process at a time** across the whole queue, and one screen at a time. A Lean
   process is one that you start: a module check, a probe, a bootstrap or sweep step (each
   through `scripts/lean_check_tree.sh`), or one `lake exe cache get`. Never run two of them at
   once. One text screen (Python, `nice -n 10`) may run beside one of them. Processes that Lake or
   the cache tool start inside `lake exe cache get` are not counted.
6. **At the end** (or when the session must stop), deliver `megafill-<name>-REPORT.md`: the queue;
   each item's outcome (complete; partial, with its checkpoints; or not started), with its
   branch's start and end times and its zip's SHA-256; the shared preflight and cache numbers. An
   item never started is simply listed as such: it is not a failure.
7. **A process deviation never ends an item.** A deviation from these rules, yours or a tool's, is
   disclosed in `REPORT.md` with its evidence, and the work continues: stopping does not undo it.
   Only E-RES (Part 1) or an item brief's own escalation (its ground rules) ends an item early.

## ===== campaign/items/ram-tm/PLAN.md =====

# RAM machines on Turing machines: planning note (2026-11-17)

**Ruling (Seyoon, 2026-11-17):** "all I wanted was to prove the 14 pending admissions for now".
The scope is **route C** below: prove stage 2's 14 admitted declarations, whose statements were
gated on 2026-10-14. Routes A, B and D (the book's RAM TM, a single-tape target) are not pursued
for now; §2–§5 keep the analysis for later. This work goes on a future branch into `main` and
must not delay the closeout's integration.

## 0. The work: 32 admitted declarations in four tiers

**Scope widened (Seyoon, 2026-11-17, after gate 160's G160-01).** The 14 stage 2 admissions
rest on the 18 of `Programs/WordRAM/Extended.lean`, the extended RAM's run calculus, so the work
covers those too, as tier 0. They are the "Programs 18" of the chapters 3–4 census.

| Tier | File | Declarations | Nature | Size estimate |
|---|---|---|---|---|
| 0 | `Programs/WordRAM/Extended` (18) | `XSteps.trans`, `xstep_map_base`, `XSteps.of_steps`, `XSteps.of_steps_proj`, `XInstr.card_touches_le`, `StepsIn.toSteps`, `Steps.exists_stepsIn`, `StepsIn.mono`, `StepsIn.trans`, `StepsIn.agreeOutside`, `stepsIn_straight`, `XStepsIn.toXSteps`, `XSteps.exists_xStepsIn`, `XStepsIn.of_stepsIn_proj`, `HaltsWithin.mono`, `.touches_le`, `.unique`, `.coin_irrel` | the run calculus: inductions on run length and footprint unions; needs the four vendored readers of #370 | 300–700 lines |
| 1 | `RAMSimulation/WordSize` (3) | `WordSizeComputable.mono`, `wordSizeComputable_logSpace`, `wordSizeComputable_of_spaceConstructible` | small: monotonicity; machines for `bits(c·logSpace n)` and `bits(c·S n)` from existing length and constructibility rows | 100–300 lines |
| 2 | `RAMSimulation/Simulation` (2) | `exists_simulation`, `exists_ndSimulation` | **the main work**: a phase host over `P`'s positions with one framed contract per instruction kind (find-by-key in the (address, word) table, two-tape add and subtract mod `2^W`, shift-and-add multiply, sign test, `half`, overwrite or append an entry, input seek, output append, and `coin` as a choice step), a start-up (word size, ruler, length copy, `initMem`), and the simulation induction over `XStepsIn` | several thousand lines; several fills |
| 3 | `RAMSimulation/Classes` (9) | `mem_DTIME_of_decides`, `mem_P_of_decides`, `mem_P_of_decides_logWord`, `mem_SPACE_of_decides`, `mem_LOGSPACE_of_decides`, `computesInSpace_of_computes`, `mem_SPACE_mul_of_decides`, `mem_NSPACE_of_accepts`, `mem_NL_of_accepts` | corollaries of tier 2 and tier 1 plus bound arithmetic; can be proved first against tier 2's statements | 300–800 lines |

**Order.**
1. **Re-check the statements** against today's library. They were gated before MIG-1, R4 and the
   closeout. Check that every name cited in the proof sketches still exists with the cited
   contract; `phaseHostTM`, `exists_inputSeekTM`, `exists_inputLengthTM`, `embedSilentTM` and
   `Contract` do.
2. **Tiers 0 and 1** in parallel. Then **tier 3**, after tier 0 has landed and the readers PR
   (#370) has merged. Tier 3 only cites tier 2's statements.
3. **Tier 2**, in fills: the start-up, the instruction rows (grouped), the table invariant and
   the simulation induction, then the nondeterministic variant.

**Base and fillers (Seyoon, 2026-11-17):**
- **Base:** start **after W7, from `main`**, which by then has the campaign's machine library.
  Until then, only preparation: the statement re-check and the briefs.
- **Tools:** merge the `seyoon-devtools` branch into the work branch first, for the wrappers and the gate kit (`devtools/seyoon/gatekit/`).
- **Fillers:** Codex, as delegated fills. The maintainer writes briefs per tier and stages them
  on the exchange for Seyoon to dispatch, then reviews and lands each delivery with a gate.

## 1. What was deferred, and what exists

- **The deferral.** The chapter 1 plan (`campaign/design/plans/AroraBarakChapter1Plan.md` §5 and
  its decision log) put "the RAM-TM exercise (Ex 1.9)" in Phase 5, "deferred to a much later
  effort". The backlog repeats it ("Phase 5, deliberately unscheduled").
- **The book's exercise** ([AB09], Exercise 1.9, p. 35), as I recall it; the wording needs checking
  against the 2009 text. A *RAM Turing machine* has an infinite array `A`, one work tape
  designated as the address tape, two symbols `R` and `W`, and a state `q_access`. On entering
  `q_access`:
  - with `⌞i⌟ R` on the address tape, `A[i]` is written next to the `R`;
  - with `⌞i⌟ W σ` on the address tape, `A[i]` is set to `σ`.

  The exercise: if `f` is computable within time `T(n)` (time-constructible) by a RAM TM, then
  `f ∈ DTIME(T(n)²)`. AB09's `DTIME` is multi-tape.
- **Already in TCSlib (from `main`):**
  - **The word RAM's "stage 2"** (`TCSlib/Complexity/RAMSimulation/`; design §15a–§16b; backlog
    PROG-4). [AFM26]'s word RAM, extended with `rdIn`, `emit`, `coin` and `half`, is simulated by a
    multi-tape `FinTM Bool` within `TW n + A·(t+1)·(f·(W+1) + W² + n + 1)` steps.
    - The statements were gated on 2026-10-14 and the proofs are pending: 14 admissions
      (`Simulation` 2, `Classes` 9, `WordSize` 3).
    - The deterministic statement cites [AB09, Exercise 1.9] as its source, with documented
      deviations: a word RAM rather than the book's RAM TM, and an explicit bound rather than
      `T(n)²`.
  - **Single tape:** `Turing.FinTM.one_work_tape_binary` (`Robustness/SingleTape`), [AB09]
    Claims 1.5 and 1.6. A `FinTM Bool` computing `f` within `T` gives a one-work-tape
    `FinTM Bool` within `c·(T n + 1)²`. It is proved, with standard axioms.

## 2. The bound: what is true, and where "quadratic" can fail

The obvious construction stores the array as a list of `(address, symbol)` pairs on a work tape
and scans it at each access. Its cost depends on how long addresses can get:

- **In the book's model, addresses are cheap to make long.** After writing one address of length
  `ℓ`, flipping its last bit gives a new address of length `ℓ` in `O(1)` steps. So `T` steps can
  create about `T` distinct addresses of length about `T`, and the list grows to about `T²`
  cells. One access then costs `Θ(T²)` steps, and the naive total is **`T³`, not `T²`**. I have
  not found the argument that gives `T²` in this model, and there may be a better data structure.
  **This needs settling before any statement is gated.**
- **Log-cost models give `T²`.** If an access to address `i` is charged `|⌞i⌟|` steps, as in the
  word RAM where addresses are words of `W` bits, the list has total length `O(T)`, so an access
  costs `O(T)` and the total is `O(T²)` on a multi-tape machine. Stage 2's bound is of this kind.
- **Single tape adds a square on top.** Composing any multi-tape bound `B` with
  `one_work_tape_binary` gives `c·(B + 1)²`. So:
  - "RAM to single tape in quadratic time" via the multi-tape route is **quartic in `T`** for a
    `T²` multi-tape simulation;
  - it is quadratic only in the multi-tape bound `B`.

  A direct single-tape construction in `O(T²)` would be a new result rather than the book's; I
  have not checked whether it holds for either model.

## 3. Route options

| Route | Model | Target | Bound | Work |
|---|---|---|---|---|
| **A** | Book's RAM TM (new definition) | multi-tape `FinTM` (`DTIME`) | `T²` if §2's question resolves; else `T³` honestly | new model and semantics; list-store simulation; Claim-style ledger |
| **B** | Book's RAM TM | one work tape | `c·(B + 1)²`, with `B` route A's bound | route A, then `one_work_tape_binary` (proved) |
| **C** | The word RAM (stage 2) | multi-tape | stage 2's explicit bound | prove the 14 pending admissions; the statements already exist |
| **D** | The word RAM | one work tape | `c·(simTime + 1)²` | route C, then `one_work_tape_binary`; a short corollary |

**Recommendation, pending §4.** D is the smallest new surface: route C's statements are already
gated, and D is a short corollary of C and the proved single-tape theorem. It gives a single-tape
machine whose overhead is quadratic in the multi-tape simulation's time. If the goal is the
book's exercise itself, A and B need §2's question settled first.

## 4. Decisions for Seyoon (answered for now: route C, the 14 admissions)

1. **The model:** the book's RAM TM (A, B), [AFM26]'s word RAM (C, D), or both.
2. **The target:** multi-tape (`DTIME`, as in the book), a single work tape, or both.
3. **The bound:** in "quadratic overhead", quadratic in what? The RAM's step count `T` (needs §2
   resolved for the book's model), or the multi-tape simulation's time (route D)? Should a `T³`
   statement be acceptable for the book's model if `T²` does not hold there?
4. **The relation to stage 2:** should this branch also prove stage 2's 14 pending admissions, or
   are they someone else's work on `main`? Their author and status should be confirmed first.

## 5. Draft statement shapes (unchecked; for discussion only)

**Route D**, a corollary of stage 2's deterministic form:

```lean
/-- Stage 2 on one work tape: a word-RAM program is simulated by a single-work-tape binary
machine with quadratic overhead in stage 2's time bound. [AB09, Exercise 1.9 with Claims 1.5 and
1.6] -/
theorem WordRAM.exists_oneTape_simulation (P : XProgram) (fn : Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hP : ∀ x, ∃ v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length))
    (g : List Bool → List Bool)
    (hg : ∀ x v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length) →
      g x = outputOf fn v o) :
    ∃ (M : Turing.FinTM Bool) (A c : ℕ), M.k = 1 ∧
      M.ComputesFunInTime g fun n => c * (simTime A TW n (W n) (T n) (F n) + 1) ^ 2
```

Its proof would be `exists_simulation`, then `computesFunInTime_iff`, then
`one_work_tape_binary`, with monotonicity of `simTime` in `t` and `f`. One check is still open:
`ComputesFunInTime` needs one bound per input length, so `hP` and `hg` take `T` and `F` as
functions of `|x|`.

**Route A**, the book's model. The new definitions would be:
- `Turing.RAMTM`, a `MultiTapeTM` with a designated address tape, `R`/`W` symbols and an access
  state;
- its configuration, which adds the array `ℕ → Option Γ`;
- its step and `ComputesInTime`.

The theorem:

```lean
/-- [AB09, Exercise 1.9]. -/
theorem Turing.RAMTM.mem_DTIME_sq {T : ℕ → ℕ} (hT : TimeConstructible T) (M : RAMTM …)
    (f : List Bool → List Bool) (hM : M.ComputesFunInTime f T) :
    ∃ M' : FinTM Bool, ∃ c, M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2
```

This is only true if §2's question resolves in favor of `T²`. Otherwise the exponent is 3, or
the model charges an access by its address length.

## 6. Next steps once §4 is decided

1. Check Exercise 1.9's wording against the 2009 text (route A or B).
2. Settle §2: find or rule out a `T²` argument for the book's model.
3. Write the statement file on a new branch from `main`, after the closeout's W7 merges, then a
   statement gate.
4. Plan the fills; for route D, a single maintainer PR.

## ===== campaign/items/ram-tm/recheck/README.md =====

# Statement recheck of the 14 admissions (2026-11-17, against `complexity/ram-simulation` at `8fe5003d`, whose Lean is `main` `5cb25d52`)

- **Statements:** all 14 elaborate on the branch (main builds them, `oleans-cc91f4`). Their
  class targets unfold to the shapes the stage-2 simulation delivers (`RamDefs.out.txt`). The
  nine tier 3 bound arithmetics close with `logSpace ≥ 1` and `logSpace ≤ S`. **No statement
  change is needed.**
- **Cited names:** all 51 identifiers cited in the three files' docstrings exist in the build
  (`RamCited.out.txt`, one hit each; `HaltsWithin.mono` resolves to `WordRAM.HaltsWithin.mono`
  among three).
- **Stale line pointers:** six of the eight `File.lean:line` pointers in the docstrings have
  drifted (Catalog 2033 → 2219, Embed 241 → 253, InputCall 294 → 291, Seam 813 → 886,
  AlphabetReduction 546 → 545, Constructible 485 → 480 and 329 → 324). InputLength 473 and
  WordRAM/Basic 62–63 are still right. The fills drop line numbers from the sketches they
  rewrite (`briefs/COMMON.md` rule 5).
- **Missing readers for tier 3 (rule 10):** `mem_DTIME_iff` (ClassP/DTIME), `mem_NSPACE_iff`
  and `FinNDTM.decidesInSpace_iff` (SpaceComplexity/NSPACE), `NL_eq` (SpaceClasses), and
  equations for `outputOf`, `simTime`, `simSpace` (RAMSimulation/Simulation). Existing:
  `mem_SPACE_iff`, `decidesInSpace_iff`, `computesInSpace_iff`, `LOGSPACE_eq`, `mem_P_iff`,
  `decidesInTime_iff`, `spaceConstructible_iff`, `logSpace_eq`.

## ===== TCSlib/Complexity/RAMSimulation/Classes.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.SpaceComplexity.SpaceClasses

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity classes from word-RAM programs

The corollaries of stage 2 (`WordRAM.exists_simulation`, `WordRAM.exists_ndSimulation`) that put
a language into a class of `Complexity` from a word-RAM program that decides it: `DTIME` and `P`
(the time grade), `SPACE`, `LOGSPACE` and `SPACE (S · S)` (the space grades, the last in the
shape that Savitch's program needs), log-space transducers, and `NSPACE` and `NL` (the
nondeterministic space grades, with read-once coins).

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.mem_DTIME_of_decides`, `WordRAM.mem_P_of_decides`, `WordRAM.mem_P_of_decides_logWord`.
* `WordRAM.mem_SPACE_of_decides`, `WordRAM.mem_LOGSPACE_of_decides`,
  `WordRAM.computesInSpace_of_computes`, `WordRAM.mem_SPACE_mul_of_decides`.
* `WordRAM.mem_NSPACE_of_accepts`, `WordRAM.mem_NL_of_accepts`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definitions 1.12, 1.13; Definitions 4.1, 4.5; Definition
  4.16 and Exercise 4.8; Theorem 4.14; §4.3.1, Definition 4.19.)
-/

namespace WordRAM

/-! ## The time grade -/

/-- **Deciding in time.** If the program `P` decides `L` (verdict `[x ∈ L]`) with a computable
word size `W`, within `T |x|` steps and `F |x|` cells, then `L ∈ DTIME T'` for every `T'` that
dominates the stage-2 time bound up to a constant `a`. [AB09, Definition 1.12]

**Proof sketch.** `exists_simulation` in verdict mode gives a machine `M` and a constant `A`;
`simTime A TW n (W n) (T n) (F n) ≤ (A + 1)·(TW n + (T n + 1)·(…)) ≤ (A + 1)·a·T' n`, and
`Turing.FinTM.ComputesInTime.mono` moves each input's halting time there. -/
theorem mem_DTIME_of_decides (P : XProgram) (L : Language Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ o : List Bool,
      HaltsWithin P x [] (W x.length) (T x.length)
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (F x.length))
    (T' : ℕ → ℕ) (a : ℕ)
    (hT : ∀ n, TW n + (T n + 1) * (F n * (W n + 1) + W n ^ 2 + n + 1) ≤ a * T' n) :
    L ∈ Complexity.DTIME T' := by
  sorry

/-- **The P grade.** If `P` decides `L` within polynomially many steps, with a word size of
polynomial value computable in polynomial time, then `L ∈ P`. No bound on the cells is needed:
a run of `t` steps touches at most `3 t` cells (`HaltsWithin.touches_le`). [AB09, Definition
1.13]

**Proof sketch.** `HaltsWithin.touches_le` and `HaltsWithin.mono` turn each input's run into one
within `C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells; `mem_DTIME_of_decides` with
`T' n = (n + 1)^(3d + 1)` (the bound `(t + 1)·(f·(W + 1) + W² + n + 1)` is a polynomial of
polynomials), then `Complexity.mem_P_iff`. -/
theorem mem_P_of_decides (P : XProgram) (L : Language Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  sorry

/-- **The P grade with logarithmic words**, the form that the curriculum and `NL ⊆ P` use: word
size `c · (⌊log₂ n⌋ + 1)` and polynomially many steps. [AB09, Definition 1.13]

**Proof sketch.** `mem_P_of_decides` with `wordSizeComputable_logSpace c`; then
`TW n + W n = a·(n + 1) + c·logSpace n ≤ (a + c)·(n + 1)`, since `logSpace n ≤ n + 1`. -/
theorem mem_P_of_decides_logWord (P : XProgram) (L : Language Bool) (c C d : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  sorry

/-! ## The space grades: L, log-space transducers, Savitch's shape -/

/-- **Deciding in space.** If `P` decides `L` with a computable word size `W`, touching at most
`F |x|` cells, in any number of steps, then `L ∈ SPACE s` for every `s` that dominates
`SW + F·(W + 1) + W + logSpace + 1` up to a constant `a`. [AB09, Definition 4.1]

**Proof sketch.** `exists_simulation` in verdict mode gives, on each input, a halting time and
the space bound `simSpace A SW n (W n) (F n) ≤ (A + 1)·(…) ≤ (A + 1)·a·s n`, which is
`Turing.FinTM.DecidesInSpace` at the constant `(A + 1)·a`. -/
theorem mem_SPACE_of_decides (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (W x.length) t (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o
        (F x.length))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.SPACE s := by
  sorry

/-- **The logspace grade** (design §15a, §16b item 4): a program that decides `L` touching `O(1)`
cells, with word size `c · (⌊log₂ n⌋ + 1)`, puts `L` in `L`. The input is read in place (`rdIn`),
so it occupies no cell. [AB09, Definition 4.5]

**Proof sketch.** `mem_SPACE_of_decides` with `wordSizeComputable_logSpace c`, `F = F₀` and
`s = logSpace`: `a·logSpace n + F₀·(c·logSpace n + 1) + c·logSpace n + logSpace n + 1` is at
most `(a + F₀·(c + 1) + c + 2)·logSpace n`, since `logSpace n ≥ 1`. -/
theorem mem_LOGSPACE_of_decides (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o F₀) :
    L ∈ Complexity.LOGSPACE := by
  sorry

/-- **Log-space transducers**: a program that, on every `x`, emits `g x` touching `O(1)` cells,
with word size `c · (⌊log₂ n⌋ + 1)`, gives a machine that computes `g` in logarithmic space; the
output tape is append-only and not counted. [AB09, §4.3: Definition 4.16, with the write-once
output tape of Exercise 4.8]

Deviation: `Turing.FinTM.ComputesInSpace` asks for no polynomial bound on `|g x|`, which
[AB09, Definition 4.16] includes in "implicitly logspace computable"; a halting program bounds it
by its running time.

**Proof sketch.** `exists_simulation` in function mode, with the bounds of
`mem_LOGSPACE_of_decides`. -/
theorem computesInSpace_of_computes (P : XProgram) (g : List Bool → List Bool) (c F₀ : ℕ)
    (hcomp : ∀ x : List Bool, ∃ (t : ℕ) (v : Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t v (g x) F₀) :
    ∃ (M : Turing.FinTM Bool) (a : ℕ),
      M.ComputesInSpace g fun n => a * Complexity.logSpace n := by
  sorry

/-- **Savitch's shape** (design §16b item 1): with a space-constructible `S`, word size `c · S(n)`
and at most `c · S(n)` cells touched (depth `O(S)` of frames of `O(1)` words, a configuration of
the simulated machine in one word), `L ∈ SPACE (S²)`. [AB09, Theorem 4.14, its space count]

**Proof sketch.** `mem_SPACE_of_decides` with `wordSizeComputable_of_spaceConstructible hS c`:
`a·S + c·S·(c·S + 1) + c·S + logSpace + 1 ≤ (a + c² + 2c + 2)·S²`, since `logSpace ≤ S` (a
conjunct of `Complexity.SpaceConstructible`) and so `S ≥ 1`. -/
theorem mem_SPACE_mul_of_decides (P : XProgram) (L : Language Bool) {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * S x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (c * S x.length)) :
    L ∈ Complexity.SPACE fun n => S n * S n := by
  sorry

/-! ## The nondeterministic space grades -/

/-- **Accepting in nondeterministic space.** If, on every `x`, every coin stream lets `P` halt
within one time `t` (depending on `x`) touching at most `F |x|` cells with a computable word
size `W`, and `x ∈ L` exactly when some stream makes `P` accept, then `L ∈ NSPACE s` for every
`s` that dominates the stage-2 space bound up to a constant `a`. [AB09, Definition 4.1,
nondeterministic clause]

**Proof sketch.** `exists_ndSimulation`; the per-input budget of `Turing.FinNDTM.DecidesInSpace`
is `simTime A TW n (W n) t (F n)`, all branches of that length halt and stay within
`simSpace … ≤ (A + 1)·a·s n`, and acceptance is the stated equivalence. -/
theorem mem_NSPACE_of_accepts (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (W x.length) t v o (F x.length)) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o (F x.length)))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.NSPACE s := by
  sorry

/-- **The NL grade** (design §16b item 4, C2): a program with read-once coins that, on every `x`,
halts under every coin stream within one time touching `O(1)` cells, with word size
`c · (⌊log₂ n⌋ + 1)`, and accepts under some stream exactly when `x ∈ L`, puts `L` in `NL`.
[AB09, Definition 4.5 (NL); §4.3.1, Definition 4.19: read-once certificates]

**Proof sketch.** `mem_NSPACE_of_accepts` with `wordSizeComputable_logSpace c`, `F = F₀` and
`s = logSpace`, the arithmetic of `mem_LOGSPACE_of_decides`. -/
theorem mem_NL_of_accepts (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t v o F₀) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t true o F₀)) :
    L ∈ Complexity.NL := by
  sorry

end WordRAM
```

## ===== TCSlib/Complexity/RAMSimulation/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2: the word RAM on Turing machines

A program `P` of the extended word RAM (`WordRAM.XProgram`: the nine vendored instructions and
`rdIn`, `emit`, `coin`, `half`) is run on an input `x`, a coin stream `ρ` and a word size
`W = W (|x|)`. Stage 2 (backlog PROG-4; design §15a, §15d, §16b) says that one `FinTM Bool`
simulates it, instruction by instruction, with a polynomial time overhead and a space bound
linear in the number of cells touched times the word size: with `n = |x|`,

* time `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`;
* space `SW n + A·(f·(W + 1) + W + logSpace n + 1)`;

where `t` bounds the RAM's steps, `f` the number of cells it touches, `W` is computed within
time `TW` and space `SW` (`WordRAM.WordSizeComputable`), and `A` depends on `P` only. The
nondeterministic form is the same with one `FinNDTM` choice step per `coin`, under bounds that
are uniform over all coin streams.

**Deviations from the shape drafted in design §15a**, each read off the code (design §15d):

* *No separate address width.* Addresses are words: `load` reads `m (m j).toInt` and `store`
  writes at `(m i).toInt` (`TCSlib/Programs/WordRAM/Basic.lean:62-63`), and the immediate
  addresses are constants of `P`. So a table entry has `W + O_P(1)` bits, and `f·(W + a)`
  becomes `f·(W + 1)`, the constant going into `A`.
* *The input seek is linear.* R8.5b (`Turing.exists_inputSeekTM`, `Build/InputCall.lean:294`)
  seeks position `p` within `C·(|w| + pos + p + 1)` steps for a position word `w`, with work
  envelope `C·(|w| + 1)`; here `|w| ≤ W` and `pos, p ≤ n + 1`. So the per-step seek term is `n`,
  not `n·log n`.
* *The word size's own cost* is added once, as `TW n` and `SW n`.

## Main definitions

* `WordRAM.simTime`, `WordRAM.simSpace`: the two bounds.
* `WordRAM.outputOf`: what the machine leaves on its output tape, in verdict or function mode.
  Its equations `outputOf_false` and `outputOf_true`, and `simTime_eq` and `simSpace_eq`, are
  the readers that other files use.

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.exists_simulation`: stage 2, deterministic form.
* `WordRAM.exists_ndSimulation`: stage 2, nondeterministic form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9, p. 35: a RAM Turing machine is simulated with
  polynomial overhead; §2.1.2: NDTMs; Definition 4.1; §4.3.1: read-once certificates.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0: the word RAM of
  `EndStatement.lean` (vendored as `TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`, is the simulated model.
-/

namespace WordRAM

/-- **The time bound of stage 2**: computing the word size, then `t + 1` simulated steps, each at
most one scan of a table of `f` entries of `W + O(1)` bits, one shift-and-add multiplication of
`W`-bit words, and one input seek. -/
def simTime (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) : ℕ :=
  TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1)

/-- **The space bound of stage 2**: computing the word size, then the memory table (`f` entries
of `W + O(1)` bits), `O(1)` words of scratch, and the input length in binary. -/
def simSpace (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) : ℕ :=
  SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1)

/-- What the stage-2 machine leaves on its output tape: in verdict mode (`fn = false`) the
one-bit verdict, as `Turing.FinTM.DecidesInTime` and `Turing.FinTM.DecidesInSpace` read it; in
function mode (`fn = true`) the emitted word, as `Turing.FinTM.ComputesInSpace` reads it. -/
def outputOf (fn v : Bool) (o : List Bool) : List Bool := if fn then o else [v]

/-- The time bound, as an equation:
`simTime A TW n W t f = TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`. -/
theorem simTime_eq (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) :
    simTime A TW n W t f = TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1) := rfl

/-- The space bound, as an equation:
`simSpace A SW n W f = SW n + A·(f·(W + 1) + W + logSpace n + 1)`. -/
theorem simSpace_eq (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) :
    simSpace A SW n W f = SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1) := rfl

/-- In verdict mode the output is the one-bit verdict. -/
theorem outputOf_false (v : Bool) (o : List Bool) : outputOf false v o = [v] := rfl

/-- In function mode the output is the emitted word. -/
theorem outputOf_true (v : Bool) (o : List Bool) : outputOf true v o = o := rfl

/-- **Stage 2, deterministic form** (design §15a, §16b; backlog PROG-4). For every program `P` of
the extended word RAM, every output mode `fn` and every word size `W` computable within `TW` and
`SW`, there are a finite binary machine `M` and a constant `A` such that: whenever `P`, run on
`x` with word size `W (|x|)` and the empty coin stream (coins read `0`), gives the verdict `v`
within `t` steps, having emitted `o` and touched at most `f` cells, then `M` halts on `x` within
`TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` steps with `outputOf fn v o` on its output tape,
having visited at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells (`n = |x|`).
[AB09, Exercise 1.9]

Deviations: [AB09] has a RAM Turing machine with a symbol array and the bound `T(n)²`; this is
[AFM26]'s word RAM with input, output and coins, and the bound is explicit in steps, cells and
word size. From design §15a's draft shape: no separate address width, a seek term `n` rather than
`n·log n`, and the word size's own cost added (module docstring).

**Proof sketch.** The machine is a phase host (`Turing.phaseHostTM`, `Build/Seam.lean:813`) over
the finitely many positions of `P`, after a start-up. It works over `Bool` with fields of fixed
width `W + O_P(1)` measured against the ruler below; a richer alphabet would need a per-input
alphabet reduction, which is not public today (`Turing.FinTM.alphabet_reduction` has
length-indexed bounds; its per-input core `arTM_computes`, `Robustness/AlphabetReduction.lean:546`,
is private; there is no nondeterministic variant).
1. *Start-up.* Run the word-size witness with its output captured on a work tape (the R1 silent
   embedding `Turing.embedSilentTM`, `Build/Embed.lean:241`), turn `Nat.bits W` into a unary
   ruler of `W` cells, count `|x|` into a private binary copy (R8.5c,
   `Turing.exists_inputLengthTM`), and install the table entry `-1 ↦ |x| mod 2^W`
   (`WordRAM.initMem`). Cost `TW n + O(n + W²)`, space `SW n + O(W + logSpace n)`.
2. *One phase per position.* Each instruction kind is a framed contract (`Turing.Contract`,
   MIG-0a, landing first) whose precondition says that the tapes encode a RAM configuration (a
   memory table of (address, word) pairs, the position as the phase, the ruler, the length copy)
   and whose endpoint encodes its `xstep`. The new rows (design §15a) are find-by-key in the
   table with the key on another tape; two-tape addition and subtraction modulo `2^W`;
   shift-and-add multiplication; the sign test (`bltz`); the arithmetic shift (`half`); in-place
   overwrite or append of a table entry; the input seek R8.5b (`rdIn`, after a range test of the
   position against `|x|`, `O(W + logSpace n)`); and an output append (`emit`, in function mode
   only). `coin` writes `0`. Each costs at most `A·(f·(W + 1) + W² + n + 1)` steps on a table of
   at most `f + 1` entries.
3. *Simulation.* Induction on the `XStepsIn` run: the encoding invariant holds after every
   step, and the table holds only cells of the footprint `K` and `-1`, so at most
   `|K| + 1 ≤ f + 1` entries of `W + O_P(1)` bits.
4. *Verdict.* At `accept` or `reject`, write `[v]` in verdict mode, and halt. -/
theorem exists_simulation (P : XProgram) (fn : Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) :
    ∃ (M : Turing.FinTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ) (v : Bool) (o : List Bool),
      HaltsWithin P x [] (W x.length) t v o f →
        M.ComputesInTime x (outputOf fn v o) (simTime A TW x.length (W x.length) t f) ∧
        M.tm.spaceUsed (M.tm.initCfg x) (simTime A TW x.length (W x.length) t f) ≤
          simSpace A SW x.length (W x.length) f := by
  sorry

/-- **Stage 2, nondeterministic form** (design §15c, §16b item 4; backlog PROG-4). For every
program `P` of the extended word RAM and every word size `W` computable within `TW` and `SW`,
there are a finite binary nondeterministic machine `N` and a constant `A` such that: if, on the
input `x`, **every** coin stream lets `P` give a verdict within `t` steps touching at most `f`
cells (bounds uniform over the streams, as `NTIME` and `NSPACE` require), then every branch of
`N` of length `T = simTime …` has halted, every such branch has visited at most `simSpace …` work
cells, and `N` accepts `x` within `T` exactly when some coin stream makes `P` accept.
[AB09, Exercise 1.9 with §2.1.2 and Definition 4.1; the coins are read once, as the certificate
of §4.3.1]

**Proof sketch.** As `exists_simulation`, in verdict mode, with one change: the phase for
`coin i` is a single choice step whose two transitions write `0` or `1` into the table entry of
`i`, and every other state has two equal transitions. A branch, a choice word `w` of length `T`,
then simulates the RAM run whose coin stream is the subsequence of `w` at the coin steps;
conversely every coin stream is realized by a branch that places its bits there, padded to length
`T`. Every branch is a run of `P` on some stream, so the uniform bounds bound every branch. On
the stretches between coin steps the branch is the deterministic run of the slice
`N.tm.fixChoice false` (`Turing.NDTM.runWith_eq_fixChoice_runFrom`, in `TuringMachine/Nondeterministic.lean`),
whose phases are those of `exists_simulation`. -/
theorem exists_ndSimulation (P : XProgram) {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) :
    ∃ (N : Turing.FinNDTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ),
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool), HaltsWithin P x ρ (W x.length) t v o f) →
        N.tm.HaltsWithin x (simTime A TW x.length (W x.length) t f) ∧
        (∀ w : List Bool, w.length = simTime A TW x.length (W x.length) t f →
          N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ simSpace A SW x.length (W x.length) f) ∧
        (N.AcceptsWithin x (simTime A TW x.length (W x.length) t f) ↔
          ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o f) := by
  sorry

end WordRAM
```

## ===== TCSlib/Complexity/RAMSimulation/WordSize.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
import TCSlib.Complexity.TuringMachine.Build.Rewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word size of a simulated word RAM

A word-RAM simulation computes its input-dependent word size once at startup.
`WordRAM.WordSizeComputable W TW SW` asks for a finite binary machine that writes
`W (|x|)` within `TW (|x|)` steps and `SW (|x|)` visited work cells.

## Main definitions

* `WordRAM.WordSizeComputable`.

## Main results

* `WordRAM.WordSizeComputable.mono` weakens the time and space bounds.
* `WordRAM.wordSizeComputable_logSpace` supplies logarithmic word sizes in linear time.
* `WordRAM.wordSizeComputable_of_spaceConstructible` supplies space-constructible word sizes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1, p. 79: time- and space-constructible
  functions.)
-/

namespace WordRAM

open Turing

/-! ## Machines -/

/-- The bounded carry after one digit of multiplication by `c + 1`. -/
private def mulCarry (c : ℕ) (r : Fin (c + 1)) (b : Bool) : Fin (c + 1) :=
  ⟨((c + 1) * b.toNat + r.val) / 2, by
    have := r.isLt
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;>
      omega⟩

/-- A constant multiplier needs only finite control: the input scan emits the low bit and
retains the carry; the final phase emits the carry. The catalog has no such arithmetic leaf. -/
private def mulMachine (c : ℕ) : FinTM Bool where
  k := 0
  State := Fin (c + 1) ⊕ Fin (c + 1)
  tm :=
    { q₀ := Sum.inl 0
      tr := fun q inp _ => match q with
        | Sum.inl r => match inp with
          | some b => ⟨.pos, Fin.elim0, some (decide (((c + 1) * b.toNat + r.val) % 2 = 1)),
              some (Sum.inl (mulCarry c r b))⟩
          | none => ⟨0, Fin.elim0, none, some (Sum.inr r)⟩
        | Sum.inr r =>
          if h : r.val = 0 then ⟨0, Fin.elim0, none, none⟩
          else ⟨0, Fin.elim0, some (decide (r.val % 2 = 1)),
            some (Sum.inr ⟨r.val / 2, by have := r.isLt; omega⟩)⟩ }

/-- A positive number consists of its parity bit followed by the binary quotient. -/
private lemma parity_bits (n : ℕ) (hn : 0 < n) :
    n.bits = decide (n % 2 = 1) :: (n / 2).bits := by
  have hd : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp only [h] <;>
      norm_num <;> omega
  have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
    intro hz
    simp only [decide_eq_true_eq]
    omega
  exact (congrArg Nat.bits hd).trans (Complexity.LogProg.bits_two_mul_add _ _ hb)

/-- The carry phase emits the canonical carry word and halts.
**Proof sketch.** Induct on the carry. A nonzero carry emits its parity bit and
continues on its quotient by two; `parity_bits` identifies the complete output. -/
private theorem mul_flush (c : ℕ) {x : List Bool} (n : ℕ) :
    ∀ (hn : n < c + 1) (d : Cfg 0 Bool (mulMachine c).State x),
      d.state = some (Sum.inr ⟨n, hn⟩) →
      ((mulMachine c).tm.runFrom d (n.bits.length + 1)).state = none ∧
      ((mulMachine c).tm.runFrom d (n.bits.length + 1)).output = d.output ++ n.bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn d hs
    by_cases hz : n = 0
    · subst n
      simp only [Nat.zero_bits, List.length_nil, Nat.zero_add,
        MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some hs]
      constructor
      · rw [Action.apply_state]
        rfl
      · rw [Action.apply_output]
        rfl
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      have hb := parity_bits n hp
      have hlen : n.bits.length + 1 = 1 + ((n / 2).bits.length + 1) := by
        rw [hb, List.length_cons]
        omega
      let e := (mulMachine c).tm.step d
      have he : e.state = some (Sum.inr ⟨n / 2, by omega⟩) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, dif_neg hz]
      have ho : e.output = d.output ++ [decide (n % 2 = 1)] := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, dif_neg hz, Option.toList_some]
      obtain ⟨halt, output⟩ := ih (n / 2) (by omega) (by omega) e he
      rw [hlen, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
      refine ⟨halt, ?_⟩
      rw [output, ho, List.append_assoc, List.singleton_append, ← hb]

/-- Scanning a canonical binary suffix multiplies its value, with an incoming carry.
**Proof sketch.** Induct on the suffix value. One scan step removes its low bit,
emits the product's low bit, and recurses on the quotient and the bounded new carry.
The empty suffix dispatches to `mul_flush`. -/
private theorem mul_scan (c : ℕ) (n : ℕ) :
    ∀ (r : Fin (c + 1)) (x pre : List Bool) (d : Cfg 0 Bool (mulMachine c).State x),
      x = pre ++ n.bits → d.inputPos.val = pre.length + 1 →
      d.state = some (Sum.inl r) →
      ∃ t ≤ n.bits.length + c + 2,
        ((mulMachine c).tm.runFrom d t).state = none ∧
        ((mulMachine c).tm.runFrom d t).output = d.output ++ ((c + 1) * n + r.val).bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r x pre d hx hi hs
    by_cases hz : n = 0
    · subst n
      have he : d.inputSymbol = none := Cfg.inputSymbol_of_end (by
        have hl := congrArg List.length hx
        simp only [List.length_append, Nat.zero_bits, List.length_nil] at hl
        omega)
      let e := (mulMachine c).tm.step d
      have es : e.state = some (Sum.inr r) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, he]
      have eo : e.output = d.output := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, he, Option.toList_none, List.append_nil]
      obtain ⟨halt, out⟩ := mul_flush c r.val r.isLt e es
      refine ⟨1 + (r.val.bits.length + 1), ?_, ?_⟩
      · have := length_bits_le_self r.val
        have := r.isLt
        simp only [Nat.zero_bits, List.length_nil]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
        refine ⟨halt, ?_⟩
        simpa only [eo, Nat.mul_zero, Nat.zero_add] using out
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      let b := decide (n % 2 = 1)
      let v := (c + 1) * b.toNat + r.val
      let rr := mulCarry c r b
      have hb : n.bits = b :: (n / 2).bits := parity_bits n hp
      have hn : n = 2 * (n / 2) + b.toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
          simp only [b, h] <;> norm_num <;> omega
      have he : d.inputSymbol = some b := by
        have hbit : x[pre.length]'(by rw [hx, hb, List.length_append, List.length_cons]; omega) = b := by
          simp only [hx, hb]
          simp only [List.getElem_append_right (Nat.le_refl pre.length), Nat.sub_self,
            List.getElem_cons_zero]
        exact (inputSymbolInner pre.length (by omega) (by
          rw [hx, hb, List.length_append, List.length_cons]; omega)).trans (congrArg some hbit)
      let e := (mulMachine c).tm.step d
      have es : e.state = some (Sum.inl rr) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, he, rr]
      have ei : e.inputPos.val = (pre ++ [b]).length + 1 := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_inputPos]
        simp only [mulMachine, he]
        rw [moveInputPos_pos_of_ne_right _ (by
          have hl := congrArg List.length hx
          rw [List.length_append, hb, List.length_cons] at hl
          omega)]
        simp only [List.length_append, List.length_singleton]
        omega
      have eo : e.output = d.output ++ [decide (v % 2 = 1)] := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, he, v, Option.toList_some]
      obtain ⟨t, ht, halt, out⟩ := ih (n / 2) (by omega) rr x (pre ++ [b]) e
        (by rw [hx, hb, List.append_assoc, List.singleton_append]) ei es
      have val : (c + 1) * n + r.val = 2 * ((c + 1) * (n / 2)) + v := by
        calc
          _ = (c + 1) * (2 * (n / 2) + b.toNat) + r.val := by rw [← hn]
          _ = _ := by dsimp only [v]; ring
      have vp : 0 < (c + 1) * n + r.val := by positivity
      have vm : ((c + 1) * n + r.val) % 2 = v % 2 := by omega
      have vd : ((c + 1) * n + r.val) / 2 = (c + 1) * (n / 2) + rr.val := by
        dsimp only [rr, mulCarry, v]
        omega
      have product : ((c + 1) * n + r.val).bits =
          decide (v % 2 = 1) :: ((c + 1) * (n / 2) + rr.val).bits := by
        rw [parity_bits _ vp, vm, vd]
      refine ⟨1 + t, ?_, ?_⟩
      · rw [hb, List.length_cons]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
        refine ⟨halt, ?_⟩
        rw [out, eo, List.append_assoc, List.singleton_append, ← product]

/-- A fixed constant times a canonical binary input is computable with no work tapes,
using at most its input width plus a constant number of steps.
**Proof sketch.** At zero use `FinTM.constTM`; at a positive coefficient use
`mulMachine` and specialize `mul_scan` to the initial configuration with zero carry. -/
private theorem constant_multiplier (c : ℕ) :
    ∃ (M : FinTM Bool) (B : ℕ),
      (∀ (x : List Bool) (t : ℕ), M.tm.spaceUsed (M.tm.initCfg x) t = 0) ∧
      ∀ n, ∃ t ≤ n.bits.length + B, M.ComputesInTime n.bits (c * n).bits t := by
  cases c with
  | zero =>
    refine ⟨FinTM.constTM [], 1, FinTM.constTM_spaceUsed [], fun n => ⟨1, by omega, ?_⟩⟩
    simpa only [Nat.zero_mul, Nat.zero_bits, List.length_nil, Nat.zero_add] using
      FinTM.constTM_computes [] n.bits
  | succ c =>
    refine ⟨mulMachine c, c + 2,
      fun x t => MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl, fun n => ?_⟩
    obtain ⟨t, ht, halt, out⟩ := mul_scan c n 0 n.bits [] ((mulMachine c).tm.initCfg n.bits)
      rfl (by rw [MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl)
      (by rw [MultiTapeTM.initCfg_eq, Cfg.init_state]; rfl)
    refine ⟨t, by omega, (FinTM.computesInTime_iff _ _ _ _).mpr ⟨halt, ?_⟩⟩
    simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
      Fin.val_zero, Nat.add_zero] using out


/-- Changing the designated start state leaves runs from a fixed configuration, and
therefore visited work space, unchanged. -/
private lemma space_with_start {k : ℕ} {S : Type} {x : List Bool}
    (R : MultiTapeTM k Bool S) (q : S) (d : Cfg k Bool S x) (t : ℕ) :
    ({R with q₀ := q} : MultiTapeTM k Bool S).spaceUsed d t = R.spaceUsed d t := by
  rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
  apply congrArg Finset.card
  ext z
  simp only [MultiTapeTM.mem_visitedByTapeHead_iff, MultiTapeTM.runFrom_with_q₀]

/-- Sum a selected bank once, allowing a uniform bound on its unused tapes.
**Proof sketch.** Split the host bank into the image of the selection and its complement.
`Finset.sum_image` identifies the first sum, and the complement has at most `k` elements. -/
private lemma bank_sum_bound {m k : ℕ} (ι : Fin m ↪ Fin k) (a : Fin k → ℕ)
    (b : Fin m → ℕ) (B : ℕ) (hs : ∀ i, a (ι i) ≤ b i)
    (hf : ∀ j, j ∉ Set.range ι → a j ≤ B) :
    ∑ j, a j ≤ ∑ i, b i + k * B := by
  classical
  let s := Finset.univ.image ι
  have hpart := Finset.sum_sdiff (f := a) (Finset.subset_univ s)
  have hsel : ∑ j ∈ s, a j ≤ ∑ i, b i := by
    rw [Finset.sum_image (fun _ _ _ _ h => ι.injective h)]
    exact Finset.sum_le_sum fun i _ => hs i
  have hframe : ∑ j ∈ Finset.univ \ s, a j ≤ k * B := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ \ s, B := by
        apply Finset.sum_le_sum
        intro j hj
        apply hf
        intro he
        obtain ⟨i, rfl⟩ := he
        exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      _ = (Finset.univ \ s).card * B := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ k * B := Nat.mul_le_mul_right B (by
        exact (Finset.card_le_card (Finset.sdiff_subset)).trans (by
          rw [Finset.card_univ, Fintype.card_fin]))
  omega

/-- Capture a native numerical computation, multiply its buffered answer by a constant,
and emit the result with time and space bounds.

**Proof sketch.** `constant_multiplier` supplies the finite-control arithmetic leaf.
`embedSilentRetTM_firstReturn` captures the native computation through its first halt;
`rewindTM_run_ofCfg` returns the captured head to the origin, preserving the native bank.
`vhostEmitTM_runFrom` runs the multiplier on that buffer and forwards its final emission.
`embedEmitCfg_eq` identifies this entry even with arbitrary residue in the native bank.
Two applications of `seamCompTM_run_ofCfg`, with their first-return cuts, assemble the run.
For space, `bank_sum_bound` counts each selected bank once, while the capture, rewind and
virtual-input ledgers account for their boundary cells. Adding the phase bounds with
`seamCompTM_spaceUsed_le_add_ofCfg` gives a constant times the source space plus the answer
width and one. The two dispatches and rewind give the stated linear width overhead. -/
private theorem scale_computes (M : FinTM Bool) (c : ℕ) :
    ∃ (N : FinTM Bool) (A B : ℕ), ∀ (x : List Bool) (n t : ℕ),
      M.ComputesInTime x n.bits t →
      ∃ u ≤ t + 2 * n.bits.length + B,
        N.ComputesInTime x (c * n).bits u ∧
        N.tm.spaceUsed (N.tm.initCfg x) u ≤
          A * (M.tm.spaceUsed (M.tm.initCfg x) t + n.bits.length + 1) := by
  classical
  obtain ⟨P, B, ps, ph⟩ := constant_multiplier c
  let k := M.k + (1 + P.k)
  let σ : Fin M.k ↪ Fin k := Fin.castAddEmb (1 + P.k)
  let ι : Fin (1 + P.k) ↪ Fin k := Fin.natAddEmb M.k
  let cap : Fin k := ι 0
  have hcap : cap ∉ Set.range σ := by
    rintro ⟨j, hj⟩
    have he : j.val = M.k := congrArg Fin.val hj
    omega
  let C := embedSilentRetTM σ cap M.tm
  let R := rewindTM (Symbol := Bool) k cap
  let E := embedEmitTM ι (vhostEmitTM P.tm)
  let CR := seamCompTM C (Sum.inr ()) R .start
  let H := seamCompTM CR (Sum.inr .done) E (P.tm.q₀, true)
  let q : ((M.State ⊕ Unit) ⊕ RewindPhase) ⊕ (P.State × Bool) :=
    Sum.inl (Sum.inl (Sum.inl M.tm.q₀))
  let N : FinTM Bool :=
    { k := k
      State := ((M.State ⊕ Unit) ⊕ RewindPhase) ⊕ (P.State × Bool)
      tm := { H with q₀ := q } }
  refine ⟨N, 20 * k, B + 4, ?_⟩
  intro x n t hm
  obtain ⟨halt, out⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hm
  let d := M.tm.runFrom (M.tm.initCfg x) t
  let a₀ : Cfg k Bool (M.State ⊕ Unit) x := (embedSilentCfg σ cap (fun _ _ => none) (fun _ => 0) [] []
    (M.tm.initCfg x)).mapState Sum.inl
  let a₁ : Cfg k Bool (M.State ⊕ Unit) x :=
    { embedSilentCfg σ cap (fun _ _ => none) (fun _ => 0) [] [] d with
      state := some (Sum.inr ()) }
  obtain ⟨a, ha, arun, acut⟩ := embedSilentRetTM_firstReturn M x σ cap hcap
    (fun _ _ => none) (fun _ => 0) [] t halt
  have aword : a₁.workTapes cap = FinTM.bufferTape n.bits ∧
      a₁.workTapePos cap = (n.bits.length : ℤ) := by
    simpa only [a₁, d, List.nil_append, out] using
      embedSilentCfg_cap σ cap hcap (fun _ _ => none) (fun _ => 0) [] [] d
  have aout : a₁.output = [] := by
    dsimp only [a₁]
    rw [embedSilentCfg_output]
  let r₀ := a₁.mapState (fun _ => RewindPhase.start)
  obtain ⟨rrun, rcut, rheads⟩ := rewindTM_run_ofCfg cap n.bits n.bits.length (le_refl _) r₀
    (by rw [Cfg.mapState_state]; rfl) (by
      intro p hp hlt
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, aword.1, aword.2]
      congr 1
      omega)
  let r₁ : Cfg k Bool RewindPhase x :=
    { r₀ with
      state := some .done
      workTapePos := Function.update r₀.workTapePos cap (r₀.workTapePos cap - n.bits.length) }
  have crun := seamCompTM_run_ofCfg C (Sum.inr ()) R .start arun rfl acut rrun
  have ccut := seamCompTM_firstReturn_ofCfg C (Sum.inr ()) R .start .done
    arun rfl acut rrun rfl rcut
  obtain ⟨b, hb, hp⟩ := ph n
  let v₀ := vhostCfg (P.tm.initCfg n.bits) true r₁.inputPos []
  let e₀ := embedEmitCfg ι r₁.workTapes r₁.workTapePos [] v₀
  have tag : FinTM.VirtualTag (P.tm.initCfg n.bits).inputPos true := by
    rw [FinTM.VirtualTag_iff, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      have : (1 : ℕ) ≠ 0 := by decide
      exact (this (by simpa only [Fin.val_one] using h)).elim
    · intro _
      rfl
  have estart : e₀ = r₁.mapState (fun _ => (P.tm.q₀, true)) := by
    apply embedEmitCfg_eq
    · rw [vhostCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state,
        Cfg.mapState_state, Option.map_some]
      rfl
    · dsimp only [v₀]
      simp only [vhostCfg_inputPos, Cfg.mapState_inputPos]
    · rw [vhostCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
        Cfg.mapState_output]
      simp only [List.nil_append]
      simpa only [r₁, r₀, Cfg.mapState_output] using aout.symm
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have iz : i = 0 := Subsingleton.elim _ _
        subst i
        constructor
        · funext z
          dsimp only [v₀, r₁, r₀]
          simp only [vhostCfg_workTapes, Fin.addCases_left, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) aword.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_left, MultiTapeTM.initCfg_eq,
            Cfg.init_inputPos, Fin.val_one, Cfg.mapState_workTapePos]
          dsimp only [r₁]
          rw [show ι (Fin.castAdd P.k (0 : Fin 1)) = cap from rfl,
            Function.update_self, Cfg.mapState_workTapePos, aword.2]
          omega
      · have hsel : ι (Fin.natAdd 1 i) ∉ Set.range σ := by
          rintro ⟨j, hj⟩
          have he : j.val = M.k + (1 + i.val) := congrArg Fin.val hj
          omega
        have hne : ι (Fin.natAdd 1 i) ≠ cap := by
          intro he
          have hh : M.k + (1 + i.val) = M.k := congrArg Fin.val he
          omega
        have framed := embedSilentCfg_unselected σ cap (fun _ _ => none) (fun _ => 0)
          [] [] d (ι (Fin.natAdd 1 i)) hsel hne
        constructor
        · funext z
          dsimp only [v₀, r₁, r₀, a₁]
          simp only [vhostCfg_workTapes, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapes, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) framed.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapePos, Cfg.mapState_workTapePos]
          dsimp only [r₁]
          rw [Function.update_of_ne hne, Cfg.mapState_workTapePos]
          exact framed.2.symm
    · intro j _
      exact ⟨funext fun z => (Cfg.mapState_workTapes _ _ j z).symm,
        (Cfg.mapState_workTapePos _ _ j).symm⟩
  obtain ⟨tagEnd, _, vrun⟩ := vhostEmitTM_runFrom P.tm (P.tm.initCfg n.bits) true tag
    r₁.inputPos [] b
  have erun : E.runFrom e₀ b =
      embedEmitCfg ι r₁.workTapes r₁.workTapePos []
        (vhostCfg (P.tm.runFrom (P.tm.initCfg n.bits) b) tagEnd r₁.inputPos []) := by
    rw [embedEmitTM_runFrom, vrun]
  have hrun := seamCompTM_run_ofCfg CR (Sum.inr .done) E (P.tm.q₀, true)
    crun (by rw [Cfg.mapState_state]; rfl) ccut (by
      simpa only [Turing.Cfg.mapState_mapState, Function.comp_apply] using estart.symm ▸ erun)
  have nstart : N.tm.initCfg x = ((a₀.mapState Sum.inl).mapState Sum.inl) := by
    rw [MultiTapeTM.initCfg_with_q₀]
    rw [show a₀ = Cfg.init (Sum.inl M.tm.q₀) x from
      embedSilentCfg_initCfg M.tm σ cap hcap x]
    apply Cfg.ext
    · simp only [Cfg.init_state, Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.init_inputPos, Cfg.mapState_inputPos]
    · funext j z
      simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    · funext j
      simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    · simp only [Cfg.init_output, Cfg.mapState_output]
  let u := (a + 1 + (n.bits.length + 2)) + 1 + b
  refine ⟨u, by dsimp only [u]; omega, ?_, ?_⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [nstart, MultiTapeTM.runFrom_with_q₀, hrun]
    obtain ⟨phh, pho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hp
    simp only [Cfg.mapState_state, Cfg.mapState_output, embedEmitCfg_state,
      embedEmitCfg_output, vhostCfg_state, vhostCfg_output, phh, pho,
      Option.map_none, List.nil_append, and_self]
  · rw [nstart, space_with_start]
    have cspace : C.spaceUsed a₀ a ≤ M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) := by
      have sumBound := bank_sum_bound σ
        (fun j => C.spaceUsedByTape a₀ a j)
        (fun i => M.tm.spaceUsedByTape (M.tm.initCfg x) a i) (n.bits.length + 1)
        (fun i => by
          dsimp only
          rw [MultiTapeTM.spaceUsedByTape_eq_card,
            embedSilentRetTM_visitedByTapeHead,
            (embedSilentTM_visitedByTapeHead σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a i).1,
            ← MultiTapeTM.spaceUsedByTape_eq_card])
        (fun j hj => by
          dsimp only
          rw [MultiTapeTM.spaceUsedByTape_eq_card, embedSilentRetTM_visitedByTapeHead,
            ← MultiTapeTM.spaceUsedByTape_eq_card]
          by_cases he : j = cap
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a
            have ho := (M.tm.output_prefix (M.tm.initCfg x) ha).length_le
            rw [out] at ho
            omega
          · rw [(embedSilentTM_visitedByTapeHead_frame σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a j hj he).2]
            omega)
      dsimp only at sumBound
      simp only [← MultiTapeTM.spaceUsed_eq_sum] at sumBound
      exact sumBound.trans (Nat.add_le_add_right
        (M.tm.spaceUsed_mono (M.tm.initCfg x) ha) _)
    have rspace : R.spaceUsed r₀ (n.bits.length + 2) ≤ k * (2 * (n.bits.length + 2) + 1) := by
      apply MultiTapeTM.spaceUsed_le_of_abs_le
      intro v hv j
      have h := rheads j v hv
      by_cases hj : j = cap
      · rw [if_pos hj, Finset.mem_Icc] at h
        rw [abs_le]
        constructor <;> omega
      · rw [if_neg hj] at h
        rw [h, sub_self, abs_zero]
        positivity
    have espace : E.spaceUsed e₀ b ≤ n.bits.length + 2 + k := by
      have sumBound := bank_sum_bound ι
        (fun j => E.spaceUsedByTape e₀ b j)
        (fun i => (vhostEmitTM P.tm).spaceUsedByTape v₀ b i) 1
        (fun i => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead ι (vhostEmitTM P.tm) r₁.workTapes
            r₁.workTapePos [] v₀ b i).2])
        (fun j hj => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead_frame ι (vhostEmitTM P.tm) r₁.workTapes
            r₁.workTapePos [] v₀ b j hj).2])
      dsimp only at sumBound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at sumBound
      have hs := vhostEmitTM_spaceUsed_le P.tm (P.tm.initCfg n.bits) true tag r₁.inputPos [] b
      rw [ps] at hs
      exact sumBound.trans (Nat.add_le_add_right (by simpa only [Nat.zero_add] using hs) _)
    have crspace := seamCompTM_spaceUsed_le_add_ofCfg C (Sum.inr ()) R .start
      (T₂ := n.bits.length + 2) arun rfl acut
    have hspace := seamCompTM_spaceUsed_le_add_ofCfg CR (Sum.inr .done) E (P.tm.q₀, true)
      (T₂ := b) crun (by rw [Cfg.mapState_state]; rfl) ccut
    have eh : (r₁.mapState (Sum.inr : RewindPhase → (M.State ⊕ Unit) ⊕ RewindPhase)).mapState (fun _ => (P.tm.q₀, true)) = e₀ := by
      rw [Turing.Cfg.mapState_mapState]
      exact estart.symm
    rw [eh] at hspace
    have combined : H.spaceUsed ((a₀.mapState Sum.inl).mapState Sum.inl) u ≤
        M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) +
        k * (2 * (n.bits.length + 2) + 1) + (n.bits.length + 2 + k) := by
      exact hspace.trans ((Nat.add_le_add_right crspace _).trans
        (Nat.add_le_add (Nat.add_le_add cspace rspace) espace))
    apply combined.trans
    have hk : 0 < k := by dsimp only [k]; omega
    have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ k * M.tm.spaceUsed (M.tm.initCfg x) t :=
      Nat.le_mul_of_pos_left _ hk
    have hw : n.bits.length + 2 ≤ k * (n.bits.length + 2) := Nat.le_mul_of_pos_left _ hk
    calc
      _ ≤ k * M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) +
          k * (2 * (n.bits.length + 2) + 1) + (k * (n.bits.length + 2) + k) := by omega
      _ = k * (M.tm.spaceUsed (M.tm.initCfg x) t + 4 * n.bits.length + 9) := by ring
      _ ≤ k * (20 * (M.tm.spaceUsed (M.tm.initCfg x) t + n.bits.length + 1)) := by
        apply Nat.mul_le_mul_left
        omega
      _ = _ := by ring

/-- Count a word's length in binary, returning `1` instead of `0` for the empty word.
**Proof sketch.** A fixed-word equality test chooses between the constant word `[true]`
and the catalog's binary length counter. The conditional time bound is linear. -/
private theorem normalized_counter :
    ∃ (V : FinTM Bool) (A : ℕ), ∀ w : List Bool,
      V.ComputesInTime w (if w = [] then [true] else w.length.bits) (A * (w.length + 1)) := by
  obtain ⟨L, b, hl, _⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let D := FinTM.ifEqTM [] [true] [false]
  have hd : D.ComputesFunInTime (fun w => [decide (w = [])]) (fun n => 4 * (n + 1)) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro w
    have h := (FinTM.computesFunInTime_iff _ _ _).mp
      (FinTM.ifEqTM_computes [] [true] [false]) w
    by_cases hw : w = []
    · simpa only [hw, if_pos rfl, decide_true, List.length_nil,
        List.length_singleton, max_self, Nat.zero_add] using h
    · simpa only [hw, if_false, decide_false, List.length_nil,
        List.length_singleton, max_self, Nat.zero_add] using h
  have hc : (FinTM.constTM [true]).ComputesFunInTime (fun _ => [true])
      (fun n => 2 * (n + 1)) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro w
    exact (FinTM.constTM_computes [true] w).mono (by
      simp only [List.length_singleton]
      omega)
  obtain ⟨V, A, hv⟩ := FinTM.computesFunInTime_cond hd hc hl
  refine ⟨V, A * (b + 7), fun w => ?_⟩
  have h := (FinTM.computesFunInTime_iff _ _ _).mp hv w
  simp only [decide_eq_true_eq] at h
  apply h.mono
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hm : max (2 * (w.length + 1)) (b * (w.length + 1)) ≤
      (b + 2) * (w.length + 1) := by
    rw [Nat.add_mul]
    exact max_le (by omega) (by omega)
  calc
    _ ≤ 4 * (w.length + 1) + (b + 2) * (w.length + 1) + 1 := by omega
    _ ≤ (b + 7) * (w.length + 1) := by ring_nf; omega

/-- Compute the normalized logarithmic width in linear time and logarithmic space.
**Proof sketch.** `exists_inputLengthTM` supplies the input length in binary, restores its
work heads to their origins and bounds their displacement by a constant times the answer
width plus one. A reversed native-bank embedding puts that counter tape beside a fresh
bank for a virtual-input `normalized_counter`. The latter emits the counter word's length
in binary, treating its empty input as length one; `length_bits_eq_log` and `logSpace_eq`
identify this value with the normalized logarithm. `seamCompTM_run_ofCfg` joins the phases
at the native counter's first exit. `bank_sum_bound` combines the native head envelope,
the hosted counter's time-derived space bound, and the virtual-input boundary cells.
The counter word has at most the normalized logarithmic width, and at most the original
input length, giving logarithmic space and linear total time. -/
private theorem logarithmic_computation :
    ∃ (M : FinTM Bool) (A : ℕ), ∀ x : List Bool,
      ∃ t ≤ A * (x.length + 1),
        M.ComputesInTime x (Complexity.logSpace x.length).bits t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ A * Complexity.logSpace x.length := by
  classical
  obtain ⟨K, S, fs, ds, R, entry, exit, C, counter⟩ := exists_inputLengthTM
  letI := fs
  letI := ds
  obtain ⟨V, A, hv⟩ := normalized_counter
  let k := K + (1 + V.k)
  let σ : Fin (K + 1) ↪ Fin k :=
    Fin.revPerm.toEmbedding.trans (Fin.castLEEmb (by dsimp only [k]; omega))
  let ι : Fin (1 + V.k) ↪ Fin k := Fin.natAddEmb K
  have shared : σ 0 = ι 0 := by
    apply Fin.ext
    change (K + 1) - 1 - 0 = K + 0
    omega
  let F := embedEmitTM σ R
  let E := embedEmitTM ι (vhostEmitTM V.tm)
  let H := seamCompTM F exit E (V.tm.q₀, true)
  let N : FinTM Bool :=
    { k := k
      State := S ⊕ (V.State × Bool)
      tm := { H with q₀ := Sum.inl entry } }
  let D := (K + 1) * (2 * C + 1) + V.k * (A + 1) + 2 * k + 3
  let B := C + 2 * A + 1 + 2 * D
  refine ⟨N, B, fun x => ?_⟩
  let y := x.length.bits
  let d₀ : Cfg (K + 1) Bool S x := Cfg.init entry x
  obtain ⟨t, ht, cut, heads, finished⟩ := counter d₀
    (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
    (by intro p _ _; rw [Cfg.init_workTapePos, zero_add, Cfg.init_workTapes])
    (by intro j _ p; rw [Cfg.init_workTapes])
  let d₁ : Cfg (K + 1) Bool S x :=
    { d₀ with
      state := some exit
      workTapes := fun j z =>
        if j = 0 ∧ d₀.workTapePos j ≤ z ∧ z < d₀.workTapePos j + (y.length : ℤ)
          then FinTM.bufferTape y (z - d₀.workTapePos j) else d₀.workTapes j z }
  let f₀ := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] d₀
  let f₁ := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] d₁
  have frun : F.runFrom f₀ t = f₁ := by
    rw [embedEmitTM_runFrom, finished]
  have fcut : ∀ u < t, (F.runFrom f₀ u).state ≠ some exit := by
    intro u hu
    rw [embedEmitTM_runFrom, embedEmitCfg_state]
    exact cut u hu
  have fstate : f₁.state = some exit := by
    rw [embedEmitCfg_state]
  have fword : f₁.workTapes (ι 0) = FinTM.bufferTape y := by
    rw [← shared, embedEmitCfg_selected_tape]
    funext z
    dsimp only [d₁, d₀]
    simp only [Cfg.init_workTapePos, Cfg.init_workTapes, zero_add, sub_zero,
      true_and]
    by_cases hz : 0 ≤ z ∧ z < (y.length : ℤ)
    · rw [if_pos hz]
    · rw [if_neg hz, FinTM.bufferTape_eq_none_of_not_mem y hz]
  have fpos : f₁.workTapePos (ι 0) = 0 := by
    rw [← shared, embedEmitCfg_selected_pos, Cfg.init_workTapePos]
  have fout : f₁.output = [] := by
    rw [embedEmitCfg_output, Cfg.init_output, List.nil_append]
  let v₀ := vhostCfg (V.tm.initCfg y) true f₁.inputPos []
  let e₀ := embedEmitCfg ι f₁.workTapes f₁.workTapePos [] v₀
  have estart : e₀ = f₁.mapState (fun _ => (V.tm.q₀, true)) := by
    apply embedEmitCfg_eq
    · simp only [v₀, vhostCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state,
        Cfg.mapState_state, fstate, Option.map_some]
    · dsimp only [v₀]
      simp only [vhostCfg_inputPos, Cfg.mapState_inputPos]
    · rw [vhostCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
        Cfg.mapState_output]
      simp only [List.nil_append]
      exact fout.symm
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have iz : i = 0 := Subsingleton.elim _ _
        subst i
        constructor
        · funext z
          dsimp only [v₀]
          simp only [vhostCfg_workTapes, Fin.addCases_left, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) fword.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_left, MultiTapeTM.initCfg_eq,
            Cfg.init_inputPos, Fin.val_one, Cfg.mapState_workTapePos]
          rw [show Fin.castAdd V.k (0 : Fin 1) = (0 : Fin (1 + V.k)) from rfl, fpos]
          norm_num
      · have outside : ι (Fin.natAdd 1 i) ∉ Set.range σ := by
          rintro ⟨j, hj⟩
          have hh : (σ j).val < K + 1 := j.rev.isLt
          have he : (σ j).val = K + (1 + i.val) := congrArg Fin.val hj
          omega
        have framed := embedEmitCfg_unselected σ (fun _ _ => none) (fun _ => 0) []
          d₁ (ι (Fin.natAdd 1 i)) outside
        constructor
        · funext z
          dsimp only [v₀]
          simp only [vhostCfg_workTapes, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapes, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) framed.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapePos, Cfg.mapState_workTapePos]
          exact framed.2.symm
    · intro j _
      exact ⟨funext fun z => (Cfg.mapState_workTapes _ _ j z).symm,
        (Cfg.mapState_workTapePos _ _ j).symm⟩
  have width : (if y = [] then [true] else y.length.bits) =
      (Complexity.logSpace x.length).bits := by
    by_cases hx : x.length = 0
    · simp only [y, hx, Nat.zero_bits, Complexity.logSpace_eq,
        Nat.log_zero_right, Nat.zero_add, Nat.one_bits, if_true]
    · have he := Complexity.LogProg.length_bits_eq_log hx
      have hn : y ≠ [] := by
        intro heq
        have hlen := congrArg List.length heq
        dsimp only [y] at hlen
        rw [he, List.length_nil] at hlen
        omega
      rw [if_neg hn]
      exact congrArg Nat.bits (he.trans (Complexity.logSpace_eq x.length).symm)
  let b := A * (y.length + 1)
  have vcomp : V.ComputesInTime y (Complexity.logSpace x.length).bits b := by
    rw [← width]
    exact hv y
  have tag : FinTM.VirtualTag (V.tm.initCfg y).inputPos true := by
    rw [FinTM.VirtualTag_iff, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      have : (1 : ℕ) ≠ 0 := by decide
      exact (this (by simpa only [Fin.val_one] using h)).elim
    · intro _
      rfl
  obtain ⟨tagEnd, _, vrun⟩ := vhostEmitTM_runFrom V.tm (V.tm.initCfg y) true tag
    f₁.inputPos [] b
  have erun : E.runFrom e₀ b =
      embedEmitCfg ι f₁.workTapes f₁.workTapePos []
        (vhostCfg (V.tm.runFrom (V.tm.initCfg y) b) tagEnd f₁.inputPos []) := by
    rw [embedEmitTM_runFrom, vrun]
  have hrun := seamCompTM_run_ofCfg F exit E (V.tm.q₀, true)
    frun fstate fcut (estart ▸ erun)
  have fstart : f₀ = Cfg.init entry x := by
    apply embedEmitCfg_eq
    · rw [Cfg.init_state, Cfg.init_state]
    · rw [Cfg.init_inputPos, Cfg.init_inputPos]
    · rw [Cfg.init_output, Cfg.init_output, List.nil_append]
    · intro i
      constructor
      · funext z
        rw [Cfg.init_workTapes, Cfg.init_workTapes]
      · rw [Cfg.init_workTapePos, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext z
        rw [Cfg.init_workTapes]
      · rw [Cfg.init_workTapePos]
  have nstart : N.tm.initCfg x = f₀.mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_with_q₀, fstart]
    apply Cfg.ext
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.init_state, Option.map_some]
    · simp only [Cfg.init_inputPos, Cfg.mapState_inputPos]
    · funext j z
      simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    · funext j
      simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    · simp only [Cfg.init_output, Cfg.mapState_output]
  refine ⟨t + 1 + b, ?_, ?_, ?_⟩
  · have hb : b ≤ A * (x.length + 1) := Nat.mul_le_mul_left A
      (Nat.add_le_add_right (length_bits_le_self x.length) 1)
    calc
      _ ≤ C * (x.length + 1) + (x.length + 1) + A * (x.length + 1) := by omega
      _ = (C + A + 1) * (x.length + 1) := by ring
      _ ≤ B * (x.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [B]; omega)
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [nstart, MultiTapeTM.runFrom_with_q₀, hrun]
    obtain ⟨vh, vo⟩ := (FinTM.computesInTime_iff _ _ _ _).mp vcomp
    simp only [Cfg.mapState_state, Cfg.mapState_output, embedEmitCfg_state,
      embedEmitCfg_output, vhostCfg_state, vhostCfg_output, vh, vo,
      Option.map_none, List.nil_append, and_self]
  · rw [nstart, space_with_start]
    have nativeSpace : R.spaceUsed d₀ t ≤ (K + 1) * (2 * (C * (y.length + 1)) + 1) :=
      R.spaceUsed_le_of_abs_le d₀ t (C * (y.length + 1)) heads
    have fspace : F.spaceUsed f₀ t ≤
        (K + 1) * (2 * C + 1) * (y.length + 1) + k := by
      have bound := bank_sum_bound σ (fun j => F.spaceUsedByTape f₀ t j)
        (fun i => R.spaceUsedByTape d₀ t i) 1
        (fun i => by
          dsimp only [f₀, F]
          rw [(embedEmitTM_visitedByTapeHead σ R (fun _ _ => none) (fun _ => 0) [] d₀ t i).2])
        (fun j hj => by
          dsimp only [f₀, F]
          rw [(embedEmitTM_visitedByTapeHead_frame σ R (fun _ _ => none)
            (fun _ => 0) [] d₀ t j hj).2])
      dsimp only at bound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at bound
      apply bound.trans
      apply Nat.add_le_add_right
      apply nativeSpace.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      ring_nf
      omega
    have espace : E.spaceUsed e₀ b ≤ V.k * (A * (y.length + 1) + 1) + y.length + 2 + k := by
      have bound := bank_sum_bound ι (fun j => E.spaceUsedByTape e₀ b j)
        (fun i => (vhostEmitTM V.tm).spaceUsedByTape v₀ b i) 1
        (fun i => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead ι (vhostEmitTM V.tm) f₁.workTapes
            f₁.workTapePos [] v₀ b i).2])
        (fun j hj => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead_frame ι (vhostEmitTM V.tm) f₁.workTapes
            f₁.workTapePos [] v₀ b j hj).2])
      dsimp only at bound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at bound
      have hs := vhostEmitTM_spaceUsed_le V.tm (V.tm.initCfg y) true tag f₁.inputPos [] b
      have vs : V.tm.spaceUsed (V.tm.initCfg y) b ≤ V.k * (A * (y.length + 1) + 1) :=
        vcomp.spaceUsed_le b
      exact bound.trans (Nat.add_le_add_right (hs.trans (by omega)) _)
    have total := seamCompTM_spaceUsed_le_add_ofCfg F exit E (V.tm.q₀, true)
      (T₂ := b) frun fstate fcut
    rw [← estart] at total
    have bound : H.spaceUsed (f₀.mapState Sum.inl) (t + 1 + b) ≤ D * (y.length + 1) := by
      apply (total.trans (Nat.add_le_add fspace espace)).trans
      have vk : V.k * (A * (y.length + 1) + 1) ≤ V.k * ((A + 1) * (y.length + 1)) := by
        apply Nat.mul_le_mul_left
        ring_nf
        omega
      have kk : k ≤ k * (y.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      calc
        _ ≤ (K + 1) * (2 * C + 1) * (y.length + 1) + k * (y.length + 1) +
            (V.k * ((A + 1) * (y.length + 1)) + 2 * (y.length + 1) + k * (y.length + 1)) := by omega
        _ = ((K + 1) * (2 * C + 1) + V.k * (A + 1) + 2 * k + 2) * (y.length + 1) := by ring
        _ ≤ D * (y.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [D]; omega)
    apply bound.trans
    have logpos : 1 ≤ Complexity.logSpace x.length := by rw [Complexity.logSpace_eq]; omega
    have widthle : y.length ≤ Complexity.logSpace x.length := by
      rw [Complexity.logSpace_eq]
      exact Complexity.LogProg.length_bits_le_log x.length
    calc
      _ ≤ D * (2 * Complexity.logSpace x.length) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * D) * Complexity.logSpace x.length := by ring
      _ ≤ B * Complexity.logSpace x.length := Nat.mul_le_mul_right _ (by dsimp only [B]; omega)

/-- **The word size is computable within `TW` and `SW`**: some finite binary machine, on every
input `x`, halts within `TW |x|` steps with the binary representation of `W (|x|)` on its output
tape (`Nat.bits`, as in `Complexity.SpaceConstructible` and `Complexity.TimeConstructible`), having
visited at most `SW |x|` work cells up to then. The stage-2 machine runs it once, at the start,
with its output captured on a work tape, and pays `TW` and `SW` once. Deviation: it bounds time
and space together, where [AB09] has separate time- and space-constructibility (§1.3, §4.1);
design §16b item 1. -/
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length

/-- A word size computable within `TW` and `SW` is computable within any larger bounds.

**Proof sketch.** The same machine and halting times; `t ≤ TW n ≤ TW' n`, and the space bound
weakens pointwise. -/
theorem WordSizeComputable.mono {W TW SW TW' SW' : ℕ → ℕ} (h : WordSizeComputable W TW SW)
    (hT : ∀ n, TW n ≤ TW' n) (hS : ∀ n, SW n ≤ SW' n) : WordSizeComputable W TW' SW' := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun x => ?_⟩
  obtain ⟨t, ht, hcomp, hspace⟩ := hM x
  exact ⟨t, ht.trans (hT x.length), hcomp, hspace.trans (hS x.length)⟩

/-- **Logarithmic word sizes** (the P and L grades): for every `c`, the word size
`c · (⌊log₂ n⌋ + 1)` is computable in linear time and logarithmic space.

**Proof sketch.** `logarithmic_computation` computes the normalized logarithm in linear
time and logarithmic space, including its value one on the empty input. `scale_computes`
then captures that binary answer, multiplies it by `c` using `constant_multiplier`, and
emits the result. `Turing.length_bits_le_self` and `Complexity.logSpace_le_succ` absorb
the extra binary-width time into a linear bound. The positivity of the normalized
logarithm absorbs the constant space allowance. -/
theorem wordSizeComputable_logSpace (c : ℕ) :
    ∃ a : ℕ, WordSizeComputable (fun n => c * Complexity.logSpace n) (fun n => a * (n + 1))
      (fun n => a * Complexity.logSpace n) := by
  obtain ⟨M, a, hm⟩ := logarithmic_computation
  obtain ⟨N, A, B, scaled⟩ := scale_computes M c
  let d := a + 2 + B + A * (a + 2)
  refine ⟨d, N, fun x => ?_⟩
  obtain ⟨t, ht, comp, space⟩ := hm x
  obtain ⟨u, hu, answer, used⟩ := scaled x (Complexity.logSpace x.length) t comp
  have one : 1 ≤ Complexity.logSpace x.length := by rw [Complexity.logSpace_eq]; omega
  have width := length_bits_le_self (Complexity.logSpace x.length)
  have linear := Complexity.logSpace_le_succ x.length
  refine ⟨u, ?_, answer, ?_⟩
  · have hb : B ≤ B * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc
      _ ≤ t + 2 * (Complexity.logSpace x.length).bits.length + B := hu
      _ ≤ a * (x.length + 1) + 2 * (x.length + 1) + B * (x.length + 1) := by omega
      _ = (a + 2 + B) * (x.length + 1) := by ring
      _ ≤ d * (x.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [d]; omega)
  · calc
      _ ≤ A * (M.tm.spaceUsed (M.tm.initCfg x) t +
          (Complexity.logSpace x.length).bits.length + 1) := used
      _ ≤ A * (a * Complexity.logSpace x.length + Complexity.logSpace x.length +
          Complexity.logSpace x.length) := by
        apply Nat.mul_le_mul_left
        omega
      _ = (A * (a + 2)) * Complexity.logSpace x.length := by ring
      _ ≤ d * Complexity.logSpace x.length := Nat.mul_le_mul_right _ (by dsimp only [d]; omega)

/-- **Space-constructible word sizes** (Savitch's shape): if `S` is space-constructible, then for
every `c` the word size `c · S(n)` is computable in space `O(S(n))`, within some time bound `TW`
that is not controlled and that the space grades do not need.

**Proof sketch.** Read the witness through `Complexity.spaceConstructible_iff`.
`Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` gives a uniform
configuration-count deadline and retains the original space bound at that deadline.
`scale_computes` captures the witness's binary output, multiplies it by `c`, and emits
it. `Turing.length_bits_le_self` bounds the captured width by `S`, while
`logSpace ≤ S` and `logSpace_eq` give `1 ≤ S`. Thus all extra space is absorbed into a
constant times `S`. The source deadline plus the scaling overhead defines `TW`. -/
theorem wordSizeComputable_of_spaceConstructible {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ) :
    ∃ (a : ℕ) (TW : ℕ → ℕ), WordSizeComputable (fun n => c * S n) TW (fun n => a * S n) := by
  obtain ⟨lower, C, _, M, hm⟩ := (Complexity.spaceConstructible_iff S).mp hS
  obtain ⟨ht, hs⟩ := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨N, A, B, scaled⟩ := scale_computes M c
  let T := fun n => M.configBound n (C * S n)
  refine ⟨A * (C + 2), (fun n => T n + 2 * (S n).bits.length + B), N, ?_⟩
  intro x
  obtain ⟨u, hu, comp, space⟩ := scaled x (S x.length) (T x.length)
    ((FinTM.computesFunInTime_iff _ _ _).mp ht x)
  refine ⟨u, hu, comp, space.trans ?_⟩
  have one : 1 ≤ S x.length := by
    have hh := lower x.length
    rw [Complexity.logSpace_eq] at hh
    omega
  have width := length_bits_le_self (S x.length)
  have hspace := hs x (T x.length)
  calc
    _ ≤ A * (C * S x.length + S x.length + S x.length) := by
      apply Nat.mul_le_mul_left
      omega
    _ = _ := by ring

end WordRAM
```

## ===== TCSlib/Programs/WordRAM/Extended.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Steps
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The extended word RAM: input, output, coins and halving; footprints and halting

The word RAM of [AFM26] (`WordRAM.Instr`, nine instructions) is extended by a wrapper:
`WordRAM.XInstr` has the vendored instructions as `XInstr.base`, and four more:

* `rdIn i j`, the input bit at the position held in a cell, read in place;
* `emit i`, which appends the bit "`[i]` is nonzero" to an append-only output;
* `coin i`, the next coin of a read-once coin stream;
* `half i j`, an arithmetic shift right.

A configuration `WordRAM.XCfg` extends `WordRAM.Cfg` by the emitted bits and the number of
coins consumed. Input and coin streams are parameters of a run. The vendored run calculus
applies through `XProgram.proj`, as proved by `XSteps.of_steps_proj`.

The run calculus also records which memory cells a run touches and when the program halts
within given bounds on steps and cells. All run, footprint, and halting results below are proved.

## Main definitions

* `WordRAM.XInstr`, `WordRAM.XProgram`, `WordRAM.XCfg`, `WordRAM.xstep`, `WordRAM.XSteps`:
  the extended machine and its runs.
* `WordRAM.CoinFree`, `WordRAM.XProgram.proj`: coin-free programs and the vendored projection.
* `WordRAM.baseTouches`, `WordRAM.XInstr.touches`: the cells one instruction reads or writes.
* `WordRAM.StepsIn`, `WordRAM.XStepsIn`: runs within a footprint.
* `WordRAM.initMem`, `WordRAM.XCfg.init`, `WordRAM.HaltsWithin`: initialization and bounded halting.

## Main results

* `WordRAM.XSteps.trans`, `WordRAM.xstep_map_base`, `WordRAM.XSteps.of_steps`,
  `WordRAM.XSteps.of_steps_proj`: composition and conservativity over the vendored RAM.
* `WordRAM.StepsIn.agreeOutside`: intermediate memories agree outside the footprint.
* `WordRAM.stepsIn_straight`: straight-line execution with a footprint.
* `WordRAM.XSteps.exists_xStepsIn`, `WordRAM.HaltsWithin.touches_le`: a run of `n` steps
  touches at most `3 * n` cells, giving a cell bound from a time bound.
* `WordRAM.HaltsWithin.mono`, `WordRAM.HaltsWithin.unique`, `WordRAM.HaltsWithin.coin_irrel`:
  monotonicity, determinism, and independence of the coin stream for coin-free programs.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math` (https://github.com/anthropics/formal-math),
  project `3sum-apsp`, commit `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05),
  Apache-2.0, © Anthropic, PBC. Design adaptation: the word RAM of `EndStatement.lean`
  and the run calculus of `ThreeSumApsp/Machine/Steps.lean`, vendored as
  `TCSlib/Programs/WordRAM/Basic.lean` and `Steps.lean`, which this file wraps. `xstep` restates
  the match of `WordRAM.step`, routing the six memory instructions through `WordRAM.effect`;
  `XSteps` and `StepsIn` use the same finite-run convention as `WordRAM.Steps`. The proofs cite
  the vendored equations and lemmas. The footprint notion is ours: upstream's
  `ThreeSumApsp/Machine/Footprint.lean` bounds how many cells a run changes and reads, not which.
-/

namespace WordRAM

/-! ## The machine -/

/-- **The instructions of the extended word RAM** (design §15c, §15d): the nine instructions of
the vendored `WordRAM.Instr`, as `base`, and four more. `rdIn i j` sets `[i]` to the input bit at
position `[j]`, as `0` or `1` (`0` off the input, negative positions included); `emit i` appends
the bit "`[i]` is nonzero" to the output; `coin i` sets `[i]` to the next coin, as `0` or `1`,
and consumes it; `half i j` sets `[i]` to `[j]` shifted right by one place with the sign kept,
that is `⌊[j] / 2⌋`. The extension wraps `Instr` instead of adding constructors to it (user
decision, 2026-10-12), so the vendored files and their run calculus are unchanged.
[AFM26, `EndStatement.lean`], extended per design §15c. -/
inductive XInstr : Type where
  | base (i : Instr)
  | rdIn (i j : ℤ)
  | emit (i : ℤ)
  | coin (i : ℤ)
  | half (i j : ℤ)

/-- A program of the extended word RAM: its instructions, at positions `0, 1, 2, …`. -/
abbrev XProgram : Type := List XInstr

/-- **A configuration of the extended RAM**: the vendored configuration (the position of the
next instruction and the memory), the bits emitted so far, and the number of coins consumed so
far. The input and the coin stream are not part of it: they are parameters of a run. -/
structure XCfg (W : ℕ) extends Cfg W where
  /-- The bits emitted so far, oldest first. -/
  out : List Bool
  /-- The number of coins consumed so far. -/
  rd : ℕ

/-- The word that `rdIn` writes for the position `p` of the input `x`: `1` if `0 ≤ p` and the bit
of `x` at `p` is `true`, and `0` otherwise, in particular off the input. -/
def inBitWord (W : ℕ) (x : List Bool) (p : ℤ) : BitVec W :=
  if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0

/-- The word that `coin` writes for the coin `b`: `1` for `true`, `0` for `false`. -/
def coinWord (W : ℕ) (b : Bool) : BitVec W := if b then 1 else 0

/-- **One step of the extended RAM** on the input `x` with the coin stream `ρ`: the next
configuration, or the verdict. The nine vendored instructions behave as in `WordRAM.step` (the
six that only change the memory through the vendored `WordRAM.effect`) and leave the output and
the coin count alone; past its end the program rejects. The coin is read as `ρ.getD rd false`,
so a stream that has run out reads `false`; quantifying over all lists `ρ` covers every stream. -/
def xstep {W : ℕ} (P : XProgram) (x ρ : List Bool) (c : XCfg W) : XCfg W ⊕ Bool :=
  let m := c.mem
  match P.getD c.pc (.base .reject) with
  | .base .accept => .inr true
  | .base .reject => .inr false
  | .base (.bltz i l) => .inl { c with pc := if (m i).toInt < 0 then l else c.pc + 1 }
  | .base ins => .inl { c with pc := c.pc + 1, mem := effect ins m }
  | .rdIn i j =>
    .inl { c with pc := c.pc + 1, mem := Function.update m i (inBitWord W x (m j).toInt) }
  | .emit i => .inl { c with pc := c.pc + 1, out := c.out ++ [decide (m i ≠ 0)] }
  | .coin i =>
    .inl { c with pc := c.pc + 1, mem := Function.update m i (coinWord W (ρ.getD c.rd false)),
                  rd := c.rd + 1 }
  | .half i j => .inl { c with pc := c.pc + 1, mem := Function.update m i ((m j).sshiftRight 1) }

/-- `XSteps P x ρ n c c'`: exactly `n` steps of `P` on the input `x` with the coin stream `ρ`
lead from `c` to `c'`, none of them a verdict. The extended counterpart of `WordRAM.Steps`. -/
def XSteps {W : ℕ} (P : XProgram) (x ρ : List Bool) : ℕ → XCfg W → XCfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, xstep P x ρ c = .inl c₁ ∧ XSteps P x ρ n c₁ c'

/-- A program is **coin-free** when none of its instructions is a `coin`. -/
def CoinFree (P : XProgram) : Prop := ∀ ins ∈ P, ∀ a : ℤ, ins ≠ .coin a

/-- **The vendored projection** of a program of the extended RAM: the same program with each new
instruction replaced by `reject`. A run of the projection that gives no verdict never executes a
replaced position, so it is also a run of the extended program (`XSteps.of_steps_proj`). This is
how the vendored run calculus and the compiler's segment lemmas serve code that mixes old and new
instructions. -/
def XProgram.proj (P : XProgram) : List Instr :=
  P.map fun
    | .base i => i
    | _ => .reject

/-! ## Private instruction comparison -/

/-- Mapping a fetch follows `List.getElem?_map` and `Option.getD_map`. -/
private theorem mapped_fetch {α β : Type} (l : List α) (d : α) (f : α → β) (n : ℕ) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

/-- A base instruction has the same effect in both machines. The instruction cases use
`step_def` and `effect_def`; `Function.update_apply` identifies the memory functions. -/
private theorem xstep_base_fetch {W : ℕ} {P : XProgram} {Q : List Instr}
    (x ρ : List Bool) (c : Cfg W) (o : List Bool) (r : ℕ)
    (h : P.getD c.pc (.base .reject) = .base (Q.getD c.pc .reject)) :
    xstep P x ρ ⟨c, o, r⟩ =
      Sum.map (fun d => (⟨d, o, r⟩ : XCfg W)) id (step Q c) := by
  rw [xstep, h, step_def]
  cases Q.getD c.pc .reject <;>
    simp only [effect_def, Sum.map_inl, Sum.map_inr, id_eq]
  all_goals congr 3; funext a; simp only [Function.update_apply]; try rfl

/-- A non-verdict step of the projection can only fetch a base instruction. -/
private theorem projected_fetch {W : ℕ} {P : XProgram} {c d : Cfg W}
    (hs : step P.proj c = .inl d) :
    P.getD c.pc (.base .reject) = .base (P.proj.getD c.pc .reject) := by
  have hget : P.proj.getD c.pc .reject =
      (match P.getD c.pc (.base .reject) with | .base i => i | _ => .reject) :=
    by simpa only [XProgram.proj] using
      (mapped_fetch (β := Instr) P (.base .reject)
        (fun i : XInstr => match i with | .base j => j | _ => Instr.reject) c.pc)
  cases hi : P.getD c.pc (.base .reject) <;> simp only [hi] at hget
  case base i => exact congrArg XInstr.base hget.symm
  all_goals
    have hv := step_reject hget
    rw [hs] at hv
    contradiction

/-! ## Private run lifting -/

/-- A map that preserves single steps preserves finite runs. -/
private theorem lift_run {C D : Type} {S : C → C → Prop} {T : D → D → Prop}
    {R : ℕ → C → C → Prop} {R' : ℕ → D → D → Prop}
    (hz : ∀ c d, R 0 c d ↔ c = d)
    (hs : ∀ n c d, R (n + 1) c d ↔ ∃ e, S c e ∧ R n e d)
    (hz' : ∀ c d, R' 0 c d ↔ c = d)
    (hs' : ∀ n c d, R' (n + 1) c d ↔ ∃ e, T c e ∧ R' n e d)
    (f : C → D) (hstep : ∀ c d, S c d → T (f c) (f d))
    {n : ℕ} {c d : C} (h : R n c d) : R' n (f c) (f d) := by
  induction n generalizing c with
  | zero => exact (hz' _ _).mpr (congrArg f ((hz c d).mp h))
  | succ n ih =>
    obtain ⟨e, hstep', hr⟩ := (hs n c d).mp h
    exact (hs' n _ _).mpr ⟨f e, hstep c e hstep', ih hr⟩

section RunCalculus

variable {W : ℕ} {P : XProgram} {x ρ : List Bool}

/-- One run after the other: `n` steps from `c` to `c₁`, then `k` steps from `c₁` to `c₂`, are
`n + k` steps from `c` to `c₂`. The counterpart of `WordRAM.Steps.trans`.

**Proof sketch.** Induct on the first run length, generalizing the starting configuration.
The zero case is the second run; the successor case keeps the first step and composes the
tail by induction, as in `WordRAM.Steps.trans`. -/
theorem XSteps.trans {n k : ℕ} {c c₁ c₂ : XCfg W} (h₁ : XSteps P x ρ n c c₁)
    (h₂ : XSteps P x ρ k c₁ c₂) : XSteps P x ρ (n + k) c c₂ := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h₁
    simpa only [Nat.zero_add] using h₂
  | succ n ih =>
    obtain ⟨d, hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨d, hs, ih hr⟩

/-- **Conservativity, one step.** On a program of vendored instructions, a step of the extended
RAM is the vendored step, with the output and the coin count unchanged.

**Proof sketch.** `mapped_fetch` identifies the instruction in the mapped program.
Apply `xstep_base_fetch`, whose single instruction case analysis uses `step_def` and
`effect_def`; `Function.update_apply` identifies the memory functions. -/
theorem xstep_map_base (P : List Instr) (c : Cfg W) (o : List Bool) (r : ℕ) :
    xstep (P.map .base) x ρ ⟨c, o, r⟩ =
      Sum.map (fun c' => (⟨c', o, r⟩ : XCfg W)) id (step P c) := by
  exact xstep_base_fetch x ρ c o r (mapped_fetch P .reject XInstr.base c.pc)

/-- **Conservativity, runs.** A run of a vendored program is a run of its extended copy, with
the output and the coin count unchanged.

**Proof sketch.** Apply `lift_run` with the configuration embedding that preserves
the output and coin count. `Steps.zero_iff` and `Steps.succ_iff` expose the vendored run,
and `xstep_map_base` preserves each step. -/
theorem XSteps.of_steps {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : Steps P n c c')
    (o : List Bool) (r : ℕ) : XSteps (P.map .base) x ρ n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P c = .inl d)
    (T := fun c d => xstep (P.map .base) x ρ c = .inl d)
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  change xstep (P.map .base) x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
  rw [xstep_map_base, hs, Sum.map_inl]

/-- **The vendored run calculus on mixed code.** A verdict-free run of the projection `P.proj` is
a run of `P` itself, with the output and the coin count unchanged.

**Proof sketch.** Use `lift_run` with the configuration embedding. At each step,
`projected_fetch` rules out a replacement instruction using `step_reject`.
`xstep_base_fetch` then identifies the extended transition with the projected one. -/
theorem XSteps.of_steps_proj {n : ℕ} {c c' : Cfg W} (h : Steps P.proj n c c')
    (o : List Bool) (r : ℕ) : XSteps P x ρ n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P.proj c = .inl d)
    (T := fun c d => xstep P x ρ c = .inl d)
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  change xstep P x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
  rw [xstep_base_fetch x ρ c o r (projected_fetch hs), hs, Sum.map_inl]

end RunCalculus

/-! ## The cells a run touches (backlog PROG-3, RAM level) -/

/-- The cells that a vendored instruction reads or writes in the memory `m`: the cells it names
and, for `load` and `store`, the cell whose address it reads from memory (the source of `load`,
the target of `store`). The verdicts touch nothing. -/
def baseTouches {W : ℕ} (ins : Instr) (m : ℤ → BitVec W) : Finset ℤ :=
  match ins with
  | .one i => {i}
  | .add i j k => {i, j, k}
  | .sub i j k => {i, j, k}
  | .mul i j k => {i, j, k}
  | .load i j => {i, j, (m j).toInt}
  | .store i j => {i, j, (m i).toInt}
  | .bltz i _ => {i}
  | .accept => ∅
  | .reject => ∅

/-- The cells that an instruction of the extended RAM reads or writes in the memory `m`: those of
`baseTouches` for a vendored instruction, and the cells named by a new one. The input and the
coin stream are not cells. -/
def XInstr.touches {W : ℕ} : XInstr → (ℤ → BitVec W) → Finset ℤ
  | .base ins, m => baseTouches ins m
  | .rdIn i j, _ => {i, j}
  | .emit i, _ => {i}
  | .coin i, _ => {i}
  | .half i j, _ => {i, j}

/-- Every instruction touches at most three cells.

**Proof sketch.** Case on the instruction and use `Finset.card_le_three`,
`Finset.card_le_two`, `Finset.card_singleton`, and `Finset.card_empty` for the listed cells. -/
theorem XInstr.card_touches_le {W : ℕ} (ins : XInstr) (m : ℤ → BitVec W) :
    (ins.touches m).card ≤ 3 := by
  cases ins <;> simp only [touches]
  case base i =>
    cases i <;> simp only [baseTouches] <;>
      first | exact Finset.card_le_three
            | simp only [Finset.card_singleton, Finset.card_empty]; omega
  all_goals first
    | exact Finset.card_le_two.trans (by decide)
    | simp only [Finset.card_singleton]; omega

/-- `XStepsIn P x ρ K n c c'`: an `XSteps` run in which every step reads and writes only cells of
`K`, the *footprint*. Every run is such a run for the set of the cells it touches
(`XSteps.exists_xStepsIn`). -/
def XStepsIn {W : ℕ} (P : XProgram) (x ρ : List Bool) (K : Set ℤ) :
    ℕ → XCfg W → XCfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, xstep P x ρ c = .inl c₁ ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K ∧ XStepsIn P x ρ K n c₁ c'

/-- `StepsIn P K n c c'`: a `WordRAM.Steps` run of a vendored program in which every step reads
and writes only cells of `K`. The PROG-3 strengthening of `WordRAM.Steps`, added beside it; the
vendored definition is unchanged. -/
def StepsIn {W : ℕ} (P : List Instr) (K : Set ℤ) : ℕ → Cfg W → Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, step P c = .inl c₁ ∧
      ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K ∧ StepsIn P K n c₁ c'

/-! ## Private footprint inclusion -/

/-- Footprint inclusion for any run relation with the same first-step equations. -/
private theorem footprint_mono {C : Type} {S : C → C → Prop} {F : C → Finset ℤ}
    {R : Set ℤ → ℕ → C → C → Prop}
    (hz : ∀ K c d, R K 0 c d ↔ c = d)
    (hs : ∀ K n c d, R K (n + 1) c d ↔
      ∃ e, S c e ∧ ↑(F c) ⊆ K ∧ R K n e d)
    {K L : Set ℤ} {n : ℕ} {c d : C} (h : R K n c d) (hKL : K ⊆ L) :
    R L n c d := by
  induction n generalizing c with
  | zero => exact (hz L c d).mpr ((hz K c d).mp h)
  | succ n ih =>
    obtain ⟨e, hstep, hK, hr⟩ := (hs K n c d).mp h
    exact (hs L n c d).mpr ⟨e, hstep, hK.trans hKL, ih hr⟩

/-- A run whose steps each touch at most three cells has a finite footprint.

**Proof sketch.** Induct on the run length using its zero and successor equations. In
the successor case unite the first step's footprint with the recursively obtained set.
`Finset.card_union_le` gives the cardinal bound and `footprint_mono` enlarges the tail. -/
private theorem exists_footprint {C : Type} {S : C → C → Prop} {F : C → Finset ℤ}
    {R : ℕ → C → C → Prop} {RI : Set ℤ → ℕ → C → C → Prop}
    (hz : ∀ c d, R 0 c d ↔ c = d)
    (hs : ∀ n c d, R (n + 1) c d ↔ ∃ e, S c e ∧ R n e d)
    (hIz : ∀ K c d, RI K 0 c d ↔ c = d)
    (hIs : ∀ K n c d, RI K (n + 1) c d ↔
      ∃ e, S c e ∧ ↑(F c) ⊆ K ∧ RI K n e d)
    (hcard : ∀ c, (F c).card ≤ 3) {n : ℕ} {c d : C} (h : R n c d) :
    ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ RI (↑K) n c d := by
  induction n generalizing c with
  | zero =>
    obtain rfl := (hz c d).mp h
    exact ⟨∅, by simp only [Finset.card_empty, Nat.mul_zero, le_refl], (hIz _ _ _).mpr rfl⟩
  | succ n ih =>
    obtain ⟨e, hstep, hr⟩ := (hs n c d).mp h
    obtain ⟨L, hL, hrL⟩ := ih hr
    refine ⟨F c ∪ L, ?_, (hIs _ n c d).mpr ⟨e, hstep, ?_, ?_⟩⟩
    · have hc := Finset.card_union_le (F c) L
      have hF := hcard c
      omega
    · intro a ha
      exact Finset.mem_union.mpr (Or.inl ha)
    · exact footprint_mono hIz hIs hrL
        (fun _ ha => Finset.mem_union.mpr (Or.inr ha))

section Footprints

variable {W : ℕ} {K K' : Set ℤ}

/-- A run within a footprint is a `WordRAM.Steps` run, the footprint forgotten.

**Proof sketch.** Apply `lift_run` with the identity configuration map, dropping the
footprint part of the step relation. Read the target run through `Steps.zero_iff` and
`Steps.succ_iff`. -/
theorem StepsIn.toSteps {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : StepsIn P K n c c') :
    Steps P n c c' := by
  exact lift_run (S := fun c d => step P c = .inl d ∧
      ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K)
    (T := fun c d => step P c = .inl d) (R := StepsIn P K) (R' := Steps P)
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [StepsIn, and_assoc])
    (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    id (fun _ _ hs => hs.1) h

/-- **Every run has a small footprint**: a run of `n` steps of a vendored program stays within a
finite set of at most `3 n` cells, the cells it touches. So `StepsIn` loses nothing.

**Proof sketch.** Apply `exists_footprint` to the vendored step and the
`baseTouches` footprint. `Steps.zero_iff` and `Steps.succ_iff` expose the run, while
`XInstr.card_touches_le` for a base instruction bounds each step by three cells. -/
theorem Steps.exists_stepsIn {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : Steps P n c c') :
    ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ StepsIn P (↑K) n c c' := by
  exact exists_footprint (S := fun c d => step P c = .inl d)
    (F := fun c => baseTouches (P.getD c.pc .reject) c.mem)
    (RI := StepsIn P) (fun _ _ => Steps.zero_iff) (fun _ _ _ => Steps.succ_iff)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun c => XInstr.card_touches_le (.base _) c.mem) h

/-- A run within a footprint is a run within every larger set of cells.

**Proof sketch.** Apply `footprint_mono`: induction on the run length composes each
first-step inclusion with the larger footprint inclusion. -/
theorem StepsIn.mono {P : List Instr} {n : ℕ} {c c' : Cfg W} (h : StepsIn P K n c c')
    (hK : K ⊆ K') : StepsIn P K' n c c' := by
  exact footprint_mono (S := fun c d => step P c = .inl d)
    (F := fun c => baseTouches (P.getD c.pc .reject) c.mem)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl) h hK

/-- One run after the other, within the union of the two footprints.

**Proof sketch.** Induct on the first run length. Enlarge the second run to the union
with `StepsIn.mono` in the zero case; in the successor case include the first footprint
in the union and compose the tail by induction. -/
theorem StepsIn.trans {P : List Instr} {n k : ℕ} {c c₁ c₂ : Cfg W}
    (h₁ : StepsIn P K n c c₁) (h₂ : StepsIn P K' k c₁ c₂) :
    StepsIn P (K ∪ K') (n + k) c c₂ := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h₁
    simpa only [Nat.zero_add] using h₂.mono Set.subset_union_right
  | succ n ih =>
    obtain ⟨d, hs, hK, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨d, hs, hK.trans Set.subset_union_left, ih hr⟩

/-! ### Private one-step framing -/

/-- A base step changes no cell outside its footprint.

**Proof sketch.** Read the transition through `step_def`. Each writing arm is an update
at a cell listed by `baseTouches`, so `AgreeOutside.update` applies to
`AgreeOutside.refl`. The branch leaves the memory unchanged, and verdicts cannot step. -/
private theorem step_agreeOutside {P : List Instr} {c d : Cfg W}
    (hs : step P c = .inl d)
    (hK : ↑(baseTouches (P.getD c.pc .reject) c.mem) ⊆ K) :
    AgreeOutside K c.mem d.mem := by
  have write (a : ℤ) (v : BitVec W) (ha : a ∈ K) :
      AgreeOutside K c.mem (fun z => if z = a then v else c.mem z) := by
    have he : (fun z => if z = a then v else c.mem z) = Function.update c.mem a v := by
      funext z
      exact (Function.update_apply c.mem a v z).symm
    rw [he]
    exact (AgreeOutside.refl K c.mem).update ha v
  cases hi : P.getD c.pc .reject <;>
    simp only [step_def, hi, Sum.inl.injEq, Sum.inr_ne_inl] at hs
  all_goals
    subst d
    simp only [hi, baseTouches] at hK
    first | exact AgreeOutside.refl K c.mem
          | exact write _ _ (hK (by simp))

/-- **Every intermediate memory stays inside the footprint** (design §15c, obstacle 1). Along a
run within `K`, the configuration reached after any `k ≤ n` steps splits the run into two runs
within `K`, and its memory agrees with the starting memory outside `K`. The vendored `Finished`
and `compileProgram_correct` speak of the last memory only.

**Proof sketch.** Induct on the prefix length. Split off the first step and
apply induction to the remaining run. `step_agreeOutside` frames that step by
`AgreeOutside.update`, including the indirect target of a store; `AgreeOutside.trans`
composes this frame with that of the remaining prefix. -/
theorem StepsIn.agreeOutside {P : List Instr} {n : ℕ} {c c' : Cfg W}
    (h : StepsIn P K n c c') {k : ℕ} (hk : k ≤ n) :
    ∃ d : Cfg W, StepsIn P K k c d ∧ StepsIn P K (n - k) d c' ∧ AgreeOutside K c.mem d.mem := by
  induction k generalizing n c with
  | zero => exact ⟨c, rfl, h, AgreeOutside.refl K c.mem⟩
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨d, hs, hK, hr⟩ := h
      obtain ⟨e, hp, ht, hm⟩ := ih hr (Nat.le_of_succ_le_succ hk)
      refine ⟨e, ⟨d, hs, hK, hp⟩, ?_, (step_agreeOutside hs hK).trans hm⟩
      simpa only [Nat.add_sub_add_right] using ht

/-- **Straight-line code with its footprint.** A list of straight-line instructions runs through
in its length, as in `WordRAM.steps_straight`, within any `K` that contains what each instruction
touches in every memory. For `load` and `store` the hypothesis asks `K` to contain every address
a word can hold, so in practice this row serves code without them; loads and stores take the
known-number rows `steps_load`/`steps_store`, with their address added to the footprint.

**Proof sketch.** Induct on the instruction list. Obtain the first transition by
specializing `steps_straight` to the singleton head, using `CodeAt.left` and the published
`Steps` equations. Add the footprint inclusion from `hK` and recurse on `CodeAt.tail`;
`effects_cons` identifies the final memory. -/
theorem stepsIn_straight {P : List Instr} (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W)
    (hcode : CodeAt P pc l) (hl : ∀ i ∈ l, Straight i)
    (hK : ∀ i ∈ l, ∀ m' : ℤ → BitVec W, ↑(baseTouches i m') ⊆ K) :
    StepsIn P K l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => simp only [List.length_nil, Nat.add_zero, effects_nil, StepsIn]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.mp hl
    have hfirst : Steps P 1 ⟨pc, m⟩ ⟨pc + 1, effect i m⟩ := by
      simpa only [List.length_singleton, effects_cons, effects_nil] using
        (steps_straight [i] pc m (CodeAt.left (l₂ := l) hcode)
          (by simpa only [List.forall_mem_singleton] using hi))
    obtain ⟨d, hs, he⟩ := Steps.succ_iff.mp hfirst
    obtain rfl := Steps.zero_iff.mp he
    simp only [List.length_cons, effects_cons]
    refine ⟨⟨pc + 1, effect i m⟩, hs, ?_, ?_⟩
    · rw [hcode.head]
      exact hK i (List.mem_cons_self) m
    · have ht := ih (pc + 1) (effect i m) hcode.tail hl
        (fun j hj m' => hK j (List.mem_cons_of_mem i hj) m')
      convert ht using 1; congr 1; omega

/-- An extended run within a footprint is an `XSteps` run, the footprint forgotten.

**Proof sketch.** Apply `lift_run` with the identity configuration map, dropping
only the footprint inclusion from each extended step. -/
theorem XStepsIn.toXSteps {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W}
    (h : XStepsIn P x ρ K n c c') : XSteps P x ρ n c c' := by
  exact lift_run (S := fun c d => xstep P x ρ c = .inl d ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K)
    (T := fun c d => xstep P x ρ c = .inl d) (R := XStepsIn P x ρ K)
    (R' := XSteps P x ρ) (fun _ _ => Iff.rfl)
    (fun _ _ _ => by simp only [XStepsIn, and_assoc])
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) id (fun _ _ hs => hs.1) h

/-- **Every extended run has a small footprint**: a run of `n` steps stays within a finite set of
at most `3 n` cells, the cells it touches.

**Proof sketch.** Apply the shared `exists_footprint` construction to
`xstep` and `XInstr.touches`. `XInstr.card_touches_le` bounds each step, and
`Finset.card_union_le` bounds their accumulated union. -/
theorem XSteps.exists_xStepsIn {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W}
    (h : XSteps P x ρ n c c') : ∃ K : Finset ℤ, K.card ≤ 3 * n ∧ XStepsIn P x ρ (↑K) n c c' := by
  exact exists_footprint (S := fun c d => xstep P x ρ c = .inl d)
    (F := fun c => (P.getD c.pc (.base .reject)).touches c.mem)
    (RI := XStepsIn P x ρ) (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun c => XInstr.card_touches_le _ c.mem) h

/-- The footprint form of `XSteps.of_steps_proj`: a verdict-free run of the projection within `K`
is a run of the extended program within `K`.

**Proof sketch.** Use `lift_run` to preserve both the transition and its
footprint. `projected_fetch` identifies the fetched base instruction, and
`xstep_base_fetch` identifies its transition; its `XInstr.touches` is the projected
instruction's `baseTouches`. -/
theorem XStepsIn.of_stepsIn_proj {P : XProgram} {x ρ : List Bool} {n : ℕ}
    {c c' : Cfg W} (h : StepsIn P.proj K n c c') (o : List Bool) (r : ℕ) :
    XStepsIn P x ρ K n ⟨c, o, r⟩ ⟨c', o, r⟩ := by
  refine lift_run (S := fun c d => step P.proj c = .inl d ∧
      ↑(baseTouches (P.proj.getD c.pc .reject) c.mem) ⊆ K)
    (T := fun c d => xstep P x ρ c = .inl d ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K)
    (R := StepsIn P.proj K) (R' := XStepsIn P x ρ K)
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [StepsIn, and_assoc])
    (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
    (fun d => (⟨d, o, r⟩ : XCfg W)) (fun c d hs => ?_) h
  obtain ⟨hs, hK⟩ := hs
  have hf := projected_fetch hs
  constructor
  · change xstep P x ρ ⟨c, o, r⟩ = .inl ⟨d, o, r⟩
    rw [xstep_base_fetch x ρ c o r hf, hs, Sum.map_inl]
  · change ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K
    rw [hf]
    exact hK

end Footprints

/-! ## Starting and halting -/

/-- **The memory in which a run starts**, on an input of length `n`: the cell `-1` holds `n`
(as a word, so modulo `2^W`) and every other cell holds `0`. The cell `-1` is the compiler's
first argument cell (`Light.Compiler.cARG1`, `Light/Compiler/StatementCode.lean:82`), so a
compiled program receives `|x|` as its first argument (design §15c: `inLen` from an argument
cell, no `len` instruction). -/
def initMem (W n : ℕ) : ℤ → BitVec W :=
  Function.update (fun _ => 0) (-1) (wd W n)

/-- The start configuration on an input of length `n`: position `0`, `initMem W n`, nothing
emitted, no coin consumed. -/
def XCfg.init (W n : ℕ) : XCfg W := { pc := 0, mem := initMem W n, out := [], rd := 0 }

/-- **Halting within steps and cells** (stage 2's hypothesis). `HaltsWithin P x ρ W t v o f`: run
on the input `x` with the coin stream `ρ` and word size `W` from `XCfg.init W |x|`, the program
`P` gives the verdict `v` within `t` steps, the verdict step counted as in `WordRAM.exec`; it has
then emitted `o`; and every step before the verdict stays within a set of at most `f` cells. -/
def HaltsWithin (P : XProgram) (x ρ : List Bool) (W t : ℕ) (v : Bool) (o : List Bool) (f : ℕ) :
    Prop :=
  ∃ (n : ℕ) (c : XCfg W) (K : Finset ℤ), n < t ∧ K.card ≤ f ∧
    XStepsIn P x ρ (↑K) n (XCfg.init W x.length) c ∧ xstep P x ρ c = .inr v ∧ c.out = o

section Halting

variable {P : XProgram} {x ρ : List Bool} {W t t' f f' : ℕ} {v v' : Bool} {o o' : List Bool}

/-- A run that halts within `t` steps and `f` cells halts within any larger bounds.

**Proof sketch.** Keep the same witnesses, composing `n < t` with `t ≤ t'` and
the footprint cardinal bound with `f ≤ f'`. -/
theorem HaltsWithin.mono (h : HaltsWithin P x ρ W t v o f) (ht : t ≤ t') (hf : f ≤ f') :
    HaltsWithin P x ρ W t' v o f' := by
  obtain ⟨n, c, K, hn, hK, hr, hv, ho⟩ := h
  exact ⟨n, c, K, hn.trans_le ht, hK.trans hf, hr, hv, ho⟩

/-- **A bound in steps gives one in cells**: a run that halts within `t` steps halts within `t`
steps touching at most `3 t` cells. So for time bounds the cell count needs no separate proof.

**Proof sketch.** Forget the footprint with `XStepsIn.toXSteps`, then use
`XSteps.exists_xStepsIn` to obtain at most `3 * n` cells. Multiply `n < t` by three
to place that footprint within the required bound. -/
theorem HaltsWithin.touches_le (h : HaltsWithin P x ρ W t v o f) :
    HaltsWithin P x ρ W t v o (3 * t) := by
  obtain ⟨n, c, _, hn, _, hr, hv, ho⟩ := h
  obtain ⟨K, hK, hrun⟩ := hr.toXSteps.exists_xStepsIn
  exact ⟨n, c, K, hn, hK.trans (Nat.mul_le_mul_left 3 hn.le), hrun, hv, ho⟩

/-! ### Private halting-run determinism -/

/-- Two runs from one configuration that end in verdicts have the same last configuration
and verdict.

**Proof sketch.** Induct on the first length and case on the second. A zero-length run
already gives a verdict, so a positive-length competitor contradicts the disjointness of
`Sum.inl` and `Sum.inr`. If both lengths are positive, injectivity of `Sum.inl` identifies
the first successors and the induction hypothesis identifies the tails. -/
private theorem xSteps_verdict_unique {n k : ℕ} {c d e : XCfg W}
    (h₁ : XSteps P x ρ n c d) (hv : xstep P x ρ d = .inr v)
    (h₂ : XSteps P x ρ k c e) (hv' : xstep P x ρ e = .inr v') :
    d = e ∧ v = v' := by
  induction n generalizing c k with
  | zero =>
    obtain rfl := h₁
    cases k with
    | zero =>
      obtain rfl := h₂
      exact ⟨rfl, Sum.inr.inj (hv.symm.trans hv')⟩
    | succ k =>
      obtain ⟨a, hs, _⟩ := h₂
      have bad := hv.symm.trans hs
      contradiction
  | succ n ih =>
    obtain ⟨a, hs, hr⟩ := h₁
    cases k with
    | zero =>
      obtain rfl := h₂
      have bad := hv'.symm.trans hs
      contradiction
    | succ k =>
      obtain ⟨b, hs', hr'⟩ := h₂
      have he : a = b := Sum.inl.inj (hs.symm.trans hs')
      subst b
      exact ih hr hr'

/-- **The run is determined** by the input, the coin stream and the word size: two halting runs
give the same verdict and the same output.

**Proof sketch.** Forget the footprints and apply `xSteps_verdict_unique`.
That helper synchronizes the two runs using injectivity of `Sum.inl` and excludes
stepping past a verdict. Equality of the last configurations identifies their outputs. -/
theorem HaltsWithin.unique (h : HaltsWithin P x ρ W t v o f)
    (h' : HaltsWithin P x ρ W t' v' o' f') : v = v' ∧ o = o' := by
  obtain ⟨_, c, _, _, _, hr, hv, ho⟩ := h
  obtain ⟨_, d, _, _, _, hr', hv', ho'⟩ := h'
  obtain ⟨he, hvv⟩ := xSteps_verdict_unique hr.toXSteps hv hr'.toXSteps hv'
  exact ⟨hvv, ho.symm.trans ((congrArg XCfg.out he).trans ho')⟩

/-! ### Private coin-free transition -/

/-- A coin-free program takes the same step for every coin stream. -/
private theorem xstep_coin_irrel (hP : CoinFree P) (ρ' : List Bool) (c : XCfg W) :
    xstep P x ρ c = xstep P x ρ' c := by
  have hnot : ∀ a, P.getD c.pc (.base .reject) ≠ .coin a := by
    intro a ha
    rw [List.getD_eq_getElem?_getD, Option.getD_eq_iff] at ha
    rcases ha with hm | ⟨_, he⟩
    · exact hP (.coin a) (List.mem_of_getElem? hm) a rfl
    · cases he
  cases hi : P.getD c.pc (.base .reject) <;> simp only [xstep, hi]
  case base i => cases i <;> rfl
  case coin i => exact (hnot i hi).elim

/-- **A coin-free program does not depend on the coin stream.**

**Proof sketch.** `xstep_coin_irrel` excludes a fetched coin instruction
using `CoinFree` and `List.mem_of_getElem?`. Apply `lift_run` with the identity map to
transport each footprint run between coin streams, preserving the final verdict and output.
The same transport proves both directions. -/
theorem HaltsWithin.coin_irrel (hP : CoinFree P) (ρ' : List Bool) :
    HaltsWithin P x ρ W t v o f ↔ HaltsWithin P x ρ' W t v o f := by
  have transport (σ τ : List Bool) (h : HaltsWithin P x σ W t v o f) :
      HaltsWithin P x τ W t v o f := by
    obtain ⟨n, c, K, hn, hK, hr, hv, ho⟩ := h
    refine ⟨n, c, K, hn, hK, ?_, (xstep_coin_irrel hP τ c).symm.trans hv, ho⟩
    exact lift_run (S := fun a b => xstep P x σ a = .inl b ∧
        ↑((P.getD a.pc (.base .reject)).touches a.mem) ⊆ (↑K : Set ℤ))
      (T := fun a b => xstep P x τ a = .inl b ∧
        ↑((P.getD a.pc (.base .reject)).touches a.mem) ⊆ (↑K : Set ℤ))
      (R := XStepsIn P x σ (↑K)) (R' := XStepsIn P x τ (↑K))
      (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
      (fun _ _ => Iff.rfl) (fun _ _ _ => by simp only [XStepsIn, and_assoc])
      id (fun a _ hs => ⟨(xstep_coin_irrel hP τ a).symm.trans hs.1, hs.2⟩) hr
  exact ⟨transport ρ ρ', transport ρ' ρ⟩

end Halting

end WordRAM
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.mem_DTIME_iff` — membership in `DTIME`, unfolded.
* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

/-- `M` decides `L` in time `T` exactly when it computes `L`'s Boolean indicator, as a one-bit
output, in time `T`. -/
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔
      M.ComputesFunInTime (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T := by
  rw [computesFunInTime_iff]; rfl

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- **Membership in `DTIME`, unfolded**: `L ∈ DTIME T` exactly when some machine decides `L`
within `c · T` steps for some constant `c`. -/
theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity
```

## ===== TCSlib/Complexity/ClassP/P.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  obtain ⟨a, M, hM⟩ := hL
  refine dtime_poly_subset_P d ⟨a * c, M, fun x => (hM x).mono ?_⟩
  calc a * T x.length ≤ a * (c * (x.length ^ d + 1)) :=
        Nat.mul_le_mul (le_refl a) (hT x.length)
    _ = a * c * (x.length ^ d + 1) := by ring

/-- The key pointwise inequality behind the padding normalization:
`(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)` for every `n` and `d`. -/
lemma succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * (n ^ d + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _)
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := Nat.mul_pow 2 n d
      _ ≤ 2 ^ d * (n ^ d + 1) := Nat.mul_le_mul (le_refl _) (Nat.le_succ _)

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content: forward, a witness for the degree-`c`
component gives a bound `a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`; backward, `succ_pow_le`
turns a `C · (n + 1) ^ d` decider into a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing
in the degree-`d` component. (`audits/phase1-findings.md`, "Polynomial-time
normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨c, hs⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, M, hM⟩ := hs
    refine ⟨2 * a, c, M, fun x => (hM x).mono ?_⟩
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 0 < (x.length + 1) ^ c := Nat.pow_pos (Nat.succ_pos _)
    calc a * (x.length ^ c + 1)
        ≤ a * ((x.length + 1) ^ c + (x.length + 1) ^ c) :=
          Nat.mul_le_mul (le_refl a) (Nat.add_le_add h1 h2)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  · rintro ⟨C, d, M, hM⟩
    refine Set.mem_iUnion.mpr ⟨d, C * 2 ^ d, M, fun x => (hM x).mono ?_⟩
    calc C * (x.length + 1) ^ d
        ≤ C * (2 ^ d * (x.length ^ d + 1)) :=
          Nat.mul_le_mul (le_refl C) (succ_pow_le x.length d)
      _ = C * 2 ^ d * (x.length ^ d + 1) := by ring

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := fun _ hL =>
  mem_P_of_dtime_le hL 1 1 fun n => by
    rw [one_mul]
    exact Nat.le_add_left 1 (n ^ 1)

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Basic.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded computation, `SPACE`, `L`, and implicitly logspace computable functions

[AB09, Def 4.1]: a language is in `SPACE(s(n))` when some machine decides it while
visiting at most `c · s(n)` work-tape cells on every input of length `n`; `L = SPACE(log n)`
[AB09, Def 4.5]. [AB09, Def 4.16]: a function `f` is *implicitly logspace computable* when it
is polynomially bounded and the two languages "the `i`-th bit of `f(x)` is `1`" and
"`i` is a position of `f(x)`" are in `L`.

## The machine model

We reuse the campaign's machines (`Turing.FinTM Bool`) unchanged. They already have the
shape of [AB09, Fig. 4.1]:

* **the input tape is read-only**: a transition (`Turing.Action`) has no write component
  for the input tape, only a head move, clamped to the input and its two boundary blanks;
* **the output tape is write-once, append-only**: a step appends at most one symbol;
* **space is the number of work-tape cells visited** (`Turing.MultiTapeTM.spaceUsed`, the
  sum over the work tapes of the visited cells), exactly the measure of [AB09, Def 4.1]
  ("at most `c · s(n)` locations on M's work tapes (excluding the input tape) are ever
  visited by M's head").

## Main definitions

* `Turing.FinTM.ComputesInSpace` — `M` computes `f`, halting on every input, visiting at most
  `s(|x|)` work cells.
* `Turing.FinTM.DecidesInSpace` — `M` decides `L` within space `s`. [AB09, Def 4.1]
* `Complexity.SPACE` — the class of languages decidable in space `c · s(n)`. [AB09, Def 4.1]
* `Complexity.logSpace` — the logarithmic space bound `⌊log₂ n⌋ + 1`.
* `Complexity.LOGSPACE` — the class `L = SPACE(log n)`. [AB09, Def 4.5]
* `Complexity.indexLang` — the language `{⟨x, i⟩ | p x i}` with `i` in binary.
* `Complexity.ImplicitlyLogspaceComputable` — [AB09, Def 4.16].

## Main results

* `Turing.FinTM.computesInSpace_iff`, `Complexity.logSpace_eq` — the definitions of
  `ComputesInSpace` and `logSpace` as an equivalence and an equation.
* `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff`, `Complexity.LOGSPACE_eq` —
  the definitions of `DecidesInSpace`, `SPACE` and `LOGSPACE`, unfolded.
* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.
* `Complexity.logSpace_le_succ`, `Complexity.logSpace_le_of_le_mul_two_pow` — the logarithmic
  bound is at most linear, and at most `(A + 1) s` below `A · 2^s`.
* `Complexity.logSpace_le_size_succ` — the logarithmic bound is at most one more than the
  binary length.
* `Complexity.SPACE.mono_const` — `SPACE` absorbs constant factors (added 2026-10-10).
* `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` — no work tapes, zero space (added
  2026-10-10).

## Divergences from [AB09]

* **The logarithm.** [AB09] writes `SPACE(log n)` and requires `s(n) ≥ log n` (p. 79). We use
  `logSpace n = ⌊log₂ n⌋ + 1`, which is at least `1` (so short inputs get constant space, the
  standard reading of the convention) and is `Θ(log n)` for `n ≥ 2`.
* **Pairs and indices** (Def 4.16). The pair `⟨x, i⟩` is `Turing.pairEncode x (Nat.bits i)`:
  the campaign's self-delimiting pairing with the index in little-endian binary without
  redundant zeros (`Nat.bits 0 = []`). Indices are **`0`-based**: the bit language is
  `{⟨x, i⟩ | f(x)ᵢ = 1}` with `f(x)ᵢ` the `i`-th bit from `0`, and the length language is
  `{⟨x, i⟩ | i < |f(x)|}` where [AB09] writes `i ≤ |f(x)|` for `1`-based `i`.
* **Polynomial bound** (Def 4.16). [AB09] asks `|f(x)| ≤ |x|^c`; at `x = ε` that forces
  `f(ε) = ε` for `c ≥ 1`. We use the campaign normal form `|f(x)| ≤ C · (|x| + 1)^c`
  (`Complexity.PolyBound` shape).
* **Halting.** Deciding (resp. computing) includes halting on every input, as in [AB09]
  ("a TM M deciding L"); the space bound is checked at the halting time, and since space is
  monotone in time and frozen after halting this is the space of the whole computation.
* **One measure for both classes.** [AB09, Def 4.1]'s own wording splits: *visited*
  work-tape locations for `SPACE` (the clause quoted above) but *nonblank* locations for
  `NSPACE`. The campaign convention is the visited-cells measure for both; the planned
  `NSPACE` (`AroraBarakChapters3-4Plan.md`, phase P4.1) counts visited cells along every
  choice word, with all branches halting.
* **Zero bounds collapse the class** (P0 reception audit, round 1, finding 1): every
  work tape's visited set contains its origin, so every machine satisfies
  `M.k ≤ spaceUsed` on every input at every time. A single length with `s n = 0`
  therefore forces a deciding machine to have **no work tapes at all** — and then it
  has zero space on *every* input — so `SPACE s = SPACE (fun _ => 0)` (semantically
  the two-way-finite-automaton class) whenever `s` has a zero; multiplicative
  absorption cannot repair this, since `c * 0 = 0`. In particular the literal
  `SPACE (fun n => n)` is **not** linear space: `n = 0` collapses it. **Campaign
  convention:** every asymptotic chapter statement uses an everywhere-positive bound —
  `fun n => n + 1`, `fun n => n ^ c + 1`, `Complexity.logSpace` — never a bound with a
  zero. The characterization and the harmless-normalization identities are the sanity
  layer `TCSlib.Complexity.SpaceComplexity.ZeroSpace`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5; §4.3, Definition 4.16.)
-/

namespace Turing.FinTM

/-- The machine `M` computes `f` in space `s`: on every input `x` it halts with output `f x`,
and up to that time it has visited at most `s |x|` work-tape cells (summed over its work
tapes). The input tape (read-only) and the output tape (append-only) do not count.
[AB09, Def 4.1, for functions] -/
def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length

/-- **Computing in space, unfolded**: `M` computes `f` in space `s` exactly when on every input
`x` there is a time `t` at which `M` has halted with output `f x`
(`Turing.FinTM.ComputesInTime`), having visited at most `s |x|` work-tape cells by then. -/
theorem computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length :=
  Iff.rfl

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

/-- **Deciding in space, unfolded**: `M` decides `L` in space `s` exactly when it computes the
one-bit indicator `x ↦ [x ∈ L]` in space `s`. -/
theorem decidesInSpace_iff (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
    M.DecidesInSpace L s ↔
      M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s :=
  Iff.rfl

/-- A space bound can be weakened. -/
theorem ComputesInSpace.mono {M : FinTM Bool} {f : List Bool → List Bool} {s s' : ℕ → ℕ}
    (h : M.ComputesInSpace f s) (hs : ∀ n, s n ≤ s' n) : M.ComputesInSpace f s' := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact ⟨t, ht, hsp.trans (hs _)⟩

/-- A machine with no work tapes computes in zero space whatever it computes at all: the
space measure counts only work-tape cells. (Shared by the zero-space layer; added
2026-10-10.)

**Proof sketch.** With `M.k = 0` the space measure is an empty sum
(`Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`), at every halting time. -/
theorem computesInSpace_zero_of_k_eq_zero {M : FinTM Bool} {f : List Bool → List Bool}
    (hk : M.k = 0) (h : ∀ x, ∃ t, M.ComputesInTime x (f x) t) :
    M.ComputesInSpace f fun _ => 0 := by
  intro x
  obtain ⟨t, ht⟩ := h x
  exact ⟨t, ht, (MultiTapeTM.spaceUsed_zero_tapes_eq_zero (tm := M.tm) _ t hk).le⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- **`SPACE(s)`** [AB09, Def 4.1]: the languages decided by some finite binary-alphabet
machine visiting at most `c · s(n)` work-tape cells on inputs of length `n`, for some
constant `c`. -/
def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}

/-- **Membership in `SPACE`, unfolded**: `L ∈ SPACE s` exactly when some machine decides `L` in
space `c · s` for some constant `c`. -/
theorem mem_SPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
    L ∈ SPACE s ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n :=
  Iff.rfl

/-- `SPACE` is monotone in the space bound. -/
theorem SPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, hM.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `SPACE` absorbs constant factors: if `s₁ ≤ a · s₂` pointwise, then
`SPACE s₁ ⊆ SPACE s₂`. [AB09, Def 4.1: the constant `c` absorbs `a`] (Shared by the
zero-space layer and the hierarchy arguments; added 2026-10-10.)

**Proof sketch.** A witness at constant `c` for `s₁` is a witness at constant `c · a`
for `s₂`, since `c · s₁ n ≤ c · (a · s₂ n) = (c · a) · s₂ n`
(`Turing.FinTM.ComputesInSpace.mono`). -/
theorem SPACE.mono_const {s₁ s₂ : ℕ → ℕ} {a : ℕ} (h : ∀ n, s₁ n ≤ a * s₂ n) :
    SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  refine ⟨c * a, M, hM.mono fun n => ?_⟩
  calc c * s₁ n ≤ c * (a * s₂ n) := Nat.mul_le_mul_left c (h n)
    _ = c * a * s₂ n := (Nat.mul_assoc c a (s₂ n)).symm

/-- The logarithmic space bound `⌊log₂ n⌋ + 1`: `Θ(log n)`, and at least `1`, following the
convention `s(n) ≥ log n` of [AB09, p. 79]. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The logarithmic bound's formula: `logSpace n = Nat.log 2 n + 1`. -/
theorem logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl

/-- The logarithmic bound is at most linear: `logSpace n ≤ n + 1`.

**Proof sketch.** `Nat.log 2 n ≤ n` (`Nat.log_le_self`), then `Complexity.logSpace_eq`. -/
theorem logSpace_le_succ (n : ℕ) : logSpace n ≤ n + 1 := by
  have := Nat.log_le_self 2 n
  rw [logSpace_eq]
  omega

/-- The logarithmic width is at most one more than the binary length:
`logSpace n ≤ Nat.size n + 1`.

**Proof sketch.** At `n = 0` both sides are `1`. Otherwise `2 ^ Nat.log 2 n ≤ n < 2 ^ Nat.size n`
(`Nat.pow_log_le_self`, `Nat.lt_size_self`), so `Nat.log 2 n < Nat.size n`. -/
lemma logSpace_le_size_succ (n : ℕ) : logSpace n ≤ Nat.size n + 1 := by
  unfold logSpace
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have : Nat.log 2 n < Nat.size n :=
      (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp (lt_of_le_of_lt h1 h2)
    omega

/-- A number at most `A · 2^s` (with `s ≥ 1`) has `logSpace` at most `(A + 1) s`. -/
theorem logSpace_le_of_le_mul_two_pow {v A s : ℕ} (h : v ≤ A * 2 ^ s) (hs : 1 ≤ s) :
    logSpace v ≤ (A + 1) * s := by
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hlt : v < 2 ^ (A + s) := by
    rw [pow_add]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos s))
  have hle : A + s ≤ (A + 1) * s := by
    have := Nat.le_mul_of_pos_right A (show 0 < s by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [logSpace, Nat.log_zero_right]; omega
  · have := Nat.log_lt_of_lt_pow (by omega) hlt
    simp only [logSpace]; omega

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

/-- `LOGSPACE` is `SPACE logSpace`. -/
theorem LOGSPACE_eq : LOGSPACE = SPACE logSpace := rfl

/-- The language `{⟨x, i⟩ | p x i}`, the pair encoded as `Turing.pairEncode x (Nat.bits i)`
(index in little-endian binary). The shape of the two languages of [AB09, Def 4.16]. -/
def indexLang (p : List Bool → ℕ → Prop) : Language Bool :=
  {w | ∃ x i, w = pairEncode x (Nat.bits i) ∧ p x i}

/-- **Implicitly logspace computable functions** [AB09, Def 4.16]: `f` is polynomially
bounded, `|f(x)| ≤ C · (|x| + 1)^c`, and both the bit language
`{⟨x, i⟩ | f(x)ᵢ = 1}` and the length language `{⟨x, i⟩ | i < |f(x)|}` are in `L`.
Indices are `0`-based and written in binary (`Nat.bits`); see the module docstring for the
divergences (`0`-based `i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`, and the `+ 1`
in the polynomial bound). -/
def ImplicitlyLogspaceComputable (f : List Bool → List Bool) : Prop :=
  (∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c) ∧
  indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE ∧
  indexLang (fun x i => i < (f x).length) ∈ LOGSPACE

/-- `logSpace` is monotone. -/
lemma logSpace_mono {a b : ℕ} (h : a ≤ b) : logSpace a ≤ logSpace b := by
  unfold logSpace
  have := Nat.log_mono_right (b := 2) h
  omega

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/NSPACE.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space-bounded computation and `NSPACE`

[AB09, Definition 4.1, second clause]: `L ∈ NSPACE(s(n))` when some NDTM decides
`L` within `c · s(n)` work-tape cells on inputs of length `n`, regardless of its
nondeterministic choices. Built on the campaign NDTM
(`TCSlib.Complexity.TuringMachine.Nondeterministic`) with the visited-cells
branch-space measure (`Turing.NDTM.spaceUsedWith`).

## Divergences from [AB09] (shared with `SPACE` where applicable)

* **All branches halt** (`AroraBarakChapters3-4Plan.md`, CH34-Q7, maintainer
  decision 2026-10-08): deciding includes `Turing.NDTM.HaltsWithin` — every
  choice word of the budget length halts the machine. [AB09, Remark 4.3] notes
  this restriction is harmless for space-constructible bounds; adopting it
  outright matches `Complexity.NTIME`'s totality convention and the
  configuration-counting arguments of phase P4.2.
* **Visited cells, not nonblank cells**: [AB09]'s own Definition 4.1 counts
  visited locations for `SPACE` but nonblank locations for `NSPACE`; the
  campaign uses the visited measure for both (recorded in
  `TCSlib.Complexity.SpaceComplexity.Basic`).
* **Exact-length choice words**: the space condition quantifies over choice
  words of length exactly `T` (the halting budget); by
  `Turing.NDTM.spaceUsedWith_append_of_halt` all-branch halting at `T` freezes
  every branch's space, so longer words add nothing.
* Constants are absorbed as `c · s n`, and there is **no** `s(n) ≥ log n` side
  condition, as for `Complexity.SPACE`.
* **Zero bounds collapse the class, as for `Complexity.SPACE`** (P4.1 statement
  gate, note 6): every branch visits each work tape's initial head cell, so a zero
  of the bound at any input length forces the witness to have no work tapes at all.
  The normalized classes (`n ^ c + 1`, `Complexity.logSpace`) are positive
  everywhere and are unaffected. The `NSPACE` sanity twins (tape-count bound,
  collapse, normalization) are a recorded future additive layer.

## Main definitions

* `Turing.FinNDTM.DecidesInSpace` — all branches halt, all branches respect the
  space bound, and membership is existential-branch acceptance.
  [AB09, Definition 4.1]
* `Complexity.NSPACE` — the class, with constant absorption.
  [AB09, Definition 4.1]

## Main results (proved; phase-P4.1 statements)

* `Turing.FinNDTM.decidesInSpace_iff`, `Complexity.mem_NSPACE_iff` — the definitions,
  unfolded.
* `Complexity.NSPACE.mono` — monotone in the space bound.
* `Complexity.SPACE_subset_NSPACE` — [AB09, Theorem 4.2, second inclusion].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1, Remark 4.3,
  Theorem 4.2.)
-/

namespace Turing.FinNDTM

/-- The machine `N` decides `L` in space `s`, nondeterministically: on every
input `x` there is a budget `T` such that every branch of length `T` has halted
(`Turing.NDTM.HaltsWithin` — the all-branch convention, CH34-Q7), every such
branch has visited at most `s |x|` work-tape cells, and `x ∈ L` exactly when
some branch accepts. The time budget `T` is existential and unconstrained — only
space is bounded; by `Turing.NDTM.spaceUsedWith_append_of_halt` the exact-length
quantifiers already govern all longer branches. [AB09, Definition 4.1, second
clause, visited-cells convention] -/
def DecidesInSpace (N : FinNDTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ T : ℕ,
    N.tm.HaltsWithin x T ∧
    (∀ w : List Bool, w.length = T →
      N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length) ∧
    (x ∈ L ↔ N.AcceptsWithin x T)

/-- **Deciding in nondeterministic space, unfolded**: `N` decides `L` in space `s` exactly when
for every input `x` there is a budget `T` such that every branch of length `T` has halted,
every choice word of length exactly `T` visits at most `s |x|` work-tape cells, and `x ∈ L`
holds exactly when some branch accepts within `T`. -/
theorem decidesInSpace_iff (N : FinNDTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
    N.DecidesInSpace L s ↔ ∀ x : List Bool, ∃ T : ℕ,
      N.tm.HaltsWithin x T ∧
      (∀ w : List Bool, w.length = T →
        N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length) ∧
      (x ∈ L ↔ N.AcceptsWithin x T) :=
  Iff.rfl

end Turing.FinNDTM

namespace Complexity

open Turing

/-- The class of languages decidable nondeterministically in space `c · s` for
some constant `c`: `L ∈ NSPACE s` iff some finite binary-alphabet NDTM decides
it within `c · s n` visited work-tape cells on inputs of length `n`, in the
sense of `Turing.FinNDTM.DecidesInSpace`. [AB09, Definition 4.1] -/
def NSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInSpace L fun n => c * s n}

/-- **Membership in `NSPACE`, unfolded**: `L ∈ NSPACE s` exactly when some NDTM decides `L` in
space `c · s` for some constant `c`. -/
theorem mem_NSPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
    L ∈ NSPACE s ↔ ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInSpace L fun n => c * s n :=
  Iff.rfl

/-- `NSPACE` is monotone in the space bound.

**Proof sketch.** The same machine and the same per-input budgets witness the
larger bound: `c · s₁ n ≤ c · s₂ n` pointwise (`Nat.mul_le_mul_left`), and only
the space inequality mentions the bound. -/
theorem NSPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : NSPACE s₁ ⊆ NSPACE s₂ := by
  intro L hL
  obtain ⟨c, N, hN⟩ := hL
  refine ⟨c, N, fun x => ?_⟩
  obtain ⟨T, hhalt, hsp, hacc⟩ := hN x
  refine ⟨T, hhalt, ?_, hacc⟩
  intro w hw
  exact (hsp w hw).trans (Nat.mul_le_mul_left c (h x.length))

/-- **Deterministic space is nondeterministic space**: `SPACE s ⊆ NSPACE s`.
[AB09, Theorem 4.2, second inclusion]

**Proof sketch.** Let `M` decide `L` in space `c · s` with halting time `t x` on
input `x` (`Turing.FinTM.DecidesInSpace` supplies both). Embed as
`M.toFinNDTM`; take the budget `T := t x`. Every choice word of length `T` runs
identically to `M`'s deterministic run (`Turing.MultiTapeTM.toNDTM_runWith`), so
all-branch halting is `M`'s halting, the branch space is `M`'s space by
`Turing.MultiTapeTM.toNDTM_spaceUsedWith`, and the unique branch accepts (output
`[true]`) iff `x ∈ L` by the indicator equation — mirroring
`Complexity.DTIME_subset_NTIME`. -/
theorem SPACE_subset_NSPACE (s : ℕ → ℕ) : SPACE s ⊆ NSPACE s := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, ?_⟩
  intro x
  obtain ⟨t, hcomp, hsp⟩ := hM x
  have hbranch := M.toFinNDTM_haltsWithin_and_accepts_iff hcomp
  refine ⟨t, hbranch.1, ?_, hbranch.2⟩
  intro w hw
  change M.tm.toNDTM.spaceUsedWith w (M.tm.initCfg x) ≤ c * s x.length
  rw [M.tm.toNDTM_spaceUsedWith, hw]
  exact hsp

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space complexity classes: `PSPACE`, `NPSPACE`, `NL`, `coNL`

[AB09, Definition 4.5]: `PSPACE = ⋃_c SPACE(n^c)`, `NPSPACE = ⋃_c NSPACE(n^c)`,
`L = SPACE(log n)` and `NL = NSPACE(log n)`. The deterministic logarithmic class
already exists as `Complexity.LOGSPACE` (received surface, phase P0); this
module adds the remaining three, in the campaign's polynomial normal form
`n ^ c + 1` (mirroring `Complexity.P`/`Complexity.EXP`) and with the received
`Complexity.logSpace` bound (`⌊log₂ n⌋ + 1`). `coNL` is the complement class,
in the same complement form as `Complexity.coNP` — [AB09, §4.3.2]; the
Immerman-Szelepcsényi theorem (`NL = coNL`) is a phase-P4.4 statement, not
claimed here.

## Main definitions

* `Complexity.PSPACE`, `Complexity.NPSPACE` — polynomial space, deterministic
  and nondeterministic. [AB09, Definition 4.5]
* `Complexity.NL` — nondeterministic logarithmic space. [AB09, Definition 4.5]
* `Complexity.coNL` — complements of `NL` languages. [AB09, §4.3.2]

## Main results (proved; phase-P4.1 statements)

* `Complexity.space_poly_subset_PSPACE`, `Complexity.PSPACE_subset_NPSPACE`,
  `Complexity.LOGSPACE_subset_NL` — the definitional inclusions.
* `Complexity.NL_eq` — `NL = NSPACE logSpace`.
* `Complexity.LOGSPACE_subset_PSPACE` — `L ⊆ PSPACE`.
* `Complexity.SPACE_succ_pow_subset_PSPACE` — the shifted polynomial bounds `(n + 1)^k` give
  polynomial space.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Definition 4.5; §4.3.2.)
-/

namespace Complexity

/-- **`PSPACE`** [AB09, Definition 4.5]: the languages decidable in polynomial
space, `⋃ c, SPACE (n ^ c + 1)` in the campaign's polynomial normal form. -/
def PSPACE : Set (Language Bool) := ⋃ c : ℕ, SPACE fun n => n ^ c + 1

/-- **`NPSPACE`** [AB09, Definition 4.5]: the languages decidable in
nondeterministic polynomial space. `PSPACE = NPSPACE` is Savitch's theorem
([AB09, Theorem 4.14], phase P4.2), not a definitional fact. -/
def NPSPACE : Set (Language Bool) := ⋃ c : ℕ, NSPACE fun n => n ^ c + 1

/-- **`NL`** [AB09, Definition 4.5]: the languages decidable in nondeterministic
logarithmic space, over the received bound `Complexity.logSpace` (whose `+ 1`
floor and missing `s ≥ log n` convention are recorded divergences — see
`TCSlib.Complexity.SpaceComplexity.Basic`). -/
def NL : Set (Language Bool) := NSPACE logSpace

/-- `NL` is `NSPACE logSpace`, as an equation. -/
theorem NL_eq : NL = NSPACE logSpace := rfl

/-- **`coNL`** [AB09, §4.3.2]: the complements of `NL` languages, in the same
complement form as `Complexity.coNP`. `NL = coNL` is the Immerman-Szelepcsényi
theorem ([AB09, Theorem 4.20], phase P4.4). -/
def coNL : Set (Language Bool) := {L | Lᶜ ∈ NL}

/-- Every fixed-degree polynomial space class is contained in `PSPACE`.

**Proof sketch.** `Set.subset_iUnion` at the given degree, as for
`Complexity.dtime_poly_subset_P`. -/
theorem space_poly_subset_PSPACE (c : ℕ) : SPACE (fun n => n ^ c + 1) ⊆ PSPACE := by
  exact Set.subset_iUnion (fun d : ℕ => SPACE fun n => n ^ d + 1) c

/-- **`L ⊆ PSPACE`** [AB09, §4.1.2, the chain `L ⊆ … ⊆ PSPACE` of p. 92 (its first and
last members)]: a logspace decider uses at most `c · (n + 1)` cells.

**Proof sketch.** `logSpace n ≤ n + 1 = n ^ 1 + 1` (`Complexity.logSpace_le_succ`), so
`SPACE (logSpace) ⊆ SPACE (n ^ 1 + 1)` (`Complexity.SPACE.mono`), which lies in `PSPACE` at degree
one. -/
theorem LOGSPACE_subset_PSPACE : LOGSPACE ⊆ PSPACE := by
  rw [LOGSPACE_eq]
  exact (SPACE.mono fun n => by simpa only [pow_one] using logSpace_le_succ n).trans
    (space_poly_subset_PSPACE 1)

/-- `SPACE ((n + 1)^k) ⊆ PSPACE`: the shifted polynomial bound gives polynomial space.

**Proof sketch.** `(n + 1)^k ≤ 2^k (n^k + 1)` (`Complexity.succ_pow_le`), so
`Complexity.SPACE.mono_const` and `Complexity.space_poly_subset_PSPACE` at degree `k`. -/
theorem SPACE_succ_pow_subset_PSPACE (k : ℕ) : SPACE (fun n => (n + 1) ^ k) ⊆ PSPACE :=
  (SPACE.mono_const (a := 2 ^ k) fun n => succ_pow_le n k).trans
    (space_poly_subset_PSPACE k)

/-- `PSPACE ⊆ NPSPACE`: determinism is a special case, degree by degree.

**Proof sketch.** `Complexity.SPACE_subset_NSPACE` at each degree, then the
union is monotone (`Set.iUnion_mono`). -/
theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE := by
  exact Set.iUnion_mono fun c => SPACE_subset_NSPACE (fun n => n ^ c + 1)

/-- `L ⊆ NL` (in the campaign's names, `LOGSPACE ⊆ NL`).
[AB09, p. 92 chain]

**Proof sketch.** `Complexity.SPACE_subset_NSPACE` at `Complexity.logSpace`. -/
theorem LOGSPACE_subset_NL : LOGSPACE ⊆ NL := by
  exact SPACE_subset_NSPACE logSpace

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Constructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.TuringMachine.Build.WordTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-constructible functions

[AB09, §4.1, p. 79]: `S : ℕ → ℕ` is space-constructible when some machine
computes `S(|x|)` from `x` within `O(S(|x|))` space, and the book's standing
convention is `S(n) > log n`. The definition mirrors
`Complexity.TimeConstructible` — output in binary (`Nat.bits`), constant slack
`c · S n`, which implements the book's own asymptotic space convention
([AB09, p. 79]: "computes `S(|x|)` in `O(S(|x|))` space"); an exact-space
variant is not posed here (the exact-**time** refutation of chapter 1 does not
transfer: a space deadline forces no premature halt) — and carries the book's
convention as the conjunct `∀ n, logSpace n ≤ S n`, so that downstream
statements (the space hierarchy, Savitch) can draw on it without restating it;
results needing only weaker hypotheses must say so.

## Main definitions

* `Complexity.SpaceConstructible` — the binary-output, constant-slack,
  above-log form. [AB09, §4.1, p. 79]

## Main results (proved)

* `Complexity.spaceConstructible_iff` — the definition as an equivalence.
* `Complexity.spaceConstructible_logSpace` — `log` is space-constructible.
* `Complexity.spaceConstructible_linear` — `n + 1` is space-constructible.
* `Complexity.spaceConstructible_poly` — `n ^ c + 1` is space-constructible for `c ≥ 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, p. 79.)
-/

namespace Complexity

open Turing

/-- A function `S` is **space-constructible** when it dominates the logarithm
(`Complexity.logSpace`, the book's standing `S(n) > log n` convention carried as
data) and some machine computes the binary representation of `S (|x|)` from `x`
within `c · S (|x|)` visited work-tape cells. Mirrors
`Complexity.TimeConstructible` (binary output via `Nat.bits`, constant slack).
[AB09, §4.1, p. 79] -/
def SpaceConstructible (S : ℕ → ℕ) : Prop :=
  (∀ n, logSpace n ≤ S n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
    M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n

/-- **Space constructibility, unfolded**: `S` is space constructible exactly when
`logSpace n ≤ S n` for every `n` and, for some constant `c > 0`, some machine computes
`x ↦ (S |x|).bits` in space `c · S` (`Turing.FinTM.ComputesInSpace`). -/
theorem spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n :=
  Iff.rfl

/-- Positive binary words have exactly the normalized logarithmic width. -/
private lemma b3a_bits_length {n : ℕ} (hn : n ≠ 0) :
    n.bits.length = logSpace n :=
  (LogProg.length_bits_eq_log hn).trans (logSpace_eq n).symm

/-- The counter word with its first cell overwritten by `true`. -/
private def b3a_word (n : ℕ) : List Bool := true :: n.bits.tail

/-- The overwrite handles zero while preserving every positive counter width. -/
private lemma b3a_word_length (n : ℕ) : (b3a_word n).length = logSpace n := by
  by_cases hn : n = 0
  · subst n
    simp [b3a_word, logSpace, Nat.bits]
  · simp only [b3a_word, List.length_cons, List.length_tail, b3a_bits_length hn]
    unfold logSpace
    omega

/-- Restricting a buffer to its occupied nonnegative interval does not change it. -/
private lemma b3a_buffer_restrict (w : List Bool) (z : ℤ) :
    (if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape w z else none) =
      FinTM.bufferTape w z := by
  by_cases hzero : 0 ≤ z
  · by_cases hlast : z < (w.length : ℤ)
    · simp [hzero, hlast]
    · have out : w.length ≤ z.toNat := by omega
      simp [hzero, hlast, FinTM.bufferTape]
  · simp [hzero, FinTM.bufferTape]

/-- Setting the first buffered cell yields `true :: tail`, including an empty buffer. -/
private lemma b3a_buffer_overwrite (w : List Bool) (z : ℤ) :
    (if z = 0 then some true else FinTM.bufferTape w z) =
      FinTM.bufferTape (true :: w.tail) z := by
  by_cases hz : z = 0
  · subst z
    simp [FinTM.bufferTape]
  · by_cases hp : 0 ≤ z
    · have ht : z.toNat ≠ 0 := by omega
      simp only [if_neg hz, FinTM.bufferTape, if_pos hp, List.getElem?_cons,
        if_neg ht, List.getElem?_tail]
      congr 1
      omega
    · simp [hz, FinTM.bufferTape, hp]

/-- A live phase seam: its word is on tape zero and all heads are at the origin. -/
private def b3a_cfg {k : ℕ} [NeZero k] {S : Type} (s : S)
    (x w : List Bool) : Cfg k Bool S x :=
  { Cfg.init s x with
    workTapes := fun j => if j = 0 then FinTM.bufferTape w else fun _ => none }

/-- Map only the control field of a canonical phase seam. -/
private lemma b3a_cfg_map {k : ℕ} [NeZero k] {S T : Type} (f : S → T)
    (s : S) (x w : List Bool) :
    (b3a_cfg (k := k) s x w).mapState f = b3a_cfg (f s) x w := rfl

/-- Relocate a single-buffer seam along a selection preserving tape zero.
**Proof sketch.** Selected tapes use the public configuration projections;
other tapes use the frame theorem at time zero. All unused cells and heads are blank. -/
private lemma b3a_embed_cfg {m k : ℕ} [NeZero m] [NeZero k] {S : Type}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (hzero : ι 0 = 0)
    (s : S) (x w : List Bool) :
    embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] (b3a_cfg s x w) =
      b3a_cfg (k := k) s x w := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_tape]
      have hz : ι i = 0 ↔ i = 0 := by rw [← hzero, ι.injective.eq_iff]
      simp only [b3a_cfg, hz]
    · have frame := (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen
      have hj : j ≠ 0 := fun eq => chosen ⟨0, hzero.trans eq.symm⟩
      simpa [b3a_cfg, hj] using frame.1
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_pos]
      rfl
    · exact (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen |>.2
  · rfl

/-- A coarse constant-factor space bound for tape relocation.
**Proof sketch.** Every selected tape is bounded by the source's total space;
each unused tape contributes one cell. Sum this common bound over the host bank. -/
private lemma b3a_embed_space {m k : ℕ} {S : Type} {x : List Bool}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k)
    (d : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι R).spaceUsed
        (embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] d) t ≤
      k * (R.spaceUsed d t + 1) := by
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _j : Fin k, (R.spaceUsed d t + 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases chosen : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := chosen
        rw [(embedEmitTM_visitedByTapeHead ι R (fun _ _ => none) (fun _ => 0) [] d t i).2]
        exact (R.spaceUsedByTape_le_spaceUsed d t i).trans (Nat.le_succ _)
      · rw [(embedEmitTM_visitedByTapeHead_frame ι R (fun _ _ => none)
          (fun _ => 0) [] d t j chosen).2]
        omega
    _ = _ := by simp [MultiTapeTM.spaceUsed]

/-- The additive space ledger for an arbitrary live-exit seam: the general seam space lemma
`Turing.seamCompTM_spaceUsed_le_add_ofCfg`, with this file's argument names. -/
private lemma b3a_seam_space {k : ℕ} {S T : Type} [DecidableEq S] {x : List Bool}
    (R : MultiTapeTM k Bool S) (exit : S) (Q : MultiTapeTM k Bool T) (entry : T)
    {d e : Cfg k Bool S x} {a b : ℕ} (run : R.runFrom d a = e)
    (live : e.state = some exit) (cut : ∀ u < a, (R.runFrom d u).state ≠ some exit) :
    (seamCompTM R exit Q entry).spaceUsed (d.mapState Sum.inl) (a + 1 + b) ≤
      R.spaceUsed d a + Q.spaceUsed (e.mapState fun _ => entry) b :=
  seamCompTM_spaceUsed_le_add_ofCfg R exit Q entry run live cut

/-- The public native counter, specialized to blank origin tapes with a cardinality ledger.
**Proof sketch.** Instantiate R8.5c at its entry, identify the globally blank frame
with the buffer layout, and enclose each head's visited set in the promised interval.
The first-exit clause is retained for the subsequent dispatch. -/
private theorem b3a_counter :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) Bool S) (entry exit : S) (B : ℕ),
      ∀ x : List Bool, ∃ t,
        R.runFrom (b3a_cfg entry x []) t = b3a_cfg exit x x.length.bits ∧
        (∀ u < t, (R.runFrom (b3a_cfg entry x []) u).state ≠ some exit) ∧
        R.spaceUsed (b3a_cfg entry x []) t ≤ B * (x.length.bits.length + 1) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, C, contract⟩ := exists_inputLengthTM
  letI := fs
  letI := ds
  refine ⟨K, S, fs, ds, R, entry, exit, (K + 1) * (2 * C + 1), ?_⟩
  intro x
  obtain ⟨t, _, cut, heads, finished⟩ := contract (b3a_cfg entry x []) rfl rfl
    (by intros; simp [b3a_cfg]) (by intros; simp [b3a_cfg])
  refine ⟨t, ?_, cut, ?_⟩
  · rw [finished]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      by_cases hj : j = 0
      · simp [b3a_cfg, hj, b3a_buffer_restrict]
      · simp [b3a_cfg, hj]
    · rfl
    · rfl
  · have perTape (j : Fin (K + 1)) : R.spaceUsedByTape (b3a_cfg entry x []) t j ≤
        2 * (C * (x.length.bits.length + 1)) + 1 := by
      calc
        _ ≤ (Finset.Icc (-((C * (x.length.bits.length + 1) : ℕ) : ℤ))
            ((C * (x.length.bits.length + 1) : ℕ) : ℤ)).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
          have bound := heads u (Nat.le_of_lt_succ (Finset.mem_range.mp hu)) j
          simpa [b3a_cfg, Finset.mem_Icc, abs_le] using bound
        _ = _ := by rw [Int.card_Icc]; omega
    calc
      _ ≤ ∑ _j : Fin (K + 1), (2 * (C * (x.length.bits.length + 1)) + 1) :=
        Finset.sum_le_sum fun j _ => perTape j
      _ = (K + 1) * (2 * (C * (x.length.bits.length + 1)) + 1) := by simp
      _ ≤ (K + 1) * ((2 * C + 1) * (x.length.bits.length + 1)) := by
        apply Nat.mul_le_mul_left
        ring_nf; omega
      _ = _ := by ring

/-- The public constant writer overwrites cell zero and returns to its origin.
**Proof sketch.** Use R8.4 with `[true]`. Its four-step trace supplies the exact
exit cut and two-cell head interval; the buffer update is the tail identity above. -/
private theorem b3a_overwrite (x w : List Bool) :
    (writeConstTM 1 0 [true]).runFrom (b3a_cfg (.wr 0) x w) 4 =
        b3a_cfg .done x (true :: w.tail) ∧
      (∀ u < 4, ((writeConstTM 1 0 [true]).runFrom
        (b3a_cfg (.wr 0) x w) u).state ≠ some .done) ∧
      (writeConstTM 1 0 [true]).spaceUsed (b3a_cfg (.wr 0) x w) 4 ≤ 2 := by
  obtain ⟨run, cut, heads⟩ := writeConstTM_run_ofCfg (0 : Fin 1) [true]
    (b3a_cfg (.wr 0) x w) rfl
  norm_num only [List.length_singleton] at run
  refine ⟨?_, cut, ?_⟩
  · rw [run]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      have hj : j = 0 := Subsingleton.elim _ _
      simp only [b3a_cfg, Cfg.init, hj, if_pos, List.length_singleton,
        zero_add, sub_zero]
      simp only [true_and, show (0 ≤ z ∧ z < 1) ↔ z = 0 by omega]
      by_cases hz : z = 0
      · simp [hz, FinTM.bufferTape]
      · simpa [hz] using b3a_buffer_overwrite w z
    · rfl
    · rfl
  · change ∑ j : Fin 1, _ ≤ 2
    rw [Fintype.sum_subsingleton _ (0 : Fin 1)]
    calc
      _ ≤ (Finset.Icc (0 : ℤ) 1).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa [b3a_cfg] using heads 0 u (Nat.le_of_lt_succ (Finset.mem_range.mp hu))
      _ = 2 := by decide

/-- The emitting phase shares tape zero and places its bank after the native counter bank. -/
private def b3a_virtualSelect (K m : ℕ) : Fin (1 + m) ↪ Fin (K + 1 + m) where
  toFun i := ⟨if i.val = 0 then 0 else K + i.val, by split_ifs <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have vals := congrArg Fin.val eq
    dsimp at vals
    split_ifs at vals <;> omega

/-- The initial virtual-input layout is the single-buffer phase seam.
**Proof sketch.** Split the host tapes into its buffer and source bank. The source
starts at input position one, with blank work tapes and all heads at zero. -/
private lemma b3a_virtual_cfg (L : FinTM Bool) (x y : List Bool) :
    vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) [] =
      b3a_cfg (L.tm.q₀, true) x y := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have zero : Fin.castAdd L.k (0 : Fin 1) = 0 := rfl
      change FinTM.bufferTape y z =
        (if Fin.castAdd L.k (0 : Fin 1) = 0 then FinTM.bufferTape y else fun _ => none) z
      rw [if_pos zero]
    · have nonzero : Fin.natAdd 1 i ≠ (0 : Fin (1 + L.k)) := by
        intro eq
        have vals := congrArg Fin.val eq
        simp only [Fin.coe_natAdd, Fin.val_zero] at vals
        omega
      simp only [vhostCfg, Fin.addCases_right, b3a_cfg, if_neg nonzero,
        MultiTapeTM.initCfg, Cfg.init]
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
  · rfl

/-- Assemble the three public phases with an explicit boundary-inclusive space allowance.
**Proof sketch.** Count on a native bank, overwrite its first cell, then host the
length counter on that word. Both seams dispatch at their first exits. The public
relocation and seam ledgers bound total space by a fixed multiple of the normalized
logarithm plus one; the final virtual-input halt emits the full binary answer. -/
private theorem b3a_log_machine :
    ∃ (A : ℕ), 0 < A ∧ ∃ M : FinTM Bool,
      M.ComputesInSpace (fun x => (logSpace x.length).bits)
        (fun n => A * (logSpace n + 1)) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, B, counter⟩ := b3a_counter
  letI := fs
  letI := ds
  obtain ⟨L, b, computes, space⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let k := K + 1 + L.k
  let ic : Fin (K + 1) ↪ Fin k := Fin.castAddEmb L.k
  let iw : Fin 1 ↪ Fin k := Fin.castLEEmb (by dsimp [k]; omega)
  let iv := b3a_virtualSelect K L.k
  have ic0 : ic 0 = 0 := rfl
  have iw0 : iw 0 = 0 := rfl
  have iv0 : iv 0 = 0 := by apply Fin.ext; simp [iv, b3a_virtualSelect]
  let C := embedEmitTM ic R
  let W := embedEmitTM iw (writeConstTM 1 0 [true])
  let E := embedEmitTM iv (vhostEmitTM L.tm)
  let CW := seamCompTM C exit W (.wr 0)
  let H := seamCompTM CW (Sum.inr .done) E (L.tm.q₀, true)
  let M : FinTM Bool :=
    { k := k
      State := (S ⊕ WritePhase 1) ⊕ (L.State × Bool)
      tm := {H with q₀ := Sum.inl (Sum.inl entry)} }
  refine ⟨k * (B + b + 8) + 1, by omega, M, ?_⟩
  intro x
  let y := b3a_word x.length
  obtain ⟨t, counted, countCut, countSpace⟩ := counter x
  obtain ⟨written, writeCut, writeSpace⟩ := b3a_overwrite x x.length.bits
  -- Count and overwrite share the buffer; their first-exit cuts justify both dispatches.
  have countRun : C.runFrom (b3a_cfg entry x []) t =
      b3a_cfg exit x x.length.bits := by
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom, counted,
      b3a_embed_cfg R ic ic0]
  have countFirst : ∀ u < t, (C.runFrom (b3a_cfg entry x []) u).state ≠ some exit := by
    intro u hu
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom]
    exact countCut u hu
  have writeRun : W.runFrom (b3a_cfg (.wr 0) x x.length.bits) 4 =
      b3a_cfg .done x y := by
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom, written, b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0]
    rfl
  have writeFirst : ∀ u < 4,
      (W.runFrom (b3a_cfg (.wr 0) x x.length.bits) u).state ≠ some .done := by
    intro u hu
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom]
    exact writeCut u hu
  have cwRun : CW.runFrom (b3a_cfg (Sum.inl entry) x []) (t + 1 + 4) =
      b3a_cfg (Sum.inr .done) x y := by
    simpa only [b3a_cfg_map] using seamCompTM_run_ofCfg C exit W (.wr 0)
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun)
  have cwFirst : ∀ u < t + 1 + 4,
      (CW.runFrom (b3a_cfg (Sum.inl entry) x []) u).state ≠ some (Sum.inr .done) := by
    simpa only [b3a_cfg_map] using seamCompTM_firstReturn_ofCfg C exit W (.wr 0) .done
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun) rfl
      (by simpa only [b3a_cfg_map] using writeFirst)
  -- The last phase forwards the hosted counter's full output, including its halting step.
  let u := b * (y.length + 1)
  have tag : FinTM.VirtualTag (L.tm.initCfg y).inputPos true := by
    simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨tagEnd, _, hosted⟩ := vhostEmitTM_runFrom L.tm (L.tm.initCfg y) true tag
    (1 : Fin (x.length + 2)) [] u
  have emitted : E.runFrom (b3a_cfg (L.tm.q₀, true) x y) u =
      embedEmitCfg iv (fun _ _ => none) (fun _ => 0) []
        (vhostCfg (L.tm.runFrom (L.tm.initCfg y) u) tagEnd (1 : Fin (x.length + 2)) []) := by
    rw [← b3a_embed_cfg (vhostEmitTM L.tm) iv iv0 (L.tm.q₀, true) x y,
      ← b3a_virtual_cfg, embedEmitTM_runFrom, hosted]
  have fullRun := seamCompTM_run_ofCfg CW (Sum.inr .done) E (L.tm.q₀, true)
    cwRun rfl cwFirst (by simpa only [b3a_cfg_map] using emitted)
  have start : M.tm.initCfg x = b3a_cfg (Sum.inl (Sum.inl entry)) x [] := by
    apply Cfg.ext <;> simp [M, MultiTapeTM.initCfg, b3a_cfg, Cfg.init]
  refine ⟨(t + 1 + 4) + 1 + u, ?_, ?_⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [start]
    change (H.runFrom _ _).state = none ∧ (H.runFrom _ _).output = _
    rw [show b3a_cfg (Sum.inl (Sum.inl entry)) x [] =
      (b3a_cfg (Sum.inl entry) x []).mapState Sum.inl from rfl, fullRun]
    obtain ⟨halted, output⟩ := (FinTM.computesInTime_iff L y _ u).mp (computes y)
    simp only [Cfg.mapState, embedEmitCfg, vhostCfg, List.nil_append,
      halted, output, Option.map_none, y, b3a_word_length, and_self]
  · rw [start]
    change H.spaceUsed _ _ ≤ _
    -- Add the three boundary-inclusive ledgers before absorbing the constant slack.
    have firstLedger := b3a_seam_space C exit W (.wr 0) (b := 4)
      countRun rfl countFirst
    have lastLedger := b3a_seam_space CW (Sum.inr .done) E (L.tm.q₀, true) (b := u)
      cwRun rfl cwFirst
    simp only [b3a_cfg_map] at firstLedger lastLedger
    have cSpace := b3a_embed_space R ic (b3a_cfg entry x []) t
    rw [b3a_embed_cfg R ic ic0] at cSpace
    have wSpace := b3a_embed_space (writeConstTM 1 0 [true]) iw
      (b3a_cfg (.wr 0) x x.length.bits) 4
    rw [b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0] at wSpace
    have eSpace := b3a_embed_space (vhostEmitTM L.tm) iv
      (vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) []) u
    rw [b3a_virtual_cfg, b3a_embed_cfg (vhostEmitTM L.tm) iv iv0] at eSpace
    have eSource := vhostEmitTM_spaceUsed_le L.tm (L.tm.initCfg y) true tag
      (1 : Fin (x.length + 2)) [] u
    rw [b3a_virtual_cfg] at eSource
    have sizeBound : Nat.size y.length ≤ y.length := by
      rw [← Nat.size_eq_bits_len]
      exact length_bits_le_self _
    have width := LogProg.length_bits_le_log x.length
    have yLength : y.length = logSpace x.length := b3a_word_length _
    have nativeBound : C.spaceUsed (b3a_cfg entry x []) t ≤
        k * (B * (logSpace x.length + 1) + 1) := by
      apply cSpace.trans
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_right
      exact countSpace.trans (Nat.mul_le_mul_left B (Nat.add_le_add_right width 1))
    have writerBound : W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 ≤ k * 3 := by
      exact wSpace.trans (Nat.mul_le_mul_left _ (by omega))
    have emitterBound : E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u ≤
        k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
      apply eSpace.trans
      apply Nat.mul_le_mul_left
      have ls := space y u
      have bound := (Nat.mul_le_mul_left b (Nat.add_le_add_right sizeBound 1))
      rw [yLength] at bound eSource ls
      omega
    calc
      _ ≤ C.spaceUsed (b3a_cfg entry x []) t +
          W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 +
          E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u :=
        lastLedger.trans (Nat.add_le_add_right firstLedger _)
      _ ≤ k * (B * (logSpace x.length + 1) + 1) + k * 3 +
          k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
        exact Nat.add_le_add (Nat.add_le_add nativeBound writerBound) emitterBound
      _ ≤ (k * (B + b + 8) + 1) * (logSpace x.length + 1) := by
        ring_nf; omega

/-- **The logarithm is space-constructible.** [AB09, p. 79: "all functions of
interest, including `log n`, …, are space-constructible"]

**Proof sketch.** Fill obligations: a machine that (i) counts the input length
in binary on a work tape by one left-to-right input scan with a binary
increment at each step (the `Turing.counterTM`/`incrementTM` idiom — P11 of
`machine-library-design.md` §4, space-annotated per §12 R3) — the counter word
has `|Nat.bits n| = logSpace n` cells **for `n > 0` only** (`Nat.bits 0 = []`
has length `0 ≠ logSpace 0 = 1`), so (ii) the empty
input is special-cased to emit `(logSpace 0).bits = [true]` directly, and
otherwise the machine computes the counter word's bit-length by a second count
and emits its bits. Space: the counters and markers fit in
`A·(logSpace n + 1) ≤ 2A·logSpace n` visited cells (boundary cells included
before absorbing, since `logSpace n ≥ 1`); the dominance conjunct is `le_refl`
at `S = logSpace`.

**Fill appendix.** The empty-input special case is realized uniformly: after
R8.5c counts the native input, the constant writer sets the first buffered cell
to `true`. The resulting word has length `logSpace n`, including at zero. A
Z1-hosted Catalog length counter emits its binary length and genuinely halts.
Both live exits are intercepted at their first visits. The space ledger includes
the native head intervals, the overwrite boundary, the virtual-input boundary
cells and the fresh bank, giving `A * (logSpace n + 1)` before absorption. -/
theorem spaceConstructible_logSpace : SpaceConstructible logSpace := by
  obtain ⟨A, hA, M, hM⟩ := b3a_log_machine
  refine ⟨fun _ => le_rfl, 2 * A, by omega, M, ?_⟩
  intro x
  obtain ⟨t, ht, hs⟩ := hM x
  refine ⟨t, ht, hs.trans ?_⟩
  have hlog : logSpace x.length + 1 ≤ 2 * logSpace x.length := by
    unfold logSpace
    omega
  calc
    A * (logSpace x.length + 1) ≤ A * (2 * logSpace x.length) :=
      Nat.mul_le_mul_left _ hlog
    _ = (2 * A) * logSpace x.length := by ring

/-- **Linear space is constructible**: `n ↦ n + 1` is space-constructible (the
`+ 1` prevents the inherited zero-bound collapse at `n = 0` — the zero-bound
convention, `SpaceComplexity/ZeroSpace.lean` — and satisfies the dominance
conjunct; zero-space classes are nonempty, so this is about collapse, not
vacuity).

**Proof sketch.** The input-scan counter of
`Complexity.spaceConstructible_logSpace`, **initialized at `1`** so that after
`n` consumed symbols it holds `n + 1` (an uncorrected length counter holds `n`
and emits the wrong word); emit its bits. Space:
the counter's binary width plus fixed administrative cells fit in
`A·(n + 2) ≤ 2A·(n + 1)` visited cells; dominance is `logSpace n ≤ n + 1`
(`1 ≤ 1` at `n = 0`; a small arithmetic lemma otherwise).

**Fill appendix.** The counter initialized at `1` is realized by the Catalog
length counter on `true :: x`, using the proved prepend and buffered-composition
rows. Its linear running time bounds all visited work-tape cells, including
the counter width and boundary cells. -/
theorem spaceConstructible_linear : SpaceConstructible fun n => n + 1 := by
  refine ⟨logSpace_le_succ, ?_⟩
  obtain ⟨P, a, hp, _⟩ := FinTM.computesFunInTime_prepend_spaceUsed [true]
  obtain ⟨L, b, hl, _⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let M := FinTM.bufferedCompTM P L
  refine ⟨M.k * (a + 2 * b + 4) + 1, by omega, M, ?_⟩
  intro x
  let t := a * (x.length + 1) + (x.length + 1) + 2 + b * (x.length + 2)
  refine ⟨t, ?_, ?_⟩
  · simpa [M, t] using FinTM.bufferedCompTM_computesInTime P L (hp x) (hl ([true] ++ x))
  · have ht : t + 1 ≤ (a + 2 * b + 4) * (x.length + 1) := by
      dsimp [t]
      ring_nf; omega
    calc
      M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (t + 1) :=
        M.tm.spaceUsed_le_mul_succ _ _
      _ ≤ M.k * ((a + 2 * b + 4) * (x.length + 1)) := Nat.mul_le_mul_left _ ht
      _ ≤ (M.k * (a + 2 * b + 4) + 1) * (x.length + 1) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- The tail transducer's transition: one bit of state, "the first bit has been read". -/
private def scp_tailδ : Bool → Bool → Bool := fun _ _ => true

/-- The tail transducer's emission: nothing on the first bit, the bit itself afterwards. -/
private def scp_tailO : Bool → Bool → Option Bool := fun q b => if q then some b else none

/-- After the first bit the tail transducer copies its input. -/
private theorem scp_transduce_copy (l : List Bool) : transduce scp_tailδ scp_tailO true l = l :=
  transduce_of_copy _ _ true (fun _ => rfl) (fun _ => rfl) l

/-- From its start state the tail transducer computes `List.tail`. -/
private theorem scp_transduce_tail (x : List Bool) :
    transduce scp_tailδ scp_tailO false x = x.tail := by
  cases x with
  | nil => exact transduce_nil _ _ _
  | cons b l =>
    rw [transduce_cons]
    simp only [scp_tailO, scp_tailδ, Bool.false_eq_true, if_false, Option.toList_none,
      List.nil_append, scp_transduce_copy, List.tail_cons]

/-- The unary intermediate is short: `(|x.tail| + 1) ^ c ≤ |x| ^ c + 1`. -/
private theorem scp_tail_pow_le (c : ℕ) (x : List Bool) :
    (x.tail.length + 1) ^ c ≤ x.length ^ c + 1 := by
  cases x with
  | nil => simp
  | cons b l => simp

/-- The conditional's value: for `1 ≤ c`, the branch function is `x ↦ (|x| ^ c + 1).bits`
(`0 ^ c + 1 = 1` on the empty input; otherwise the count of `true :: 1ᴾ` with
`P = (|x.tail| + 1) ^ c = |x| ^ c`). -/
private theorem scp_value (c : ℕ) (hc : 1 ≤ c) (x : List Bool) :
    (if decide (x = []) then Nat.bits 1
      else Nat.bits (true :: List.replicate (1 * (x.tail.length + 1) ^ c) true).length) =
      Nat.bits (x.length ^ c + 1) := by
  cases x with
  | nil =>
    simp only [decide_true, if_true, List.length_nil]
    rw [zero_pow (by omega), Nat.zero_add]
  | cons b l =>
    simp only [reduceCtorEq, decide_false, Bool.false_eq_true, if_false, List.length_cons,
      List.length_replicate, Nat.one_mul, List.tail_cons]

/-- The main branch's time, as arithmetic: with `P = (|x.tail| + 1) ^ c ≤ N + 1`, `N = |x| ^ c`,
and `|x.tail| ≤ |x|`, the four phases' exact times sum to at most
`(5c + 20 + 3c_L)(N + |x| + 1)`. -/
private theorem scp_time_arith (c cL t n P N : ℕ) (hP : P ≤ N + 1) (ht : t ≤ n) :
    n + 1 + t + 2 + (1 + 5 * c + 4) * P + P + 2 + (0 + 1 + P + 1) + (0 + 1 + P) + 2 +
      cL * (0 + 1 + P + 1) ≤ (5 * c + 20 + 3 * cL) * (N + n + 1) := by
  have h1 := Nat.mul_le_mul_left (1 + 5 * c + 4) hP
  have h2 := Nat.mul_le_mul_left cL hP
  nlinarith [h1, h2, Nat.zero_le (c * n), Nat.zero_le (cL * n), Nat.zero_le (cL * N),
    Nat.zero_le (c * N)]

/-- The conditional's time, as arithmetic: with `n ≤ N`, the bound
`c_M (c_D (n + 1) + max (c₁ (n + 1)) (K (N + n + 1)) + 1) + 1` is at most `A (N + 1)` for
`A = c_M (c_D + c₁ + 2K + 2) + 1`. -/
private theorem scp_space_arith (cM cD c₁ K n N : ℕ) (hn : n ≤ N) :
    cM * (cD * (n + 1) + max (c₁ * (n + 1)) (K * (N + n + 1)) + 1) + 1 ≤
      (cM * (cD + c₁ + 2 * K + 2) + 1) * (N + 1) := by
  have hmax : max (c₁ * (n + 1)) (K * (N + n + 1)) ≤ c₁ * (n + 1) + K * (N + n + 1) :=
    max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)
  have e1 := Nat.mul_le_mul_left cD hn
  have e2 := Nat.mul_le_mul_left c₁ hn
  have e3 := Nat.mul_le_mul_left K hn
  have hin : cD * (n + 1) + max (c₁ * (n + 1)) (K * (N + n + 1)) + 1 ≤
      (cD + c₁ + 2 * K + 2) * (N + 1) := by
    nlinarith [hmax, e1, e2, e3]
  have h4 := Nat.mul_le_mul_left cM hin
  nlinarith [h4, Nat.zero_le (cM * (cD + c₁ + 2 * K + 2))]

/-- **Polynomial bounds are space-constructible** [AB09, p. 79]: for `1 ≤ c`, the normal-form
bound `n ^ c + 1` is `Complexity.SpaceConstructible`. (Degree zero is excluded: `n ^ 0 + 1 = 2`
fails the bundled `logSpace n ≤ S n` at large `n`; consumers route degree
zero through monotonicity into degree one.)

**Proof sketch.** Dominance: `logSpace n ≤ n + 1 ≤ n ^ c + 1` (`Complexity.logSpace_le_succ`,
and `n ≤ n ^ c` for `1 ≤ c`). The witness machine computes
`x ↦ (|x| ^ c + 1).bits` as a timed conditional on `x = []`
(`Turing.FinTM.computesFunInTime_cond`, with the decider
`Turing.FinTM.computesFunInTime_decideEq []`). On the empty input the constant
writer emits `(1).bits`, which is the value since `0 ^ c + 1 = 1`. Otherwise four phases run by
buffered composition (`Turing.FinTM.bufferedCompTM_computesInTime`), each at its exact time:
1. a two-state transducer drops the first bit (`Complexity.transducerTM_computes`; from its
   second state it copies, `Complexity.transduce_of_copy`);
2. the unary generator `polyUnaryTM 1 c` writes `(|x| - 1 + 1) ^ c = |x| ^ c` ones;
3. `prependTM [true]` adds one more;
4. the length counter emits the binary length `|x| ^ c + 1`.
The four times sum to `O(|x| ^ c + |x| + 1)`, because the unary word has length at most
`|x| ^ c + 1`, so the conditional halts within `A (|x| ^ c + 1)` steps for a constant `A`
(`|x| ≤ |x| ^ c`). Space follows from time: a `k`-tape machine visits at most `k (t + 1)`
work-tape cells in `t` steps (`Turing.MultiTapeTM.spaceUsed_le_mul_succ`), which gives the
space constant `k A + 1`. -/
theorem spaceConstructible_poly (c : ℕ) (hc : 1 ≤ c) :
    SpaceConstructible fun n => n ^ c + 1 := by
  -- the published rows
  obtain ⟨L, cL, hL⟩ := FinTM.computesFunInTime_lengthBits
  obtain ⟨D, cD, hD'⟩ := FinTM.computesFunInTime_decideEq []
  obtain ⟨K₁, c₁, hK₁⟩ := FinTM.computesFunInTime_const (Nat.bits 1)
  let T := transducerTM scp_tailδ scp_tailO false
  let U := FinTM.polyUnaryTM 1 c
  let P := FinTM.prependTM [true]
  let N := FinTM.bufferedCompTM (FinTM.bufferedCompTM (FinTM.bufferedCompTM T U) P) L
  let f₂ : List Bool → List Bool := fun x =>
    Nat.bits (true :: List.replicate (1 * (x.tail.length + 1) ^ c) true).length
  -- the main branch, input by input: exact times of the four phases, composed
  have hN : N.ComputesFunInTime f₂ fun n => (5 * c + 20 + 3 * cL) * (n ^ c + n + 1) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro x
    have hT : T.ComputesInTime x x.tail (x.length + 1) := by
      have h := (FinTM.computesFunInTime_iff _ _ _).mp
        (transducerTM_computes scp_tailδ scp_tailO false) x
      rwa [scp_transduce_tail] at h
    have hU := (FinTM.computesFunInTime_iff _ _ _).mp (FinTM.polyUnaryTM_computes 1 c) x.tail
    have hP := (FinTM.computesFunInTime_iff _ _ _).mp (FinTM.prependTM_computes [true])
      (List.replicate (1 * (x.tail.length + 1) ^ c) true)
    have hL' := (FinTM.computesFunInTime_iff _ _ _).mp hL
      ([true] ++ List.replicate (1 * (x.tail.length + 1) ^ c) true)
    have h₁ := FinTM.bufferedCompTM_computesInTime T U hT hU
    have h₂ := FinTM.bufferedCompTM_computesInTime _ P h₁ hP
    have h₃ := FinTM.bufferedCompTM_computesInTime _ L h₂ hL'
    apply h₃.mono
    have hp := scp_tail_pow_le c x
    have htl : x.tail.length ≤ x.length := by simp
    simp only [List.length_replicate, Nat.one_mul, List.length_append, List.length_cons,
      List.length_nil]
    exact scp_time_arith c cL x.tail.length x.length _ _ hp htl
  obtain ⟨M, cM, hM⟩ := FinTM.computesFunInTime_cond hD' hK₁ hN
  -- the value
  have hval : (fun x : List Bool => if decide (x = []) then Nat.bits 1 else f₂ x) =
      fun x => Nat.bits (x.length ^ c + 1) := by
    funext x
    exact scp_value c hc x
  rw [hval] at hM
  -- time, then space from time
  refine (spaceConstructible_iff _).mpr ⟨fun n => ?_,
    M.k * (cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) + 1, by omega, M, ?_⟩
  · have h1 := logSpace_le_succ n
    have h2 : n ≤ n ^ c := Nat.le_self_pow (by omega) n
    omega
  · apply (FinTM.computesInSpace_iff _ _ _).mpr
    intro x
    refine ⟨_, (FinTM.computesFunInTime_iff _ _ _).mp hM x, ?_⟩
    apply (MultiTapeTM.spaceUsed_le_mul_succ _ _ _).trans
    have hB := scp_space_arith cM cD c₁ (5 * c + 20 + 3 * cL) x.length (x.length ^ c)
      (Nat.le_self_pow (by omega) x.length)
    calc M.k * (cM * (cD * (x.length + 1) + max (c₁ * (x.length + 1))
            ((5 * c + 20 + 3 * cL) * (x.length ^ c + x.length + 1)) + 1) + 1)
        ≤ M.k * ((cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) * (x.length ^ c + 1)) :=
          Nat.mul_le_mul_left _ hB
      _ ≤ (M.k * (cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) + 1) *
            (x.length ^ c + 1) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)

end Complexity
```
