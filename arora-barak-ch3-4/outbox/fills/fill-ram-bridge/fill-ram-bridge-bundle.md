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

## Tier 2 addendum (jobs A–E; Seyoon, 2026-11-18)

Tier 2 proves the 15 statements of PR #372 (gate 162, CLEAR) and then the two targets
`WordRAM.exists_simulation` and `WordRAM.exists_ndSimulation`. Five jobs run **in parallel**, all
on the same base. The design is `campaign/items/ram-tm/TIER2-DESIGN.md`; the statements' gate
pack and findings are in `campaign/gates/162-ram-tier2-statements/`. Read the auditor's notes
there: several give routes.

These rules extend or replace the ones above, for tier 2 only:
- **Proved modulo the other jobs.** You may cite the tier 2 statements owned by other jobs
  exactly as stated. Your brief lists which. Each target's dependency walk may then list those
  statements, and nothing else that is admitted. Never cite `Turing.exists_tableFindTM`,
  `Turing.exists_tableAppendTM` or any other declaration admitted in `Build/RecordTable`.
- **Files.** The jobs are larger than earlier fills (Seyoon: larger jobs, run in parallel).
  - Jobs A, B and C keep their helpers `private` in their owned files. If a file passes about
    1,500 lines, keep going and say so in the report: the maintainer splits it at landing.
  - Jobs D and E may add new files under `TCSlib/Complexity/RAMSimulation/Sim/`, as their briefs
    say. Their declarations are public in the namespace `WordRAM.Sim`: the simulation's internal
    namespace (decision D1), not an API for other consumers. Each new file has the standard
    header, a module docstring, docstrings with proof sketches, and is imported by the owned file
    that needs it. List every new file and public declaration in `REPORT.md`.
- **Reuse.** The construction layer is `TCSlib/Complexity/TuringMachine/Build/`. Compose with
  `Turing.Contract` (`Build/Contract/*`): `Contract.ofReaches` turns a `ReachesWithin` row into
  a contract, and `Contract.seq`, `inPhase`, `branch` and `embed` compose and place them. Cite the
  catalog's rows (`copyTM`, `compareTM`, `clearTM`, `scanTM`, `skipTM`, the seek family,
  `writeConstTM`, `rewindTM`, the counters) and their contracts, rather than writing a transition
  table, wherever one fits. A hand-built machine is fine where none fits; its docstring says
  what was missing.
- **Checkpoints** are welcome: push `<fill-name>-checkpoint-N.zip` at each proved target.
- **Missing readers (Seyoon, 2026-11-18).** Rule 2's E-READER stop is relaxed for pure
  restatements. Suppose you need to read another file's definition and its file publishes no
  equation for it. Then add the reader yourself, **beside the definition in its home file**:
  - its statement restates the definition exactly (an equation `D … = body`, or an equivalence
    `P … ↔ body` for a `Prop`);
  - its proof is `rfl` or `Iff.rfl`;
  - its docstring says what it reads.

  Then continue. List every such reader in `REPORT.md`, with its file. The maintainer gates it
  with your PR and reconciles duplicates between parallel jobs. Anything more than a restatement
  is still a stop: a lemma that needs a proof, a `private` lemma made public, a changed statement.
  Before adding a reader, check that it is not already published, including by PR #375 (below).
- **Readers published since dispatch** (PR #375):
  - `Build/RecordTable`: `tableFields_eq`, `tableWF_iff`, `tableAt_iff`;
  - `Build/Catalog`: `catalogTrace_eq`, `mealyRun_nil`, `mealyRun_cons`, `scanResult_eq`, and
    `mealyRun_append`, `mealyRun_induction`, `mealyRun_length`, `mealyRun_next`, now public;
  - `Programs/WordRAM/Steps`: `inRange_iff`.

## ===== campaign/items/ram-tm/briefs/fill-ram-bridge.md =====

# RAM fill (Codex), bridge job F: polynomial-time functions from programs (4 admissions, 2 files)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind, the reader rule among
them. **Fill name:** `fill-ram-bridge`. **Base:** the commit given in the dispatch prompt: PR #379's
head, branch `ram/bridge-statements`.

## What this is

The first wave of the bridge from word-RAM programs to the library's polynomial-time functions,
for the cryptography campaign. Programs written for the word RAM become `PolyTimeComputable`
functions through stage 2's simulation. PR #379 states four results. **This job proves them:**

1. `WordRAM.wordSizeComputable_of_timeConstructible` (`RAMSimulation/WordSize`): a
   time-constructible `T` is a word size computable within `a·(T n + 1)` steps and cells.
2. `WordRAM.wordSizeComputable_poly` (`RAMSimulation/WordSize`): `n ↦ C·(n+1)^(c+1)`, for `C > 0`,
   within `a·(n+1)^(c+1)`.
3. `WordRAM.polyTimeComputable_of_computes` (`RAMSimulation/Classes`): a program that emits `g x`
   on every input within `C·(|x|+1)^d` steps, with `TW n + W n ≤ C·(n+1)^d`, makes `g`
   `Complexity.PolyTimeComputable`.
4. `WordRAM.polyTimeComputable_progOut` (`RAMSimulation/Classes`): the same for `progOut P W`, from
   halting alone.

Each has a proof sketch.

## Route

- **Target 1:**
  - `Complexity.timeConstructible_iff` gives `c > 0` and a machine writing `(T |x|).bits` within
    `c·(T |x| + 1)` steps;
  - space: `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`TuringMachine/Finite`), at most
    `k·(t + 1)` cells;
  - take `a = (k + 1)·(c + 1)` or similar; `WordSizeComputable` is in the same file and may be
    unfolded.
- **Target 2:** target 1 at `Complexity.timeConstructible_poly C c hC`
  (`ClassP/TimeConstructiblePoly`), then `WordSizeComputable.mono` with
  `C·(n+1)^(c+1) + 1 ≤ (C + 1)·(n+1)^(c+1)`.
- **Target 3:** follow `mem_P_of_decides`'s proof in the same file, in function mode.
  - **The machine:** `exists_simulation P true hW`, read through `outputOf_true` and
    `simTime_eq`.
  - **The bounds:** `HaltsWithin.touches_le` and `HaltsWithin.mono` give `C·(n+1)^d` steps and
    `3·C·(n+1)^d` cells.
  - **The arithmetic:** the existing private `polynomial_time_bound` bounds the deadline by
    `(A + 1)·a·(n+1)^(3d+1)`.
  - **Packaging:** `Turing.FinTM.ComputesInTime.mono` enlarges each run's deadline, and
    `Complexity.polyTimeComputable_iff` and `Turing.FinTM.computesFunInTime_iff` package the
    machine.
- **Target 4:** target 3 with `g := progOut P W`. `WordRAM.progOut_eq` (`Programs/WordRAM/Output`)
  turns each halting run's output into `progOut P W x`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/WordSize.lean`: targets 1 and 2.
- `TCSlib/Complexity/RAMSimulation/Classes.lean`: targets 3 and 4.

Statements byte-identical. Private helpers in each file; factor any arithmetic shared by targets 3
and 4, or with `mem_P_of_decides`, rather than copying it.

## Admitted dependencies allowed

`WordRAM.exists_simulation`, for targets 3 and 4 only, and whatever it reaches. Targets 1 and 2
reach no admission.

## Downstream check

The `RAMSimulation` facade.

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
import TCSlib.Complexity.ClassP.TimeConstructiblePoly

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
* `WordRAM.wordSizeComputable_of_timeConstructible` and `WordRAM.wordSizeComputable_poly` supply
  time-constructible and polynomial word sizes, in time linear in their value.

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

/-! ## Polynomial word sizes -/

/-- **A time-constructible function is a word size computable in time and space linear in its
value.** [AB09, §1.3]

**Proof sketch.** `Complexity.timeConstructible_iff` gives a machine writing `Nat.bits (T |x|)`
within `c·(T |x| + 1)` steps. Its visited work cells are at most its number of tapes times the
time plus one (`Turing.MultiTapeTM.spaceUsed_le_mul_succ`), which is linear in `T |x| + 1`. -/
theorem wordSizeComputable_of_timeConstructible {T : ℕ → ℕ}
    (hT : Complexity.TimeConstructible T) :
    ∃ a : ℕ, WordSizeComputable T (fun n => a * (T n + 1)) (fun n => a * (T n + 1)) := by
  sorry

/-- **Polynomial word sizes**: `n ↦ C·(n+1)^(c+1)`, for `C > 0`, is a word size computable within
time and space `a·(n+1)^(c+1)`. Words this wide hold, for instance, residues modulo a prime of
polynomially many bits. [AB09, §1.3]

**Proof sketch.** `wordSizeComputable_of_timeConstructible` applied to
`Complexity.timeConstructible_poly C c hC`, then `WordSizeComputable.mono` with
`C·(n+1)^(c+1) + 1 ≤ (C + 1)·(n+1)^(c+1)`. -/
theorem wordSizeComputable_poly (C c : ℕ) (hC : 0 < C) :
    ∃ a : ℕ, WordSizeComputable (fun n => C * (n + 1) ^ (c + 1))
      (fun n => a * (n + 1) ^ (c + 1)) (fun n => a * (n + 1) ^ (c + 1)) := by
  sorry

end WordRAM
```

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
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Programs.WordRAM.Output

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

## Main results

* `WordRAM.mem_DTIME_of_decides`, `WordRAM.mem_P_of_decides`, `WordRAM.mem_P_of_decides_logWord`.
* `WordRAM.polyTimeComputable_of_computes`, `WordRAM.polyTimeComputable_progOut`: polynomial-time
  functions from programs (function mode).
* `WordRAM.mem_SPACE_of_decides`, `WordRAM.mem_LOGSPACE_of_decides`,
  `WordRAM.computesInSpace_of_computes`, `WordRAM.mem_SPACE_mul_of_decides`.
* `WordRAM.mem_NSPACE_of_accepts`, `WordRAM.mem_NL_of_accepts`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definitions 1.12, 1.13; Definitions 4.1, 4.5; Definition
  4.16 and Exercise 4.8; Theorem 4.14; §4.3.1, Definition 4.19.)
-/

namespace WordRAM

/-! ## Private bound arithmetic -/

/-- Absorb the start-up cost and the simulation constant into one multiplicative constant. -/
private lemma simulation_constant_bound (A u v : ℕ) :
    u + A * v ≤ (A + 1) * (u + v) := by
  nlinarith

/-- A bound for the space expression without its simulation constant bounds `simSpace`. -/
private lemma simulation_space_bound (A : ℕ) (SW W F s : ℕ → ℕ) (a n : ℕ)
    (hs : SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    simSpace A SW n (W n) (F n) ≤ ((A + 1) * a) * s n := by
  rw [simSpace_eq]
  calc
    _ ≤ (A + 1) * (SW n + (F n * (W n + 1) + W n + Complexity.logSpace n + 1)) :=
      simulation_constant_bound _ _ _
    _ ≤ (A + 1) * (a * s n) :=
      Nat.mul_le_mul_left _ (by simpa only [Nat.add_assoc] using hs)
    _ = _ := by ring

/-- Constantly many logarithmic words and the start-up space occupy logarithmic space. -/
private lemma logarithmic_space_bound (a c F n : ℕ) :
    a * Complexity.logSpace n + F * (c * Complexity.logSpace n + 1) +
      c * Complexity.logSpace n + Complexity.logSpace n + 1 ≤
        (a + F * (c + 1) + c + 2) * Complexity.logSpace n := by
  have hlog : 1 ≤ Complexity.logSpace n := by rw [Complexity.logSpace_eq]; omega
  nlinarith [Nat.mul_le_mul_left F hlog]

/-- The time overhead is cubic in a common bound for steps and word size, times the input
length allowance.

**Proof sketch.** Bound `w + 1` by `(C + 1) b` and the per-step cost by
`(4 C² + 3 C + 1) b² z`. Multiply by the step bound, and use `b ≤ b³ z` for the
start-up cost. The power comparisons are `Nat.le_self_pow`; all factors are natural numbers. -/
private lemma polynomial_time_bound (C b z tw w : ℕ) (hb : 1 ≤ b) (hz : 1 ≤ z)
    (h : tw + w ≤ C * b) :
    tw + (C * b + 1) * (3 * C * b * (w + 1) + w ^ 2 + z) ≤
      (C + (C + 1) * (4 * C ^ 2 + 3 * C + 1)) * (b ^ 3 * z) := by
  have htw : tw ≤ C * b := by omega
  have hw : w ≤ C * b := by omega
  have hwone : w + 1 ≤ (C + 1) * b := by nlinarith
  have htone : C * b + 1 ≤ (C + 1) * b := by nlinarith
  have hb2 : b ^ 2 ≤ b ^ 2 * z := Nat.le_mul_of_pos_right _ (by omega)
  have hz2 : z ≤ b ^ 2 * z := Nat.le_mul_of_pos_left _ (by nlinarith)
  have hcost : 3 * C * b * (w + 1) + w ^ 2 + z ≤
      (4 * C ^ 2 + 3 * C + 1) * b ^ 2 * z := by
    calc
      _ ≤ (4 * C ^ 2 + 3 * C) * b ^ 2 + z := by
        nlinarith [Nat.mul_le_mul_left (3 * C * b) hwone, Nat.pow_le_pow_left hw 2]
      _ ≤ (4 * C ^ 2 + 3 * C) * (b ^ 2 * z) + b ^ 2 * z :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb2) hz2
      _ = _ := by ring
  have hb3 : b ≤ b ^ 3 * z :=
    (Nat.le_self_pow (by decide) b).trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    _ ≤ C * (b ^ 3 * z) + ((C + 1) * b) *
        ((4 * C ^ 2 + 3 * C + 1) * b ^ 2 * z) :=
      Nat.add_le_add (htw.trans (Nat.mul_le_mul_left C hb3))
        (Nat.mul_le_mul htone hcost)
    _ = _ := by ring

/-! ## The time grade -/

/-- **Deciding in time.** If the program `P` decides `L` (verdict `[x ∈ L]`) with a computable
word size `W`, within `T |x|` steps and `F |x|` cells, then `L ∈ DTIME T'` for every `T'` that
dominates the stage-2 time bound up to a constant `a`. [AB09, Definition 1.12]

**Proof sketch.** `exists_simulation` in verdict mode gives a machine and a constant `A`.
Read its output with `outputOf_false` and its deadline with `simTime_eq`.
`simulation_constant_bound` and the assumed domination bound that deadline by
`(A + 1)·a·T' n`. `Turing.FinTM.ComputesInTime.mono` enlarges the deadline, and
`Complexity.mem_DTIME_iff`, `Turing.FinTM.decidesInTime_iff` and
`Turing.FinTM.computesFunInTime_iff` package the resulting decider. -/
theorem mem_DTIME_of_decides (P : XProgram) (L : Language Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ o : List Bool,
      HaltsWithin P x [] (W x.length) (T x.length)
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (F x.length))
    (T' : ℕ → ℕ) (a : ℕ)
    (hT : ∀ n, TW n + (T n + 1) * (F n * (W n + 1) + W n ^ 2 + n + 1) ≤ a * T' n) :
    L ∈ Complexity.DTIME T' := by
  obtain ⟨M, A, hM⟩ := exists_simulation P false hW
  apply Complexity.mem_DTIME_iff.mpr
  refine ⟨(A + 1) * a, M, (Turing.FinTM.decidesInTime_iff _ _ _).mpr ?_⟩
  apply (Turing.FinTM.computesFunInTime_iff _ _ _).mpr
  intro x
  obtain ⟨o, ho⟩ := hdec x
  have hm := (hM x (T x.length) (F x.length) _ o ho).1
  rw [outputOf_false] at hm
  apply hm.mono
  rw [simTime_eq, mul_assoc]
  calc
    _ ≤ (A + 1) * (TW x.length + (T x.length + 1) *
        (F x.length * (W x.length + 1) + W x.length ^ 2 + x.length + 1)) :=
      simulation_constant_bound _ _ _
    _ ≤ (A + 1) * (a * T' x.length) := Nat.mul_le_mul_left _ (hT x.length)
    _ = _ := by ring

/-- **The P grade.** If `P` decides `L` within polynomially many steps, with a word size of
polynomial value computable in polynomial time, then `L ∈ P`. No bound on the cells is needed:
a run of `t` steps touches at most `3 t` cells (`HaltsWithin.touches_le`). [AB09, Definition
1.13]

**Proof sketch.** `HaltsWithin.touches_le` and `HaltsWithin.mono` give uniform bounds
`C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells. `polynomial_time_bound`, with
`b = (n + 1)^d` and `z = n + 1`, bounds the time expression without its simulation
constant by `a·(n + 1)^(3d + 1)`, where
`a = C + (C + 1)·(4C² + 3C + 1)`. Apply `mem_DTIME_of_decides`, then read its witness
through `Complexity.mem_DTIME_iff` and package it with `Complexity.mem_P_iff`. -/
theorem mem_P_of_decides (P : XProgram) (L : Language Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  let a := C + (C + 1) * (4 * C ^ 2 + 3 * C + 1)
  have hdt : L ∈ Complexity.DTIME (fun n => (n + 1) ^ (3 * d + 1)) := by
    refine mem_DTIME_of_decides P L (T := fun n => C * (n + 1) ^ d)
      (F := fun n => 3 * C * (n + 1) ^ d) hW ?_ _ a ?_
    · intro x
      obtain ⟨t, f, o, ht, ho⟩ := hdec x
      refine ⟨o, ho.touches_le.mono ht ?_⟩
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 ht
    · intro n
      have hb : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d _ (by omega)
      have hp : ((n + 1) ^ d) ^ 3 * (n + 1) = (n + 1) ^ (3 * d + 1) := by
        rw [← pow_mul, Nat.mul_comm d 3, pow_succ]
      have h := polynomial_time_bound C ((n + 1) ^ d) (n + 1) (TW n) (W n)
        hb (by omega) (hWpoly n)
      rw [hp] at h
      simpa only [Nat.add_assoc] using h
  obtain ⟨A, M, hM⟩ := Complexity.mem_DTIME_iff.mp hdt
  exact Complexity.mem_P_iff.mpr ⟨A, 3 * d + 1, M, hM⟩

/-- **The P grade with logarithmic words**, the form that the curriculum and `NL ⊆ P` use: word
size `c · (⌊log₂ n⌋ + 1)` and polynomially many steps. [AB09, Definition 1.13]

**Proof sketch.** `wordSizeComputable_logSpace c` gives the word-size computation with
linear-time coefficient `a`. `Complexity.logSpace_le_succ` bounds its time plus its
value by `(a + c)·(n + 1)`. Enlarge both this bound and the program's step bound to
`(a + c + C)·(n + 1)^(d + 1)` using `Nat.le_self_pow` and `Nat.pow_le_pow_right`, then
apply `mem_P_of_decides`. -/
theorem mem_P_of_decides_logWord (P : XProgram) (L : Language Bool) (c C d : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  apply mem_P_of_decides P L hW (a + c + C) (d + 1)
  · intro n
    calc
      _ ≤ (a + c) * (n + 1) := by
        nlinarith [Nat.mul_le_mul_left c (Complexity.logSpace_le_succ n)]
      _ ≤ (a + c + C) * (n + 1) ^ (d + 1) :=
        Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) _)
  · intro x
    obtain ⟨t, f, o, ht, ho⟩ := hdec x
    refine ⟨t, f, o, ht.trans ?_, ho⟩
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Polynomial-time functions from programs.** If `P`, with a word size of polynomial value
computable in polynomial time, emits `g x` on every input `x` within polynomially many steps, then
`g` is computable in polynomial time. [AB09, Definition 1.13, Exercise 1.9]

**Proof sketch.** As `mem_P_of_decides`, in function mode. `exists_simulation P true hW` gives a
machine and a constant `A`; `outputOf_true` reads its output as `g x`. `HaltsWithin.touches_le`
and `HaltsWithin.mono` give the bounds `C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells, and
`polynomial_time_bound` bounds the simulation's deadline by `(A + 1)·a·(n + 1)^(3d + 1)`.
`Turing.FinTM.ComputesInTime.mono` enlarges each run's deadline to it, and
`Complexity.polyTimeComputable_iff` packages the machine. -/
theorem polyTimeComputable_of_computes (P : XProgram) (g : List Bool → List Bool)
    {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hcomp : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t v (g x) f) :
    Complexity.PolyTimeComputable g := by
  sorry

/-- **The output of a program halting in polynomial time is computable in polynomial time.** If
`P` halts on every input within polynomially many steps, with a word size of polynomial value
computable in polynomial time, then its output function `progOut P W` is computable in polynomial
time. A consumer then proves halting on every input, and correctness, `progOut P W x = g x`, only
where it needs it. [AB09, Definition 1.13, Exercise 1.9]

**Proof sketch.** `polyTimeComputable_of_computes` with `g := progOut P W`, where `progOut_eq`
identifies each halting run's output with `progOut P W x`. -/
theorem polyTimeComputable_progOut (P : XProgram) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ) (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hhalt : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool) (o : List Bool),
      t ≤ C * (x.length + 1) ^ d ∧ HaltsWithin P x [] (W x.length) t v o f) :
    Complexity.PolyTimeComputable (progOut P W) := by
  sorry

/-! ## The space grades: L, log-space transducers, Savitch's shape -/

/-- **Deciding in space.** If `P` decides `L` with a computable word size `W`, touching at most
`F |x|` cells, in any number of steps, then `L ∈ SPACE s` for every `s` that dominates
`SW + F·(W + 1) + W + logSpace + 1` up to a constant `a`. [AB09, Definition 4.1]

**Proof sketch.** `exists_simulation` in verdict mode gives a halting computation on
each input. `outputOf_false` identifies its one-bit answer, and
`simulation_space_bound` bounds its visited work cells by `(A + 1)·a·s n`.
`Turing.FinTM.computesInSpace_iff`, `Turing.FinTM.decidesInSpace_iff` and
`Complexity.mem_SPACE_iff` package the same times and space bounds. -/
theorem mem_SPACE_of_decides (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (W x.length) t (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o
        (F x.length))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.SPACE s := by
  obtain ⟨M, A, hM⟩ := exists_simulation P false hW
  apply Complexity.mem_SPACE_iff.mpr
  refine ⟨(A + 1) * a, M, (Turing.FinTM.decidesInSpace_iff _ _ _).mpr ?_⟩
  apply (Turing.FinTM.computesInSpace_iff _ _ _).mpr
  intro x
  obtain ⟨t, o, ho⟩ := hdec x
  obtain ⟨hm, hspace⟩ := hM x t (F x.length) _ o ho
  rw [outputOf_false] at hm
  exact ⟨_, hm, hspace.trans (simulation_space_bound A SW W F s a _ (hs _))⟩

/-- **The logspace grade** (design §15a, §16b item 4): a program that decides `L` touching `O(1)`
cells, with word size `c · (⌊log₂ n⌋ + 1)`, puts `L` in `L`. The input is read in place (`rdIn`),
so it occupies no cell. [AB09, Definition 4.5]

**Proof sketch.** Obtain the word-size witness from `wordSizeComputable_logSpace c`.
`logarithmic_space_bound` bounds the space expression by
`(a + F₀·(c + 1) + c + 2)·logSpace n`, using `Complexity.logSpace_eq` for positivity.
Apply `mem_SPACE_of_decides` and identify the class with `Complexity.LOGSPACE_eq`. -/
theorem mem_LOGSPACE_of_decides (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o F₀) :
    L ∈ Complexity.LOGSPACE := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  rw [Complexity.LOGSPACE_eq]
  exact mem_SPACE_of_decides P L hW hdec Complexity.logSpace
    (a + F₀ * (c + 1) + c + 2) (logarithmic_space_bound a c F₀)

/-- **Log-space transducers**: a program that, on every `x`, emits `g x` touching `O(1)` cells,
with word size `c · (⌊log₂ n⌋ + 1)`, gives a machine that computes `g` in logarithmic space; the
output tape is append-only and not counted. [AB09, §4.3: Definition 4.16, with the write-once
output tape of Exercise 4.8]

Deviation: `Turing.FinTM.ComputesInSpace` asks for no polynomial bound on `|g x|`, which
[AB09, Definition 4.16] includes in "implicitly logspace computable"; a halting program bounds it
by its running time.

**Proof sketch.** Use `wordSizeComputable_logSpace c` and `exists_simulation` in
function mode. `outputOf_true` identifies the emitted word with `g x`.
`logarithmic_space_bound` and `simulation_space_bound` bound the visited work cells by
`(A + 1)·(a + F₀·(c + 1) + c + 2)·logSpace n`; retain the simulation's halting time and
apply `Turing.FinTM.computesInSpace_iff`. -/
theorem computesInSpace_of_computes (P : XProgram) (g : List Bool → List Bool) (c F₀ : ℕ)
    (hcomp : ∀ x : List Bool, ∃ (t : ℕ) (v : Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t v (g x) F₀) :
    ∃ (M : Turing.FinTM Bool) (a : ℕ),
      M.ComputesInSpace g fun n => a * Complexity.logSpace n := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  obtain ⟨M, A, hM⟩ := exists_simulation P true hW
  refine ⟨M, (A + 1) * (a + F₀ * (c + 1) + c + 2),
    (Turing.FinTM.computesInSpace_iff _ _ _).mpr ?_⟩
  intro x
  obtain ⟨t, v, hv⟩ := hcomp x
  obtain ⟨hm, hspace⟩ := hM x t F₀ v (g x) hv
  rw [outputOf_true] at hm
  exact ⟨_, hm, hspace.trans (simulation_space_bound A (fun n => a * Complexity.logSpace n)
    (fun n => c * Complexity.logSpace n) (fun _ => F₀)
    Complexity.logSpace _ _ (logarithmic_space_bound a c F₀ _))⟩

/-- **Savitch's shape** (design §16b item 1): with a space-constructible `S`, word size `c · S(n)`
and at most `c · S(n)` cells touched (depth `O(S)` of frames of `O(1)` words, a configuration of
the simulated machine in one word), `L ∈ SPACE (S²)`. [AB09, Theorem 4.14, its space count]

**Proof sketch.** Obtain the word-size witness from
`wordSizeComputable_of_spaceConstructible hS c`, and apply `mem_SPACE_of_decides`.
`Complexity.spaceConstructible_iff` gives `logSpace ≤ S`; `Complexity.logSpace_eq`
therefore gives `1 ≤ S`, hence `S ≤ S²`. Bound the remaining linear terms by
`(a + 2c + 2)·S²` and retain the quadratic table term `c²·S²`, giving total coefficient
`a + c² + 2c + 2`. -/
theorem mem_SPACE_mul_of_decides (P : XProgram) (L : Language Bool) {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * S x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (c * S x.length)) :
    L ∈ Complexity.SPACE fun n => S n * S n := by
  obtain ⟨a, TW, hW⟩ := wordSizeComputable_of_spaceConstructible hS c
  apply mem_SPACE_of_decides P L (F := fun n => c * S n) hW hdec
    (fun n => S n * S n) (a + c ^ 2 + 2 * c + 2)
  intro n
  have hlog := ((Complexity.spaceConstructible_iff S).mp hS).1 n
  have hone : 1 ≤ S n := by
    have h := hlog
    rw [Complexity.logSpace_eq] at h
    omega
  have hsquare : S n ≤ S n * S n := by nlinarith
  have hlinear : a * S n + c * S n + c * S n + S n + 1 ≤
      (a + 2 * c + 2) * (S n * S n) := by
    nlinarith [Nat.mul_le_mul_left (a + 2 * c + 2) hsquare]
  nlinarith

/-! ## The nondeterministic space grades -/

/-- **Accepting in nondeterministic space.** If, on every `x`, every coin stream lets `P` halt
within one time `t` (depending on `x`) touching at most `F |x|` cells with a computable word
size `W`, and `x ∈ L` exactly when some stream makes `P` accept, then `L ∈ NSPACE s` for every
`s` that dominates the stage-2 space bound up to a constant `a`. [AB09, Definition 4.1,
nondeterministic clause]

**Proof sketch.** `exists_ndSimulation` supplies a common deadline on each input,
halting of every branch, its space bound, and the acceptance equivalence.
`simulation_space_bound` bounds every branch's space by `(A + 1)·a·s n`.
Compose the supplied acceptance equivalence with the hypothesis, and package the
deadline through `Turing.FinNDTM.decidesInSpace_iff` and `Complexity.mem_NSPACE_iff`. -/
theorem mem_NSPACE_of_accepts (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (W x.length) t v o (F x.length)) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o (F x.length)))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.NSPACE s := by
  obtain ⟨N, A, hN⟩ := exists_ndSimulation P hW
  apply Complexity.mem_NSPACE_iff.mpr
  refine ⟨(A + 1) * a, N, (Turing.FinNDTM.decidesInSpace_iff _ _ _).mpr ?_⟩
  intro x
  obtain ⟨t, hhalt, hacc⟩ := hrun x
  obtain ⟨hn, hspace, haccept⟩ := hN x t (F x.length) hhalt
  refine ⟨_, hn, fun w hw => ?_, hacc.trans haccept.symm⟩
  exact (hspace w hw).trans (simulation_space_bound A SW W F s a _ (hs _))

/-- **The NL grade** (design §16b item 4, C2): a program with read-once coins that, on every `x`,
halts under every coin stream within one time touching `O(1)` cells, with word size
`c · (⌊log₂ n⌋ + 1)`, and accepts under some stream exactly when `x ∈ L`, puts `L` in `NL`.
[AB09, Definition 4.5 (NL); §4.3.1, Definition 4.19: read-once certificates]

**Proof sketch.** Obtain the word-size witness from `wordSizeComputable_logSpace c`.
`logarithmic_space_bound` supplies the same logarithmic space estimate as in
`mem_LOGSPACE_of_decides`. Apply `mem_NSPACE_of_accepts` with the unchanged uniform
halting and acceptance hypotheses, and identify the class with `Complexity.NL_eq`. -/
theorem mem_NL_of_accepts (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t v o F₀) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t true o F₀)) :
    L ∈ Complexity.NL := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  rw [Complexity.NL_eq]
  exact mem_NSPACE_of_accepts P L hW hrun Complexity.logSpace
    (a + F₀ * (c + 1) + c + 2) (logarithmic_space_bound a c F₀)

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
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.RAMSimulation.Sim.Phases

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

## ===== TCSlib/Programs/WordRAM/Output.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The output of a word-RAM program

`WordRAM.progOut P W x` is the bit string that the extended word-RAM program `P` emits on the
input `x`, with word size `W |x|` and coins reading `0`, if it halts, and `[]` if it does not. A
program's output is unique (`WordRAM.HaltsWithin.unique`), so this is well defined. It names the
function a program computes even where the program's correctness is only proved on some inputs:
a consumer proves halting within a bound on every input, and correctness only where it matters.

## Main definitions

* `WordRAM.progOut`: the output of a program on an input, `[]` if it does not halt.

## Main results

* `WordRAM.progOut_eq`: a halting run's output is `progOut`.
* `WordRAM.progOut_of_not_halts`: without a halting run, `progOut` is `[]`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM

/-- **The output of a program**: what `P` emits on `x`, with word size `W |x|` and the empty coin
stream, if some run halts; `[]` otherwise. -/
noncomputable def progOut (P : XProgram) (W : ℕ → ℕ) (x : List Bool) : List Bool :=
  haveI := Classical.propDecidable
    (∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f)
  if h : ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f
    then Classical.choose h else []

/-- **A halting run's output is `progOut`.**

**Proof sketch.** A halting run exists, so `progOut` is the output of some chosen halting run;
`HaltsWithin.unique` makes the two outputs equal. -/
theorem progOut_eq {P : XProgram} {W : ℕ → ℕ} {x : List Bool} {t f : ℕ} {v : Bool}
    {o : List Bool} (h : HaltsWithin P x [] (W x.length) t v o f) : progOut P W x = o := by
  have hex : ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ),
      HaltsWithin P x [] (W x.length) t v o f := ⟨o, t, v, f, h⟩
  unfold progOut
  rw [dif_pos hex]
  obtain ⟨t', v', f', h'⟩ := Classical.choose_spec hex
  exact (h'.unique h).2

/-- Without a halting run, `progOut` is `[]`. -/
theorem progOut_of_not_halts {P : XProgram} {W : ℕ → ℕ} {x : List Bool}
    (h : ¬ ∃ (o : List Bool) (t : ℕ) (v : Bool) (f : ℕ), HaltsWithin P x [] (W x.length) t v o f) :
    progOut P W x = [] := by
  unfold progOut
  rw [dif_neg h]

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
* Readers (equations of the definitions, for other files): `WordRAM.inBitWord_def`,
  `WordRAM.coinWord_def`, `WordRAM.xstep_def`, `WordRAM.XSteps.zero_iff`, `.succ_iff`,
  `WordRAM.baseTouches_def`, `WordRAM.XInstr.touches_def`, `WordRAM.XStepsIn.zero_iff`,
  `.succ_iff`, `WordRAM.initMem_def`, `WordRAM.XCfg.init_def`, `WordRAM.haltsWithin_iff`.

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

/-! ## Readers

Equations for the definitions above, so that other files read them without unfolding them. Each
restates its definition and is proved by `rfl` or `Iff.rfl`. -/

section Readers

variable {W : ℕ}

/-- The word of an input bit, as an equation: `1` if `0 ≤ p` and the bit of `x` at `p` is
`true`, and `0` otherwise. -/
theorem inBitWord_def (x : List Bool) (p : ℤ) :
    inBitWord W x p = if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0 := rfl

/-- The word of a coin, as an equation: `1` for `true`, `0` for `false`. -/
theorem coinWord_def (b : Bool) : coinWord W b = if b then 1 else 0 := rfl

/-- **One step of the extended RAM, as an equation**: the match on the instruction at `c.pc`
(`WordRAM.reject` past the end). -/
theorem xstep_def (P : XProgram) (x ρ : List Bool) (c : XCfg W) :
    xstep P x ρ c =
      match P.getD c.pc (.base .reject) with
      | .base .accept => .inr true
      | .base .reject => .inr false
      | .base (.bltz i l) =>
        .inl { c with pc := if (c.mem i).toInt < 0 then l else c.pc + 1 }
      | .base ins => .inl { c with pc := c.pc + 1, mem := effect ins c.mem }
      | .rdIn i j =>
        .inl { c with pc := c.pc + 1,
                      mem := Function.update c.mem i (inBitWord W x (c.mem j).toInt) }
      | .emit i => .inl { c with pc := c.pc + 1, out := c.out ++ [decide (c.mem i ≠ 0)] }
      | .coin i =>
        .inl { c with pc := c.pc + 1,
                      mem := Function.update c.mem i (coinWord W (ρ.getD c.rd false)),
                      rd := c.rd + 1 }
      | .half i j =>
        .inl { c with pc := c.pc + 1, mem := Function.update c.mem i ((c.mem j).sshiftRight 1) }
    := rfl

/-- A run of no steps stays where it is. -/
theorem XSteps.zero_iff {P : XProgram} {x ρ : List Bool} {c c' : XCfg W} :
    XSteps P x ρ 0 c c' ↔ c = c' := Iff.rfl

/-- A run of `n + 1` steps is a first step to some `c₁`, giving no verdict, followed by a run of
`n` steps from `c₁`. -/
theorem XSteps.succ_iff {P : XProgram} {x ρ : List Bool} {n : ℕ} {c c' : XCfg W} :
    XSteps P x ρ (n + 1) c c' ↔ ∃ c₁, xstep P x ρ c = .inl c₁ ∧ XSteps P x ρ n c₁ c' := Iff.rfl

/-- The cells a vendored instruction touches, as an equation. -/
theorem baseTouches_def (ins : Instr) (m : ℤ → BitVec W) :
    baseTouches ins m =
      match ins with
      | .one i => {i}
      | .add i j k => {i, j, k}
      | .sub i j k => {i, j, k}
      | .mul i j k => {i, j, k}
      | .load i j => {i, j, (m j).toInt}
      | .store i j => {i, j, (m i).toInt}
      | .bltz i _ => {i}
      | .accept => ∅
      | .reject => ∅ := rfl

/-- The cells an instruction of the extended RAM touches, as an equation. -/
theorem XInstr.touches_def (ins : XInstr) (m : ℤ → BitVec W) :
    ins.touches m =
      match ins with
      | .base ins => baseTouches ins m
      | .rdIn i j => {i, j}
      | .emit i => {i}
      | .coin i => {i}
      | .half i j => {i, j} := by
  cases ins <;> rfl

/-- A run within `K` of no steps stays where it is. -/
theorem XStepsIn.zero_iff {P : XProgram} {x ρ : List Bool} {K : Set ℤ} {c c' : XCfg W} :
    XStepsIn P x ρ K 0 c c' ↔ c = c' := Iff.rfl

/-- A run within `K` of `n + 1` steps is a first step to some `c₁`, giving no verdict and
touching only cells of `K`, followed by a run within `K` of `n` steps from `c₁`. -/
theorem XStepsIn.succ_iff {P : XProgram} {x ρ : List Bool} {K : Set ℤ} {n : ℕ}
    {c c' : XCfg W} :
    XStepsIn P x ρ K (n + 1) c c' ↔ ∃ c₁, xstep P x ρ c = .inl c₁ ∧
      ↑((P.getD c.pc (.base .reject)).touches c.mem) ⊆ K ∧ XStepsIn P x ρ K n c₁ c' := Iff.rfl

/-- The memory in which a run starts, as an equation: `n` (as a word) at the cell `-1` and `0`
everywhere else. -/
theorem initMem_def (n : ℕ) : initMem W n = Function.update (fun _ => 0) (-1) (wd W n) := rfl

/-- The start configuration, as an equation. -/
theorem XCfg.init_def (n : ℕ) :
    XCfg.init W n = { pc := 0, mem := initMem W n, out := [], rd := 0 } := rfl

/-- Halting within steps and cells, as an equivalence with its definition. -/
theorem haltsWithin_iff (P : XProgram) (x ρ : List Bool) (t : ℕ) (v : Bool) (o : List Bool)
    (f : ℕ) :
    HaltsWithin P x ρ W t v o f ↔
      ∃ (n : ℕ) (c : XCfg W) (K : Finset ℤ), n < t ∧ K.card ≤ f ∧
        XStepsIn P x ρ (↑K) n (XCfg.init W x.length) c ∧ xstep P x ρ c = .inr v ∧ c.out = o :=
  Iff.rfl

end Readers

end WordRAM
```

## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (least-significant-bit first, with no redundant
  most-significant zeros; `Nat.bits 0 = []`), where [AB09] writes `⌞T(|x|)⌟` without
  fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.
* `Turing.FinTM.lengthBitsTM` — the binary length counter `x ↦ Nat.bits |x|` (MIG-1),
  declared under its `Turing.FinTM` name.

## Main results

* `Complexity.timeConstructible_iff` — the definition as an equivalence.
* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.
* `Turing.FinTM.lengthBitsTM_computes`, `Turing.FinTM.lengthBitsTM_spaceUsed` — the
  counter's time `5 · (n + 1)` and space `5 · (Nat.size |x| + 1)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- **Time constructibility, unfolded**: `T` is time constructible exactly when `n ≤ T n` for
every `n` and, for some constant `c > 0`, some machine computes `(T |x|).bits` on every input `x`
within `c · (T |x| + 1)` steps. -/
theorem timeConstructible_iff (T : ℕ → ℕ) :
    TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) :=
  Iff.rfl

/-- Increment a little-endian binary word, extending it on overflow. -/
private def counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def counterCarry : List Bool → ℕ
  | true :: bs => counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma counterInc_potential (bs : List Bool) :
    (counterInc bs).count true + counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [counterInc, counterCarry]
    | true => simp [counterInc, counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma counterInc_bits (n : ℕ) : counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma counterInc_length (bs : List Bool) :
    (counterInc bs).length ≤ bs.length + 1 ∧
      counterCarry bs ≤ (counterInc bs).length := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [counterInc, counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- **The binary length counter**. A one-work-tape machine with four states (count `0`, carry `1`,
rewind `2`, emit `3`) that keeps a little-endian binary counter on its work tape, increments it once
per input symbol, and on the blank after the input emits the counter's bits and halts, so that it
computes `x ↦ Nat.bits |x|`. [AB09, §1.3, the examples of time-constructible functions] It is
declared under its `Turing.FinTM` name so that MIG-9 can move it into `Build/` without a rename. -/
def _root_.Turing.FinTM.lengthBitsTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => counterBump .pos (work 0)
        else if q = 1 then counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma counterTape_read (pre bs : List Bool) :
    counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (FinTM.lengthBitsTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [FinTM.lengthBitsTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .zero (counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [counterTape_read]
  unfold counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact counterTape_write pre bs _
    · funext j; simp [Action.apply, counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry]
    rw [MultiTapeTM.runFrom_one, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry]
      rw [MultiTapeTM.runFrom_one, counter_carry_step]
      simp [counterInc]
    | true =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step, counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_one]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, FinTM.lengthBitsTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : FinTM.lengthBitsTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (FinTM.lengthBitsTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [FinTM.lengthBitsTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      FinTM.lengthBitsTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (FinTM.lengthBitsTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (FinTM.lengthBitsTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [FinTM.lengthBitsTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .pos (counterTape bs 0)).apply _ =
    (counterBump .zero (counterTape bs 0)).apply _
  unfold counterBump
  by_cases h : counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : FinTM.lengthBitsTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (counterCarry bs + 1) =
      counterCfg x 2 ⟨i + 2, by omega⟩ ((counterCarry bs : ℤ) - 1) (counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * counterCarry bs + 2 = (counterCarry bs + 1) + (counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact counter_rewind x ⟨i + 2, by omega⟩ (counterInc bs) (counterCarry bs)
    (counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount, and every
head position of the elapsed run lies within twice one plus the final input length's binary
width of the origin.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions.
Each increment starts at the origin and lasts `2r + 2 ≤ 2 · (Nat.size |x| + 1)` steps, since the
carry length is at most the counter's binary width, which is monotone in the count; the
time-derived head envelope (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`) bounds the head
during the current increment. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] ∧
      ∀ u ≤ t, ∀ j : Fin 1,
        (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) u).workTapePos j ∈
          Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq]
      apply Cfg.ext
      · rw [Cfg.init_state]
        rfl
      · rw [Cfg.init_inputPos]
        rfl
      · funext j z
        rw [Cfg.init_workTapes]
        simp only [counterCfg, counterTape, Nat.zero_bits, List.getElem?_nil, ite_self]
      · funext j
        rw [Cfg.init_workTapePos]
        rfl
      · rw [Cfg.init_output]
        rfl
    · intro u hu j
      rw [show u = 0 by omega, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq,
        Cfg.init_workTapePos, Finset.mem_Icc]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc, hb⟩ := ih (by omega)
    refine ⟨t + (2 * counterCarry i.bits + 2), ?_, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]
    · intro u hu j
      by_cases hut : u ≤ t
      · exact hb u hut j
      · rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, hc]
        have hp := Finset.mem_Icc.mp (MultiTapeTM.workTapePos_runFrom_mem_Icc
          FinTM.lengthBitsTM.tm (counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits []) (u - t) j)
        have hcarry := (counterInc_length i.bits).2
        rw [counterInc_bits, Nat.size_eq_bits_len] at hcarry
        have hwidth := Nat.size_le_size hi
        change 0 - ((u - t : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((u - t : ℕ) : ℤ) at hp
        rw [Finset.mem_Icc]
        constructor <;> omega

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
      counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (FinTM.lengthBitsTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [FinTM.lengthBitsTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, counterCfg]
    · simp only [Action.apply, counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := FinTM.lengthBitsTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((FinTM.lengthBitsTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [FinTM.lengthBitsTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

/-- Reading the blank after the input, the count state enters emission without moving.

**Proof sketch.** The input head is at `|x| + 1`, so the input symbol is the right blank; the count
state's transition on a blank changes only the state. -/
private lemma counter_emit_start (x : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
  have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol = none :=
    Cfg.inputSymbol_of_end rfl
  rw [MultiTapeTM.step_of_some rfl, hin]
  apply Cfg.ext
  · rw [Action.apply_state]
    rfl
  · rw [Action.apply_inputPos]
    exact moveInputPos_zero _
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    exact Function.update_eq_self _ _
  · funext j
    rw [Action.apply_workTapePos]
    rfl
  · rw [Action.apply_output]
    rfl

/-- After counting, entering emission and emitting the stored word, the counter is halted with
output `Nat.bits |x|` at time `t + 1 + (|Nat.bits |x|| + 1)`, where `t` is the counting time. -/
private lemma counter_halt (x : List Bool) (t : ℕ)
    (hc : FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) t =
      counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) :
    FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) (t + 1) =
        counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] ∧
      FinTM.lengthBitsTM.ComputesInTime x x.length.bits
        ((t + 1) + (x.length.bits.length + 1)) := by
  have hstart : FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, counter_emit_start]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  refine ⟨hstart, (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · rw [MultiTapeTM.runFrom_add, hstart]
    exact he.1
  · rw [MultiTapeTM.runFrom_add, hstart]
    exact he.2

/-- **The length counter's time**. The counter computes `x ↦ Nat.bits |x|` within `5·(n + 1)` steps.
[AB09, §1.3]

**Proof sketch.** With twice the number of `true` counter bits as potential, elapsed time plus
potential is at most `4n` after `n` increments (`counter_count`); entering emission and the final
halt add two steps, and the emitted word, of length at most `n`, costs one step per bit
(`counter_halt`). -/
theorem _root_.Turing.FinTM.lengthBitsTM_computes : FinTM.lengthBitsTM.ComputesFunInTime
    (fun x => Nat.bits x.length) (fun n => 5 * (n + 1)) := by
  refine (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_
  obtain ⟨t, ht, hc, -⟩ := counter_count x x.length (le_refl _)
  apply (counter_halt x t hc).2.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

/-- **The length counter's space**. At every time, the counter's work tape has visited at most
`5·(Nat.size |x| + 1)` cells: logarithmic space.

**Proof sketch.** Every counting round returns the head to the origin and a carry walks at most
the counter's binary width, which never exceeds `Nat.size |x|` (`counter_count`); emission walks
the stored word once, and after the halt nothing moves. So at every time the head stays in the
interval `[-2·(Nat.size |x| + 1), 2·(Nat.size |x| + 1)]`, which has at most
`5·(Nat.size |x| + 1)` cells. -/
theorem _root_.Turing.FinTM.lengthBitsTM_spaceUsed (x : List Bool) (t : ℕ) :
    FinTM.lengthBitsTM.tm.spaceUsed (FinTM.lengthBitsTM.tm.initCfg x) t ≤
      5 * (Nat.size x.length + 1) := by
  obtain ⟨t₀, -, hc, hb⟩ := counter_count x x.length (le_refl _)
  obtain ⟨hstart, hdone⟩ := counter_halt x t₀ hc
  let T := t₀ + 1 + (x.length.bits.length + 1)
  have hhalt : (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) T).state =
      none := ((FinTM.computesInTime_iff _ _ _ _).mp hdone).1
  -- Before the halt: the counting ledger, then the emission walk from the origin.
  have hpre (v : ℕ) (hv : v ≤ T) (j : Fin 1) :
      (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) v).workTapePos j ∈
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hvt : v ≤ t₀
    · exact hb v hvt j
    · rw [show v = (t₀ + 1) + (v - (t₀ + 1)) by omega, MultiTapeTM.runFrom_add, hstart]
      have hp := Finset.mem_Icc.mp (MultiTapeTM.workTapePos_runFrom_mem_Icc
        FinTM.lengthBitsTM.tm (counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [])
        (v - (t₀ + 1)) j)
      change 0 - ((v - (t₀ + 1) : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((v - (t₀ + 1) : ℕ) : ℤ) at hp
      have hlen := Nat.size_eq_bits_len x.length
      dsimp only [T] at hv
      rw [Finset.mem_Icc]
      constructor <;> omega
  -- After the halt the configuration is frozen.
  have hall (u : ℕ) (j : Fin 1) :
      (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) u).workTapePos j ∈
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hu : u ≤ T
    · exact hpre u hu j
    · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hhalt]
      exact hpre T (le_refl _) j
  rw [MultiTapeTM.spaceUsed_eq_sum]
  change (∑ i : Fin 1, _) ≤ _
  rw [Fin.sum_univ_one]
  exact (MultiTapeTM.spaceUsedByTape_le_card_Icc _ _ t (0 : Fin 1) _ _
    fun u _ => hall u 0).trans (by omega)

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). The formal proof uses twice the number of true counter bits as
potential: elapsed time plus potential is at most `4n` after `n` increments.
Entering emission and its final halting transition add two steps; the output length
is at most `n`, so `c = 5` suffices. -/
theorem timeConstructible_id : TimeConstructible id :=
  ⟨fun n => le_refl n, 5, by decide, FinTM.lengthBitsTM,
    (FinTM.computesFunInTime_iff _ _ _).mp FinTM.lengthBitsTM_computes⟩

end Complexity
```

## ===== TCSlib/Complexity/ClassP/TimeConstructiblePoly.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Build.Primitives
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomials are time constructible

`n ↦ C·(n+1)^(c+1)` is time constructible for `C > 0` (`Complexity.timeConstructible_poly`): the
catalog's unary polynomial generator `Turing.FinTM.polyUnaryTM` writes the value in unary, and the
linear-time binary length counter of `Complexity.timeConstructible_id` converts it.

The theorem moved here from `ClassNP/TMSAT.lean`, so that consumers of time-constructible bounds
need not import the `TMSAT` development; its proof now cites the catalog's generator in place of a
private copy.

## Main results

* `Complexity.timeConstructible_poly`: `n ↦ C·(n+1)^(c+1)` is time constructible (`C > 0`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- **Polynomial bounds are time constructible**: for `C > 0`, the function
`n ↦ C·(n+1)^(c+1)` is `Complexity.TimeConstructible`. (A **new statement about
the Chapter-1 notion**, flagged for this phase's audit — see the deviations
list; the exponent `c + 1` keeps `T n ≥ n`, which degree `0` would violate.)
This is the plan's supporting obligation for the `TMSAT` reduction's unary
components.

**Proof sketch.** The bound `n ≤ n + 1 ≤ C·(n+1)^(c+1)` holds since `C ≥ 1`.
The machine: scan the input once, incrementing a little-endian binary counter
per cell to obtain `n` (the audited `Complexity.timeConstructible_id` fill is
the in-repo precedent; its private counter layer is a template, not a citable
API — phase-1 audit, finding 5); then compute `(n+1)^(c+1)` by `c + 1`
successive schoolbook binary multiplications and multiply by the constant `C`
(a fixed number of multiplications on operands of `O((c+1)·log(n+2) + log(C+1))`
bits, each polynomial in the bit length); emit the result as
`(T |x|).bits` (little-endian, the `Complexity.TimeConstructible` output
convention). Budget: the scan is `n` steps and the arithmetic polylogarithmic,
against the constant-slack budget `c'·(C·(n+1)^(c+1) + 1)` — ample.

**Implementation note (epoch 2).** The formal proof uses an exact unary
box-enumeration machine followed by the public linear-time binary length
counter, rather than formalizing schoolbook multiplication. Each of `c+1`
unary loop tapes has length `n+1`; each box point emits exactly `C` bits.
The generator costs at most `(C+5(c+1)+4)(n+1)^(c+1)`; timed composition with
`timeConstructible_id` preserves linear time in the polynomial's value.
This is a proof-route deviation only; the frozen statement is unchanged. -/
theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
    TimeConstructible fun n => C * (n + 1) ^ (c + 1) := by
  have hdom (n : ℕ) : (n + 1) ^ (c + 1) ≤ C * (n + 1) ^ (c + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((n + 1) ^ (c + 1)) hC
  refine ⟨fun n => ?_, ?_⟩
  · have hp : n + 1 ≤ (n + 1) ^ (c + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
        (show 1 ≤ c + 1 by omega)
    exact (Nat.le_succ n).trans (hp.trans (hdom n))
  · obtain ⟨_, a, ha, M, hM⟩ := timeConstructible_id
    have hcounter : M.ComputesFunInTime (fun x => x.length.bits) (fun n => a * (n + 1)) :=
      hM
    obtain ⟨N, b, hN⟩ := FinTM.computesFunInTime_comp (FinTM.polyUnaryTM_computes C (c + 1)) hcounter
      (by intro m n h; exact Nat.mul_le_mul_left a (Nat.add_le_add_right h 1))
    let A := C + 5 * (c + 1) + 4
    refine ⟨(b + 1) * (a + 1) * (A + 1),
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _), N, ?_⟩
    intro x
    have hb := hN x
    simp only [Function.comp_apply, List.length_replicate] at hb
    apply hb.mono
    have hmajor : A * (x.length + 1) ^ (c + 1) + 1 ≤
        (A + 1) * (C * (x.length + 1) ^ (c + 1) + 1) := by
      have hm := Nat.mul_le_mul_left A (hdom x.length)
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    change b * (A * (x.length + 1) ^ (c + 1) +
        a * (A * (x.length + 1) ^ (c + 1) + 1) + 1) ≤ _
    calc
      _ = b * (a + 1) * (A * (x.length + 1) ^ (c + 1) + 1) := by ring
      _ ≤ (b + 1) * (a + 1) *
          ((A + 1) * (C * (x.length + 1) ^ (c + 1) + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (a + 1) (Nat.le_succ b)) hmajor
      _ = _ := by ring

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTime.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time computable functions

The function class `FP` underlying every Karp reduction of [AB09, ch. 2]: a function
`f : {0,1}* → {0,1}*` is polynomial-time computable when some machine of this
development computes it within a bound `C · (n + 1)^c`. This module fixes the
polynomial normal form (`Complexity.PolyBound`), the class
(`Complexity.PolyTimeComputable`), and the closure calculus that the chapter's
reductions assemble with — identity, composition, and the output-length bound.

## Design

* **Normal form `C · (n + 1)^c`.** Chapter 1's `P` uses `n^c + 1`; for *function*
  bounds the `(n + 1)^c` shape is closed under the compositions the calculus
  performs and is a monotone majorant by construction (both forms bound the same
  class, by `Complexity.succ_pow_le` and its converse direction). The choice is a
  recorded phase-1 design question.
* **Closure lemmas are need-driven.** Only the combinators the mandatory core
  consumes are stated here; concatenation, constant prefixing, and unary padding
  arrive with the phases that first use them (plan §2), never speculatively.

## Main definitions

* `Complexity.PolyBound` — `p` is bounded by `C · (n + 1)^c`.
* `Complexity.PolyTimeComputable` — `f` is computed by some machine within a
  polynomial bound ([AB09]'s implicit class FP).

## Main results

* `Complexity.polyTimeComputable_id` — the identity is polynomial-time computable.
* `Complexity.PolyTimeComputable.output_length_le` — a polynomial-time computable
  function has polynomially bounded output length.
* `Complexity.PolyTimeComputable.comp` — closure under composition
  [AB09, proof of Theorem 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7 and Theorem 2.8.)
-/

namespace Complexity

open Turing

/-- The bound `p : ℕ → ℕ` is *polynomially bounded*: `p n ≤ C · (n + 1)^c` for some
constants `C, c`. A **numerical helper only**: the *majorant* `C (n+1)^c` is
monotone, but `p` itself need be neither monotone nor computable — which is
exactly why this predicate never appears in a class definition (phase-1 audit,
finding 1: an abstract length function can smuggle undecidable information
through length arithmetic). Class definitions use explicit formulas instead. -/
def PolyBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * (n + 1) ^ c

/-- A function on binary strings is *polynomial-time computable* when some finite
binary-alphabet machine computes it within `C · (n + 1)^c` steps on inputs of
length `n` — the function class FP implicit throughout [AB09, ch. 2]. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c

/-- The defining property of `PolyTimeComputable`: `f` is polynomial-time computable iff some
finite binary-alphabet machine `M` computes it within `C · (n + 1)^c` steps,
`PolyTimeComputable f ↔ ∃ M C c, M.ComputesFunInTime f (fun n => C * (n + 1) ^ c)`. -/
theorem polyTimeComputable_iff (f : List Bool → List Bool) :
    PolyTimeComputable f ↔
      ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c :=
  Iff.rfl

/-- The identity function is polynomial-time computable.

**Proof sketch.** `Turing.FinTM.computesFunInTime_id` supplies a machine computing
`id` within a linear bound; enlarge the bound into the `C · (n + 1)^c` normal form
pointwise via `Turing.FinTM.ComputesInTime.mono` (there is no
`ComputesFunInTime`-level monotonicity lemma — phase-1 audit, finding 9). -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_id
  refine ⟨M, C, 1, fun x => (hM x).mono ?_⟩
  simp only [Nat.pow_one]
  exact Nat.le_refl _

/-- A polynomial-time computable function has polynomially bounded output length:
`|f x| ≤ C · (|x| + 1)^c` for some constants `C, c` uniform over all inputs.

**Proof sketch.** A machine emits at most one symbol per step
(`Turing.MultiTapeTM.output_length_le`), so the completed output of a computation
within `t` steps has length at most `t`; instantiate `t` at the machine's own
polynomial budget on each input. -/
theorem PolyTimeComputable.output_length_le {f : List Bool → List Bool}
    (h : PolyTimeComputable f) :
    ∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c := by
  obtain ⟨M, C, c, hM⟩ := h
  refine ⟨C, c, fun x => ?_⟩
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
  simpa only [hout] using M.tm.output_length_le x (C * (x.length + 1) ^ c)

/-- The timed-composition budget is bounded by a polynomial of degree
`max c (c * c')`, uniformly in all natural coefficients, degrees, and lengths.

**Proof sketch.** Since `(n+1)^c ≥ 1`, the inner argument is at most
`(C+1)(n+1)^c`. Raising to `c'` gives the second term degree `c*c'`.
Enlarge both degrees to their maximum, absorb the constant term using
`(n+1)^(max c (c*c')) ≥ 1`, and distribute the common power. -/
private lemma comp_time_bound (a C c C' c' n : ℕ) :
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
      a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c (n + 1) hpos
  have hfirst : (n + 1) ^ c ≤ (n + 1) ^ max c (c * c') :=
    Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have hsecond : (C * (n + 1) ^ c + 1) ^ c' ≤
      (C + 1) ^ c' * (n + 1) ^ max c (c * c') := by
    calc
      (C * (n + 1) ^ c + 1) ^ c' ≤ ((C + 1) * (n + 1) ^ c) ^ c' :=
        Nat.pow_le_pow_left (by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_left hone _) c'
      _ = (C + 1) ^ c' * (n + 1) ^ (c * c') := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ (C + 1) ^ c' * (n + 1) ^ max c (c * c') :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (Nat.le_max_right _ _))
  calc
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
        a * (C * (n + 1) ^ max c (c * c') +
          C' * ((C + 1) ^ c' * (n + 1) ^ max c (c * c')) +
          (n + 1) ^ max c (c * c')) :=
      Nat.mul_le_mul_left a (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left C hfirst) (Nat.mul_le_mul_left C' hsecond))
        (Nat.one_le_pow _ _ hpos))
    _ = a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]

/-- Polynomial-time computable functions are closed under composition
[AB09, proof of Theorem 2.8: polynomials compose].

**Proof sketch.** Let `Mf` compute `f` within `C · (n + 1)^c` and `Mg` compute `g`
within `C' · (n + 1)^c'`. `Turing.FinTM.computesFunInTime_comp` composes the
machines with a factor-`2` overhead, running `Mg` on the intermediate output
`f x`, whose length is at most `C · (n + 1)^c` because a machine emits at most one
symbol per step (`Turing.MultiTapeTM.output_length_le`). The total budget
`2 · (C (n+1)^c + C' (C (n+1)^c + 1)^{c'} + 1)` is again of the form
`C'' · (n + 1)^{c''}` with `c'' = max c (c · c')` — the `max` covers `c' = 0`,
where the first machine's term still grows as `(n+1)^c` (phase-1 audit,
finding 7); since `(n+1)^c ≥ 1`, the whole budget is absorbed as
`a (C + C'(C+1)^{c'} + 1) (n+1)^{max c (c·c')}`. This is Theorem 2.8's
polynomial-composition observation. -/
theorem PolyTimeComputable.comp {f g : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) :
    PolyTimeComputable (g ∘ f) := by
  obtain ⟨Mf, C, c, hf⟩ := hf
  obtain ⟨Mg, C', c', hg⟩ := hg
  have hmono : Monotone (fun n : ℕ => C' * (n + 1) ^ c') := by
    intro m n hmn
    exact Nat.mul_le_mul_left C' (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) c')
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_comp hf hg hmono
  refine ⟨M, a * (C + C' * (C + 1) ^ c' + 1), max c (c * c'),
    fun x => (hM x).mono ?_⟩
  exact comp_time_bound a C c C' c' x.length

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files close
  to upstream (the specification API's equations sit beside their definitions there; the
  vendored headers list them).
* `Turing.MultiTapeTM.spaceUsed_le_mul_succ` — a run of `t` steps visits at most
  `k · (t + 1)` cells (shared by the space inclusions of chapter 4; added 2026-10-10).

* `Turing.MultiTapeTM.step_output_prepend`, `Turing.MultiTapeTM.runFrom_output_prepend`,
  `Turing.MultiTapeTM.runFrom_state_ne_none_of_le` — runs commute with a fixed output
  prefix, and a live endpoint has a live past (shared run facts, 12.2c/CH7-D2;
  added 2026-10-10).
* `Turing.MultiTapeTM.exists_first_halt` — a run halted by time `t` halts first at some
  `u ≤ t`, live before `u` and already in its time-`t` configuration (the first-halt
  argument, public for the oracle query capture; added 2026-10-11, B1).
* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — a head confined to an integer interval
  visits at most its cardinality (moved from `Build/Catalog` at MIG-0b's layering split, for
  the contract core, 2026-10-13).
* `Turing.MultiTapeTM.spaceUsed_le_of_abs_le` — if every work head stays within `r` cells of
  its start, the run uses at most `k · (2r + 1)` cells.
* `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` — after `u` steps every work head lies
  within `u` cells of its start (MIG-0b, 2026-10-13).
* `Turing.MultiTapeTM.runFrom_with_q₀`, `Turing.MultiTapeTM.initCfg_with_q₀` — a machine
  restarted at another initial state runs as before, from `Cfg.init` at that state (the core
  specification API's gate, finding 1).
* `Turing.FinTM.computesFunInTime_iff` — computing a function in time, input by input (the
  core specification API's gate, finding 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output and space lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays close to upstream; the specification API's equations are the exception, beside their
definitions).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

/-- A run of `t` steps visits at most `t + 1` cells on each work tape, hence at most
`k · (t + 1)` cells in all. [AB09, proof of Theorem 4.2: a machine running in time `T`
visits at most `T` cells per tape, up to the starting cell]

**Proof sketch.** Each tape's visited set is the image of `Finset.range (t + 1)`
(`Finset.card_image_le`, `Finset.card_range`); sum over the `k` tapes
(`Finset.sum_le_sum`, `Finset.sum_const_nat`). -/
theorem spaceUsed_le_mul_succ (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ k * (t + 1) := by
  calc tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i := rfl
    _ ≤ ∑ _i : Fin k, (t + 1) := Finset.sum_le_sum fun i _ => by
      unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
      exact (Finset.card_image_le).trans (Finset.card_range (t + 1)).le
    _ = k * (t + 1) := by
      rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-- Prepending a fixed word to the output commutes with one step of any machine: the
transition table reads neither the output tape nor its length, and a step only appends
to it. This is the append-only output tape of the machine model [AB09, §1.2] (the
write-only output tape is a declared variation; see `Turing.FinTM`).

**Proof sketch.** A halted configuration does not move. Otherwise both sides apply the
same action, chosen from the unchanged state, input symbol and work-tape symbols; the
output equality is associativity of append. -/
theorem step_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    tm.step { cfg with output := pre ++ cfg.output } =
      { tm.step cfg with output := pre ++ (tm.step cfg).output } := by
  have hi : ({ cfg with output := pre ++ cfg.output } : Cfg k Symbol State input).inputSymbol =
      cfg.inputSymbol := rfl
  have hw : ({ cfg with output := pre ++ cfg.output } :
      Cfg k Symbol State input).workTapeSymbols = cfg.workTapeSymbols := rfl
  cases hs : cfg.state with
  | none => simp [MultiTapeTM.step, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, hi, hw]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Action.apply, List.append_assoc]
    rfl

/-- Prepending a fixed word to the output commutes with every run: running from a
configuration whose output already starts with `pre` yields the run's result with `pre`
still in front of its output, halted tails included [AB09, §1.2].

**Proof sketch.** Iterate the one-step commutation `step_output_prepend` along the run
with `runFrom_comm_of_step`. -/
theorem runFrom_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) (t : ℕ) :
    tm.runFrom { cfg with output := pre ++ cfg.output } t =
      { tm.runFrom cfg t with output := pre ++ (tm.runFrom cfg t).output } :=
  MultiTapeTM.runFrom_comm_of_step (tm := tm) (tm' := tm)
    (fun c => { c with output := pre ++ c.output }) (fun c => step_output_prepend tm c pre) cfg t

/-- A run that is still live at time `t` was live at every time `u ≤ t`: the halting
configuration of the model is absorbing [AB09, §1.2].

**Proof sketch.** A halt at some `u ≤ t` would, by `runFrom_add` and `runFrom_of_halt`,
make the configuration at `t` equal to the halted one at `u`. -/
theorem runFrom_state_ne_none_of_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- **First halt**: if a run from `cfg` has halted by time `t`, then it halts first at
some `u ≤ t` — live at every earlier time, and already in the very configuration it
occupies at `t`, halting being absorbing [AB09, §1.2]. This is the guard-discharge form
consumed by the lockstep contracts whose hypothesis is liveness before the halting time
(`Turing.capture_run`, `Turing.emit_run`).

**Proof sketch.** Take `u` least with a halted configuration (`Nat.find`). Minimality
gives liveness below `u`; since `u ≤ t`, `runFrom_add` and `runFrom_of_halt` identify the
configurations at `u` and at `t`. -/
theorem exists_first_halt (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t : ℕ} (h : (tm.runFrom cfg t).state = none) :
    ∃ u ≤ t, (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  have hex : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, h⟩
  have hle : Nat.find hex ≤ t := Nat.find_min' hex h
  refine ⟨Nat.find hex, hle, fun v hv => Nat.find_min hex hv, ?_⟩
  rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]

/-- A run ending in a designated live stop state first enters the stop states by its deadline,
and that first entry is already the final configuration, provided every stop configuration is
fixed by one step.

**Proof sketch.** Choose the least stop-state time with `Nat.find`. Minimality gives the
strict earlier-time cut. The fixed-step hypothesis keeps every subsequent configuration equal
to that first entry; `runFrom_add` then identifies it with the given final configuration. -/
theorem exists_first_entry_of_fixed {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (stop : State → Prop) (c d : Cfg k Symbol State input) (T : ℕ)
    (hfix : ∀ z : Cfg k Symbol State input,
      (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  have hfixed : tm.step (tm.runFrom c t) = tm.runFrom c t := hfix _ hs
  have hconst (n : ℕ) : tm.runFrom (tm.runFrom c t) n = tm.runFrom c t := by
    induction n with
    | zero => exact runFrom_zero
    | succ n ih => rw [runFrom_succ_eq_step, hfixed]; exact ih
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- **A new initial state changes no run** (the core specification API, user 2026-10-16; its
gate, finding 1): the machine `{ tm with q₀ := q }` has `tm`'s transition table, so from every
configuration it takes `tm`'s run, `({ tm with q₀ := q }).runFrom cfg t = tm.runFrom cfg t`.
A consumer restarts a machine whose initial state it does not read (for example
`Complexity.LogProg.cleanTM`) at a state of its choice, without unfolding the machine. -/
theorem runFrom_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).runFrom cfg t = tm.runFrom cfg t :=
  rfl

/-- **The initial configuration at a new initial state** (the core specification API; its
gate, finding 1): `({ tm with q₀ := q }).initCfg x = Cfg.init q x`. -/
theorem initCfg_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State) (x : List Symbol) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).initCfg x = Cfg.init q x :=
  rfl

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- **Computing a function in time, input by input** (the core specification API, user
2026-10-16; its gate, finding 2): `M` computes `f` in time `T` exactly when, on every input
`x`, it halts within `T |x|` steps with `f x` on its output tape,
`M.ComputesFunInTime f T ↔ ∀ x, M.ComputesInTime x (f x) (T |x|)`. With
`Turing.FinTM.computesInTime_iff` this reads a function computation off the runs. -/
theorem computesFunInTime_iff (M : FinTM Symbol) (f : List Symbol → List Symbol)
    (T : ℕ → ℕ) :
    M.ComputesFunInTime f T ↔ ∀ input, M.ComputesInTime input (f input) (T input.length) :=
  Iff.rfl

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- **Computing via an embedding, input by input** (the core specification API): `M` computes
`f` via `e` in time `T` exactly when, on every `x`, it halts on `x.map e` within `T |x|` steps
with `(f x).map e` on its output tape. -/
theorem computesFunInTimeVia_iff {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) :
    M.ComputesFunInTimeVia e f T ↔
      ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length) :=
  Iff.rfl

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- **Computing a function, input by input** (the core specification API): `M` computes `f`
exactly when, on every input `x`, it halts after some number of steps with `f x` on its output
tape. -/
theorem computes_iff (M : FinTM Symbol) (f : List Symbol → List Symbol) :
    M.Computes f ↔ ∀ input, ∃ t, M.ComputesInTime input (f input) t :=
  Iff.rfl

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing

namespace Turing

/-- A head confined to an integer interval visits at most its cardinality.

(Moved from `Build/Zone.lean` for B4, 2026-10-12.)

**Proof sketch.** The visited set is a finite image contained in the
interval by hypothesis; `Finset.card_le_card` and `Int.card_Icc` finish. -/
theorem MultiTapeTM.spaceUsedByTape_le_card_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (lo hi : ℤ)
    (h : ∀ u ≤ t, (tm.runFrom d u).workTapePos i ∈ Finset.Icc lo hi) :
    tm.spaceUsedByTape d t i ≤ (hi + 1 - lo).toNat := by
  unfold MultiTapeTM.spaceUsedByTape
  calc
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card (by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      exact h u (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu))
    _ = _ := Int.card_Icc lo hi

/-- **A common head radius bounds the space**: if up to time `t` every work head stays within `r`
cells of its starting position, the run visits at most `2r + 1` cells on each work tape, hence
at most `k · (2r + 1)` cells in all.

**Proof sketch.** Each head stays in the integer interval of radius `r` around its start, which
has `2r + 1` cells (`Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`); sum over the tapes
(`Turing.MultiTapeTM.spaceUsed_eq_sum`). -/
theorem MultiTapeTM.spaceUsed_le_of_abs_le {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t r : ℕ)
    (h : ∀ u ≤ t, ∀ j, |(tm.runFrom d u).workTapePos j - d.workTapePos j| ≤ (r : ℤ)) :
    tm.spaceUsed d t ≤ k * (2 * r + 1) := by
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    ∑ j, tm.spaceUsedByTape d t j ≤ ∑ _j : Fin k, (2 * r + 1) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hb := tm.spaceUsedByTape_le_card_Icc d t j (d.workTapePos j - r)
        (d.workTapePos j + r) fun u hu => by
          have he := abs_le.mp (h u hu j)
          rw [Finset.mem_Icc]
          constructor <;> omega
      omega
    _ = k * (2 * r + 1) := by simp

end Turing

namespace Turing

/-- **The time-derived head envelope** (MIG-0b): after `u` steps from `cfg`, every work head
lies within `u` cells of its start. Every row with a time bound therefore has an interval
envelope, even when it states none (the install and emit calls; the find round). It is the
interval form of `Build/Catalog`'s private `f2_head_steps`, which retires with MIG-1 (backlog
F6-1(g)), and of the run head bound that the H2 promotion exports
(`CodeSimulator.h1Run_headBound`, backlog F7-1(a)); stated here over any alphabet and state
type, like the raw layer it extends.

**Proof sketch.** Induction on `u`: each step moves a head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`). -/
theorem MultiTapeTM.workTapePos_runFrom_mem_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (u : ℕ) (j : Fin k) :
    (tm.runFrom cfg u).workTapePos j ∈
      Finset.Icc (cfg.workTapePos j - u) (cfg.workTapePos j + u) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hs := abs_le.mp (tm.workTapePos_step_le (tm.runFrom cfg u) j)
    rw [Finset.mem_Icc] at ih ⊢
    rw [MultiTapeTM.runFrom_succ_eq_step']
    push_cast
    constructor <;> omega

end Turing
```
