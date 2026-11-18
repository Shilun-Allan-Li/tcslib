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

## ===== campaign/items/ram-tm/briefs/fill-ram-tmproc.md =====

# RAM fill (Codex), bridge job G: a Turing machine as a Light procedure (`Light/TMProc`, 1 admission)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind, the reader rule among
them. **Fill name:** `fill-ram-tmproc`. **Base:** the commit given in the dispatch prompt: PR #382's
head, branch `ram/tmproc-statement`.

## What this is

`TCSlib/Programs/Light/TMProc.lean` states `Light.exists_tmProc`. For every finite binary Turing
machine `M` there is a Light program `Q` with a procedure that runs `M` on a bit string in memory,
writes `M`'s output to memory, and returns its length, within `A·(t + len + 1)` steps. It is
specified by `Meets` wherever `Q` is placed (`Program.behind Pre Q ++ Post`). **This job proves
it.** It is the reverse of stage 2: Light programs, and through them word-RAM programs, can call any
polynomial-time function given only by a machine. It reaches no admission.

## Route

Read the statement's proof sketch, and the vendored Light layer it builds on:
- `Light/Syntax`: `Stmt`, `Expr`, `Exec`, `Limits`;
- `Light/Logic`, `Rules`, `Calls`, `Frames`, `Regions`: `Ends`, its rules, `Meets`, `SameOutside2`;
- `Light/Tactics`: `light_keep`, `light_time`, `light_side` and the rest;
- `Light/Lib`: worked procedures with loops and their specifications. `Copy.lean` and `Pass.lean`
  are short models of a loop proved with `Ends`.

**The encoding.**
- **State and symbols.** The state is a number, by `Fintype.equivFin` on `M.State`. Cells hold `0`
  for blank and `1`, `2` for `false`, `true`.
- **Tapes.** Lay out each work tape in the scratch region so that the cells reachable in `t` steps
  occupy `O(M.k·(t + 1))` cells with no bound known in advance: cell `z` of tape `j` at
  `sc + c₀ + ((2|z| + [z < 0])·M.k + j)`, after a constant header `c₀`.
- **Input.** The input head reads `x` at `a` in place. Its position runs from `0` to `len + 1`,
  with `Turing.Cfg`'s shift by one.

**One step.** Two routes; choose one and say which in the report.
- **A table.** A prologue writes `M`'s transition table into the header, generated from
  `M.tm.tr` over the finite domain. One generic interpreter loop is then proved once.
- **Code branches.** A finite case split per `(state, scanned symbols)`, generated from `M`.

The table route is recommended: one invariant, one loop.

**The invariant.** After `i` iterations, the memory and locals encode
`M.tm.runFrom (M.tm.initCfg x) i`: the state, the work tapes' cells, the heads, the input head,
and the output written so far at `b`. Read `Turing.Cfg`, `MultiTapeTM.step` and `runFrom` through
their published readers (`Configuration`, `Deterministic`, `Finite`; for instance `runFrom_one`,
`step_of_some`, `Cfg.init`'s equations). Use the reader rule for any missing one.

**Termination and time.** `M.ComputesInTime x out t` gives a halt by time `t` with output exactly
`out` (`Turing.FinTM.computesInTime_iff`). Each iteration costs `O_M(1)` Light steps, and the setup
costs `O(len)` plus the prologue.

**Placement.** Prove the specification for `Q` itself, then carry it to
`Program.behind Pre Q ++ Post` by `Ends.shift_append` (`Light/Renumber`).

## Owned file

`TCSlib/Programs/Light/TMProc.lean`: the statement byte-identical. The program, its procedures
and all helpers are `private` in this file; a public definition of `Q` is not needed. If the file
passes about 1,500 lines, keep going and say so: the maintainer splits it at landing. You may add
imports of existing `TCSlib/Programs/Light/*` and `TCSlib/Complexity/TuringMachine/*` modules, each
listed in `REPORT.md` with its reason.

Rule 10 applies to this file, which is not vendored. It reads Light's definitions through their
rules and lemmas, as the vendored `Lib` procedures do, and `Turing`'s through their readers.

## Admitted dependencies allowed

None.

## Downstream check

The `TCSlib/Programs/Light.lean` facade.

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

## ===== TCSlib/Programs/Light/TMProc.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.Renumber
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Regions
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running a Turing machine inside a Light program

For every finite binary Turing machine `M` there is a Light procedure that runs `M` on a bit string
held in memory and writes `M`'s output to memory, within a time linear in `M`'s running time plus
the input length (`Light.exists_tmProc`). The procedure is part of a program `Q` that depends on
`M` only. Placed behind any program with `Program.behind` (`Light/Renumber`), and followed by any
procedures, it keeps its specification, so other programs can call it as a subroutine.

This is the reverse of stage 2 (`WordRAM.exists_simulation`, a word-RAM program run by a Turing
machine). It lets a program call any polynomial-time function given only by a machine, for
instance an abstract operation known to be `PolyTimeComputable`.

## Main results

* `Light.exists_tmProc`: the procedure and its specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.6: Turing machines and their simulation; Exercise
  1.9.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the language Light and its logic (`TCSlib/Programs/Light`).
-/

namespace Light

/-- **A Turing machine as a Light procedure.** For every finite binary machine `M` there are a
program `Q`, a procedure number `p` in it, and constants `A` and `k` such that, wherever `Q` is
placed (behind any program `Pre`, followed by any procedures `Post`), procedure `p + |Pre|`, called
with the arguments `[a, len, b, sc]`, does the following. If the memory holds the input `x` at
`a`, one cell per bit (`0` or `1`), and `M` computes `out` from `x` within `t` steps, then within
`A·(t + len + 1)` steps it returns `|out|`, holds `out` at `b`, one cell per bit, and changes no
cell outside the output's cells and the scratch region of `A·(t + len + 1)` cells at `sc`. The
hypotheses: the regions fit in memory and are pairwise apart; addresses fit in a word; and the
procedure's call depth `k` fits.

`Q`, `p`, `A` and `k` depend on `M` only, so a uniform machine gives a uniform procedure, and a
program calling it stays one program for all inputs.

**Proof sketch.**
- **Encoding.** Keep the state as a number, by `Fintype.equivFin`. Cell values are `0` for blank
  and `1`, `2` for `false`, `true`. Each work tape is laid out in the scratch region with cell `z`
  of tape `j` at an offset determined by `(2|z| + [z < 0])·M.k + j`, so the `t + 1` cells
  reachable in `t` steps fit in `O(M.k·(t + 1))` cells, with no bound needed in advance. Keep the
  heads and the input head as numbers in locals or scratch cells.
- **One step.** Either write the transition table into the scratch region by a constant prologue
  generated from `M`, so that one interpreter is verified once, or emit one code branch per
  `(state, symbols)` case. Each step reads the `M.k + 1` scanned symbols, looks up the action,
  writes and moves, and appends the output bit at `b`, in `O_M(1)` Light steps.
- **The run.** A `while` loop until the state is halted, with the invariant that the memory
  encodes `M.tm.runFrom (M.tm.initCfg x) i` after `i` iterations (the `Turing.Cfg` fields read
  through their published readers). `ComputesInTime` gives the halting time `≤ t` and the output.
- **Placement.** `Ends.shift_append` (`Light/Renumber`) carries the specification from `Q` to
  `Program.behind Pre Q ++ Post`. -/
theorem exists_tmProc (M : Turing.FinTM Bool) :
    ∃ (Q : Program) (p A k : ℕ), ∀ (Pre Post : Program) (lim : Limits) (d : ℕ)
      (a len b sc : ℕ) (μ : ℕ → ℤ) (x out : List Bool) (t : ℕ),
      x.length = len →
      (∀ i < len, μ (a + i) = ((x.getD i false).toNat : ℤ)) →
      M.ComputesInTime x out t →
      (lim.space : ℤ) ≤ lim.word →
      a + len ≤ lim.space → b + out.length ≤ lim.space → sc + A * (t + len + 1) ≤ lim.space →
      Apart a len b out.length → Apart a len sc (A * (t + len + 1)) →
      Apart b out.length sc (A * (t + len + 1)) →
      d + k ≤ lim.depth →
      Meets lim (Program.behind Pre Q ++ Post) (p + Pre.length) d [(a : ℤ), len, b, sc] μ
        (A * (t + len + 1)) fun r μ' =>
          r = out.length ∧ (∀ i < out.length, μ' (b + i) = ((out.getD i false).toNat : ℤ)) ∧
          SameOutside2 μ μ' b out.length sc (A * (t + len + 1)) := by
  sorry

end Light
```

## ===== TCSlib/Programs/Light/Renumber.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Renumber.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Renumber.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Logic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, Apache-2.0: the source of
  this file (`ThreeSumApsp/Lang/Renumber.lean`); see the header and the repository NOTICE.
-/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The statement with n added to the number of every procedure that it calls. -/
def Stmt.shift (n : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x

/-- The program P placed behind the program Q. -/
def Program.behind (Q P : Program) : Program := Q ++ P.map (Stmt.shift Q.length)

/-- Procedure p of P is procedure `p + Q.length` of P placed behind Q, with its calls
shifted. -/
theorem Program.getElem?_behind_right (Q : Program) {p : ℕ} {body : Stmt} (h : P[p]? = some body) :
    (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  rw [Program.behind, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
    List.getElem?_map, h]
  rfl

/-- **Relocation.**  A run in P is a run, with the same states and the same number of steps, of
the shifted statement in P placed behind Q. -/
theorem Exec.shift {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (Q : Program) :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (Program.getElem?_behind_right Q h₂) h₃ ih

/-- What is proved about a statement in P holds for the shifted statement in P placed behind
Q. -/
theorem Ends.shift {s σ T post} (h : Ends lim P d s σ T post) (Q : Program) :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.shift Q, hc, hq⟩

/-- The same with more procedures appended behind. -/
theorem Ends.shift_append {s σ T post} (h : Ends lim P d s σ T post) (Q R : Program) :
    Ends lim (Program.behind Q P ++ R) d (s.shift Q.length) σ T post :=
  (h.shift Q).append R

end Light
```

## ===== TCSlib/Programs/Light/Syntax.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Syntax.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Syntax.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The light language

A small imperative language with procedures and recursion, in which the paper's procedures can be
written almost as printed.  It is a proof device: a program of this language is compiled
(`compileProgram`) to the word RAM of the end statement, and the compiler is proved to keep results
and, up to a constant factor that depends on the program text only, step counts.

* A program is a finite piece of data: a list of procedure bodies.  It contains no Lean functions.
* The memory is an array of integers addressed by natural numbers.  Each running procedure has local
  variables 0, 1, 2, ….
* Arithmetic: +, −, ×.  There is no division.  Comparisons (<, =) occur as the tests of if and
  while.
* Every executed operation costs one step: each constant, variable, operation and load of an
  expression, each comparison, assignment, store, branch, call and return.
* A run is subject to limits: it forms no value of absolute value above `word`, touches no cell at
  an address ≥ `space`, and nests calls at most `depth` deep.  A run that would break a limit does
  not exist.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

/-- The operations on two words. -/
inductive Op : Type
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The result of an operation. -/
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr

/-- Tests. -/
inductive Cond : Type
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Cond) (s₁ s₂ : Stmt)
  | while (c : Cond) (s : Stmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  deriving Repr

/-- A program: the bodies of its procedures, numbered from 0. -/
abbrev Program : Type := List Stmt

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ

/-- The value of an expression. -/
def Expr.val (s : State) : Expr → ℤ
  | .const n => n
  | .var x => s.loc x
  | .op o a b => o.eval (a.val s) (b.val s)
  | .load a => s.mem (a.val s).toNat

/-- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => a.cost + b.cost + 1
  | .load a => a.cost + 1

/-- An address within the limits. -/
def Limits.Addr (lim : Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space

/-- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
def Expr.Safe (lim : Limits) (s : State) : Expr → Prop
  | .const n => (n : ℤ) ≤ lim.word
  | .var _ => True
  | .op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | .load a => a.Safe lim s ∧ lim.Addr (a.val s)

/-- Whether a test holds. -/
def Cond.Holds (s : State) : Cond → Prop
  | .lt a b => a.val s < b.val s
  | .eq a b => a.val s = b.val s

/-- The number of steps of a test: its two sides and the comparison. -/
def Cond.cost : Cond → ℕ
  | .lt a b => a.cost + b.cost + 1
  | .eq a b => a.cost + b.cost + 1

/-- The evaluation of a test stays within the limits. -/
def Cond.Safe (lim : Limits) (s : State) : Cond → Prop
  | .lt a b => a.Safe lim s ∧ b.Safe lim s
  | .eq a b => a.Safe lim s ∧ b.Safe lim s

/-- The local variables of a procedure that has just been called: the arguments in 0, 1, …, and 0 in
all others. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- The memory that holds the list ws in the cells 0, 1, 2, … and 0 elsewhere. -/
def memOf (ws : List ℤ) : ℕ → ℤ := fun a => ws.getD a 0

/-- `Exec lim P d s σ σ' c`: within the limits lim, and at nesting depth d of calls, the statement
s of the program P, started in the state σ, ends in the state σ' after exactly c steps. -/
inductive Exec (lim : Limits) (P : Program) : ℕ → Stmt → State → State → ℕ → Prop
  | skip {d σ} : Exec lim P d .skip σ σ 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ → lim.Addr (a.val σ) →
      Exec lim P d (.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ c₁ c₂} : Exec lim P d s₁ σ σ' c₁ → Exec lim P d s₂ σ' σ'' c₂ →
      Exec lim P d (.seq s₁ s₂) σ σ'' (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ k} : c.Safe lim σ → c.Holds σ → Exec lim P d s₁ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ k} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d s₂ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d (.while c s) σ σ (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s k₁ k₂} : c.Safe lim σ → c.Holds σ → Exec lim P d s σ σ' k₁ →
      Exec lim P d (.while c s) σ' σ'' k₂ → Exec lim P d (.while c s) σ σ'' (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body → d < lim.depth →
      Exec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k →
      Exec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
        ((args.map Expr.cost).sum + 2 + k)

/-- Everything held in a variable or in a cell fits in a word. -/
def State.Bounded (lim : Limits) (σ : State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word

end Light
end
```

## ===== TCSlib/Programs/Light/Logic.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Logic.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Logic.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Syntax
import TCSlib.Programs.Util.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i,
whatever is appended after the list. -/
theorem getElem?_append_append {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i. -/
theorem getElem?_append_length_add (P₀ : Program) {R : Program} {i : ℕ} {body : Stmt}
    (h : R[i]? = some body) : (P₀ ++ R)[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h

/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) :
    Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

/-- A loop whose test holds: one round, then the loop again. -/
theorem Ends.whileStep {σ c s T} {Q : State → Prop} (T₁ T₂ : ℕ) (hs : c.Safe lim σ) (hc : c.Holds σ)
    (h : Ends lim P d s σ T₁ fun σ' => Ends lim P d (.while c s) σ' T₂ Q)
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .whileTrue hs hc he₁ he₂, by omega, hq⟩

/-- A loop whose test fails. -/
theorem Ends.whileDone {σ c s T} {Q : State → Prop} (hs : c.Safe lim σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ) (hT : c.cost + 1 ≤ T) : Ends lim P d (.while c s) σ T Q :=
  ⟨σ, _, .whileFalse hs hc, hT, hQ⟩

/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h

/-- Loops whose number of rounds depends on the data.  I is the invariant, m a quantity that every
round decreases, and b bounds the cost of a round. -/
theorem Ends.whileVariant {σ c s T} {Q : State → Prop} (I : State → Prop) (m : State → ℕ) (b : ℕ)
    (hI : I σ) (hsafe : ∀ σ, I σ → c.Safe lim σ)
    (hs : ∀ σ, I σ → c.Holds σ → Ends lim P d s σ b fun σ' => I σ' ∧ m σ' < m σ)
    (hn : ∀ σ, I σ → ¬ c.Holds σ → Q σ) (hT : m σ * (c.cost + 1 + b) + (c.cost + 1) ≤ T) :
    Ends lim P d (.while c s) σ T Q := by
  have key : ∀ n σ, I σ → m σ ≤ n →
      Ends lim P d (.while c s) σ (m σ * (c.cost + 1 + b) + (c.cost + 1)) Q := by
    intro n
    induction n with
    | zero =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, -, -, -, hlt⟩ := hs σ h hc
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
    | succ n ih =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, he₁, hk₁, hI₁, hlt⟩ := hs σ h hc
        obtain ⟨σ₂, k₂, he₂, hk₂, hq⟩ := ih σ₁ hI₁ (by omega)
        refine ⟨σ₂, _, .whileTrue (hsafe _ h) hc he₁ he₂, ?_, hq⟩
        have h1 : (m σ₁ + 1) * (c.cost + 1 + b) ≤ m σ * (c.cost + 1 + b) :=
          Nat.mul_le_mul_right _ hlt
        have h2 : (m σ₁ + 1) * (c.cost + 1 + b) = m σ₁ * (c.cost + 1 + b) + (c.cost + 1 + b) := by
          ring
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
  exact (key _ σ hI le_rfl).mono hT fun _ h => h

/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/

/-- Local variable number x. -/
abbrev v (x : ℕ) : Expr := .var x
/-- The constant n. -/
abbrev k (n : ℕ) : Expr := .const n
/-- The memory cell at address a. -/
abbrev M (a : Expr) : Expr := .load a
/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq

/-- The test a ≤ b, written as a < b + 1. -/
abbrev Cond.le (a b : Expr) : Cond := a <' b +' k 1
@[inherit_doc] infix:50 " ≤' " => Cond.le

/-- Branching on a ≠ b: the branches of the test a = b, swapped. -/
abbrev Stmt.iteNe (a b : Expr) (s₁ s₂ : Stmt) : Stmt := .ite (a =' b) s₂ s₁

/-- The test a ≤ b holds if and only if a ≤ b. -/
theorem Cond.holds_le {σ : State} {a b : Expr} : (a ≤' b).Holds σ ↔ a.val σ ≤ b.val σ :=
  Int.lt_add_one_iff

/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame

/-- `light_norm [h₁, h₂]` unfolds values, costs and safety conditions of expressions and tests, and
reads of updated variables and cells, and rewrites with the facts `h₁`, `h₂` about the variables. -/
macro "light_norm" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Expr.Safe, Expr.val, Expr.cost, Op.eval, Cond.Holds, Cond.cost, Cond.Safe,
    Function.update_apply, reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, $ts,*])

/-- Unfolds values, costs and safety conditions of expressions and tests, and reads of updated
variables and cells. -/
macro "light_norm" : tactic => `(tactic| light_norm [])

/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/

/-- The standing assumptions about the limits: an address fits in a word, and so do the constants
of the programs. -/
structure Std (lim : Limits) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  const_le : (100 : ℤ) ≤ lim.word

/-- An address fits in a word if the memory is not larger than the largest word. -/
theorem Limits.Addr.abs_le {a : ℤ} (h : lim.Addr a) (hw : (lim.space : ℤ) ≤ lim.word) :
    |a| ≤ lim.word := by
  rw [abs_of_nonneg h.1]; exact h.2.le.trans hw

/-- A natural number below the size of the memory is an address, and fits in a word. -/
theorem Limits.addr_of_lt (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x < lim.space) :
    lim.Addr (x : ℤ) ∧ |(x : ℤ)| ≤ lim.word := by
  have h : lim.Addr (x : ℤ) := ⟨Int.natCast_nonneg x, by exact_mod_cast hx⟩
  exact ⟨h, h.abs_le hw⟩

/-- A natural number at most the size of the memory fits in a word. -/
theorem Limits.abs_le_of_le (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x ≤ lim.space) :
    |(x : ℤ)| ≤ lim.word := by
  rw [abs_of_nonneg (Int.natCast_nonneg x)]
  exact le_trans (by exact_mod_cast hx) hw

end Light
end
```

## ===== TCSlib/Programs/Light/Rules.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Rules.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Rules.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Logic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Abs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/

instance Cond.decidableHolds (σ : State) : (c : Cond) → Decidable (c.Holds σ)
  | .lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | .eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))

/-- The state after a block (σ itself for a loop or a call, which are not blocks). -/
@[simp] def Stmt.after : Stmt → State → State
  | .set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | .store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | .seq s t, σ => t.after (s.after σ)
  | .ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ

/-- A bound on the number of steps of a block: the longer side of each branch counts (0 for a loop
or a call). -/
@[simp] def Stmt.blockCost : Stmt → ℕ
  | .set _ e => e.cost + 1
  | .store a e => a.cost + e.cost + 1
  | .seq s t => s.blockCost + t.blockCost
  | .ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0

/-- The statement is a block, and its run from σ stays within the limits. -/
@[simp] def Stmt.BlockSafe (lim : Limits) : Stmt → State → Prop
  | .skip, _ => True
  | .set _ e, σ => e.Safe lim σ
  | .store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | .seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | .ite c s t, σ =>
    c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬ c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False

/-- The block s, started in σ, stays within the limits and ends in a state that satisfies R. -/
abbrev Stmt.Runs (lim : Limits) (s : Stmt) (σ : State) (R : State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)

/-! ## The default proofs -/

/-- `light_time [t₁, t₂]` compares two numbers of steps, after computing the costs of the
expressions, tests, blocks and argument lists that occur and unfolding the running times `t₁`,
`t₂`. -/
macro "light_time" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, $ts,*]
       first | omega | (ring_nf; omega))
    | omega
    | (simp [$ts,*] <;> first | omega | (ring_nf; omega)))

/-- Compares two numbers of steps, after computing the costs of the expressions, tests, blocks and
argument lists that occur. -/
macro "light_time" : tactic => `(tactic| light_time [])

/-- `light_side [h₁, h₂]` proves that an expression or a test stays within the limits, has a given
value, or holds, after putting in the values of the variables.  The facts `h₁`, `h₂` say what the
cells hold that are read, or are definitions to be unfolded; everything else is linear arithmetic
over the hypotheses in the context, to which the two fields of a hypothesis `Std lim` are added. -/
macro "light_side" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    ((try have := Std.space_le (by assumption))
     (try have := Std.const_le (by assumption))
     simp [Limits.Addr, abs_le, -abs_mul, $ts,*] <;> omega))

/-- Proves that an expression or a test stays within the limits, has a given value, or holds, after
putting in the values of the variables, by linear arithmetic over the hypotheses in the context. -/
macro "light_side" : tactic => `(tactic| light_side [])

/-- Proves an inequality between addresses, sizes and bounds by linear arithmetic over the
hypotheses in the context.  A field of a record that is written out, such as
`{ dst := a, len := n }.len`, is computed first. -/
macro "light_arith" : tactic => `(tactic| first | omega | light_side)

/-! ## Rules for blocks -/

/-- A weaker conclusion. -/
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩

/-- Two blocks, one after the other. -/
theorem Stmt.Runs.seq {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ fun σ' => t.Runs lim σ' R) : (s ;; t).Runs lim σ R :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- A branch whose test holds. -/
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by light_side) (hs : c.Safe lim σ := by light_side) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

/-- A branch whose test fails. -/
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by light_side) (hs : c.Safe lim σ := by light_side) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by light_time) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by light_time) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  h

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by light_time) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by light_time) :
    Ends lim P d s σ T Q :=
  h.mono hT rest

/-- An assignment at the end of the program. -/
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h

/-- An assignment, followed by the rest of the program. -/
theorem Ends.setThen {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩ (T - (e.cost + 1)) Q)
    (hs : e.Safe lim ⟨loc, μ⟩ := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.set hs le_rfl h) hT

/-- A store at the end of the program. -/
theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {Q : State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) : Ends lim P d (.store a e) ⟨loc, μ⟩ T Q :=
  Ends.store hs.1 hs.2.1 hs.2.2 hT h

/-- A store, followed by the rest of the program. -/
theorem Ends.storeThen {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩
      (T - (a.cost + e.cost + 1)) Q)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.storeLast h hs le_rfl) hT

/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by light_side) (hT : c.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by light_side) (hT : c.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by light_side)
    (hT : c.cost + 1 ≤ T := by light_time) : Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by light_time) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/

/-- for i = 0, …, hi - 1 do body. -/
abbrev Stmt.for (i : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  .set i (k 0) ;; .while (v i <' hi) (body ;; .set i (v i +' k 1))

/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (v i +' k 1).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(v i +' k 1).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light
end
```

## ===== TCSlib/Programs/Light/Calls.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Calls.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Calls.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Frames

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/

/-- Procedure number p of the program P, run at depth d on the arguments vals in the memory μ, ends
within T steps with a result r and a memory μ' that satisfy R r μ'. -/
def Meets (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem

section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR

/-- A specification whose time is a constant times a shape holds for every larger constant. -/
theorem Meets.mono_const {c c' S : ℕ} (h : Meets lim P p d vals μ (c * S) R) (hc : c ≤ c') :
    Meets lim P p d vals μ (c' * S) R :=
  h.mono_time (Nat.mul_le_mul_right _ hc)

/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by light_side)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by light_time) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT

/-- `x := p(args) ; s`.  The rest s of the text gets the steps that are left. -/
theorem Ends.callThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨Function.update loc x r, μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by light_side)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by light_time) :
    Ends lim P d (.call p args x ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.callLast hp h ha hd le_rfl) hT

/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      light_side)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by light_time) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      light_side)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by light_time) :
    Ends lim P d (.call p args x ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light
end
```

## ===== TCSlib/Programs/Light/Regions.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Regions.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Regions.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Function.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

/-! ## Regions -/

/-- The cell `b` is among the `n` cells from address `a`. -/
abbrev Inside (a n b : ℕ) : Prop := a ≤ b ∧ b < a + n

/-- The cell `b` is not among the `n` cells from address `a`. -/
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b

/-- Two regions of the memory, of `n` cells from `a` and of `n'` cells from `a'`, do not meet. -/
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a

/-- A map of a part of the memory: the regions of the list lie one behind the other, in the order of
the list, and the last one ends at or below `top`.  A region of the list is the pair of its first
address and its number of cells. -/
abbrev InOrder (top : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | [r] => r.1 + r.2 ≤ top
  | r :: r' :: rs => r.1 + r.2 ≤ r'.1 ∧ InOrder top (r' :: rs)

/-! ## Memories that agree on some cells -/

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- The memory `μ'` agrees with `μ` outside the `n` cells from address `a`. -/
abbrev SameOutside (μ μ' : ℕ → ℤ) (a n : ℕ) : Prop := SameOn (Outside a n) μ μ'

/-- The memory `μ'` agrees with `μ` outside the `n` cells from `a` and the `m` cells from `b`. -/
abbrev SameOutside2 (μ μ' : ℕ → ℤ) (a n b m : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x) μ μ'

/-- The memory `μ'` agrees with `μ` outside three regions: `n` cells from `a`, `m` cells from `b`,
and `k` cells from `c`. -/
abbrev SameOutside3 (μ μ' : ℕ → ℤ) (a n b m c k : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x ∧ Outside c k x) μ μ'

/-- No cell below the free pointer has changed. -/
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := SameOn (· < fr) μ μ'

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'

variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)

/-- Fewer cells are kept. -/
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)

/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

/-- Writing a cell that need not be kept. -/
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}

/-- The memory `μ` after `f 0`, …, `f (j - 1)` have been written to the cells from `dst`. -/
def wrote (μ : ℕ → ℤ) (dst : ℕ) (f : ℕ → ℤ) (j : ℕ) : ℕ → ℤ :=
  fun a => if dst ≤ a ∧ a < dst + j then f (a - dst) else μ a

/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

/-- A write outside the cells that have been written can be done first. -/
theorem update_wrote {y : ℕ} (hy : Outside dst j y) (w : ℤ) :
    Function.update (wrote μ dst f j) y w = wrote (Function.update μ y w) dst f j := by
  funext a
  by_cases ha : a = y
  · subst ha
    rw [Function.update_self, wrote_rest hy, Function.update_self]
  · simp only [wrote, Function.update_of_ne ha]

/-- Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`. -/
theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)

/-! ## The tactics -/

/-- A part of `light_keep`.  For each hypothesis `SameOn K' ν ν'` in the context whose condition
`K' x` follows by linear arithmetic, it adds the equation `ν' x = ν x`.  Then it replaces the writes
`Function.update ν b z` and `wrote ν dst f j` by their definitions. -/
macro "light_keep_steps" x:ident : tactic => `(tactic|
  (repeat ((with_reducible rename SameOn _ _ _ => h); (try have := h $x (by omega)); revert h)
   intros
   try simp only [Function.update_apply, wrote] at *))

/-- The work of `light_keep`; the lemmas in brackets are used when `K x` is simplified. -/
macro "light_keep_core" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (try refine SameOn.cell ?_
   intro x hx
   first
     | (light_keep_steps x; omega)
     | (simp [$ts,*] at hx; light_keep_steps x; omega)
     | (light_keep_steps x
        fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
          its condition K x does not follow from the hypotheses.")))

/-- `light_keep` proves `SameOn K μ μ'` (also written `SameOutside`, `Kept`, …) or `μ' b = μ b`.

It takes a cell `x` with `K x`.  Each hypothesis `SameOn K' ν ν'` in the context whose condition
`K' x` follows by linear arithmetic from the hypotheses yields the equation `ν' x = ν x`; the writes
`Function.update ν b z` and `wrote ν dst f j` are replaced by their definitions.  Then `μ' x = μ x`
has to follow from these equations.  If it does not, the tactic tries once more after simplifying
`K x`, which computes the lengths of lists.  The order of the hypotheses plays no role, and further
hypotheses do no harm. -/
macro "light_keep" : tactic => `(tactic| light_keep_core [])

/-- `light_keep [h₁, h₂, …]` is `light_keep` with the terms `h₁`, `h₂`, … added to the context; the
simplification of `K x` may rewrite with them as well.  So they can be promises, inequalities, or
lemmas on the length of a list. -/
macro "light_keep" "[" hs:term,* "]" : tactic =>
  `(tactic| ($[try have := $hs];* ; light_keep_core [$[$hs:term],*]))

/-- `light_order` proves `InOrder top [(a, n), …]` by linear arithmetic from the hypotheses in the
context, which may be of this form themselves. -/
macro "light_order" : tactic => `(tactic| (simp only [InOrder]; omega))

end Light
end
```

## ===== TCSlib/Programs/Light/Frames.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Frames.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Frames.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Assigns
import TCSlib.Programs.Light.Rules

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/

/-- The list of the locals after an assignment of z to local x.  A list that is too short is filled
up with zeros. -/
@[simp] def setLocal : List ℤ → ℕ → ℤ → List ℤ
  | [], 0, z => [z]
  | [], x + 1, z => 0 :: setLocal [] x z
  | _ :: l, 0, z => z :: l
  | a :: l, x + 1, z => a :: setLocal l x z

/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/

/-- The evaluation of e in σ stays within the limits and gives z. -/
@[simp] def Expr.Gives (lim : Limits) (σ : State) (e : Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z

/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

/-- `x := e`, where e gives z, for locals that are not given as a list. -/
theorem Ends.setVal {loc : ℕ → ℤ} {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨Function.update loc x z, μ⟩)
    (he : e.Gives lim ⟨loc, μ⟩ z := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set he.1 hT (he.2 ▸ h)

/-- `x := e ; s`, where e gives z, for locals that are not given as a list. -/
theorem Ends.setValThen {loc : ℕ → ℤ} {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨Function.update loc x z, μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨loc, μ⟩ z := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.setVal z h he le_rfl) hT

/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; light_side)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI

/-- **Counting loops whose body may change scratch variables.**  S j s μ' is the state before round
j, with the values s of the scratch variables and the memory μ'; I j holds of the memory.  The
counter of S j s μ' holds j, and S (j + 1) s μ' is S j s μ' with the counter increased; for a shape
fun j s μ' => ⟨frame [.., j, s], μ'⟩ both are proved by default.  The bound hi gives n, n fits in a
word, and the body keeps the shape and takes at most b steps. -/
theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; light_side)
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ' => ∃ s μ', σ' = S j s μ' ∧ I j μ') n b ⟨s₀, μ, first, start⟩ ?_ ?_ ?_
    hn hT
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    refine (round j s μ' hj hI).mono le_rfl ?_
    rintro _ ⟨s', μ'', rfl, hI'⟩
    exact ⟨counter j s' μ'', s', μ'', next j s' μ'', hI'⟩
  · rintro _ - ⟨s, μ', rfl, hI⟩
    exact done s μ' hI
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    exact bound j s μ' hj hI

end rules

/-! ## Locals by name, and locals whose values do not matter -/

/-- The list of the locals after several assignments, each given as a local and its value. -/
@[simp] def setLocals (l : List ℤ) : List (ℕ × ℤ) → List ℤ
  | [] => l
  | p :: ps => setLocals (setLocal l p.1 p.2) ps

/-- The local variables after several assignments, each given as a local and its value. -/
@[simp] def updateLocals (loc : ℕ → ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [] => loc
  | p :: ps => updateLocals (Function.update loc p.1 p.2) ps

/-- Several assignments, in terms of the list. -/
theorem updateLocals_frame : ∀ (ps : List (ℕ × ℤ)) (l : List ℤ),
    updateLocals (frame l) ps = frame (setLocals l ps)
  | [], _ => rfl
  | p :: ps, l => by
    rw [updateLocals, update_frame_setLocal, updateLocals_frame ps, setLocals]

/-- The list `l` of the locals, with the entries `xs` read from `loc`. -/
@[simp] def refreshLocals (l : List ℤ) (loc : ℕ → ℤ) : List ℕ → List ℤ
  | [] => l
  | x :: xs => refreshLocals (setLocal l x (loc x)) loc xs

/-- Reading a local of `refreshLocals l loc xs`. -/
theorem frame_refreshLocals (loc : ℕ → ℤ) (y : ℕ) : ∀ (xs : List ℕ) (l : List ℤ),
    frame (refreshLocals l loc xs) y = if y ∈ xs then loc y else frame l y
  | [], l => by simp
  | x :: xs, l => by
    rw [refreshLocals, frame_refreshLocals loc y xs, frame_setLocal]
    by_cases hx : y = x
    · subst hx
      simp
    · simp [hx]

/-- Two lists give the same local variables: they are equal up to zeros at the end. -/
def SameFrame (l m : List ℤ) : Prop := frame l = frame m

/-- The empty list gives the same locals as itself. -/
@[simp] theorem sameFrame_nil : SameFrame [] [] := rfl

/-- Two lists give the same locals if their heads are equal and their tails give the same locals. -/
@[simp] theorem sameFrame_cons_cons {a b : ℤ} {l m : List ℤ} :
    SameFrame (a :: l) (b :: m) ↔ a = b ∧ SameFrame l m :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩

/-- A list gives the same locals as the empty list if all its entries are 0. -/
@[simp] theorem sameFrame_cons_nil {a : ℤ} {l : List ℤ} :
    SameFrame (a :: l) [] ↔ a = 0 ∧ SameFrame l [] :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩

/-- The empty list gives the same locals as a list all of whose entries are 0. -/
@[simp] theorem sameFrame_nil_cons {b : ℤ} {m : List ℤ} :
    SameFrame [] (b :: m) ↔ b = 0 ∧ SameFrame [] m :=
  ⟨fun h => ⟨(congrFun h 0).symm, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1.symm
    | succ i => exact congrFun h.2 i⟩

/-- The local variables `loc` are those of the list `l`, except perhaps the locals `xs`. -/
def LocalsBut (xs : List ℕ) (l : List ℤ) (loc : ℕ → ℤ) : Prop :=
  ∀ y ∉ xs, loc y = frame l y

section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

/-- Locals that agree with a list except at `xs` are themselves given by a list. -/
theorem LocalsBut.eq_frame (h : LocalsBut xs l loc) : loc = frame (refreshLocals l loc xs) := by
  funext y
  rw [frame_refreshLocals]
  split_ifs with hy
  · rfl
  · exact h y hy

/-- An assignment, on both sides. -/
theorem LocalsBut.update (h : LocalsBut xs l loc) (x : ℕ) (z : ℤ) :
    LocalsBut xs (setLocal l x z) (Function.update loc x z) := by
  intro y hy
  rw [frame_setLocal, Function.update_apply, h y hy]

/-- Two lists agree except at `xs` if they give the same locals once these entries are copied.  For
two lists that are written out, the hypothesis amounts to the equations between their entries, where
an entry that is missing counts as 0. -/
theorem LocalsBut.of_eq (h : SameFrame (refreshLocals l (frame l') xs) l') :
    LocalsBut xs l (frame l') := by
  intro y hy
  have hread := frame_refreshLocals (frame l') y xs l
  rw [h, if_neg hy] at hread
  exact hread

/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

/-- **From locals that are described by `LocalsBut` to a list.**  The entries `xs` of the list are
read from `loc`. -/
theorem Ends.asFrame (h : LocalsBut xs l loc)
    (hs : Ends lim P d s ⟨frame (refreshLocals l loc xs), μ⟩ T Q) :
    Ends lim P d s ⟨loc, μ⟩ T Q := by
  rw [h.eq_frame]
  exact hs

/-- **A piece of text that assigns only the locals `xs`**, at the end of the program.  `h` is the
lemma about the piece.  Afterwards the locals are the list `l` with the entries `xs` read from the
locals `loc'` of which the lemma speaks. -/
theorem Ends.pieceTo (xs : List ℕ) (h : Ends lim P d s ⟨frame l, μ⟩ T₁ R)
    (done : ∀ loc' μ', R ⟨loc', μ'⟩ → Q ⟨frame (refreshLocals l loc' xs), μ'⟩)
    (hxs : s.assigns ⊆ xs := by simp) (hT : T₁ ≤ T := by light_time) :
    Ends lim P d s ⟨frame l, μ⟩ T Q := by
  refine h.keeping.mono hT ?_
  rintro ⟨loc', μ'⟩ ⟨hR, hkeep⟩
  have hloc : LocalsBut xs l loc' := fun y hy => hkeep y fun hmem => hy (hxs hmem)
  rw [hloc.eq_frame]
  exact done loc' μ' hR

/-- **A piece of text that assigns only the locals `xs`**, followed by the rest of the program,
which gets the steps that are left. -/
theorem Ends.pieceToThen (xs : List ℕ) (h : Ends lim P d s₁ ⟨frame l, μ⟩ T₁ R)
    (rest : ∀ loc' μ', R ⟨loc', μ'⟩ →
      Ends lim P d s₂ ⟨frame (refreshLocals l loc' xs), μ'⟩ (T - T₁) Q)
    (hxs : s₁.assigns ⊆ xs := by simp) (hT : T₁ ≤ T := by light_time) :
    Ends lim P d (s₁ ;; s₂) ⟨frame l, μ⟩ T Q :=
  Ends.next T₁ (Ends.pieceTo xs h rest hxs le_rfl) hT

/-! ## Counting loops with scratch variables -/

/-- **Counting loops whose body may change the scratch variables `xs`.**  Before round j the locals
are the given ones with j in the counter and anything in the scratch variables, and I j holds of the
memory.  The round says nothing about the locals.  The counter is not among the scratch variables,
so the body does not assign it.  The bound hi gives n, n fits in a word, and the body takes at most
b steps. -/
theorem Ends.forScratch {i : ℕ} {hi : Expr} {body : Stmt} (xs : List ℕ)
    (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (loc' μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ b fun σ' =>
        I (j + 1) σ'.mem)
    (done : ∀ loc' μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal (refreshLocals l loc' xs) i n), μ'⟩)
    (bound : ∀ (j : ℕ) (loc' μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ n := by intros; light_side)
    (hxs : body.assigns ⊆ xs := by simp) (hcounter : i ∉ xs := by simp)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  have shape (j : ℕ) {σ : State} (hσ : LocalsBut (i :: xs) l σ.loc) (hj : σ.loc i = j) :
      σ = ⟨frame (setLocal (refreshLocals l σ.loc xs) i j), σ.mem⟩ := by
    refine congrArg (State.mk · σ.mem) (funext fun y => ?_)
    rw [frame_setLocal, frame_refreshLocals]
    split_ifs with hy hy'
    · rw [hy, hj]
    · rfl
    · exact hσ y (by simp [hy, hy'])
  refine Ends.for (fun j σ => LocalsBut (i :: xs) l σ.loc ∧ I j σ.mem) n b
    ⟨fun y hy => Function.update_of_ne (by simp at hy; exact hy.1) _ _, start⟩ ?_ ?_ ?_ hn hT
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    refine (round j σ.loc σ.mem hj hI).keeping.mono le_rfl ?_
    rintro σ' ⟨hI', hkeep⟩
    have hsame (y : ℕ) (hy : y ∉ xs) : σ'.loc y = σ.loc y := by
      rw [hkeep y fun hmem => hy (hxs hmem), ← shape j hσ hc]
    refine ⟨(hsame i hcounter).trans hc, fun y hy => ?_, hI'⟩
    simp only [List.mem_cons, not_or] at hy
    exact ((Function.update_of_ne hy.1 _ _).trans (hsame y hy.2)).trans
      (hσ y (by simp [hy.1, hy.2]))
  · rintro σ hc ⟨hσ, hI⟩
    rw [shape n hσ hc]
    exact done σ.loc σ.mem hI
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    exact bound j σ.loc σ.mem hj hI

end

end Light
end
```

## ===== TCSlib/Programs/Light/Tactics.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Tactics.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Tactics.lean`, with imports remapped;
* documentation: qualify the opacity promise for the `with_reducible` replacement (fidelity gate, finding 2);
* documentation: as above, for the module-level discussion;
* replaced the tactic combinator `with_unfolding_none`, absent in v4.25, by `with_reducible`;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Calls

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
(Vendoring note: at our Lean v4.25.0 pin the closing combinator is `with_reducible`, so a
*reducible* definition, such as an `abbrev`, may still unfold.)

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

/-! ## Records -/

/-- `light_facts H₁ H₂ …` adds every field of the records `H₁`, `H₂`, … to the context, as
hypotheses without names.  A record inside a record is named like any other:
`light_facts H H.limits`.  The records themselves stay: what is taken apart is the copy `id H`. -/
macro "light_facts" hs:(ppSpace colGt term:max)+ : tactic =>
  `(tactic| ($[obtain ⟨⟩ := id $hs];*))

/-! ## One statement -/

/-- Brackets to the right, and a `skip` before the rest of the program is dropped.  No definition is
opened, except that at our Lean v4.25.0 pin reducible definitions (abbreviations) may unfold: the
upstream no-unfolding combinator, absent in v4.25, is replaced by `with_reducible` (vendoring note). -/
macro "light_assoc" : tactic =>
  `(tactic| repeat with_reducible first | refine Ends.seqAssoc ?_ | refine Ends.skipThen ?_)

/-- Brings the program into the form "first statement, then the rest": a program that is defined as
a sequence is written out, and a `skip` is put behind a single statement. -/
macro "light_head" : tactic =>
  `(tactic| ((first | refine Ends.seqSelf ?_ | refine Ends.skipLast ?_); light_assoc))

/-- `light_skip` treats a program of which only `skip` is left: the goal becomes `Q` of the state.
-/
macro "light_skip" : tactic => `(tactic| with_reducible refine Ends.skip ?_)

/-- `light_set z using h₁, h₂` treats the assignment `x := e` at the head of the program, where `e`
has the value `z`; `h₁`, `h₂` go to `light_side` and `light_time`. -/
macro "light_set " z:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.setToThen $z ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      try light_skip)

/-- `light_set z` treats the assignment `x := e` at the head of the program, where `e` has the value
`z`. -/
macro "light_set " z:term:max : tactic => `(tactic| light_set $z using)

/-- `light_store b z using h₁, h₂` treats the store `mem[a] := e` at the head of the program, where
`a` has the value `b`, a natural number, and `e` the value `z`; `h₁`, `h₂` go to `light_side` and
`light_time`. -/
macro "light_store " b:term:max ppSpace z:term:max " using "
    hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.storeToThen $b $z ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      try light_skip)

/-- `light_store b z` treats the store `mem[a] := e` at the head of the program, where `a` has the
value `b`, a natural number, and `e` the value `z`. -/
macro "light_store " b:term:max ppSpace z:term:max : tactic => `(tactic| light_store $b $z using)

/-- `light_if h₁ h₂ : p using h₃, h₄` treats the branch at the head of the program, whose test says
`p`.  It leaves two goals: the first side of the branch with `h₁ : p`, and the second side with
`h₂ : ¬ p`.  One of the side conditions is the equivalence of the test and `p`; `h₃`, `h₄` go to
`light_side` and `light_time`. -/
macro "light_if " h₁:ident ppSpace h₂:ident " : " p:term " using "
    hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.iteIffThen $p (fun $h₁ => ?_) (fun $h₂ => ?_) ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      all_goals light_assoc)

/-- `light_if h₁ h₂ : p` treats the branch at the head of the program, whose test says `p`.  It
leaves two goals: the first side of the branch with `h₁ : p`, and the second side with `h₂ : ¬ p`.
One of the side conditions is the equivalence of the test and `p`. -/
macro "light_if " h₁:ident ppSpace h₂:ident " : " p:term : tactic =>
  `(tactic| light_if $h₁ $h₂ : $p using)

/-- `light_call fact using h₁, h₂ with r μ' hR` treats the call `x := p(args)` at the head of the
program, where `fact : Meets lim P p (d + 1) vals μ T' R` says what the procedure does.  The
patterns after `with` name the result, the memory after the call, and what `R` says about them;
`h₁`, `h₂` go to `light_side`, which shows that the arguments have the values `vals`, and to
`light_time`.  A `fact` that still asks for a depth `d'` and a bound on it,
`∀ d', d' + k ≤ lim.depth → Meets lim P p d' vals μ T' R`, is accepted as well. -/
macro "light_call " fact:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* " with"
    pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic|
    focus
      light_head
      first
        | refine Ends.callToThen ($fact _ (by omega)) ?_ ?_ ?_ ?_
        | refine Ends.callToThen $fact ?_ ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => omega
      on_goal -1 => light_side [$hs,*]
      on_goal -1 => (rintro $pats*; try light_skip))

/-- `light_call fact with r μ' hR` treats the call `x := p(args)` at the head of the program, where
`fact : Meets lim P p (d + 1) vals μ T' R` says what the procedure does.  The patterns after `with`
name the result, the memory after the call, and what `R` says about them.  A `fact` that still asks
for a depth `d'` and a bound on it, `∀ d', d' + k ≤ lim.depth → Meets lim P p d' vals μ T' R`, is
accepted as well. -/
macro "light_call " fact:term:max " with" pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic| light_call $fact using with $pats*)

/-- `light_piece fact using t₁, t₂ with σ' hR` treats a piece `s₁` at the head of the program, where
`fact : Ends lim P d s₁ σ T₁ R` says what the piece does.  The patterns after `with` name the state
after the piece and what `R` says about it; `t₁`, `t₂` go to `light_time`. -/
macro "light_piece " fact:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* " with"
    pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic|
    focus
      light_assoc
      first | refine Ends.pieceThen $fact ?_ ?_ | refine Ends.pieceLast $fact ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => rintro $pats*)

/-- `light_piece fact with σ' hR` treats a piece `s₁` at the head of the program, where
`fact : Ends lim P d s₁ σ T₁ R` says what the piece does.  The patterns after `with` name the state
after the piece and what `R` says about it. -/
macro "light_piece " fact:term:max " with" pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic| light_piece $fact using with $pats*)

/-- `light_piece fact` treats a piece at the end of the program, where
`fact : Ends lim P d s σ T₁ Q` says that the piece does what is to be shown. -/
macro "light_piece " fact:term:max : tactic =>
  `(tactic| focus (refine Ends.pieceLast $fact (fun _ h => h) ?_; on_goal -1 => light_time))

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Pass.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Pass.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Pass.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Rules

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- for c < len: dst[c] := e.  The local c is the counter. -/
abbrev pass (c : ℕ) (len dst e : Expr) : Stmt := Stmt.for c len (.store (dst +' v c) e)

variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]

/-- A pass that writes g of the entries of a list leaves the list mapped by g. -/
theorem seg_wrote_map (g : ℤ → ℤ) (L : List ℤ) :
    Seg (wrote μ dst (fun i => g (L.getD i 0)) L.length) dst (L.map g) :=
  seg_wrote (List.length_map g) fun i hi => by
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by simpa using hi)]

/-- **The rule for a pass.**  The locals x and y hold the length n and the address dst.  In round j
the locals are the given ones with j in the counter, and the memory is `wrote μ dst f j`; there the
expression e has to be safe and have the value f j. -/
theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by light_time) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
  -- Round j: dst[j] := e.
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Copy.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Copy.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Copy.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Lib.Pass

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy

/-- The local variables of copy: the arguments src, dst and n, and the counter. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Idx : ℕ := 3

end Copy

open Copy in
/-- copy(src, dst, n): for i < n, dst[i] := src[i]. -/
def copyBody : Stmt := pass Idx (v Len) (v Dst) (M (v Src +' v Idx))

/-- The time of copy. -/
@[simp] def copyTime (n : ℕ) : ℕ := 16 * n + 6

/-- **copy(src, dst, n)** copies the n cells from src to dst and changes nothing else. -/
theorem copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by light_keep⟩ hw hdst rfl rfl
    (hT := by light_time [copyTime]))
  -- Round i reads src[i], which no earlier round has written.
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest (by omega)
  light_side [hread]

/-! ## fill -/

namespace Fill

/-- The local variables of fill: the arguments dst, n and x, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Len : ℕ := 1
@[inherit_doc Dst] abbrev Val : ℕ := 2
@[inherit_doc Dst] abbrev Idx : ℕ := 3

end Fill

open Fill in
/-- fill(dst, n, x): for i < n, dst[i] := x. -/
def fillBody : Stmt := pass Idx (v Len) (v Dst) (v Val)

/-- The time of fill. -/
@[simp] def fillTime (n : ℕ) : ℕ := 13 * n + 6

/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by light_side)
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by light_keep⟩
    hw hdst rfl rfl (hT := by light_time [fillTime]))

end Light
end
```

## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

```
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header;
* re-proved `moveInputPos_leftBoundary`, `moveInputPos_rightBoundary`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_pos_of_ne_right` and `inputSymbolInner` for our
  mathlib pin (`dite_eq_left`/`dite_eq_right` are absent there), statements unchanged
  (2026-09-16);
* added lemmas that are not upstream, the specification API (user, 2026-10-16): the fields of
  `Cfg.init` (`Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`, generated
  by `simps` without the `simp` attribute), `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`
  and `Cfg.workTapeSymbols_eq`;
* added lemmas that are not upstream, the brief-inventory API's round 3 (user, 2026-10-17): the
  fields of `Action.apply` other than its work tapes (`Action.apply_state`, `_inputPos`,
  `_workTapePos`, `_output`, generated by `simps` without the `simp` attribute; the work tapes
  have the colocated `Action.apply_workTapes` equation).
The upstream definitions and theorems are otherwise unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

**The specification API** (user, 2026-10-16): `Turing.Cfg.init_state`, `_inputPos`,
`_workTapes`, `_workTapePos` and `_output`, the initial configuration's fields as equations.
`Turing.Cfg.inputSymbol_of_zero`, `Turing.Cfg.inputSymbol_of_end` (with `inputSymbolInner`) and
`Turing.Cfg.workTapeSymbols_eq`: the heads' readings.

**The brief-inventory API, round 3** (user, 2026-10-17): `Turing.Action.apply_state`,
`_inputPos`, `_workTapePos` and `_output`, the applied action's fields as equations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- At input position `0`, the blank left of the input, the input head reads blank:
`cfg.inputSymbol = none` (the specification API, user 2026-10-16). -/
theorem Cfg.inputSymbol_of_zero {cfg : Cfg k Symbol State input} (h : cfg.inputPos = 0) :
    cfg.inputSymbol = none := by
  simp [Cfg.inputSymbol, h]

/-- At input position `input.length + 1`, the blank right of the input, the input head reads
blank: `cfg.inputSymbol = none` (the specification API, user 2026-10-16). -/
theorem Cfg.inputSymbol_of_end {cfg : Cfg k Symbol State input}
    (h : cfg.inputPos.val = input.length + 1) : cfg.inputSymbol = none := by
  have he : cfg.inputPos = Fin.last (input.length + 1) := Fin.ext h
  simp [Cfg.inputSymbol, he]

/-- Work head `i` reads the cell under it:
`cfg.workTapeSymbols i = cfg.workTapes i (cfg.workTapePos i)`
(the specification API, user 2026-10-16). -/
theorem Cfg.workTapeSymbols_eq (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.workTapeSymbols i = cfg.workTapes i (cfg.workTapePos i) :=
  rfl

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/-! The specification API (user, 2026-10-16): `Turing.Cfg.init`'s fields as equations
(`Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`), without the
`simp` attribute. -/
attribute [simps (config := { isSimp := false })] Cfg.init

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-! The brief-inventory API, round 3 (user, 2026-10-17; the round-2 gate's finding 1): the fields
of `Turing.Action.apply` as equations, generated by `simps` without the `simp` attribute. The
state is the action's, `(a.apply c).state = a.state`; the input head moves by `moveInputPos`,
`(a.apply c).inputPos = moveInputPos c.inputPos a.inputTape`; each work head moves by its
displacement, `(a.apply c).workTapePos i = c.workTapePos i + (a.workTapes i).2`; the emission is
appended, `(a.apply c).output = c.output ++ a.output.toList`. The work tapes are
the colocated `Turing.Action.apply_workTapes` equation. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapePos output] Action.apply

/-- **Optional-write normalization:** applying an action rewrites each
work tape at its head with the proposed write, defaulting to the existing read
when the action declines to write. An explicit `some none` write remains an
erase, while an outer `none` writes back the scanned symbol unchanged. Holds
for every alphabet, state type, action, configuration, and tape index — no
finiteness, liveness, or computation hypothesis. -/
lemma Action.apply_workTapes {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header;
* corrected the module docstring's attribution of the non-blank space measure
  ([AB09, Def 4.1] counts visited cells for `SPACE`, non-blank cells only for
  `NSPACE`); comments only, no code change (2026-10-08);
* added `timed_input_bound`, promoted from the campaign (D6, 2026-10-05);
* added lemmas that are not upstream, the specification API (user, 2026-10-16):
  `initCfg_eq` and `mem_visitedByTapeHead_iff`, and the split lemmas
  `visitedByTapeHead_add_subset`, `visitedByTapeHead_step_subset`, moved here from
  `Build/StepBlock` with their statements and proofs (design note O9);
* added `step_of_some` and `outputSymbol_of_some`, the live-state cases beside the upstream
  `step_of_halt` and `outputSymbol_of_halt`, the brief-inventory API's round 3 (user,
  2026-10-17).
* added `spaceUsed_eq_sum`, the space measure as the sum of the per-tape counts, so that
  consumers read `spaceUsed` through an equation;
* added `spaceUsedByTape_eq_card`, a tape's space as the number of cells its head visited, so
  that consumers read `spaceUsedByTape` through an equation.
* added `MultiTapeTM.runFrom_one`, a one-step run as one machine step, beside the upstream
  `runFrom_zero` and `runFrom_succ_eq_step`, so that every one-step site cites one public lemma
  (dedup family RO-1; user, 2026-11-12).
* added `MultiTapeTM.indicator_of_mem` and `MultiTapeTM.indicator_of_not_mem`, the two values of
  `indicator`, so that consumers read it through equations.
The upstream definitions and theorems are otherwise unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
only consider the number of cells that contain a non-blank symbol at some point in the
execution or the number of cells written to. ([AB09] itself splits: Definition 4.1 counts
_visited_ work-tape locations for `SPACE` — the measure used here — but _nonblank_
locations for `NSPACE`.) This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

**The specification API** (user, 2026-10-16): `Turing.MultiTapeTM.initCfg_eq`,
`Turing.MultiTapeTM.mem_visitedByTapeHead_iff`,
and the split lemmas `visitedByTapeHead_add_subset` and `visitedByTapeHead_step_subset` (moved
here from `Build/StepBlock`, design note O9).

**The brief-inventory API, round 3** (user, 2026-10-17): `Turing.MultiTapeTM.step_of_some` and
`Turing.MultiTapeTM.outputSymbol_of_some`, a live step and its emission as equations.

**The space measure as a sum:** `Turing.MultiTapeTM.spaceUsed_eq_sum`, the cells visited on each
work tape, summed over the tapes.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- A machine's initial configuration on `input` is `Cfg.init` at its start state:
`tm.initCfg input = Cfg.init tm.q₀ input` (the specification API, user 2026-10-16). -/
theorem initCfg_eq (input : List Symbol) : tm.initCfg input = Cfg.init tm.q₀ input :=
  rfl

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- **A live step applies the chosen action** (the brief-inventory API, round 3; the round-2
gate's finding 1): at a live state `q` one step applies the transition table's action for the
scanned symbols, `cfg.state = some q →`
`tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg`. -/
theorem step_of_some {cfg : Cfg k Symbol State input} {q : State} (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- A one-step run from any configuration is exactly one machine step. -/
theorem _root_.Turing.MultiTapeTM.runFrom_one {k : ℕ} {Γ S : Type*} {x : List Γ}
    (tm : MultiTapeTM k Γ S) (c : Cfg k Γ S x) : tm.runFrom c 1 = tm.step c := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The physical input head can move right by at most one cell per step.
**Proof sketch.** Clamping never increases a proposed position. Check the
three movements, then induct over the run, treating halted steps as stationary. -/
lemma timed_input_bound (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).inputPos.val ≤ cfg.inputPos.val + t := by
  have hm (p : Fin (input.length + 2)) (m : SignType) :
      (moveInputPos p m).val ≤ p.val + 1 := by
    dsimp only [moveInputPos]
    split <;> dsimp <;> cases m <;> simp_all [SignType.cast] <;> omega
  have hstep (d : Cfg k Symbol State input) :
      (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hs : d.state with
    | none => simp only [MultiTapeTM.step, hs]; omega
    | some q =>
      simpa only [MultiTapeTM.step, hs, Action.apply] using
        hm d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (hstep _).trans (by omega)

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- **A live step emits the chosen action's symbol** (the brief-inventory API, round 3; the
round-2 gate's finding 1): at a live state `q`, `cfg.state = some q →`
`tm.outputSymbol cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output`. -/
theorem outputSymbol_of_some {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    tm.outputSymbol cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output := by
  unfold outputSymbol
  rw [h]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **The space measure as a sum**: the space used up to step `t` is the sum, over the work
tapes, of the number of cells each head visited up to step `t`. -/
theorem spaceUsed_eq_sum (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i :=
  rfl

/-- **A tape's space as a count**: the space tape `i` uses up to step `t` is the number of cells
its head visited up to step `t`. -/
theorem spaceUsedByTape_eq_card (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i = (tm.visitedByTapeHead cfg t i).card :=
  rfl

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

/-- **Membership in a visited set** (the specification API, user 2026-10-16): a cell is visited by
head `i` within `t` steps exactly when the head stands on it at some time `u ≤ t`.

**Proof sketch.** `Turing.MultiTapeTM.visitedByTapeHead` is the image of the head positions over
`Finset.range (t + 1)`. -/
theorem mem_visitedByTapeHead_iff (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (p : ℤ) :
    p ∈ tm.visitedByTapeHead cfg t i ↔ ∃ u ≤ t, (tm.runFrom cfg u).workTapePos i = p := by
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

/-- **Visited cells split at an intermediate time** (moved here from `Build/StepBlock`, design
note O9, with the specification API, user 2026-10-16): the cells visited by head `j` in
`T₁ + T₂` steps from `d` are those visited in the first `T₁` steps, together with those visited
in `T₂` steps from where the run is at time `T₁`.

**Proof sketch.** A visiting time `u ≤ T₁ + T₂` is either at most `T₁`, or `T₁ + v` with
`v ≤ T₂`, and then run additivity identifies the configuration. -/
lemma visitedByTapeHead_add_subset {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (d : Cfg m Bool S x) (T₁ T₂ : ℕ) (j : Fin m) :
    M.visitedByTapeHead d (T₁ + T₂) j ⊆
      M.visitedByTapeHead d T₁ j ∪ M.visitedByTapeHead (M.runFrom d T₁) T₂ j := by
  intro p hp
  simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_union, Finset.mem_image,
    Finset.mem_range] at hp ⊢
  obtain ⟨u, hu, rfl⟩ := hp
  by_cases hle : u ≤ T₁
  · exact Or.inl ⟨u, by omega, rfl⟩
  · refine Or.inr ⟨u - T₁, by omega, ?_⟩
    rw [← MultiTapeTM.runFrom_add]
    congr 2
    omega

/-- **Visited cells after the first step** (moved here from `Build/StepBlock`, with the
specification API): the cells visited in `t` steps from the successor of `c`, and `c`'s own head
cell, are among those visited in `t + 1` steps from `c`.

**Proof sketch.** Shift every visiting time by one; time `0` gives `c`'s cell. -/
lemma visitedByTapeHead_step_subset {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (c : Cfg m Bool S x) (t : ℕ) (j : Fin m) :
    insert (c.workTapePos j) (M.visitedByTapeHead (M.step c) t j) ⊆
      M.visitedByTapeHead c (t + 1) j := by
  intro p hp
  simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range] at hp ⊢
  rcases hp with rfl | ⟨v, hv, rfl⟩
  · exact ⟨0, by omega, by rw [MultiTapeTM.runFrom_zero]⟩
  · exact ⟨v + 1, by omega, by rw [MultiTapeTM.runFrom_succ_eq_step]⟩

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

open Classical in
/-- The defining equation of `indicator`: `indicator L = fun x => if x ∈ L then true else false`
(classical decidability, as in the definition). -/
theorem indicator_def {α : Type*} (L : Set α) :
    (indicator L : α → Bool) =
      (fun x => if x ∈ L then true else false :
        α → Bool) := rfl

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The indicator of a set is `true` at its members. -/
theorem indicator_of_mem {α : Type*} {L : Set α} {x : α} (hx : x ∈ L) : indicator L x = true := by
  classical
  exact if_pos hx

/-- The indicator of a set is `false` away from it. -/
theorem indicator_of_not_mem {α : Type*} {L : Set α} {x : α} (hx : x ∉ L) :
    indicator L x = false := by
  classical
  exact if_neg hx

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
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
