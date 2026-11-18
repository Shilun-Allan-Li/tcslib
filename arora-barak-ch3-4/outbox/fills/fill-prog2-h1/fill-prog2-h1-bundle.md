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

## ===== campaign/items/ram-tm/briefs/fill-prog2-h1.md =====

# PROG-2 fill H1 (Codex): input, output and coins in the Light language core

Read `COMMON.md` (bundled). Its rules bind **except where this brief replaces them**: H1 edits
vendored definitions in place, so the statement freeze and the no-new-surface rule are replaced
by the frozen mirror below. **Fill name:** `fill-prog2-h1`. **Base:** the commit given in the
dispatch prompt, on `complexity/ram-simulation`.

## What this is

The light language gains four constructs, as the extended word RAM already has them:
`x := inBit e` (the input bit at position `e`, `0` off the input), `emit e` (append the bit
"`e ≠ 0`"), `x := coin` (the next coin) and `x := half e` (`⌊e / 2⌋`). `Light.Exec` gains two
indices, the bits emitted `o` and the coins consumed `r`. `Light.Ends` keeps its type, so `Meets`
and the library routines keep working. A new file `Light/IO.lean` holds the stream-aware logic.

The signatures are **frozen**. A statement gate on a mirror (gate 167) cleared them after three
rounds: `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt` (bundled, 1,311 lines). Its header
maps every mirror name to its in-place name. The design is `campaign/items/ram-tm/PROG2-DESIGN.md`
(bundled; §1–§4). Gate 167's findings and resolutions are bundled for context.

H1 is the **language core**. Job H2 follows with the compiler: it moves the code type to
`List XInstr` and proves the compiler's new cases and the deliverables. H1 leaves those cases
as disclosed admissions (below).

## Targets: what lands

Land every mirror declaration below under its in-place name, with the mirror's statement after
the renaming (`XStmt` ↦ `Light.Stmt`, `XExec` ↦ `Light.Exec`, `XEnds` ↦ `Light.Ends`,
`XLimits` ↦ `Light.Limits`, `XProgram` ↦ `Light.Program`, `XMeets` ↦ `Light.Meets`, and so on).
The mirror's line numbers are given for finding them.

1. **Syntax and semantics, in place** (`Light/Syntax.lean`): the four constructors of `Stmt`
   (134); the field `input : List Bool` of `Limits` (163); `inBitVal` and `inBitVal_eq`
   (169–172); `Exec` with the indices `o r` and the four new rules (180).
2. **The six inductions over `Exec`, in place** (219–330): `Exec.append` (`Logic`),
   `Exec.loc_eq_of_notMem_assigns` (`Assigns`), `Exec.bounded` with its new hypothesis
   `1 ≤ lim.word` and `Exec.mem_outside` (`RunsStayInLimits`); and, new in `Light/IO.lean`,
   `Exec.coins_length_le`, `Exec.output_length_le`, `Exec.det` and the four inversions
   `Exec.inBit_inv`, `emit_inv`, `coin_inv`, `half_inv`.
3. **The logic** (334–512): `Ends` redefined in place with the same type (`Logic`); new in
   `Light/IO.lean`: `EndsIO`, `MeetsIO`, their readers (`endsIO_iff`, `meetsIO_iff`), the
   rules `EndsIO.toEnds`, `mono`, `skip`, `set`, `store`, `seq`, `ite`, `whileStep`,
   `whileDone`, `call`, `inBit`, `emit`, `coin`, `half`, `EndsIO.callLast`, and `Ends.coin`.
   `xEnds_iff` and `xMeets_iff` land as new readers beside `Ends` and `Meets`
   in `Logic` (it has none today); name them `ends_iff` and `meets_iff`.
4. **Relocation, in place** (555–597, `Light/Renumber.lean`): `Stmt.shift` gains four arms and
   `Exec.shift` four cases and the indices. `XProgram.behind` is the existing
   `Program.behind`, unchanged.
5. **Lifting I/O-free code** (599–727, new in `Light/IO.lean`): `Stmt.silent`, `Stmt.calls`,
   their readers (`silent_seq` … `calls_leaf`), `Program.SilentSet` and `silentSet_iff`,
   `Exec.traces_nil`, `SilentSet.append`, `silent_shift`, `calls_shift`, `SilentSet.behind`,
   `EndsIO.ofEnds`, `MeetsIO.ofMeets`.
6. **Streams** (738): `EndsIO.take_iff`, in `Light/IO.lean`.
7. **Permanent checks** (1265–1293), as theorems in `Light/IO.lean`: `inBitVal_boundary`,
   `half_boundary`, `check_two_coins`, `check_det_length`, `check_bounded_needs_word`.

**Not in H1:**
- the mirror-only declarations `XStmt.ofStmt`, `XExec.ofExec` and `XSetting.xlim`;
- `xmainStmt` (it is the existing `Light.mainStmt`);
- `AcceptsND`, `acceptProb` and their readers, and `acceptProb_eq_of_le`: H2 lands them in a
  Complexity-side home;
- everything from line 753 on except the five checks above: the compiler, H2.

## Rules for this round (in place of COMMON rules 1 and 3)

- **Statements.** Every landed declaration's statement is the mirror's, after the renaming,
  byte for byte up to that renaming and whitespace. Every other existing statement stays
  byte-identical, except where the four new constructors or the two new indices force a change.
  Each forced change is listed in `REPORT.md` with its reason: an added match arm, the indices
  in an `Exec` hypothesis, or the new hypothesis of `Exec.bounded`. A mirror statement you
  believe false is an **E-STATEMENT** stop.
- **Public surface:** exactly the declarations above, plus pure `rfl`/`Iff.rfl` readers beside a
  definition in its home file. Everything else you add is `private`.
- **Owned files:**
  - in `TCSlib/Programs/Light/`: `Syntax`, `Logic`, `Rules`, `Assigns`, `RunsStayInLimits`,
    `Renumber`, and the new `IO.lean`;
  - **witness lines only** (no statement change) in `Calls`, `Frames`, `Regions`, `TMProc`
    and `Lib/*`, wherever the new indices reach an `Exec` witness or a `cases`;
  - **the compiler, minimally:** `Compiler/StatementCode`, `Compiler/Simulation` and
    `Compiler/WholeProgram`. In them, thread the indices through the existing proofs and give
    `Stmt.size` and `Stmt.width` their final values for the new arms (the mirror's table at
    lines 84–93 and `xcompileStmt`'s widths). The code type stays `List Instr`.
  - Keep each file under 600 lines; split `IO.lean` if needed (`Light/IO/*.lean`).
- **Temporary admissions, and only these:** the compiler cases for the four new constructors:
  `compileStmt`'s four new arms, and the four new cases of `length_compileStmt`, the
  `Simulation` lemmas and `sim`. H2 replaces them all. List every `sorry` site in `REPORT.md`.
  Nothing outside `Compiler/` may reach an admission.
- **Vendored headers.** Each edited vendored file's header gains a "Local modifications"
  bullet naming the change (the four constructs; the indices), in the style of the existing
  bullets. `IO.lean` is new: give it the repository's standard header, citing [AFM26] as the
  language it extends.
- **Rule 10.** Proofs between vendored files are exempt (Seyoon, 2026-11-18). `IO.lean` is a
  TCSlib file: it reads Light definitions through published equations and lemmas. Add a
  missing pure reader beside its definition in the home file.
- **Cite, do not re-prove.** `Ends`'s rules and the `light_*` tactics stay the route for
  I/O-free code; `EndsIO.ofEnds` lifts them. Do not copy an `Ends` rule's proof for its
  `EndsIO` twin: derive the twin from the rule, or factor a private helper.

## REPORT.md, in addition to COMMON's checklist

- **The landing table:** every target, its in-place name and file, and its statement's diff
  against the mirror's after renaming (it should be empty).
- **Forced changes:** every existing statement that changed, and why.
- **Admissions:** every `sorry` site, all within the compiler's new cases. Give an admission
  walk (types and values) for the IO roots `EndsIO.ofEnds`, `MeetsIO.ofMeets`, `Exec.det`,
  `EndsIO.take_iff` and `EndsIO.callLast` (empty), and for `Light.exists_tmProc` (empty).
- **The axiom prints** for every landed theorem.
- **The copy screen:** `scripts/copy-text-screen-v3.py` over your owned files, `Light/Logic`
  and `Light/Rules` included. Report every pair at or above half, with the reason it remains.
- **Size:** line counts per file, before and after.

## Downstream check

Every module that imports `TCSlib.Programs.Light.Syntax`, directly or not: the Light closure,
the compiler, `TMProc` and its users in `Complexity/RAMSimulation`. Each must elaborate with no
new error. Each must have no new admission outside the compiler's new cases.

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

## ===== campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.Assigns
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.RunsStayInLimits
import TCSlib.Programs.Light.Compiler.WholeProgram
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.RAMSimulation.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Light with input and output: signatures (statement mirror for the PROG-2 statement gate, round 3)

**Status: a sorried, self-contained mirror, not for landing.** Round 2 answered gate 167
(G167-01 to G167-06, and the notes N2, N4, N8); round 3 answers round 2's G167-02, -05, -07
and -08. The real edit set changes the vendored
`Light.Stmt`, `Light.Exec`, `Light.Limits` and `Light.Ends` in place (design §15c; Option A).
Because a draft cannot change compiled modules, this file mirrors them in the namespace
`TCSlib.Draft.PROG2` under the names `XStmt`, `XExec`, `XLimits` and `XEnds`, and states the new
rules, readers and compiler contracts over the mirror. `Light.Compiler.Fits` is **unchanged**:
the input length is a separate hypothesis `|x| ≤ lim.word` (N2).

## Which declarations land

Every declaration lands under its in-place name (`XStmt` ↦ `Light.Stmt`, `XExec` ↦ `Light.Exec`,
`xcompileStmt` ↦ `Light.Compiler.compileStmt`, `xsim` ↦ `Light.Compiler.sim`, and so on), except
those marked **mirror only** in their docstrings:

* `XStmt.ofStmt` and `XExec.ofExec`, which audit conservativity over the October mirror and have
  no in-place counterpart (the vendored syntax *is* the extended syntax after the edit);
* `XSetting.xlim`, plumbing between the mirror's two records: in place `Light.Limits` carries
  `input` itself (`XLimits` ↦ `Light.Limits`), the setting's `input` field is `lim.input`, and
  `S.xlim` is `S.lim`. (G167-05; round 4.)

## The compiler's type boundary (G167-02)

* **Stay `List Instr`, unchanged:** `compileExpr`, `compileCond`, `argsCode`, `frameInit`,
  `newFrame`, `callCode`, `epilogue`, `dispatcher`, `headStraight`, `tailCode`, `startStraight`
  and their lemmas. So `Compiler/Expressions`, `Conditions`, `CallFrames`, `Cells` and
  `Dispatcher` are untouched. `Compiler/StartUp` keeps its straight-line code and memory
  calculations, but `steps_start` changes (below).
* **Become `List XInstr`:** `compileStmt` (old constructs as `(…).map .base`, the four new ones
  below), `bodiesCode`, `compileProgram`, and the code field of `Setting`.
* **The transport:** a segment `l.map .base` placed in `code` (`XCodeAt`) is a segment `l` of
  `code.proj` (`XCodeAt.proj`), so the unchanged straight-line and call lemmas apply to
  `S.code.proj`, and their `Steps` runs lift to `XSteps` runs of `S.code` by
  `WordRAM.XSteps.of_steps_proj` (tier 0, proved). Base instructions leave the output and the
  coin count alone (`WordRAM.xstep_map_base`).
* **Changed files:** `Compiler/StatementCode` (`compileStmt`, `Stmt.size`, `Stmt.width` and four
  width readers), `Compiler/ProgramCode` (round 4: `bodiesCode`, `compileProgram` and
  `mainCode`, the outermost statement's code followed by `tailCode` under `.base`, become
  `List XInstr`; the code-location lemmas `codeAt_headCode` … `codeAt_startCode` move to the
  extended code as `xcodeAt_*`, and so do `codeAt_bodiesCode` and `codeAt_bodies`, whose `code`
  becomes an `XProgram` with `XCodeAt` throughout, for its one caller, `WholeProgram`'s
  `bodyAt`; the layout definitions `frameSize`, `mainPos`, `tailPos`, `firstBody`, `entries`,
  `endPos`, `dispPos`, `codeLayout` and the `List Instr` parts `headStraight`, `headCode`,
  `tailCode`, `poolCode`, `zeroCode`, `frameCode`, `startStraight`, `startCode` keep their types),
  `Compiler/StartUp` (`steps_start`, which is stated over `compileProgram`: restated over its
  projection, `steps_start_proj`, and as an extended run, `xsteps_start`; its memory calculations
  `startMem`, `rel_startMem`, `agreeOutside_startMem` stay over `List Instr`; round 3,
  G167-02), `Compiler/Simulation` (`Setting`, `Start`, `Finished`, `Simulates`, `sim` and four
  `sim_*`), `Compiler/WholeProgram` (`compileProgram_correct` and the deliverables below), and
  `Programs/WordRAM/Extended` (`XStepsIn.mono`, `XStepsIn.trans`; round 3, G167-07).
* **The footprint is part of the simulation** (round 3, G167-07). Endpoint agreement cannot bound
  the cells a run reads, so `XFinished.run` is an `XStepsIn` run within the setting's cell interval
  `XSetting.cells = [-max(2Q, 25 + 4·disp), lim.space)`, which holds every cell a compiled step
  reads or writes: the scratch and constant cells, the pool, the stack, and memory below
  `lim.space` (a safe address). H2 proves it per segment: `stepsIn_straight` for straight-line
  code, footprint versions of the expression, condition and call lemmas, the new instructions'
  `touches` (`T₀` and the read cell), and `XStepsIn.mono`/`XStepsIn.trans` to compose.
  These are the **footprint companions H2 adds** beside the unchanged base-instruction lemmas,
  which keep their statements: footprint versions of the expression, condition, call-frame
  and dispatcher runs (the start-up's is `xsteps_start`), with state-dependent address bounds
  for indirect loads and stores. (Round 4.)
* **Boundedness:** `Exec.bounded` needs `1 ≤ lim.word` (`inBit` and `coin` write `1`), so `sim`
  and the whole-program theorems take it as a hypothesis; `Light.Std` gives `100 ≤ word`.

## The compiled statements (G167-06)

With `store x := [sub ADDR FP (pool 2x), store ADDR T₀]`, the assignment's local store:

| Statement | Code | Length |
|---|---|---|
| `x := inBit e` | `compileExpr e 0`, `rdIn T₀ T₀`, `store x` | `e.size + 3` |
| `emit e` | `compileExpr e 0`, `emit T₀` | `e.size + 1` |
| `x := coin` | `coin T₀`, `store x` | `3` |
| `x := half e` | `compileExpr e 0`, `half T₀ T₀`, `store x` | `e.size + 3` |

## The deliverables (G167-03, all three parts; G167-04)

* **Streams:** `haltsWithin_compileProgram` holds for every RAM stream `ρ` that agrees with the
  Light run's consumed word `r` on its first `|r|` places, reading past the end of `ρ` as `false`
  as the RAM does. Coin-free runs (`r = []`) hold for every `ρ`.
* **Footprint:** every compiled run stays in the cells `[-lowCell, lim.space)`, a number fixed
  by the program text and the limits, independent of the running time (`xcellCount`).
* **Padding:** `haltsWithin_of_streams` turns Light halting on all streams of length `T` into
  RAM halting on every stream (`mem_NSPACE_of_accepts`' hypothesis); `acceptsND_iff_haltsWithin`
  and `acceptProb_eq_randProb` transfer acceptance and acceptance probabilities.
* **Functions:** `polyTimeComputable_of_runs` needs, besides polynomial Light cost, one
  length-dependent word size `W` with a `WordSizeComputable` witness and `TW n + W n`
  polynomial, which `Fits` does not supply (G167-04).

## The semantics (design §15c)

* `x := inBit e`: the input bit at position `e` as `0`/`1`, `0` off the input; cost `e.cost + 1`.
  The input is a field of the limits. `inLen` is not a construct: `|x|` comes as an argument.
* `emit e`: appends the bit "`e` is nonzero"; cost `e.cost + 1`.
* `x := coin`: either bit, consumed; cost `1`. A fixed stream `ρ` selects the run whose consumed
  word is a prefix of `ρ` (`EndsIO`); that run is unique (`XExec.det`).
* `x := half e`: `⌊e / 2⌋`; cost `e.cost + 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the light
  language and its logic (vendored in `TCSlib/Programs/Light/`), of which this is an extension.
-/

namespace TCSlib.Draft.PROG2

open Light (Op Expr Cond State Limits frame)

/-- Statements of the extended light language: the seven of `Light.Stmt`, and `x := inBit e`
(the input bit at position `e`), `emit e` (append the bit "`e ≠ 0`" to the output), `x := coin`
(the next coin), `x := half e` (`⌊e / 2⌋`). [AFM26, `Lang/Syntax.lean`], extended per design
§15c. -/
inductive XStmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : XStmt)
  | ite (c : Cond) (s₁ s₂ : XStmt)
  | while (c : Cond) (s : XStmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  | inBit (x : ℕ) (e : Expr)
  | emit (e : Expr)
  | coin (x : ℕ)
  | half (x : ℕ) (e : Expr)
  deriving Repr

/-- A program of the extended language: the bodies of its procedures, numbered from 0. -/
abbrev XProgram : Type := List XStmt

/-- The vendored statements, as extended statements (**mirror only**). -/
def XStmt.ofStmt : Light.Stmt → XStmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s₁ s₂ => .seq (ofStmt s₁) (ofStmt s₂)
  | .ite c s₁ s₂ => .ite c (ofStmt s₁) (ofStmt s₂)
  | .while c s => .while c (ofStmt s)
  | .call p args x => .call p args x

/-- The limits of a run, and the input: the real edit adds the field `input` to `Light.Limits`
itself, which no vendored file constructs (design §15c). -/
structure XLimits : Type extends Limits where
  /-- The input string, read in place by `inBit`. -/
  input : List Bool

/-- The value of the input bit at position `p`: `1` if `0 ≤ p` and the bit there is `true`,
`0` otherwise (in particular off the input). -/
def inBitVal (x : List Bool) (p : ℤ) : ℤ := if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0

/-- Reading `inBitVal`: `1` exactly at a nonnegative position holding `true`. -/
theorem inBitVal_eq (x : List Bool) (p : ℤ) :
    inBitVal x p = if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0 := rfl


/-- `XExec lim P d s σ σ' o r c`: within the limits `lim`, at nesting depth `d`, the statement
`s` of `P`, started in `σ`, ends in `σ'` after exactly `c` steps, having emitted the bits `o`
and consumed the coins `r`. The rules of `Light.Exec` with the two indices, and one rule for
each new statement; `coin` has a rule for each bit. -/
inductive XExec (lim : XLimits) (P : XProgram) :
    ℕ → XStmt → State → State → List Bool → List Bool → ℕ → Prop
  | skip {d σ} : XExec lim P d .skip σ σ [] [] 0
  | set {d σ x e} : e.Safe lim.toLimits σ →
      XExec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } [] []
        (e.cost + 1)
  | store {d σ a e} : a.Safe lim.toLimits σ → e.Safe lim.toLimits σ →
      lim.toLimits.Addr (a.val σ) →
      XExec lim P d (.store a e) σ
        { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } [] []
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ o₁ o₂ r₁ r₂ c₁ c₂} : XExec lim P d s₁ σ σ' o₁ r₁ c₁ →
      XExec lim P d s₂ σ' σ'' o₂ r₂ c₂ →
      XExec lim P d (.seq s₁ s₂) σ σ'' (o₁ ++ o₂) (r₁ ++ r₂) (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ o r k} : c.Safe lim.toLimits σ → c.Holds σ →
      XExec lim P d s₁ σ σ' o r k → XExec lim P d (.ite c s₁ s₂) σ σ' o r (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ o r k} : c.Safe lim.toLimits σ → ¬ c.Holds σ →
      XExec lim P d s₂ σ σ' o r k → XExec lim P d (.ite c s₁ s₂) σ σ' o r (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim.toLimits σ → ¬ c.Holds σ →
      XExec lim P d (.while c s) σ σ [] [] (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s o₁ o₂ r₁ r₂ k₁ k₂} : c.Safe lim.toLimits σ → c.Holds σ →
      XExec lim P d s σ σ' o₁ r₁ k₁ → XExec lim P d (.while c s) σ' σ'' o₂ r₂ k₂ →
      XExec lim P d (.while c s) σ σ'' (o₁ ++ o₂) (r₁ ++ r₂) (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body o r k} : (∀ e ∈ args, e.Safe lim.toLimits σ) → P[p]? = some body →
      d < lim.depth → XExec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' o r k →
      XExec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩ o r
        ((args.map Expr.cost).sum + 2 + k)
  | inBit {d σ x e} : e.Safe lim.toLimits σ →
      XExec lim P d (.inBit x e) σ
        { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } [] [] (e.cost + 1)
  | emit {d σ e} : e.Safe lim.toLimits σ →
      XExec lim P d (.emit e) σ σ [decide (e.val σ ≠ 0)] [] (e.cost + 1)
  | coin {d σ x} (b : Bool) :
      XExec lim P d (.coin x) σ { σ with loc := Function.update σ.loc x (if b then 1 else 0) } []
        [b] 1
  | half {d σ x e} : e.Safe lim.toLimits σ →
      XExec lim P d (.half x e) σ { σ with loc := Function.update σ.loc x (e.val σ / 2) } [] []
        (e.cost + 1)

/-! ## The six inductions over `Exec`, restated (the edit set extends each by the new cases) -/

section Inductions

variable {lim : XLimits} {P : XProgram} {d : ℕ} {s : XStmt} {σ σ' : State} {o r : List Bool}
  {c : ℕ}

/-- **Conservativity** (**mirror only**: over the October mirror types; after the in-place edit
the vendored syntax is the extended syntax). A run of the vendored language is a run of the
extended language that emits nothing and consumes no coin.

**Proof sketch.** Induction on the vendored run, rule by rule. -/
theorem XExec.ofExec {P₀ : Light.Program} {s₀ : Light.Stmt}
    (h : Light.Exec lim.toLimits P₀ d s₀ σ σ' c) :
    XExec lim (P₀.map XStmt.ofStmt) d (XStmt.ofStmt s₀) σ σ' [] [] c := by
  sorry

/-- A run stays a run when procedures are appended (the extension of `Light.Exec.append`,
`Logic.lean:62`). -/
theorem XExec.append (h : XExec lim P d s σ σ' o r c) (R : XProgram) :
    XExec lim (P ++ R) d s σ σ' o r c := by
  sorry

/-- The locals that a statement assigns: those of `Light.Stmt.assigns` (`Assigns.lean:43`), and
the targets of `inBit`, `coin` and `half`. -/
@[simp] def XStmt.assigns : XStmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]
  | .inBit x _ => [x]
  | .emit _ => []
  | .coin x => [x]
  | .half x _ => [x]

/-- A run leaves a local that the statement does not assign as it was (the extension of
`Light.Exec.loc_eq_of_notMem_assigns`, `Assigns.lean:54`). -/
theorem XExec.loc_eq_of_notMem_assigns {y : ℕ} (h : XExec lim P d s σ σ' o r c)
    (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by
  sorry

/-- A run that starts with words everywhere ends with words everywhere (the extension of
`Light.Exec.bounded`, `RunsStayInLimits.lean:83`). **New hypothesis** `1 ≤ lim.word`: `inBit`
and `coin` write `1`, which the vendored rules never do without a `Safe` premise; `Light.Std`
gives it (`100 ≤ word`). `half` needs nothing, since `|⌊v / 2⌋| ≤ |v|`. -/
theorem XExec.bounded (h : XExec lim P d s σ σ' o r c) (hw : (1 : ℤ) ≤ lim.word)
    (hσ : σ.Bounded lim.toLimits) : σ'.Bounded lim.toLimits := by
  sorry

/-- A run does not change the cells from `lim.space` on (the extension of
`Light.Exec.mem_outside`, `RunsStayInLimits.lean:99`); the new statements change no cell. -/
theorem XExec.mem_outside (h : XExec lim P d s σ σ' o r c) (a : ℕ) (ha : lim.space ≤ a) :
    σ'.mem a = σ.mem a := by
  sorry

/-- Each coin costs one step, so a run of `c` steps consumes at most `c` coins: streams of
length `c` suffice.

**Proof sketch.** Induction on the run; every rule's cost is at least the sum of its parts'
plus, for `coin`, one. -/
theorem XExec.coins_length_le (h : XExec lim P d s σ σ' o r c) : r.length ≤ c := by
  sorry

/-- Each emitted bit costs at least one step. -/
theorem XExec.output_length_le (h : XExec lim P d s σ σ' o r c) : o.length ≤ c := by
  sorry

/-- **Determinism.** Two runs of the same statement from the same state whose consumed words are
both prefixes of one stream `ρ` are the same run: same final state, output, consumed word and
cost. Randomized acceptance (`acceptProb`) needs it (design §15c, obstacle 2).

**Proof sketch.** Induction on the first run, inversion on the second. A test's outcome is a
function of the state, so both runs take the same rule. For `seq` and `whileTrue` the first
parts' consumed words are prefixes of `ρ`, so the induction hypothesis makes them equal; the
second parts then consume prefixes of the same rest of `ρ`. For `coin` the two bits are the
first bit of `ρ`. -/
theorem XExec.det {σ₁ σ₂ : State} {o₁ o₂ r₁ r₂ : List Bool} {c₁ c₂ : ℕ} {ρ : List Bool}
    (h₁ : XExec lim P d s σ σ₁ o₁ r₁ c₁) (h₂ : XExec lim P d s σ σ₂ o₂ r₂ c₂)
    (hr₁ : r₁ <+: ρ) (hr₂ : r₂ <+: ρ) : σ₁ = σ₂ ∧ o₁ = o₂ ∧ r₁ = r₂ ∧ c₁ = c₂ := by
  sorry


/-- **Inversion for `inBit`** (G167-05): its only run sets `x` to the input bit, emits and
consumes nothing, and costs `e.cost + 1`. -/
theorem XExec.inBit_inv {x : ℕ} {e : Expr} (h : XExec lim P d (.inBit x e) σ σ' o r c) :
    e.Safe lim.toLimits σ ∧
      σ' = { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } ∧
      o = [] ∧ r = [] ∧ c = e.cost + 1 := by
  sorry

/-- **Inversion for `emit`**: its only run emits the one bit "`e ≠ 0`", keeps the state, consumes
nothing, and costs `e.cost + 1`. -/
theorem XExec.emit_inv {e : Expr} (h : XExec lim P d (.emit e) σ σ' o r c) :
    e.Safe lim.toLimits σ ∧ σ' = σ ∧ o = [decide (e.val σ ≠ 0)] ∧ r = [] ∧ c = e.cost + 1 := by
  sorry

/-- **Inversion for `coin`**: a run consumes one bit `b`, sets `x` to it, emits nothing, and
costs `1`. -/
theorem XExec.coin_inv {x : ℕ} (h : XExec lim P d (.coin x) σ σ' o r c) :
    ∃ b : Bool, σ' = { σ with loc := Function.update σ.loc x (if b then 1 else 0) } ∧
      o = [] ∧ r = [b] ∧ c = 1 := by
  sorry

/-- **Inversion for `half`**: its only run sets `x` to `⌊e / 2⌋`, emits and consumes nothing, and
costs `e.cost + 1`. -/
theorem XExec.half_inv {x : ℕ} {e : Expr} (h : XExec lim P d (.half x e) σ σ' o r c) :
    e.Safe lim.toLimits σ ∧ σ' = { σ with loc := Function.update σ.loc x (e.val σ / 2) } ∧
      o = [] ∧ r = [] ∧ c = e.cost + 1 := by
  sorry

end Inductions

/-! ## The logic: `Ends` unchanged in type, `EndsIO` -/

/-- The statement `s`, started in `σ`, ends within `T` steps in a state that satisfies `Q`, for
some output and some consumed coins (hidden). The real edit redefines `Light.Ends` so, keeping
its type, so that `Light.Meets` and the vendored routines are untouched. For a statement with
coins this is an existential (some coin outcome): specifications that are to hold for every
stream use `EndsIO`. -/
def XEnds (lim : XLimits) (P : XProgram) (d : ℕ) (s : XStmt) (σ : State) (T : ℕ)
    (Q : State → Prop) : Prop :=
  ∃ σ' o r c, XExec lim P d s σ σ' o r c ∧ c ≤ T ∧ Q σ'

/-- `EndsIO lim P d s σ ρ T Q`: with the coin stream `ρ`, the statement `s`, started in `σ`,
ends within `T` steps in a state `σ'`, having emitted `o` and consumed a prefix `r` of `ρ`, with
`Q σ' o r`. By `XExec.det` there is at most one such run. -/
def EndsIO (lim : XLimits) (P : XProgram) (d : ℕ) (s : XStmt) (σ : State) (ρ : List Bool) (T : ℕ)
    (Q : State → List Bool → List Bool → Prop) : Prop :=
  ∃ σ' o r c, XExec lim P d s σ σ' o r c ∧ r <+: ρ ∧ c ≤ T ∧ Q σ' o r


/-- Reading `XEnds` (in place, `Light.ends_iff`): a run, its cost within `T`, and `Q` at its end,
for some output and some consumed word. -/
theorem xEnds_iff (lim : XLimits) (P : XProgram) (d : ℕ) (s : XStmt) (σ : State) (T : ℕ)
    (Q : State → Prop) :
    XEnds lim P d s σ T Q ↔ ∃ σ' o r c, XExec lim P d s σ σ' o r c ∧ c ≤ T ∧ Q σ' := Iff.rfl

/-- Reading `EndsIO` (G167-05): the witnesses a downstream proof inspects are a run, a consumed
word that is a prefix of the stream, its cost within `T`, and `Q` of the end state, output and
consumed word. -/
theorem endsIO_iff (lim : XLimits) (P : XProgram) (d : ℕ) (s : XStmt) (σ : State) (ρ : List Bool)
    (T : ℕ) (Q : State → List Bool → List Bool → Prop) :
    EndsIO lim P d s σ ρ T Q ↔
      ∃ σ' o r c, XExec lim P d s σ σ' o r c ∧ r <+: ρ ∧ c ≤ T ∧ Q σ' o r := Iff.rfl

section Rules

variable {lim : XLimits} {P : XProgram} {d : ℕ} {σ : State} {ρ : List Bool} {T : ℕ}
  {Q : State → List Bool → List Bool → Prop}

/-- An `EndsIO` fact is an `Ends` fact. -/
theorem EndsIO.toXEnds {s : XStmt} {Q' : State → Prop} (h : EndsIO lim P d s σ ρ T Q)
    (hQ : ∀ σ' o r, Q σ' o r → Q' σ') : XEnds lim P d s σ T Q' := by
  sorry

/-- An `EndsIO` fact holds with more time and any weaker conclusion. -/
theorem EndsIO.mono {s : XStmt} {T' : ℕ} {Q' : State → List Bool → List Bool → Prop}
    (h : EndsIO lim P d s σ ρ T Q) (hT : T ≤ T') (hQ : ∀ σ' o r, Q σ' o r → Q' σ' o r) :
    EndsIO lim P d s σ ρ T' Q' := by
  sorry

/-- `skip` ends at once, in its start state, emitting and consuming nothing. -/
theorem EndsIO.skip (h : Q σ [] []) : EndsIO lim P d .skip σ ρ T Q := by
  sorry

/-- An assignment of a safe expression ends within its cost, emitting and consuming nothing. -/
theorem EndsIO.set {x : ℕ} {e : Expr} (hs : e.Safe lim.toLimits σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) } [] []) :
    EndsIO lim P d (.set x e) σ ρ T Q := by
  sorry

/-- A store of a safe expression at an address within the limits ends within its cost, emitting
and consuming nothing. -/
theorem EndsIO.store {a e : Expr} (ha : a.Safe lim.toLimits σ) (he : e.Safe lim.toLimits σ)
    (hA : lim.toLimits.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } [] []) :
    EndsIO lim P d (.store a e) σ ρ T Q := by
  sorry

/-- Sequencing: the second statement runs on the rest of the stream, and the outputs and the
consumed words are concatenated. -/
theorem EndsIO.seq {s₁ s₂ : XStmt} (T₁ T₂ : ℕ)
    (h : EndsIO lim P d s₁ σ ρ T₁ fun σ' o₁ r₁ =>
      EndsIO lim P d s₂ σ' (ρ.drop r₁.length) T₂ fun σ'' o₂ r₂ => Q σ'' (o₁ ++ o₂) (r₁ ++ r₂))
    (hT : T₁ + T₂ ≤ T) : EndsIO lim P d (.seq s₁ s₂) σ ρ T Q := by
  sorry

/-- A branch: the side that the test selects, on the same stream, after the test's cost. -/
theorem EndsIO.ite {c : Cond} {s₁ s₂ : XStmt} (T' : ℕ) (hs : c.Safe lim.toLimits σ)
    (h₁ : c.Holds σ → EndsIO lim P d s₁ σ ρ T' Q) (h₂ : ¬ c.Holds σ → EndsIO lim P d s₂ σ ρ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : EndsIO lim P d (.ite c s₁ s₂) σ ρ T Q := by
  sorry

/-- A loop whose test holds: one round on the stream, then the loop on the rest. -/
theorem EndsIO.whileStep {c : Cond} {s : XStmt} (T₁ T₂ : ℕ) (hs : c.Safe lim.toLimits σ)
    (hc : c.Holds σ)
    (h : EndsIO lim P d s σ ρ T₁ fun σ' o₁ r₁ =>
      EndsIO lim P d (.while c s) σ' (ρ.drop r₁.length) T₂ fun σ'' o₂ r₂ =>
        Q σ'' (o₁ ++ o₂) (r₁ ++ r₂))
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : EndsIO lim P d (.while c s) σ ρ T Q := by
  sorry

/-- A loop whose test fails ends after the test, emitting and consuming nothing. -/
theorem EndsIO.whileDone {c : Cond} {s : XStmt} (hs : c.Safe lim.toLimits σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ [] []) (hT : c.cost + 1 ≤ T) : EndsIO lim P d (.while c s) σ ρ T Q := by
  sorry

/-- Calls: the body runs on the same stream; the output and the consumed coins pass through. -/
theorem EndsIO.call {p x : ℕ} {args : List Expr} {body : XStmt} (T' : ℕ)
    (ha : ∀ e ∈ args, e.Safe lim.toLimits σ) (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : EndsIO lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ ρ T' fun σ' o r =>
      Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩ o r)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : EndsIO lim P d (.call p args x) σ ρ T Q := by
  sorry

/-- `x := inBit e` sets `x` to the input bit at the position `e` (`0` off the input), within
`e.cost + 1` steps, emitting and consuming nothing. -/
theorem EndsIO.inBit {x : ℕ} {e : Expr} (hs : e.Safe lim.toLimits σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } [] []) :
    EndsIO lim P d (.inBit x e) σ ρ T Q := by
  sorry

/-- `emit e` emits the one bit "`e ≠ 0`" within `e.cost + 1` steps and changes no variable or
cell. -/
theorem EndsIO.emit {e : Expr} (hs : e.Safe lim.toLimits σ) (hT : e.cost + 1 ≤ T)
    (h : Q σ [decide (e.val σ ≠ 0)] []) : EndsIO lim P d (.emit e) σ ρ T Q := by
  sorry

/-- A coin reads the first bit of the stream. -/
theorem EndsIO.coin {x : ℕ} {b : Bool} {ρ' : List Bool} (hρ : ρ = b :: ρ') (hT : 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (if b then 1 else 0) } [] [b]) :
    EndsIO lim P d (.coin x) σ ρ T Q := by
  sorry

/-- `x := half e` sets `x` to `⌊e / 2⌋` within `e.cost + 1` steps, emitting and consuming
nothing. -/
theorem EndsIO.half {x : ℕ} {e : Expr} (hs : e.Safe lim.toLimits σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ / 2) } [] []) :
    EndsIO lim P d (.half x e) σ ρ T Q := by
  sorry

/-- The `Ends` rule for a coin: some bit leads to `Q` (the existential reading of `Ends`). -/
theorem XEnds.coin {x : ℕ} {Q' : State → Prop} (b : Bool) (hT : 1 ≤ T)
    (h : Q' { σ with loc := Function.update σ.loc x (if b then 1 else 0) }) :
    XEnds lim P d (.coin x) σ T Q' := by
  sorry

end Rules

/-! ## Specifications of procedures with input and output -/

/-- `MeetsIO lim P p d vals μ ρ T R`: procedure `p`, run at depth `d` on the arguments `vals` in
the memory `μ` with the stream `ρ`, ends within `T` steps with a result, a memory, an output and
a consumed word that satisfy `R`. The I/O counterpart of `Light.Meets` (`Calls.lean:57`), which
stays as it is. -/
def MeetsIO (lim : XLimits) (P : XProgram) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (ρ : List Bool)
    (T : ℕ) (R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧
    EndsIO lim P d body ⟨frame vals, μ⟩ ρ T fun σ' o r => R (σ'.loc 0) σ'.mem o r

/-- `x := p(args)` with a specification that sees the output and the coins (the I/O counterpart
of `Light.Ends.callLast`, `Calls.lean:113`). -/
theorem EndsIO.callLast {lim : XLimits} {P : XProgram} {d p x T T' : ℕ} {loc μ : ℕ → ℤ}
    {args : List Expr} {vals : List ℤ} {ρ : List Bool}
    {R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop} {Q : State → List Bool → List Bool → Prop}
    (hp : MeetsIO lim P p (d + 1) vals μ ρ T' R)
    (h : ∀ v μ' o r, R v μ' o r → Q ⟨Function.update loc x v, μ'⟩ o r)
    (ha : (∀ e ∈ args, e.Safe lim.toLimits ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals)
    (hd : d < lim.depth) (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    EndsIO lim P d (.call p args x) ⟨loc, μ⟩ ρ T Q := by
  sorry


/-- Reading `MeetsIO` (G167-05). -/
theorem meetsIO_iff (lim : XLimits) (P : XProgram) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ)
    (ρ : List Bool) (T : ℕ) (R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop) :
    MeetsIO lim P p d vals μ ρ T R ↔ ∃ body, P[p]? = some body ∧
      EndsIO lim P d body ⟨frame vals, μ⟩ ρ T fun σ' o r => R (σ'.loc 0) σ'.mem o r := Iff.rfl

/-- `XMeets lim P p d vals μ T R`: the mirror of `Light.Meets` (`Calls.lean:57`), whose type the
in-place edit keeps: procedure `p` ends within `T` steps with a result and memory satisfying `R`,
for some output and consumed word. -/
def XMeets (lim : XLimits) (P : XProgram) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ XEnds lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem

/-- Reading `XMeets` (in place, `Light.meets_iff`). -/
theorem xMeets_iff (lim : XLimits) (P : XProgram) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) :
    XMeets lim P p d vals μ T R ↔ ∃ body, P[p]? = some body ∧
      XEnds lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem := Iff.rfl

/-! ## Acceptance -/

/-- The outermost statement of a whole program: procedure `p0` on the locals 1 and 2 (the copy
of `Light.mainStmt`, `ProgramCode.lean`, for the extended syntax). With `inLen` from an argument,
local 1 holds `|x|`. -/
def xmainStmt (p0 : ℕ) : XStmt := .call p0 [.var 1, .var 2] 0

/-- **Nondeterministic acceptance** (design §15c): some coin stream of length `T` makes the
outermost call, on `|x| = |lim.input|` and `j`, end within `T` steps with a positive result.
Time bounds are stated separately and uniformly over all streams, as `NTIME` and `NSPACE`
require. [AB09, §2.1.2] -/
def AcceptsND (lim : XLimits) (P : XProgram) (p0 : ℕ) (j : ℤ) (μ : ℕ → ℤ) (T : ℕ) : Prop :=
  ∃ ρ : List Bool, ρ.length = T ∧
    EndsIO lim P 0 (xmainStmt p0) ⟨frame [0, lim.input.length, j], μ⟩ ρ T fun σ' _ _ => 0 < σ'.loc 0

open Classical in
/-- **Randomized acceptance** (design §15c): the probability, over a uniform stream of `m` coins,
that the outermost call ends within `T` steps with a positive result. Well defined as a
probability of runs because the run of each stream is unique (`XExec.det`). [AB09, Def 7.2] -/
noncomputable def acceptProb (lim : XLimits) (P : XProgram) (p0 : ℕ) (j : ℤ) (μ : ℕ → ℤ)
    (m T : ℕ) : ℚ :=
  Randomized.randProb m fun ρ =>
    EndsIO lim P 0 (xmainStmt p0) ⟨frame [0, lim.input.length, j], μ⟩ ρ T fun σ' _ _ => 0 < σ'.loc 0


/-- Reading `xmainStmt`. -/
theorem xmainStmt_eq (p0 : ℕ) : xmainStmt p0 = .call p0 [.var 1, .var 2] 0 := rfl

/-- Reading `AcceptsND` (G167-05). -/
theorem acceptsND_iff (lim : XLimits) (P : XProgram) (p0 : ℕ) (j : ℤ) (μ : ℕ → ℤ) (T : ℕ) :
    AcceptsND lim P p0 j μ T ↔ ∃ ρ : List Bool, ρ.length = T ∧
      EndsIO lim P 0 (xmainStmt p0) ⟨frame [0, lim.input.length, j], μ⟩ ρ T
        fun σ' _ _ => 0 < σ'.loc 0 := Iff.rfl

open Classical in
/-- Reading `acceptProb` (G167-05). -/
theorem acceptProb_eq (lim : XLimits) (P : XProgram) (p0 : ℕ) (j : ℤ) (μ : ℕ → ℤ) (m T : ℕ) :
    acceptProb lim P p0 j μ m T = Randomized.randProb m fun ρ =>
      EndsIO lim P 0 (xmainStmt p0) ⟨frame [0, lim.input.length, j], μ⟩ ρ T
        fun σ' _ _ => 0 < σ'.loc 0 := rfl

/-! ## Relocation (the extension of `Light/Renumber`, vendored since October) -/

/-- The statement with `n` added to the number of every procedure it calls: `Light.Stmt.shift`,
with the four new statements unchanged. -/
def XStmt.shift (n : ℕ) : XStmt → XStmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x
  | .inBit x e => .inBit x e
  | .emit e => .emit e
  | .coin x => .coin x
  | .half x e => .half x e

/-- The program `P` placed behind `Q`: `Light.Program.behind`. -/
def XProgram.behind (Q P : XProgram) : XProgram := Q ++ P.map (XStmt.shift Q.length)

/-- **Relocation with input and output** (the extension of `Light.Exec.shift`): a run in `P` is
a run of the shifted statement in `P` placed behind `Q`, with the same states, output, coins and
steps.

**Proof sketch.** Induction on the run; only `call` uses the program, through the shifted
procedure's index; the four new rules are unchanged. -/
theorem XExec.shift {lim : XLimits} {P : XProgram} {d : ℕ} {s : XStmt} {σ σ' : State}
    {o r : List Bool} {c : ℕ} (h : XExec lim P d s σ σ' o r c) (Q : XProgram) :
    XExec lim (XProgram.behind Q P) d (s.shift Q.length) σ σ' o r c := by
  sorry


/-! ## Lifting I/O-free code to `EndsIO` (G167-01)

After the in-place edit, `Light.Ends` hides an output and a consumed word, so an `Ends` fact
alone does not give an `EndsIO` fact (`coin` and `emit` end with nonempty traces). The lifting
condition is on the procedures a statement can reach: a **silent set** `S` of procedure numbers
is closed under calls, lies within the program, and its bodies emit and consume nothing. It is
stable under appending procedures and under relocation (`behind`), so the 14 library routines,
whose bodies are silent, keep a silent set inside any program built around them, even one whose
other procedures use input, output and coins. -/

/-- A statement is **silent** if it contains no `emit` and no `coin` (calls are checked
separately, through a silent set). `inBit` and `half` are silent. -/
def XStmt.silent : XStmt → Bool
  | .skip => true
  | .set _ _ => true
  | .store _ _ => true
  | .seq s t => s.silent && t.silent
  | .ite _ s t => s.silent && t.silent
  | .while _ s => s.silent
  | .call _ _ _ => true
  | .inBit _ _ => true
  | .emit _ => false
  | .coin _ => false
  | .half _ _ => true

/-- The procedures a statement calls directly. -/
def XStmt.calls : XStmt → List ℕ
  | .seq s t => s.calls ++ t.calls
  | .ite _ s t => s.calls ++ t.calls
  | .while _ s => s.calls
  | .call p _ _ => [p]
  | _ => []

/-- Reading `XStmt.silent` on a sequence. -/
theorem XStmt.silent_seq (s t : XStmt) : (XStmt.seq s t).silent = (s.silent && t.silent) := rfl

/-- Reading `XStmt.silent` on a branch. -/
theorem XStmt.silent_ite (c : Cond) (s t : XStmt) :
    (XStmt.ite c s t).silent = (s.silent && t.silent) := rfl

/-- Reading `XStmt.silent` on a loop. -/
theorem XStmt.silent_while (c : Cond) (s : XStmt) : (XStmt.while c s).silent = s.silent := rfl

/-- `emit` and `coin` are the statements that are not silent. -/
theorem XStmt.silent_emit (e : Expr) : (XStmt.emit e).silent = false := rfl

@[inherit_doc XStmt.silent_emit]
theorem XStmt.silent_coin (x : ℕ) : (XStmt.coin x).silent = false := rfl

/-- Reading `XStmt.calls` on a call. -/
theorem XStmt.calls_call (p : ℕ) (args : List Expr) (x : ℕ) :
    (XStmt.call p args x).calls = [p] := rfl

/-- Reading `XStmt.silent` on the remaining leaves: all are silent (round 3, G167-05). -/
theorem XStmt.silent_leaf (x p : ℕ) (a e : Expr) (args : List Expr) :
    XStmt.skip.silent = true ∧ (XStmt.set x e).silent = true ∧ (XStmt.store a e).silent = true ∧
      (XStmt.call p args x).silent = true ∧ (XStmt.inBit x e).silent = true ∧
      (XStmt.half x e).silent = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading `XStmt.calls` on compound statements. -/
theorem XStmt.calls_seq (s t : XStmt) : (XStmt.seq s t).calls = s.calls ++ t.calls := rfl

@[inherit_doc XStmt.calls_seq]
theorem XStmt.calls_ite (c : Cond) (s t : XStmt) :
    (XStmt.ite c s t).calls = s.calls ++ t.calls := rfl

@[inherit_doc XStmt.calls_seq]
theorem XStmt.calls_while (c : Cond) (s : XStmt) : (XStmt.while c s).calls = s.calls := rfl

/-- Reading `XStmt.calls` on the leaves other than `call`: they call nothing. -/
theorem XStmt.calls_leaf (x : ℕ) (a e : Expr) :
    XStmt.skip.calls = [] ∧ (XStmt.set x e).calls = [] ∧ (XStmt.store a e).calls = [] ∧
      (XStmt.inBit x e).calls = [] ∧ (XStmt.emit e).calls = [] ∧ (XStmt.coin x).calls = [] ∧
      (XStmt.half x e).calls = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `S` is a **silent set** of `P`: its procedures exist, their bodies are silent, and they call
only procedures in `S`. -/
def XProgram.SilentSet (P : XProgram) (S : Set ℕ) : Prop :=
  ∀ p ∈ S, ∃ b, P[p]? = some b ∧ b.silent = true ∧ ∀ q ∈ b.calls, q ∈ S

/-- Reading `XProgram.SilentSet`. -/
theorem XProgram.silentSet_iff (P : XProgram) (S : Set ℕ) :
    P.SilentSet S ↔ ∀ p ∈ S, ∃ b, P[p]? = some b ∧ b.silent = true ∧ ∀ q ∈ b.calls, q ∈ S :=
  Iff.rfl

/-- **Silent code has empty traces.** A run of a silent statement that calls only procedures in a
silent set emits nothing and consumes nothing.

**Proof sketch.** Induction on the run. The leaves other than `emit` and `coin` have empty
traces; `seq`, `ite` and `while` inherit silence and the call condition from their parts; a call
goes to a procedure of `S`, whose body is silent and calls into `S`. -/
theorem XExec.traces_nil {lim : XLimits} {P : XProgram} {S : Set ℕ} {d : ℕ} {s : XStmt}
    {σ σ' : State} {o r : List Bool} {c : ℕ} (hS : P.SilentSet S) (hs : s.silent = true)
    (hc : ∀ q ∈ s.calls, q ∈ S) (h : XExec lim P d s σ σ' o r c) : o = [] ∧ r = [] := by
  sorry

/-- A silent set stays one when procedures are appended. -/
theorem XProgram.SilentSet.append {P : XProgram} {S : Set ℕ} (hS : P.SilentSet S)
    (R : XProgram) : (P ++ R).SilentSet S := by
  sorry

/-- Shifting a statement's calls keeps it silent. -/
theorem XStmt.silent_shift (n : ℕ) (s : XStmt) : (s.shift n).silent = s.silent := by
  sorry

/-- Shifting a statement's calls shifts the procedures it calls. -/
theorem XStmt.calls_shift (n : ℕ) (s : XStmt) : (s.shift n).calls = s.calls.map (· + n) := by
  sorry

/-- **Relocation of a silent set**: `P`'s silent set, shifted, is a silent set of `P` placed
behind `Q`; `Q`'s own silent sets stay silent sets (`append`). -/
theorem XProgram.SilentSet.behind {P : XProgram} {S : Set ℕ} (hS : P.SilentSet S)
    (Q : XProgram) : (XProgram.behind Q P).SilentSet ((· + Q.length) '' S) := by
  sorry

/-- **Lifting an `Ends` fact** (replaces round 1's `EndsIO.ofEnds`, G167-01). An `XEnds` fact
(in place, `Light.Ends`) about silent code that calls into a silent set holds for every stream,
with nothing emitted and nothing consumed.

**Proof sketch.** Take the run of the `XEnds` fact; `XExec.traces_nil` makes its traces empty,
and `[]` is a prefix of every stream. -/
theorem EndsIO.ofXEnds {lim : XLimits} {P : XProgram} {S : Set ℕ} {d : ℕ} {s : XStmt}
    {σ : State} {ρ : List Bool} {T : ℕ} {Q₀ : State → Prop} (hS : P.SilentSet S)
    (hs : s.silent = true) (hc : ∀ q ∈ s.calls, q ∈ S) (h : XEnds lim P d s σ T Q₀) :
    EndsIO lim P d s σ ρ T fun σ' o r => Q₀ σ' ∧ o = [] ∧ r = [] := by
  sorry

/-- **Lifting a procedure specification**: a library routine `p` in a silent set meets its
`XMeets` specification (in place, `Light.Meets`) for every stream, with empty traces. This is
how the 14 routines of `Light.Std`, placed by `behind` inside an I/O program, are used under
`EndsIO` (with `EndsIO.callLast`).

**Proof sketch.** Unfold both specifications to the body's facts and apply `EndsIO.ofXEnds`
with the body's silence and calls from the silent set. -/
theorem MeetsIO.ofXMeets {lim : XLimits} {P : XProgram} {S : Set ℕ} {p d : ℕ} {vals : List ℤ}
    {μ : ℕ → ℤ} {ρ : List Bool} {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (hS : P.SilentSet S)
    (hp : p ∈ S) (h : XMeets lim P p d vals μ T R) :
    MeetsIO lim P p d vals μ ρ T fun v μ' o r => R v μ' ∧ o = [] ∧ r = [] := by
  sorry

/-! ## Streams beyond the run (N8)

A run within `T` steps consumes at most `T` coins (`XExec.coins_length_le`), so only the first
`T` bits of a stream matter. -/

/-- An `EndsIO` fact within `T` steps depends only on the first `T` bits of the stream.

**Proof sketch.** The consumed word has length at most the cost, hence at most `T`; a word of
length at most `T` is a prefix of `ρ` exactly when it is a prefix of `ρ.take T`. -/
theorem EndsIO.take_iff {lim : XLimits} {P : XProgram} {d : ℕ} {s : XStmt} {σ : State}
    {ρ : List Bool} {T : ℕ} {Q : State → List Bool → List Bool → Prop} :
    EndsIO lim P d s σ ρ T Q ↔ EndsIO lim P d s σ (ρ.take T) T Q := by
  sorry

/-- **Padding randomness beyond `T` changes no acceptance probability.**

**Proof sketch.** By `EndsIO.take_iff`, acceptance on a stream of length `m` depends on its
first `T ≤ m₁` bits, so `Randomized.randProb_take` reduces `m` coins to `m₁`. -/
theorem acceptProb_eq_of_le {lim : XLimits} {P : XProgram} {p0 : ℕ} {j : ℤ} {μ : ℕ → ℤ}
    {T m₁ m : ℕ} (hT : T ≤ m₁) (hm : m₁ ≤ m) :
    acceptProb lim P p0 j μ m T = acceptProb lim P p0 j μ m₁ T := by
  sorry


/-! ## The compiler, in place (G167-02, G167-06)

The definitions below are the in-place `Light.Compiler` declarations for the extended syntax,
stated concretely. The straight-line code they call (`compileExpr`, `compileCond`, `callCode`,
`epilogue`, `dispatcher`, `tailCode`, `headStraight`, `startStraight`) is the vendored
`List Instr` code, unchanged, embedded by `List.map WordRAM.XInstr.base`. -/

section Compiler

open Light.Compiler (CodeLayout compileExpr compileCond callCode callSize epilogue epilogueSize
  dispatcher cADDR cFP cPool cT cNEG Sizes Framed Rel Writable Fits Input Holds stepsPerStep
  mainFrame mainPos tailPos tailCode headStraight startStraight)

/-- The local store `x := T₀` of an assignment, as base instructions (`compileStmt`'s `.set`
case, after its expression). -/
def xstoreLocal (x : ℕ) : List WordRAM.XInstr :=
  [.base (.sub cADDR cFP (cPool (2 * x))), .base (.store cADDR (cT 0))]

/-- Reading `xstoreLocal` (round 3, G167-05). -/
theorem xstoreLocal_eq (x : ℕ) :
    xstoreLocal x = [.base (.sub cADDR cFP (cPool (2 * x))), .base (.store cADDR (cT 0))] := rfl

/-- **The length of the code of a statement** (in place, `Light.Stmt.size`): the vendored seven
cases, and `inBit`/`half` `e.size + 3`, `emit` `e.size + 1`, `coin` `3` (G167-06). -/
def XStmt.size (F : ℕ) : XStmt → ℕ
  | .skip => 0
  | .set _ e => e.size + 2
  | .store a e => a.size + e.size + 1
  | .seq s t => s.size F + t.size F
  | .ite c s t => c.size + s.size F + 1 + t.size F
  | .while c s => c.size + s.size F + 1
  | .call _ args _ => callSize F args + 2
  | .inBit _ e => e.size + 3
  | .emit e => e.size + 1
  | .coin _ => 3
  | .half _ e => e.size + 3

/-- **The code of a statement, for the position `pos`** (in place, `Light.Compiler.compileStmt`,
now emitting extended instructions). The seven vendored cases are the vendored code under
`.base`; the four new cases evaluate their expression into `T₀`, apply the new instruction to
`T₀`, and store `T₀` into the target local as an assignment does (G167-06). -/
def xcompileStmt (G : CodeLayout) : XStmt → ℕ → List WordRAM.XInstr
  | .skip, _ => []
  | .set x e, _ => (compileExpr e 0).map .base ++ xstoreLocal x
  | .store a e, _ => (compileExpr a 0 ++ compileExpr e 1 ++ [WordRAM.Instr.store (cT 0) (cT 1)]).map .base
  | .seq s t, pos => xcompileStmt G s pos ++ xcompileStmt G t (pos + s.size G.F)
  | .ite c s t, pos =>
    (compileCond c (pos + c.size + s.size G.F + 1)).map .base ++ xcompileStmt G s (pos + c.size) ++
      [.base (.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F))] ++
      xcompileStmt G t (pos + c.size + s.size G.F + 1)
  | .while c s, pos =>
    (compileCond c (pos + c.size + s.size G.F + 1)).map .base ++ xcompileStmt G s (pos + c.size) ++
      [.base (.bltz cNEG pos)]
  | .call p args x, pos =>
    (callCode G p args (pos + callSize G.F args)).map .base ++
      [.base (.sub cADDR cFP (cPool (2 * x))), .base (.store cADDR Light.Compiler.cRET)]
  | .inBit x e, _ => (compileExpr e 0).map .base ++ [.rdIn (cT 0) (cT 0)] ++ xstoreLocal x
  | .emit e, _ => (compileExpr e 0).map .base ++ [.emit (cT 0)]
  | .coin x, _ => [.coin (cT 0)] ++ xstoreLocal x
  | .half x e, _ => (compileExpr e 0).map .base ++ [.half (cT 0) (cT 0)] ++ xstoreLocal x

/-- The code of a statement has `size` instructions (in place, `length_compileStmt`). -/
theorem length_xcompileStmt (G : CodeLayout) (s : XStmt) (pos : ℕ) :
    (xcompileStmt G s pos).length = s.size G.F := by
  sorry

/-- **The width of a statement** (in place, `Light.Stmt.width`): the locals and temporaries its
code uses. The new statements use their target and their expression's width. -/
def XStmt.width : XStmt → ℕ
  | .skip => 0
  | .set x e => max (x + 1) e.width
  | .store a e => max a.width e.width
  | .seq s t => max s.width t.width
  | .ite c s t => max c.width (max s.width t.width)
  | .while c s => max c.width s.width
  | .call _ args x => max (x + 1) (max args.length (Light.maxOf Light.Expr.width args))
  | .inBit x e => max (x + 1) e.width
  | .emit e => e.width
  | .coin x => x + 1
  | .half x e => max (x + 1) e.width

/-- Width reader for `inBit` (in place, `Light.Stmt.width_inBit_le_iff`). -/
theorem XStmt.width_inBit_le_iff {F x : ℕ} {e : Expr} :
    (XStmt.inBit x e).width ≤ F ↔ x < F ∧ e.width ≤ F := by
  sorry

/-- Width reader for `emit`. -/
theorem XStmt.width_emit_le_iff {F : ℕ} {e : Expr} : (XStmt.emit e).width ≤ F ↔ e.width ≤ F :=
  Iff.rfl

/-- Width reader for `coin`. -/
theorem XStmt.width_coin_le_iff {F x : ℕ} : (XStmt.coin x).width ≤ F ↔ x < F := Iff.rfl

/-- Width reader for `half`. -/
theorem XStmt.width_half_le_iff {F x : ℕ} {e : Expr} :
    (XStmt.half x e).width ≤ F ↔ x < F ∧ e.width ≤ F := by
  sorry

/-- `l` is the code at position `pos` of the extended program `code` (in place, the code-at
relation of the extended code; the vendored `WordRAM.CodeAt` stays for `List Instr`). -/
def XCodeAt (code : WordRAM.XProgram) (pos : ℕ) (l : List WordRAM.XInstr) : Prop :=
  l <+: code.drop pos

/-- Reading `XCodeAt`. -/
theorem xCodeAt_iff (code : WordRAM.XProgram) (pos : ℕ) (l : List WordRAM.XInstr) :
    XCodeAt code pos l ↔ l <+: code.drop pos := Iff.rfl

/-- **The transport** (G167-02): vendored code placed as base instructions is vendored code of
the projection, so the unchanged segment lemmas of `Compiler/Expressions`, `Conditions` and
`CallFrames` apply to `code.proj`, and their runs lift by `WordRAM.XSteps.of_steps_proj`. -/
theorem XCodeAt.proj {code : WordRAM.XProgram} {pos : ℕ} {l : List WordRAM.Instr}
    (h : XCodeAt code pos (l.map .base)) : WordRAM.CodeAt code.proj pos l := by
  sorry

/-- **What the simulation assumes** (in place, `Light.Compiler.Setting`): `Sizes`, the program,
the input, and the extended code with each body at its entry. -/
structure XSetting (W : ℕ) extends Sizes W where
  /-- The program. -/
  P : XProgram
  /-- The input, read by `inBit` (in place, the field `lim.input`). -/
  input : List Bool
  /-- The code of the whole program. -/
  code : WordRAM.XProgram
  /-- Every procedure body is at its entry, followed by the return sequence, before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : XStmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    XCodeAt code e (xcompileStmt toCodeLayout b e ++ (epilogue toCodeLayout).map .base) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : XCodeAt code disp ((dispatcher disp).map .base)
  /-- Every body has width at most `F`. -/
  width : ∀ b ∈ P, b.width ≤ F

/-- The limits of the setting, with its input (**mirror only**: in place `Light.Limits` carries
the input and this is the setting's `lim` itself). -/
def XSetting.xlim {W : ℕ} (S : XSetting W) : XLimits := { toLimits := S.lim, input := S.input }

/-- **The cells a simulated run may touch** (round 3, G167-07): from the end of the pool and the
stack, `-max(2Q, 25 + 4·disp)`, up to the memory limit. -/
def XSetting.cells {W : ℕ} (S : XSetting W) : Set ℤ :=
  {a | -(max (2 * S.Q) (25 + 4 * S.disp) : ℤ) ≤ a ∧ a < S.lim.space}

/-- Reading `XSetting.cells`. -/
theorem XSetting.cells_eq {W : ℕ} (S : XSetting W) :
    S.cells = {a | -(max (2 * S.Q) (25 + 4 * S.disp) : ℤ) ≤ a ∧ a < S.lim.space} := rfl

/-- Footprints compose (in place, `WordRAM.XStepsIn.mono`, new in `Extended`; the extended
counterpart of the vendored `StepsIn.mono`). -/
theorem xStepsIn_mono {W : ℕ} {P : WordRAM.XProgram} {x ρ : List Bool} {K K' : Set ℤ} {n : ℕ}
    {c c' : WordRAM.XCfg W} (h : WordRAM.XStepsIn P x ρ K n c c') (hK : K ⊆ K') :
    WordRAM.XStepsIn P x ρ K' n c c' := by
  sorry

/-- Runs within one footprint concatenate (in place, `WordRAM.XStepsIn.trans`, new in
`Extended`; the extended counterpart of `StepsIn.trans`). -/
theorem xStepsIn_trans {W : ℕ} {P : WordRAM.XProgram} {x ρ : List Bool} {K : Set ℤ} {n k : ℕ}
    {c c₁ c₂ : WordRAM.XCfg W} (h₁ : WordRAM.XStepsIn P x ρ K n c c₁)
    (h₂ : WordRAM.XStepsIn P x ρ K k c₁ c₂) : WordRAM.XStepsIn P x ρ K (n + k) c c₂ := by
  sorry

variable {W : ℕ} (S : XSetting W)

/-- The situation before the code of `s` runs at depth `d` (in place, `Start`; unchanged apart
from the extended code). -/
structure XStart (d : ℕ) (s : XStmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  codeAt : XCodeAt S.code pos (xcompileStmt S.toCodeLayout s pos)
  below : pos + s.size S.F ≤ S.disp
  width : s.width ≤ S.F
  bounded : σ.Bounded S.lim
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q

/-- The code of `s`, started with output `out` and `k` coins consumed, has matched a run that
ends in `σ'` having emitted `o` and consumed `r` (in place, `Finished`, with the two traces):
`n` steps on the stream `ρ`, every one within the setting's cells (round 3, G167-07), reach the
end of the code with output `out ++ o` and `k + |r|` coins consumed. -/
structure XFinished (ρ : List Bool) (s : XStmt) (σ' : State) (o r : List Bool) (c pos q : ℕ)
    (m m' : ℤ → BitVec W) (out : List Bool) (k n : ℕ) : Prop where
  run : WordRAM.XStepsIn S.code S.input ρ S.cells n { pc := pos, mem := m, out := out, rd := k }
    { pc := pos + s.size S.F, mem := m', out := out ++ o, rd := k + r.length }
  le : n ≤ stepsPerStep S.disp * c
  rel : Rel S.toSizes σ' q m'
  agree : WordRAM.AgreeOutside (Writable S.toSizes q) m m'

/-- The code of `s` matches the run of `s` from `σ` to `σ'` with traces `o` and `r` (in place,
`Simulates`): from any start, on any stream that agrees with `r` from the current coin count on
(reading past its end as `false`, as the RAM does). -/
def XSimulates (ρ : List Bool) (d : ℕ) (s : XStmt) (σ σ' : State) (o r : List Bool) (c : ℕ) :
    Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W) (out : List Bool) (k : ℕ), XStart S d s σ pos q m →
    (∀ i < r.length, ρ.getD (k + i) false = r.getD i false) →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), XFinished S ρ s σ' o r c pos q m m' out k n

/-- **The simulation** (in place, `Light.Compiler.sim`): the code of a statement matches every
run of it, with the output appended and the coins read from the stream. New hypothesis
`1 ≤ lim.word`, for `Exec.bounded` (G167-02).

**Proof sketch.** Induction on the run, as the vendored `sim`, threading `out` and `k`. The base
segments run through `XCodeAt.proj`, footprint versions of the vendored segment lemmas on
`S.code.proj` (`StepsIn`, within `S.cells`: every load and store address is a frame, stack,
pool or constant cell, or a safe memory address below `lim.space`), and
`XStepsIn.of_stepsIn_proj`; they change neither output nor coin count. Segments compose by
`xStepsIn_trans`. The four new cases run their
expression code, one new instruction (`rdIn` reads `inBitWord`, equal to `inBitVal` in range;
`emit` appends "`T₀ ≠ 0`"; `coin` reads `ρ.getD k false`, which is the consumed bit; `half` is
`sshiftRight 1`, equal to `⌊v / 2⌋` in range), and the local store. -/
theorem xsim (hw : (1 : ℤ) ≤ S.lim.word) {d : ℕ} {s : XStmt} {σ σ' : State}
    {o r : List Bool} {c : ℕ} (ρ : List Bool) (h : XExec S.xlim S.P d s σ σ' o r c) :
    XSimulates S ρ d s σ σ' o r c := by
  sorry

end Compiler


/-! ## Whole programs (in place, `Compiler/ProgramCode` and `Compiler/WholeProgram`) -/

section Program

open Light.Compiler (CodeLayout epilogue epilogueSize dispatcher cNEG Fits Input Holds
  stepsPerStep mainFrame mainPos tailPos tailCode headStraight startStraight startMem)

/-- The frame size: the width of the text, at least 3 (in place, `frameSize`). -/
def xframeSize (P : XProgram) : ℕ := max 3 (Light.maxOf XStmt.width P)

/-- The positions of the bodies, from `pos` on (in place, `entries`). -/
def xentries (F : ℕ) : XProgram → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: xentries F bs (pos + b.size F + epilogueSize)

/-- The position after the bodies (in place, `endPos`). -/
def xendPos (F : ℕ) : XProgram → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => xendPos F bs (pos + b.size F + epilogueSize)

/-- The position of the first body (in place, `firstBody`; the outermost call and the verdict
code are unchanged). -/
def xfirstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length

/-- The dispatcher's position (in place, `dispPos`). -/
def xdispPos (P : XProgram) (dec : Bool) : ℕ :=
  xendPos (xframeSize P) P (xfirstBody (xframeSize P) dec)

/-- The layout (in place, `codeLayout`). -/
def xcodeLayout (P : XProgram) (dec : Bool) : CodeLayout :=
  ⟨xframeSize P, xentries (xframeSize P) P (xfirstBody (xframeSize P) dec), xdispPos P dec⟩

/-- The bodies with their return sequences (in place, `bodiesCode`). -/
def xbodiesCode (G : CodeLayout) : XProgram → ℕ → List WordRAM.XInstr
  | [], _ => []
  | b :: bs, pos => (xcompileStmt G b pos ++ (epilogue G).map .base) ++
      xbodiesCode G bs (pos + b.size G.F + epilogueSize)

/-- **The code of a program** (in place, `Light.compileProgram`, now `List XInstr`): the
vendored head, outermost call, verdict code, dispatcher and start-up code under `.base`, and the
compiled bodies. -/
def xcompileProgram (P : XProgram) (p0 : ℕ) (dec : Bool) : WordRAM.XProgram :=
  (headStraight ++ [WordRAM.Instr.bltz cNEG (3 * xdispPos P dec)]).map .base ++
    (xcompileStmt (xcodeLayout P dec) (xmainStmt p0) mainPos ++
      (tailCode dec (tailPos (xframeSize P))).map .base) ++
    xbodiesCode (xcodeLayout P dec) P (xfirstBody (xframeSize P) dec) ++
    (dispatcher (xdispPos P dec)).map .base ++
    (startStraight (xframeSize P) (xdispPos P dec) ++ [WordRAM.Instr.bltz cNEG mainPos]).map .base

/-! ### Where the parts of a compiled program are (round 3, G167-02)

In place these are `codeAt_headCode`, `codeAt_mainStmt`, `codeAt_tailCode`,
`codeAt_dispatcher_dispPos` and `codeAt_startCode` of `Compiler/ProgramCode`, now stated over the
extended code; and `steps_start` of `Compiler/StartUp`, whose conclusion was over
`compileProgram` itself. -/

/-- The head is at position `0`. -/
theorem xcodeAt_headCode (P : XProgram) (p0 : ℕ) (dec : Bool) :
    XCodeAt (xcompileProgram P p0 dec) 0
      ((headStraight ++ [WordRAM.Instr.bltz cNEG (3 * xdispPos P dec)]).map .base) := by
  sorry

/-- The outermost call is at `mainPos`. -/
theorem xcodeAt_mainStmt (P : XProgram) (p0 : ℕ) (dec : Bool) :
    XCodeAt (xcompileProgram P p0 dec) mainPos
      (xcompileStmt (xcodeLayout P dec) (xmainStmt p0) mainPos) := by
  sorry

/-- The verdict code follows the outermost call. -/
theorem xcodeAt_tailCode (P : XProgram) (p0 : ℕ) (dec : Bool) :
    XCodeAt (xcompileProgram P p0 dec) (tailPos (xframeSize P))
      ((tailCode dec (tailPos (xframeSize P))).map .base) := by
  sorry

/-- The dispatcher is at `xdispPos`. -/
theorem xcodeAt_dispatcher (P : XProgram) (p0 : ℕ) (dec : Bool) :
    XCodeAt (xcompileProgram P p0 dec) (xdispPos P dec)
      ((dispatcher (xdispPos P dec)).map .base) := by
  sorry

/-- The start-up code follows the dispatcher. -/
theorem xcodeAt_startCode (P : XProgram) (p0 : ℕ) (dec : Bool) :
    XCodeAt (xcompileProgram P p0 dec) (3 * xdispPos P dec)
      ((startStraight (xframeSize P) (xdispPos P dec) ++
        [WordRAM.Instr.bltz cNEG mainPos]).map .base) := by
  sorry

/-- **The start-up, over the projection** (in place, `steps_start`, restated over
`(compileProgram P p0 dec).proj`): from the first instruction to the outermost statement.

**Proof sketch.** The vendored proof, with `XCodeAt.proj` turning `xcodeAt_headCode` and
`xcodeAt_startCode` into code locations of the projection. -/
theorem steps_start_proj {W : ℕ} (P : XProgram) (p0 : ℕ) (dec : Bool)
    (hneg : WordRAM.InRange W (-1)) (m : ℤ → BitVec W) :
    WordRAM.Steps (xcompileProgram P p0 dec).proj (xdispPos P dec + xframeSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (xframeSize P) (xdispPos P dec) m⟩ := by
  sorry

/-- The start-up cost (in place, `startCost`). -/
def xstartCost (P : XProgram) (dec : Bool) : ℕ := xdispPos P dec + xframeSize P + 13

/-- The RAM steps for a Light run of cost `c` (in place, `Light.ramSteps`). -/
def xramSteps (P : XProgram) (dec : Bool) (c : ℕ) : ℕ :=
  xstartCost P dec + stepsPerStep (xdispPos P dec) * c

/-- The stack cells (in place, `stackCells`). -/
def xstackCells (P : XProgram) (lim : Limits) : ℕ :=
  mainFrame + (xframeSize P + 1) * (lim.depth + 1)

/-- The extent of the negative cells (in place, `lowCell`). -/
def xlowCell (P : XProgram) (dec : Bool) (lim : Limits) : ℕ :=
  max (2 * xstackCells P lim) (25 + 4 * xdispPos P dec)

/-- **The cells a compiled run may touch** (G167-03): `[-lowCell, lim.space)`. -/
def xcells (P : XProgram) (dec : Bool) (lim : Limits) : Finset ℤ :=
  Finset.Ico (-(xlowCell P dec lim : ℤ)) lim.space

/-- **The footprint of a compiled run**, fixed by the text and the limits, independent of the
running time (G167-03). -/
def xcellCount (P : XProgram) (dec : Bool) (lim : Limits) : ℕ := xlowCell P dec lim + lim.space

/-- Reading `xcells` (round 3, G167-05). -/
theorem xcells_eq (P : XProgram) (dec : Bool) (lim : Limits) :
    xcells P dec lim = Finset.Ico (-(xlowCell P dec lim : ℤ)) lim.space := rfl

/-- Reading `xcellCount` (round 3, G167-05). -/
theorem xcellCount_eq (P : XProgram) (dec : Bool) (lim : Limits) :
    xcellCount P dec lim = xlowCell P dec lim + lim.space := rfl

/-- **The start-up as an extended run, with its footprint**: on any input and stream, from
any coin count, the start-up reaches the outermost statement within `xcells`, emitting nothing.

**Proof sketch.** `steps_start_proj` with footprints (`stepsIn_straight` for its two
straight-line parts): it writes the constants, the pool up to `cPool (xdispPos)`, `FP` and the
outermost frame, and reads the argument cells, all at least `-xlowCell` and negative; then
`XStepsIn.of_stepsIn_proj`. -/
theorem xsteps_start {W : ℕ} (P : XProgram) (p0 : ℕ) (dec : Bool) (lim : Limits)
    (hneg : WordRAM.InRange W (-1)) (m : ℤ → BitVec W) (x ρ : List Bool) (k : ℕ) :
    WordRAM.XStepsIn (xcompileProgram P p0 dec) x ρ ↑(xcells P dec lim)
      (xdispPos P dec + xframeSize P + 9) { pc := 0, mem := m, out := [], rd := k }
      { pc := mainPos, mem := startMem (xframeSize P) (xdispPos P dec) m, out := [], rd := k } := by
  sorry


/-- The number of cells in `xcells` is `xcellCount`. -/
theorem card_xcells (P : XProgram) (dec : Bool) (lim : Limits) :
    (xcells P dec lim).card = xcellCount P dec lim := by
  sorry

/-- What a compiled run leaves (in place, `Outcome`, over the extended program). -/
structure XOutcome {W : ℕ} (lim : Limits) (P : XProgram) (dec : Bool) (m : ℤ → BitVec W)
    (σ' : State) (m' : ℤ → BitVec W) : Prop where
  holds : Holds W lim σ'.mem m'
  result : (m' Light.Compiler.cRESULT).toInt = σ'.loc 0
  arg1 : m' Light.Compiler.cARG1 = m Light.Compiler.cARG1
  arg2 : m' Light.Compiler.cARG2 = m Light.Compiler.cARG2
  far : ∀ a : ℤ, a < -(xlowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a

/-- **The compiler is correct, with input and output** (in place, `compileProgram_correct`,
restated over `XStepsIn`). A run of the outermost call that emits `o` and consumes `r`, on a
stream `ρ` that agrees with `r` (past its end read as `false`), is matched by a run of the
compiled program from `⟨0, m⟩` that stays in `xcells` (G167-03: a footprint independent of
time), reaches the verdict before `xramSteps` steps, has emitted `o`, and leaves the outcome.

**Proof sketch.** As the vendored proof: `xsteps_start`; `xsim` on the outermost call with
`out = []`, `k = 0`; `steps_tail` on `code.proj` with its footprint (`stepsIn_straight`), lifted.
All three runs are within the setting's cells, which for the whole-program setting
(`Q = xstackCells`, `disp = xdispPos`) are exactly `xcells` (round 3, G167-07); compose them with
`xStepsIn_trans`. -/
theorem xcompileProgram_correct {W : ℕ} {lim : XLimits} {P : XProgram} {p0 : ℕ} {dec : Bool}
    {μ : ℕ → ℤ} {i j : ℤ} {σ' : State} {o r : List Bool} {c : ℕ} {m : ℤ → BitVec W}
    {ρ : List Bool} (hw : (1 : ℤ) ≤ lim.word)
    (h : XExec lim P 0 (xmainStmt p0) ⟨frame [0, i, j], μ⟩ σ' o r c)
    (hρ : ∀ k < r.length, ρ.getD k false = r.getD k false)
    (hfit : Fits W lim.toLimits (xdispPos P dec) (xstackCells P lim.toLimits))
    (hm : Input lim.toLimits μ i j m) :
    ∃ (n : ℕ) (cfg : WordRAM.XCfg W), n < xramSteps P dec c ∧
      WordRAM.XStepsIn (xcompileProgram P p0 dec) lim.input ρ ↑(xcells P dec lim.toLimits) n
        { pc := 0, mem := m, out := [], rd := 0 } cfg ∧
      WordRAM.xstep (xcompileProgram P p0 dec) lim.input ρ cfg =
        .inr (Light.verdictOf dec (σ'.loc 0)) ∧
      cfg.out = o ∧ XOutcome lim.toLimits P dec m σ' cfg.mem := by
  sorry

/-! ## The deliverables -/

/-- The start state of the outermost call on the input `x`: argument 1 is `|x|`, argument 2 is
`0`, the memory is `0` (what `WordRAM.initMem` holds). -/
def xstartState (x : List Bool) : State := ⟨frame [0, x.length, 0], fun _ => 0⟩

/-- Reading `xstartState`. -/
theorem xstartState_eq (x : List Bool) : xstartState x = ⟨frame [0, x.length, 0], fun _ => 0⟩ :=
  rfl

/-- **Compiled programs halt with their output, on every compatible stream** (G167-03, part 1).
A run of the outermost call on `x` that emits `o` and consumes `r` makes the compiled program
halt on `x` with any stream `ρ` that agrees with `r`, within `xramSteps P true c` steps, with
the verdict "the result is positive", the output `o`, and footprint `xcellCount`, independent of
time. A coin-free run (`r = []`) qualifies for every `ρ`.

**Proof sketch.** `xcompileProgram_correct` from `initMem W |x|`, which is an `Input` with `μ = 0`,
`i = |x|` (in range by `|x| ≤ lim.word` and `Fits.inRange`) and `j = 0`; its run stays in `xcells`,
whose card is `xcellCount` (`card_xcells`). -/
theorem haltsWithin_compileProgram {W : ℕ} {lim : XLimits} {P : XProgram} {p0 : ℕ}
    {x ρ o r : List Bool} {σ' : State} {c : ℕ}
    (hx : lim.input = x) (hxw : (x.length : ℤ) ≤ lim.word) (hw : (1 : ℤ) ≤ lim.word)
    (h : XExec lim P 0 (xmainStmt p0) (xstartState x) σ' o r c)
    (hρ : ∀ k < r.length, ρ.getD k false = r.getD k false)
    (hfit : Fits W lim.toLimits (xdispPos P true) (xstackCells P lim.toLimits)) :
    WordRAM.HaltsWithin (xcompileProgram P p0 true) x ρ W (xramSteps P true c)
      (decide (0 < σ'.loc 0)) o (xcellCount P true lim.toLimits) := by
  sorry

/-- **Uniform halting on every RAM stream** (G167-03, part 3, padding). If the Light program
ends within `T` steps on every stream of length `T`, the compiled program halts within
`xramSteps P true T` steps on every RAM stream, of any length: `mem_NSPACE_of_accepts`' first
hypothesis.

**Proof sketch.** Pad `ρ` to `ρ' := (ρ ++ replicate T false).take T`. The Light run on `ρ'`
consumes a prefix `r` of `ρ'` of length at most `T` (`coins_length_le`), and `ρ` agrees with `ρ'`,
hence with `r`, on its first `T` places, reading `false` past its end. Apply
`haltsWithin_compileProgram` and `HaltsWithin.mono` (`xramSteps` is monotone in the cost). -/
theorem haltsWithin_of_streams {W : ℕ} {lim : XLimits} {P : XProgram} {p0 : ℕ} {x : List Bool}
    {T : ℕ} (hx : lim.input = x) (hxw : (x.length : ℤ) ≤ lim.word) (hw : (1 : ℤ) ≤ lim.word)
    (hfit : Fits W lim.toLimits (xdispPos P true) (xstackCells P lim.toLimits))
    (hall : ∀ ρ : List Bool, ρ.length = T →
      EndsIO lim P 0 (xmainStmt p0) (xstartState x) ρ T fun _ _ _ => True) :
    ∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
      WordRAM.HaltsWithin (xcompileProgram P p0 true) x ρ W (xramSteps P true T) v o
        (xcellCount P true lim.toLimits) := by
  sorry

/-- **Nondeterministic acceptance transfers** (G167-03, part 3): under uniform halting, the Light
program accepts nondeterministically within `T` exactly when the compiled program accepts on
some stream: `mem_NSPACE_of_accepts`' second hypothesis.

**Proof sketch.** (→) An accepting stream of length `T` gives an accepting RAM run
(`haltsWithin_compileProgram`). (←) Pad an accepting RAM stream as in `haltsWithin_of_streams`;
the Light run on the padded stream gives a RAM run on the original stream, whose verdict is
`true` by `HaltsWithin.unique`, so the Light result is positive. -/
theorem acceptsND_iff_haltsWithin {W : ℕ} {lim : XLimits} {P : XProgram} {p0 : ℕ}
    {x : List Bool} {T : ℕ} (hx : lim.input = x) (hxw : (x.length : ℤ) ≤ lim.word)
    (hw : (1 : ℤ) ≤ lim.word)
    (hfit : Fits W lim.toLimits (xdispPos P true) (xstackCells P lim.toLimits))
    (hall : ∀ ρ : List Bool, ρ.length = T →
      EndsIO lim P 0 (xmainStmt p0) (xstartState x) ρ T fun _ _ _ => True) :
    AcceptsND lim P p0 0 (fun _ => 0) T ↔ ∃ ρ o : List Bool,
      WordRAM.HaltsWithin (xcompileProgram P p0 true) x ρ W (xramSteps P true T) true o
        (xcellCount P true lim.toLimits) := by
  sorry

open Classical in
/-- **Acceptance probabilities transfer** (G167-03, part 3): under uniform halting, with `m ≥ T`
coins, the Light acceptance probability is the probability that the compiled program accepts on
a uniform stream of `m` coins.

**Proof sketch.** Pointwise on streams of length `m`: by uniform halting and `EndsIO.take_iff`
the Light run on `ρ` exists; the compiled run on `ρ` halts with the verdict "the result is
positive" (`haltsWithin_compileProgram`), and any accepting RAM run on `ρ` has that verdict
(`HaltsWithin.unique`). -/
theorem acceptProb_eq_randProb {W : ℕ} {lim : XLimits} {P : XProgram} {p0 : ℕ} {x : List Bool}
    {T m : ℕ} (hTm : T ≤ m) (hx : lim.input = x) (hxw : (x.length : ℤ) ≤ lim.word)
    (hw : (1 : ℤ) ≤ lim.word)
    (hfit : Fits W lim.toLimits (xdispPos P true) (xstackCells P lim.toLimits))
    (hall : ∀ ρ : List Bool, ρ.length = T →
      EndsIO lim P 0 (xmainStmt p0) (xstartState x) ρ T fun _ _ _ => True) :
    acceptProb lim P p0 0 (fun _ => 0) m T = Randomized.randProb m fun ρ =>
      ∃ o, WordRAM.HaltsWithin (xcompileProgram P p0 true) x ρ W (xramSteps P true T) true o
        (xcellCount P true lim.toLimits) := by
  sorry

/-- **Polynomial-time functions from Light programs** (G167-04). A Light program whose coin-free
run on every input `x` emits `g x` within `C·(|x|+1)^d` Light steps, with limits `L |x|` that
admit the input length and fit a word size `W |x|`, computes a `PolyTimeComputable` function,
**provided** that word size is computable (`WordSizeComputable W TW SW`) with `TW n + W n`
polynomial. `Fits` gives only lower bounds on a sufficient word size; the upper bounds and the
computability are the consumer's obligations (a loop of `n` squarings forces `W` exponential).

**Proof sketch.** `haltsWithin_compileProgram` with `ρ = []` gives halting within
`xramSteps P true c ≤ xstartCost P true + stepsPerStep (xdispPos P true) · C·(n+1)^d`; with
`C' := C + xstartCost P true + stepsPerStep (xdispPos P true) * C`, both this and `TW n + W n` are
at most `C'·(n+1)^d`; apply `WordRAM.polyTimeComputable_of_computes`. -/
theorem polyTimeComputable_of_runs (P : XProgram) (p0 : ℕ) (L : ℕ → Limits)
    {W TW SW : ℕ → ℕ} (hW : WordRAM.WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d) (g : List Bool → List Bool)
    (hL : ∀ n : ℕ, (n : ℤ) ≤ (L n).word ∧ (1 : ℤ) ≤ (L n).word ∧
      Fits (W n) (L n) (xdispPos P true) (xstackCells P (L n)))
    (hrun : ∀ x : List Bool, ∃ (σ' : State) (c : ℕ),
      XExec { toLimits := L x.length, input := x } P 0 (xmainStmt p0) (xstartState x) σ' (g x) []
        c ∧ c ≤ C * (x.length + 1) ^ d) :
    Complexity.PolyTimeComputable g := by
  sorry

end Program

/-! ## Permanent checks (N4, N8) -/

/-- Input reads at the boundary (N8): on `[true]`, positions `-1`, `0`, `1` read `0`, `1`, `0`. -/
theorem inBitVal_boundary :
    inBitVal [true] (-1) = 0 ∧ inBitVal [true] 0 = 1 ∧ inBitVal [true] 1 = 0 := by
  sorry

/-- `half` rounds down, as the arithmetic shift does (N8): `⌊-3/2⌋ = -2`, `⌊-1/2⌋ = -1`. -/
theorem half_boundary : (-3 : ℤ) / 2 = -2 ∧ (-1 : ℤ) / 2 = -1 := by
  sorry

/-- Two coins in sequence consume both, in order (N4). -/
theorem check_two_coins (lim : XLimits) (P : XProgram) (d : ℕ) (σ : State) :
    ∃ σ'', XExec lim P d (.seq (.coin 0) (.coin 1)) σ σ'' [] [true, false] 2 := by
  sorry

/-- Determinism fixes the consumed word's length, even when two runs are offered with words of
different lengths (N4): they cannot both be prefixes of one stream. -/
theorem check_det_length {lim : XLimits} {P : XProgram} {d : ℕ} {s : XStmt} {σ σ₁ σ₂ : State}
    {o₁ o₂ r₁ r₂ : List Bool} {c₁ c₂ : ℕ} {ρ : List Bool}
    (h₁ : XExec lim P d s σ σ₁ o₁ r₁ c₁) (h₂ : XExec lim P d s σ σ₂ o₂ r₂ c₂)
    (hr₁ : r₁ <+: ρ) (hr₂ : r₂ <+: ρ) (hne : r₁.length ≠ r₂.length) : False := by
  sorry

/-- `XExec.bounded` needs `1 ≤ lim.word` (N8): at word limit `0`, `coin` with the bit `true`
leaves a bounded state for an unbounded one. -/
theorem check_bounded_needs_word :
    ∃ (lim : XLimits) (σ σ' : State), lim.word = 0 ∧ σ.Bounded lim.toLimits ∧
      XExec lim [] 0 (.coin 0) σ σ' [] [true] 1 ∧ ¬ σ'.Bounded lim.toLimits := by
  sorry

/-- Emitting a value and returning it differ on negatives (round 3, G167-08): `emit` of `-3`
emits `true` (nonzero), while a returned `-3` rejects (`verdictOf` tests positivity). -/
theorem check_emit_vs_verdict :
    decide ((-3 : ℤ) ≠ 0) = true ∧ Light.verdictOf true (-3) = false := by
  sorry

/-- The outermost call does not run if its entry procedure is missing (round 3, G167-08). -/
theorem check_missing_entry {lim : XLimits} {P : XProgram} {p0 : ℕ} {σ σ' : State}
    {o r : List Bool} {c : ℕ} (hp : P[p0]? = none) :
    ¬ XExec lim P 0 (xmainStmt p0) σ σ' o r c := by
  sorry

/-- The outermost call does not run at depth limit zero (round 3, G167-08). -/
theorem check_zero_depth {lim : XLimits} {P : XProgram} {p0 : ℕ} {σ σ' : State}
    {o r : List Bool} {c : ℕ} (hd : lim.depth = 0) :
    ¬ XExec lim P 0 (xmainStmt p0) σ σ' o r c := by
  sorry

end TCSlib.Draft.PROG2

## ===== campaign/items/ram-tm/PROG2-DESIGN.md =====

# (a5): string input and output for Light (PROG-2), design draft

2026-11-18, maintainer draft for Seyoon. Bridge item (a5) of the RAM bridge assessment, Option A
(PROG-2, decided by Seyoon on 2026-11-18). Base: `complexity/ram-simulation` after #381.

## 1. What it is for

A Light program can read only its preloaded memory and two integer arguments, and can return only
one integer and a verdict. The crypto bridge needs programs that read a bit string and write one,
written in Light with its program logic, and then compiled to the word RAM. Its `HaltsWithin`
run then feeds `WordRAM.polyTimeComputable_progOut` (#379). PROG-2 adds this I/O to the language
itself, as designed in October (design §15c, §15d):

- `x := inBit e`: the input bit at position `e`, as `0` or `1`; `0` off the input. Read in place.
- `emit e`: append the bit "`e ≠ 0`" to the output.
- `x := coin`: the next coin, for nondeterministic and randomized programs.
- `x := half e`: `⌊e / 2⌋`.

These match the extended RAM's `rdIn`, `emit`, `coin` and `half` one for one. Each compiles to its
expression, the one new instruction on `T₀`, and, when it writes a local, the assignment's
two-instruction store: `inBit` and `half` take `e.size + 3` instructions, `coin` 3, `emit`
`e.size + 1` (G167-06).

## 2. What was decided in October (Seyoon, 2026-10-12, "all four as recommended"), still binding

- **Option A:** the I/O indices are added to `Light.Exec` **in place**, with `o` (bits emitted) and
  `r` (coins consumed). `Light.Ends` keeps its type: `∃ σ' o r c, Exec … ∧ c ≤ T ∧ Q σ'`. So
  `Meets`, the 14 library routines and their proofs are untouched apart from witness lines.
- **The RAM is extended by a wrapper,** which is already done: `WordRAM.XInstr`. The compiler's code
  type becomes `List XInstr`, and the vendored segment lemmas over `Instr` apply through
  `XProgram.proj` and `XSteps.of_steps_proj` (tier 0, proved).
- `emit` appends "nonzero". The input is a new field of `Light.Limits`, which no vendored file
  constructs.

## 3. The signatures

October's mirror (`campaign/items/stage2/ExtensionsDraft.lean.txt` on the chapters 3–4 branch, 415
lines, elaborated then) states every new declaration over mirror types. In place they become:

| Mirror (October) | In place |
|---|---|
| `XStmt`: 7 constructors and 4 new | `Light.Stmt` gains `inBit`, `emit`, `coin`, `half` |
| `XLimits extends Limits` with `input` | `Light.Limits` gains the field `input : List Bool` |
| `XExec … σ σ' o r c` | `Light.Exec` gains the indices `o r`, and four rules |
| `XEnds` | `Light.Ends`, same type, with `∃ σ' o r c` |
| `XStmt.silent`, `XProgram.SilentSet`, `EndsIO.ofXEnds`, `MeetsIO.ofXMeets` | new, in `Light/IO.lean` (round 2, G167-01) |
| `EndsIO`, `MeetsIO`, the 13 `EndsIO.*` rules, `EndsIO.callLast` | new, in a new vendored-adjacent file `Light/IO.lean` |
| `XExec.det`, `coins_length_le`, `output_length_le` | new, in `Light/IO.lean` |
| `AcceptsND`, `acceptProb` | new, in a Complexity-side file (gate 10's auditor preferred that home) |
| `XFits` | removed (round 2, N2): `Fits` is unchanged; `|x| ≤ lim.word` is a separate hypothesis |
| `xcompileStmt` … `xcompileProgram_correct`, the deliverables | the in-place compiler (round 2, G167-02) |

**New since October:**
- **`Light/Renumber` (#381):** `Stmt.shift` gains four arms; `Exec.shift` gains four cases and
  the indices.
- **`Light/TMProc` (#382, job G in flight):** its statement uses only `Meets`, whose type is
  unchanged. Its proof is safe provided it reasons through `Ends` rules and does not invert `Exec`
  directly (§6, risk 1).
- **The deliverables** (round 2, after gate 167; Seyoon, 2026-11-18: "all three now"). The
  mirror `prog2/PROG2Mirror.lean.txt` states them over concrete compiler definitions:
  - `haltsWithin_compileProgram`: a Light run of the outermost call on `x` that emits `o` and
    consumes `r` makes the compiled program halt on `x`, on **every RAM stream that agrees with
    `r`** (past its end read as `false`), within `ramSteps P true c` steps, with the verdict
    "the result is positive", the output `o`, and the footprint `lowCell + lim.space`, which
    **does not grow with time**. Coin-free runs qualify for every stream.
  - `haltsWithin_of_streams`, `acceptsND_iff_haltsWithin`: Light halting on all streams of length
    `T` gives RAM halting on every stream, and nondeterministic acceptance transfers: the two
    hypotheses of `WordRAM.mem_NSPACE_of_accepts` (so `mem_NL_of_accepts`, with the constant
    footprint).
  - `acceptProb_eq_randProb`: acceptance probabilities transfer, for BPP consumers.
  - `polyTimeComputable_of_runs`: a Light program whose coin-free runs emit `g x` within
    polynomial Light cost computes a `PolyTimeComputable` `g`, **given** a length-dependent word
    size `W` with a `WordSizeComputable` witness and `TW n + W n` polynomial. Round 1 claimed this
    followed from polynomial cost alone, which is false: `Fits` gives only lower bounds on a
    sufficient word size, and a loop of `n` squarings forces `W` exponential (G167-04).
- **Lifting library routines** (G167-01): an `Ends` fact lifts to `EndsIO` for code that emits and
  consumes nothing and calls only into a **silent set** of procedures, a condition stable under
  appending and relocation, so `Light.Std`'s routines stay usable inside I/O programs.

## 4. The edit set (from October's `NOTES.md` §5, rechecked against today's tree)

- **`Stmt`, four new arms or cases each:**
  - `Syntax` (the type);
  - `Assigns` (`Stmt.assigns`);
  - `Rules` (`Ends.of_blockSafe`);
  - `Renumber` (`Stmt.shift`);
  - `Compiler/StatementCode` (`Stmt.size`, `compileStmt`, `length_compileStmt`, `Stmt.width`,
    four `Stmt.width_*_le_iff`);
  - `Compiler/Simulation` (four `codeAt_*`).
- **`Exec`, the indices and four rules:**
  - `Syntax` (the type);
  - `Logic` (`Exec.append`, `Ends`, and the rule proofs: about 22 witness lines);
  - `Rules` (8 witness lines, and 6 `cases` inversions, which keep working under Option A);
  - `Assigns` (`Exec.loc_eq_of_notMem_assigns`, plus 2 witness lines);
  - `RunsStayInLimits`:
    - `Exec.bounded`, with the new hypothesis `1 ≤ lim.word`, given by `Light.Std`;
    - `Exec.mem_outside`;
  - `Renumber` (`Exec.shift`);
  - `Compiler/Simulation` (`sim`: four new `sim_*`, with `o` and `r` threaded through `Start`,
    `Finished` and the nine existing `sim_*`);
  - `Compiler/WholeProgram` (`compileProgram_correct` restated, plus the theorem of §3).
- **Code type** (round 3, after gate 167's G167-02):
  - `compileStmt`, `bodiesCode` and `compileProgram` become `List XInstr`, as does the code field
    of `Setting`.
  - The straight-line code (`compileExpr`, `compileCond`, the call frames, the epilogue, the
    dispatcher, the start-up and verdict code) stays `List Instr`. It reaches the extended code
    through `XCodeAt.proj`; its runs lift by `XSteps.of_steps_proj` and
    `XStepsIn.of_stepsIn_proj`.
  - **Changed in `ProgramCode`** (round 4, after gate 167 round 3):
    - `mainCode` (the outermost statement's `compileStmt`, then `tailCode`) becomes
      `List XInstr`, with `tailCode` under `.base`;
    - the code-location lemmas (`codeAt_headCode`, `codeAt_mainStmt`, `codeAt_tailCode`,
      `codeAt_dispatcher_dispPos`, `codeAt_startCode`) are restated over the extended code;
    - so are `codeAt_bodiesCode` and `codeAt_bodies`: its `code` becomes an `XProgram`, with
      `XCodeAt` throughout. Its one caller is `WholeProgram`'s `bodyAt`.
  - **Unchanged in `ProgramCode`:** the layout definitions (`frameSize`, `mainPos`, `tailPos`,
    `firstBody`, `entries`, `endPos`, `dispPos`, `codeLayout`) and the `List Instr` parts
    (`headStraight`, `headCode`, `tailCode`, `poolCode`, `zeroCode`, `frameCode`,
    `startStraight`, `startCode`).
  - **Changed in `StartUp`:** `steps_start` is stated over `compileProgram`. It is restated over
    the projection, and as an extended run with its footprint (`xsteps_start` in the mirror).
    Its memory calculations stay.
  - `Dispatcher`, `Expressions`, `Conditions`, `CallFrames` and `Cells` are untouched.
- **The footprint** (round 3, G167-07): `Finished.run` becomes an `XStepsIn` run within the
  setting's cells.
  - The base-instruction lemmas keep their statements. H2 **adds** footprint companions beside
    them for the expression, condition, call-frame and dispatcher runs, with state-dependent
    address bounds for indirect loads and stores. `stepsIn_straight` exists; the start-up's is
    `xsteps_start`.
  - `Programs/WordRAM/Extended` gains `XStepsIn.mono` and `XStepsIn.trans`.
- **Mirror only:** `XStmt.ofStmt`, `XExec.ofExec` and `XSetting.xlim`. In place `Light.Limits`
  carries the input, so `xlim` is the setting's limits themselves (round 4, G167-05).
- **Vendored headers:** each edited file lists the change as a local modification. Rule 10 does
  not apply between vendored files (Seyoon, 2026-11-18).

Not affected: the `Expr`, `Cond` and `Op` inductions; `Lib`, `Frames` and `Calls`, which neither
match on `Stmt` or `Exec` nor destructure `Ends` witnesses (October's grep, to recheck).

## 5. Jobs

Definitions change in place, so a sorried statements PR cannot land first. Every exhaustive
proof must be extended in the same change. Instead:

0. **A statement gate first, on a mirror** (Codex audit). I update October's mirror to the list
   in §3, with the deliverable of §3 stated over a mirror compiler, and elaborate it as a scratch
   file. The gate audits the signatures before any vendored file changes.
1. **Job H1, the language core** (Codex, about 1,000–1,600 lines):
   - `Syntax`, `Logic`, `Rules`, `Assigns`, `RunsStayInLimits` and `Renumber`, in place;
   - the new `Light/IO.lean`: `EndsIO`, `MeetsIO`, the rules, `det`, and the length bounds.

   Its PR builds with the compiler's files still on `List Instr` and their four new
   `Stmt`/`Exec` cases left as `sorry`. That is a disclosed, temporary admission in vendored
   proofs, removed by H2.
2. **Job H2, the compiler** (Codex, about 1,800–3,000 lines with round 2's scope): the code type
   moves to `List XInstr`, with the four new `compileStmt` and `sim_*` cases, `sim` with streams,
   `compileProgram_correct` with the footprint, and the deliverables of §3, padding and
   probabilities included. Its gate checks that the vendored compiler is back to 0 admissions.
3. **(a4) and (b2) follow:** generic views and codecs as Light routines with `MeetsIO` specs, and
   `PolyTimeComputable g ⇒` a word-RAM program, from (b1) and this.

**Size:** about 2.8k–4.6k lines after round 2's scope (October's 1.4k–2.3k, the compiler cases,
streams, the footprint, and the padding and probability transfers).

## 6. Risks

1. **Job G** proves `Light.exists_tmProc` against today's `Exec`. If its proof inverts `Exec` or
   builds witnesses by hand, H1 breaks it. Either land G before H1 starts, or tell G now to reason
   only through `Ends`/`Meets` rules and the `light_*` tactics. **Recommendation: sequence H1
   after G lands** (H1 starts with the mirror gate anyway).
2. **Tier 2 jobs A–E** do not touch Light. No conflict.
3. **`Ends` hides coins existentially.** Specifications meant for every coin stream must use
   `EndsIO`. Crypto programs are coin-free (coins are read from the input), so this does not
   arise for them.
4. **Vendored drift:** after PROG-2, the Light files diverge from upstream beyond the
   module-syntax edits. Their headers list it. Upstream ports later must be merged by hand.

## 7. Decisions (Seyoon, 2026-11-18: "go with your recommendations")

Ruled: the process of §5, with a mirror statement gate (gate 167) first; H1 after job G lands;
`AcceptsND` and `acceptProb` stated in this round. The deliverable also needs `|x| ≤ lim.word`,
for the argument cell holding `|x|` (`Input.arg1_le`); the mirror carries it. The mirror is
`items/ram-tm/prog2/PROG2Mirror.lean.txt`. It elaborates with 0 errors and 27 sorried statements
(`mirror.log`).

### The decisions as posed

1. **The process of §5:** a mirror statement gate (Codex audit), then H1 and H2 in sequence, with
   H1's temporary compiler admissions. *Recommended.*
2. **Sequencing against job G:** H1 after G lands (*recommended*), or brief G now to avoid `Exec`
   inversions.
3. **`AcceptsND` and `acceptProb`:** state them in this round, as October did (*recommended*: they
   cost little and serve NL and BPP consumers), or defer them.

### Round 2 (gate 167 HOLD: 0/4/2)

Seyoon, 2026-11-18: H2's compiler theorem covers **all three** of the auditor's parts: coin
streams, a footprint independent of time, and the padding and probability interface. The
round-2 mirror answers G167-01 to G167-06 (`gates/167-prog2-statements/resolutions.md`).

### Round 3 (gate 167 round 2 HOLD: 0/1/3)

The mirror adds:
- `StartUp` to the edit set: `steps_start_proj`, `xsteps_start` and the `xcodeAt_*` lemmas
  (G167-02);
- complete readers for `silent`, `calls`, `xcells`, `xcellCount` and `xstoreLocal` (G167-05);
- the footprint inside the simulation contract (`XSetting.cells`, `XFinished.run` over
  `XStepsIn`, `xStepsIn_mono`, `xStepsIn_trans`; G167-07);
- the two remaining N8 checks (G167-08).

The H2 size estimate grows by the footprint versions of the segment lemmas, about 300–600
lines.

## ===== campaign/gates/167-prog2-statements/findings-r3.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| G167-R3-01 | minor | `PROG2Mirror.lean.txt:39` · compiler edit inventory; `PROG2-DESIGN.md` §4; `Compiler/ProgramCode.lean:147`, `:261` | G167-02's substantive compiler boundary is repaired, but the inventory retains contradictory wording and omits helper migrations inside an already changed file. | The mirror still says `StartUp` is “untouched” at lines 41–42, then correctly lists its changes at lines 53–56. Also, the existing `mainCode : List Instr` combines `compileStmt` with `tailCode`, and `codeAt_bodies` quantifies `code : List Instr`; both need extended-code adaptations when `compileStmt` and `bodiesCode` change type. The concrete `xcompileProgram` and `XSetting.bodyAt` already specify the required behavior, so this is an inventory defect, not a false compiler contract. | Remove `StartUp` from the untouched-file sentence. Explicitly include `mainCode`, `codeAt_bodiesCode` and `codeAt_bodies` in H2's ProgramCode migration list, and distinguish unchanged base-instruction APIs from the footprint companions H2 must add. |
| G167-05 | minor | `PROG2Mirror.lean.txt:31`, `:872` · landing inventory and `XSetting.xlim`; `resolutions-r3.md` | The requested readers are supplied, but “no other new landing definition lacks a reader” still needs one qualification. | `XSetting.xlim` publicly constructs `{ toLimits := S.lim, input := S.input }`, with no equation or projection readers. The header says every declaration lands except `XStmt.ofStmt` and `XExec.ofExec`; it does not exempt this helper. With input incorporated into `Light.Limits` in place, this separate conversion may instead be mirror plumbing. | Mark `XSetting.xlim` mirror-only and reconcile its separate input field with the in-place mapping, or specify its landing name and provide readers for its underlying limits and input. This leaves G167-05 open only at minor severity. |
| G167-R3-N1 | note | Exchange intake · all 34 sections; `prog2/mirror.log` | Integrity passes; the supplied elaboration evidence matches the audited mirror. | Both entries of `SHA256SUMS` pass. The bundle is 630602 bytes with SHA-256 `b2579ed557d275fc886a690d30f573c99128578d0a1c50135269cc895a7fb72b`. Its 34 section paths exactly match `BUNDLE-FILES.txt` in order; after removing framing, every section matches git commit `b295a77f316cd6c564ad0402ece64bf0b422572e`. The mirror has 1295 lines, and all 67 warning locations match its 67 sorried theorem declarations; the log ends with `exit 0` and contains no errors. No independent Lean replay was performed. | No integrity repair required. This verdict concerns the statement mirror; H1 and H2 still require their implementation checks and replays. |
| G167-R3-N2 | note | `PROG2Mirror.lean.txt:1008` · five `xcodeAt_*` lemmas; `:1043` · `steps_start_proj`; `:1087` · `xsteps_start` | The new layout and start-up statements are true; G167-02's major is resolved. | Statement lengths put the head, main statement, tail, dispatcher and start-up at the five claimed positions. Projection preserves each embedded base segment, so the vendored start-up proof applies unchanged in substance. Its count is `3 + 1 + (xdispPos + xframeSize + 4) + 1 = xdispPos + xframeSize + 9`. Start-up uses direct negative addresses, including the pool endpoint, and no indirect load/store; therefore arbitrary initial memory needs no extra address invariant. The negative-one range hypothesis suffices for its two jumps. | Accept the signatures. Correct the inventory wording in G167-R3-01. |
| G167-R3-N3 | note | `PROG2Mirror.lean.txt:876`, `:885`, `:892`, `:913`, `:943`, `:1120` · cells, footprint composition and simulation | G167-07 is resolved: the fixed footprint now constrains intermediate reads and writes. | `XFinished.run` now requires `XStepsIn` within `S.cells`. Accessed stack indices are positive and at most `Q`, hence their addresses lie between `-2·Q` and `0`; pool addresses extend down to `-(25 + 4·disp)`. Temporaries extend down to `-(23 + 8·F)`, which is above that pool bound because `disp ≥ 2·(F + 1)`. Other registers are negative constants; expression loads and stores access nonnegative addresses strictly below `lim.space` by safety and the range hypotheses. Thus execution induction can carry this invariant through expressions, conditions, calls and the four new instructions. Monotonicity and same-footprint concatenation follow by run-length induction. Substituting the whole-program setting's stack size and dispatcher position makes its cells exactly the coercion of `xcells`. | Implement the named segment footprint obligations in H2, using state-dependent address bounds for indirect loads/stores. The strengthened simulation, projection lifting and new composition statements supply the required route; endpoint agreement is no longer being used to infer a footprint. |
| G167-R3-N4 | note | `PROG2Mirror.lean.txt` · new readers and permanent checks | The requested reader additions and all three new sanity statements have their stated meanings; G167-08 is resolved. | `silent_leaf` covers all six remaining silent leaves; `calls_leaf` covers all seven non-call leaves, and the sequence, branch and loop equations complete the cases. The store, interval, cardinal-bound and setting-cell equations restate their definitions. For the new checks, `-3 ≠ 0` gives emitted bit `true`, whereas `0 < -3` is false; call inversion contradicts either a missing body lookup or `0 < 0` at zero depth. Adversarial start-up spot checks also cover an empty deciding program with word size 1 and zero memory limit (38 steps, footprint `[-129,0)`), a body `coin 9` with word size 1, and an empty nondeciding program. These executable spot checks supplement the mathematical audit and are not Lean proofs. | Accept these reader and sanity signatures, subject to the separate `xlim` inventory repair above. |
| G167-R3-N5 | note | `PROG2Mirror.lean.txt` · retained semantics, logic, lifting and deliverables | The remaining round-2 conclusions are preserved; no further substantive H1/H2 contract gap was found. | All 74 retained theorem signatures, including all 55 retained sorried statements, are identical to round 2. Execution induction still gives local preservation, boundedness with `1 ≤ lim.word`, memory preservation and trace-length bounds; reachable silent sets justify empty-trace lifting after append and relocation. Sequencing passes the unused stream suffix, and determinism identifies the consumed prefix. Padding agrees with the RAM's default-false reads, giving uniform halting and the acceptance equivalence; pointwise verdict uniqueness then gives the probability transfer. The function corollary retains the computable word-size witness and polynomial bound required by `WordRAM.polyTimeComputable_of_computes`. The nine new closed proofs are defining-equation readers; the twelve other new theorem statements remain disclosed sorries. | Preserve these hypotheses and interfaces in H1/H2. Word-size and complexity-class resource bounds remain the stated consumer obligations. |

Verdict: CLEAR — 0 blockers, 0 majors, 2 minors.

## ===== campaign/gates/167-prog2-statements/resolutions-r4.md =====

# Gate 167 round 3 minors: resolutions (round 4 text)

Round 3 was **CLEAR** (0 blockers, 0 majors, 2 minors; `findings-r3.md`). Both minors are
wording repairs to the mirror's header and the design note; no statement changed. The mirror is
`items/ram-tm/prog2/PROG2Mirror.lean.txt`, 1,311 lines; round 3's text is kept as
`PROG2Mirror-r3.lean.txt`. It elaborates with 0 errors and the same 67 sorried statements
(`prog2/mirror.log`, on `oleans-cl169-cl166`).

| # | Severity | Resolution |
|---|---|---|
| G167-R3-01 | minor | The header no longer calls `StartUp` untouched: it keeps its straight-line code and memory calculations, and `steps_start` changes. `ProgramCode`'s migration list now names `mainCode` (to `List XInstr`, with `tailCode` under `.base`), `codeAt_bodiesCode` and `codeAt_bodies` (its `code` becomes an `XProgram`, `XCodeAt` throughout; its one caller is `WholeProgram`'s `bodyAt`), and lists the layout definitions and `List Instr` parts that keep their types. The header and design §4 separate the unchanged base-instruction lemmas from the footprint companions H2 adds (expression, condition, call-frame and dispatcher runs, with state-dependent address bounds for indirect loads and stores; the start-up's is `xsteps_start`). |
| G167-05 | minor | `XSetting.xlim` is marked **mirror only**, in its docstring, the header and design §4: in place `Light.Limits` carries `input`, the setting's `input` field is `lim.input`, and `S.xlim` is `S.lim`. No new public name. |
| N1 – N5 | note | No change needed. N3's route (segment footprint obligations with state-dependent bounds) is carried into the H2 brief. |

## ===== scripts/copy-text-screen-v3.py =====

```
"""Text-level copy screen for retrofit deliveries, v3 (declaration-keyed).

Identical to audits/evidence/retrofit/copy-text-screen-v2.py except in how declarations are told
apart. v2 skipped a pair when (path, extracted name) coincided, so two distinct declarations in one
file with the same short name were never compared: the same name in two namespaces (a generic
`DiagSimulator.time_hierarchy_of_pos` beside the received `Complexity.time_hierarchy_of_pos`, both
written `theorem time_hierarchy_of_pos`), or two anonymous instances (Diagonal Part 1 gate, m2).
v3 identifies each declaration by its path and source position and skips a pair only when both
sides are the same declaration. Labels: as in v2 (`<file>::<name>`) when the extracted name is
unique among the file's screened declarations; otherwise the namespace-qualified name, with `#k`
appended (k-th in source order) when that is still not unique. Namespaces are tracked through
`namespace`, `section`, `noncomputable section`, `mutual` and `end`; a dotted `namespace A.B`
opens two scopes, as in Lean, and `_root_.` is honoured. Hence, when no file in the argument list
has two screened declarations with the same extracted name, v3's output is byte-identical to
v2's. An `end` that closes no matching scope stops the screen (exit 1, message on stderr).

For the given Lean files it lists every like-kind pair (proof vs proof, term vs term) in which one
declaration reproduces at least half of another's extracted body (at least 60 characters, greedy
tiling with blocks of at least 25), within a file and across the given files. It also prints the
total reproduced text. Run it before and after a change: a pair present after but not before is
new duplication; inlining a deleted copy into a consumer shows up as such a pair.
Usage: python3 -I copy-text-screen-v3.py <repo-root> <file.lean> [<file.lean> ...]
"""
import os, re, sys
root, files = sys.argv[1], sys.argv[2:]
paths = list(dict.fromkeys(os.path.normpath(f) for f in files))
nbase = {}
for p in paths: nbase[os.path.basename(p)] = nbase.get(os.path.basename(p), 0) + 1
label = lambda p: os.path.basename(p) if nbase[os.path.basename(p)] == 1 else p
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
SCOPE = re.compile(r"^[ \t]*(?:(namespace)[ \t]+(\S+)|(?:noncomputable[ \t]+)?(section)\b[ \t]*([^\s]*)"
                   r"|(mutual)\b|(end)\b[ \t]*([^\s]*))", re.M)
def scopes(p, t):
    """(offset, namespace) after each scope command of the stripped text `t`, in source order."""
    stack = []; ev = [(0, '')]
    for m in SCOPE.finditer(t):
        if m.group(1): stack += [('namespace', c) for c in m.group(2).split('.')]
        elif m.group(3): stack.append(('section', m.group(4)))
        elif m.group(5): stack.append(('mutual', ''))
        else:  # `end A.B` closes the innermost scopes B, then A; a bare `end` an anonymous one
            for c in reversed(m.group(7).split('.')):
                if not stack or stack[-1][1] != c:
                    sys.exit(f"copy-text-screen-v3: {p}:{t.count(chr(10), 0, m.start()) + 1}: "
                             f"`end {m.group(7)}` does not close {stack[-1] if stack else 'any scope'}")
                stack.pop()
        ev.append((m.end(), '.'.join(n for k, n in stack if k == 'namespace')))
    return ev
def qualify(ns, name):
    if name.startswith('_root_.'): return name[len('_root_.'):]
    return f'{ns}.{name}' if ns else name
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiled(a, b):
    c = 0
    while True:
        n, seg = lcs(a, b)
        if n < 25: return c
        c += n; a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
grams = lambda x: {x[i:i + 25] for i in range(len(x) - 24)}
decls = []
for p in paths:
    t = strip(open(f'{root}/{p}', encoding='utf-8').read()); ms = list(DECL.finditer(t))
    ev = scopes(p, t); found = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        ns = [n for o, n in ev if o <= m.start()][-1]
        if len(bd) >= 60: found.append((m.start(), m.group(3), qualify(ns, m.group(3)), kind, bd))
    short = {}; qual = {}
    for (_, nm, qn, _, _) in found: short[nm] = short.get(nm, 0) + 1; qual[qn] = qual.get(qn, 0) + 1
    seen = {}
    for (pos, nm, qn, kind, bd) in found:
        if short[nm] == 1: name = nm
        elif qual[qn] == 1: name = qn
        else: seen[qn] = seen.get(qn, 0) + 1; name = f'{qn}#{seen[qn]}'
        decls.append(((p, pos), name, kind, bd, grams(bd)))
pairs = []; total = 0
for (fa, a, ka, ta, ga) in decls:
    for (fb, b, kb, tb, gb) in decls:
        if fa == fb or ka != kb or not (ga & gb): continue
        sh = tiled(tb, ta)
        if sh >= 60 and 2 * sh >= len(tb):
            pairs.append((sh / len(tb), sh, len(tb), f'{label(fa[0])}::{a}', f'{label(fb[0])}::{b}')); total += sh
pairs.sort(reverse=True)
print(f"declarations screened: {len(decls)}; copy pairs (target reproduces >= half of source): {len(pairs)}; reproduced text: {total:,} chars")
for frac, sh, ln, a, b in pairs:
    print(f"   {a}  reproduces  {b}: {sh}/{ln} = {frac:.0%}")
```

## ===== TCSlib/Programs/Light/Assigns.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Assigns.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Assigns.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Logic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A statement changes only the local variables that it assigns

`s.assigns` lists the local variables that the statement `s` assigns: the targets of its
assignments and the result variables of its calls.  A run of `s` leaves every other local variable
as it was (`Exec.loc_eq_of_notMem_assigns`), so every fact about `s` may be extended by "all other
locals are as before" (`Ends.keeping`).  A lemma about a piece of program text therefore speaks
about the memory and about the locals that the piece assigns, and about no other local.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The local variables that a statement assigns: the targets of its assignments and the result
variables of its calls. -/
@[simp] def Stmt.assigns : Stmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]

/-- A run leaves a local variable that the statement does not assign as it was. -/
theorem Exec.loc_eq_of_notMem_assigns {s : Stmt} {σ σ' : State} {c y : ℕ}
    (h : Exec lim P d s σ σ' c) (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by
  induction h with
  | skip => rfl
  | set _ => exact Function.update_of_ne (by simpa using hy) _ _
  | store _ _ _ => rfl
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ fun h => hy (List.mem_append_right _ h)).trans
      (ih₁ fun h => hy (List.mem_append_left _ h))
  | iteTrue _ _ _ ih => exact ih fun h => hy (List.mem_append_left _ h)
  | iteFalse _ _ _ ih => exact ih fun h => hy (List.mem_append_right _ h)
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => exact (ih₂ hy).trans (ih₁ hy)
  | call _ _ _ _ _ => exact Function.update_of_ne (by simpa using hy) _ _

/-- **All other locals are as before.**  Whatever holds after a statement, it also holds that the
locals that the statement does not assign are unchanged. -/
theorem Ends.keeping {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ s.assigns, σ'.loc y = σ.loc y := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc, hq, fun _ hy => he.loc_eq_of_notMem_assigns hy⟩

/-- **All other locals are as before**, for a list `xs` that contains the locals that the statement
assigns. -/
theorem Ends.keepingBut {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (xs : List ℕ) (hxs : s.assigns ⊆ xs := by simp) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ xs, σ'.loc y = σ.loc y :=
  h.keeping.mono le_rfl fun _ hq => ⟨hq.1, fun y hy => hq.2 y fun hmem => hy (hxs hmem)⟩

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
* added the repository-standard `set_option` header;
* appended reading lemmas (`rfl`/`Iff.rfl` restatements of definitions) for TCSlib's own
  proofs, which do not unfold vendored definitions.
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

/-- A procedure specification consists of its body lookup and a bounded execution of that
body from the argument frame. -/
theorem meets_iff {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ}
    {μ : ℕ → ℤ} {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} :
    Meets lim P p d vals μ T R ↔
      ∃ body, P[p]? = some body ∧
        Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem :=
  Iff.rfl

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

## ===== TCSlib/Programs/Light/Compiler/CallFrames.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/CallFrames.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/CallFrames.lean`, with imports remapped;
* v4.25 proof repair (split_ifs: v4.25 leaves the `if` inside the argument);
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Conditions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/

/-- The code of the arguments only changes the memory. -/
theorem straight_argsCode : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  | [], _ => by simp [argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨straight_compileExpr e k, straight_argsCode es (k + 1)⟩

/-- The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
and the temporaries from T_k on. -/
theorem effects_argsCode (I : Framed Z σ q m) (es : List Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) := by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [argsCode, effects_append]
    refine ⟨fun i hi => ?_, Ae.trans (Aes.mono (by cells))⟩
    cases i with
    | zero => exact Aes.read (by cells) ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)

/-! ## The new frame -/

/-- The code for one more local variable. -/
private theorem frameInit_succ (F' n : ℕ) : frameInit (F' + 1) n = frameInit F' n ++
    [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] := by
  simp [frameInit, List.range_succ, List.flatMap_append]

private theorem straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ frameInit F' n, Straight i
  | 0 => by simp [frameInit]
  | F' + 1 => by
    rw [frameInit_succ]
    exact List.forall_mem_append.2 ⟨straight_frameInit n F', by simp [Straight]⟩

/-- The code that fills the first F' local variables of the new frame at q': the first n from the
temporaries, the others with 0.  It changes nothing but ADDR and stack cells from q' on. -/
private theorem effects_frameInit (Z : Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W)
    (hNFP : m cNFP = wd W (cStack q'))
    (hpool : ∀ i < F', m (cPool (2 * i)) = wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F',
        effects (frameInit F' n) m (cStack (q' + i)) = if i < n then m (cT i) else m cZERO) ∧
      AgreeOutside (insert cADDR (Stack q' Z.Q)) m (effects (frameInit F' n) m) := by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), AgreeOutside.refl _ m⟩
  | succ F' ih =>
    obtain ⟨val, A⟩ := ih (fun i hi => hpool i (by omega)) (by omega)
    -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
    rw [frameInit_succ, effects_append, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR (A.read (by cells) hNFP) (A.read (by cells) (hpool F' (by omega))),
      cStack_sub, effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨fun i hi => ?_, (A.update (by cells) _).update (by cells) _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)] <;> simp [*]
    · cell_read using val i (by omega)

/-- The code of the new frame only changes the memory. -/
theorem straight_newFrame (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [Straight], straight_frameInit n F⟩,
    by simp [Straight]⟩

/-- The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
before that frame holds the position to return to.  Of the stack, only cells from q + F on have
changed. -/
theorem effects_newFrame (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
      AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) := by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [newFrame, effects_append, effects_cons, effects_nil]
  -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
  -- frame q change, so the memory goes on representing σ in the frame q.
  rw [effect_sub cNFP R.fp (R.pool _ hN), cStack_sub, ← Nat.add_assoc]
  have A₁ := (AgreeOutside.refl (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m).update (a := cNFP) (by cells)
    (wd W (cStack (q + Z.F + 1)))
  -- the local variables of the new frame
  obtain ⟨val, A⟩ := effects_frameInit Z args.length (q + Z.F + 1) Z.F _
    (Function.update_self cNFP _ m) (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize effects (frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ cNFP = wd W (cStack (q + Z.F + 1)) :=
    A.read (by cells) (Function.update_self _ _ _)
  have A₂ := A₁.trans (A.mono (by cells))
  -- ADDR := NFP + 2
  rw [effect_add cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), cStack_succ_add]
  have A₃ := A₂.update (a := cADDR) (by cells) (wd W (cStack (q + Z.F)))
  -- the cell at ADDR := ret
  rw [effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)),
    (R.beyond hq A₃).pool ret hret]
  have A₄ := A₃.update (a := cStack (q + Z.F)) (by cells) (wd W ret)
  have R₄ := R.beyond hq A₄
  -- FP := NFP + 0
  rw [effect_add cFP (by cell_read using hNFP) R₄.zero, add_zero]
  refine ⟨?_, by cell_read,
    (A₄.mono (Set.union_subset scratch_subset_writable stack_subset_writable)).update (by cells) _⟩
  refine R₄.of_agreeOutside ((AgreeOutside.refl {cFP} _).update rfl _) (by cells)
    (Function.update_self _ _ _) (fun i hi => ?_)
    fun a ha => (Function.update_of_ne (by cells) _ _).trans (R₄.mem a ha)
  -- local variable i of the new frame: argument i, or 0
  cell_read
  rw [val i hi]
  split_ifs with h
  · cell_read using hargs i h
  · cell_read
    rw [R.zero]
    simp [frame, List.getElem?_eq_none (not_lt.1 h)]

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/Cells.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/Cells.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/Cells.lean`, with imports remapped;
* v4.25 proof repair (simp: v4.25 does not rewrite the cast in this position);
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* imports `TCSlib.Programs.Compat` for names that differ at our Mathlib pin;
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.StatementCode
import TCSlib.Programs.Compat

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr)

/-! ## The numbers that never change -/

/-- The word size is large enough for the limits: words hold 2 · word + 2 (so the difference of two
values, and one less, is in range), all addresses of the memory, all addresses of a stack of Q
cells, and all numbers 0, …, N of the pool. -/
structure Fits (W : ℕ) (lim : Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W

/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v :=
  inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h

/-- The numbers on which the proofs about compiled code depend: the layout of the code, the limits
on the runs of the light program, and the number of stack cells.  The pool holds the numbers from 0
to the position of the dispatcher. -/
structure Sizes (W : ℕ) extends CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp

/-! ## Sets of cells -/

/-- What the evaluation of an expression into T_k may change: ADDR and the temporaries T_j with
k ≤ j ≤ 2 F. -/
def Temps (k F : ℕ) : Set ℤ := {a | a = cADDR ∨ ∃ j, k ≤ j ∧ j ≤ 2 * F ∧ a = cT j}

/-- The stack cells j with q ≤ j < Q. -/
def Stack (q Q : ℕ) : Set ℤ := {a | ∃ j, q ≤ j ∧ j < Q ∧ a = cStack j}

/-- The cells of the local variables of the outermost frame. -/
def MainFrame (F : ℕ) : Set ℤ := Stack mainFrame (mainFrame + F)

/-- The cells of the pool that hold the numbers 0, …, N. -/
def Pool (N : ℕ) : Set ℤ := {a | ∃ n, n ≤ N ∧ a = cPool n}

/-- The cells that the start-up code fills and no compiled statement changes: the registers for 1,
0, -1 and the pool. -/
def Constants (N : ℕ) : Set ℤ := {cONE, cZERO, cNEG} ∪ Pool N

/-- The cells that compiled code uses freely: the registers D, RET, RR, NFP, ADDR and the
temporaries. -/
def Scratch (F : ℕ) : Set ℤ := {cD, cRET, cRR, cNFP} ∪ Temps 0 F

/-- What the code of a statement that runs in the frame q may change: scratch cells, FP, the stack
cells from q on, and the memory cells within the limits. -/
def Writable {W : ℕ} (Z : Sizes W) (q : ℕ) : Set ℤ :=
  Scratch Z.F ∪ {cFP} ∪ Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}

/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/

theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ Temps k F ↔ a = cADDR ∨ cT (2 * F) ≤ a ∧ a ≤ cT k ∧ 4 ∣ cT 0 - a := by
  simp only [Temps, cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega

theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ Stack q Q ↔ cStack Q < a ∧ a ≤ cStack q ∧ 2 ∣ a := by
  simp only [Stack, cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega

theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ Pool N ↔ cPool N ≤ a ∧ a ≤ cPool 0 ∧ 4 ∣ cPool 0 - a := by
  simp only [Pool, cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega

/-- Proves that two cells of the compiled code are different, that a cell is or is not in one of the
sets above, or that one of these sets lies in another or in its complement.  A cell is given by its
name (cFP, cT j, cStack j, …) or is an integer that the context bounds.  The names and the sets are
replaced by their definitions; what remains are inequalities between integers, which follow from
those of the context, such as 1 ≤ q. -/
macro "cells" : tactic =>
  `(tactic| (simp only [Set.subset_def, Set.mem_compl_iff, Constants, Scratch, Writable, MainFrame,
               Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
               mem_temps_iff, mem_stack_iff, mem_pool_iff, cARG1, cARG2, cRESULT, cONE, cZERO, cNEG,
               cFP, cADDR, cRET, cRR, cNFP, cD, cT, cPool, cStack, mainFrame, ne_eq, true_or,
               or_true, false_or, or_false] <;>
             intros <;> omega))

/-- Reads a cell of a memory that is given by writes: it goes through the writes from the last to
the first, until it meets a write to the cell itself or no write is left. -/
macro "cell_read" : tactic =>
  `(tactic| repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by cells)]))

/-- Reads a cell of a memory that is given by writes to other cells of a memory in which, by h, the
cell holds the number in question. -/
macro "cell_read" " using " h:term : tactic => `(tactic| (cell_read; exact $h))

variable {W : ℕ} {Z : Sizes W} {F : ℕ}

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : Temps k F ⊆ Scratch F := by cells

/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : Scratch Z.F ⊆ Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

/-- A statement may change the stack from its frame on. -/
theorem stack_subset_writable {q : ℕ} : Stack q Z.Q ⊆ Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left

/-- A statement in a later frame may change less. -/
theorem writable_subset_writable {q q' : ℕ} (h : q ≤ q') : Writable Z q' ⊆ Writable Z q :=
  Set.union_subset_union_left _ (Set.union_subset_union_right _ (by cells))

/-- A statement may change the memory cells within the limits. -/
theorem mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q :=
  Set.mem_union_right _ h

/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by
  simp only [cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by
  simp only [cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := cStack_add q 1

/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]

/-- The number -1, on which every jump branches, fits in a word. -/
theorem Sizes.inRange_neg_one (Z : Sizes W) : InRange W (-1) := by
  have hN : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]

/-! ## The relation between a state of the light language and a memory of the machine -/

/-- The memory m of the machine represents the state σ of a procedure whose frame is at q. -/
structure Rel (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m cONE = wd W 1
  zero : m cZERO = wd W 0
  neg : m cNEG = wd W (-1)
  pool : ∀ n ≤ Z.disp, m (cPool n) = wd W n
  fp : m cFP = wd W (cStack q)
  loc : ∀ x < Z.F, m (cStack (q + x)) = wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = wd W (σ.mem a)

section Rel

variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m')
    (hs : s ⊆ (Constants Z.disp)ᶜ) (hfp : m' cFP = wd W (cStack q'))
    (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by cells)).trans R.one
    zero := (keep (by cells)).trans R.zero
    neg := (keep (by cells)).trans R.neg
    pool := fun n hn => (keep (by cells)).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : Rel Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- A memory that differs only in scratch cells and in the stack beyond the frame represents the
same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.) -/
theorem Rel.beyond (R : Rel Z σ q m) (hq : 1 ≤ q)
    (A : AgreeOutside (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- Writing a local variable. -/
private theorem Rel.setLoc (R : Rel Z σ q m) (hq : 1 ≤ q) (x : ℕ) (v : ℤ) :
    Rel Z { σ with loc := Function.update σ.loc x v } q
      (Function.update m (cStack (q + x)) (wd W v)) := by
  refine R.of_agreeOutside ((AgreeOutside.refl {cStack (q + x)} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun y hy => ?_) fun a ha => by cell_read using R.mem a ha
  obtain rfl | hxy := eq_or_ne y x
  · simp
  · rw [Function.update_of_ne (by cells)]
    exact (R.loc y hy).trans (by simp [hxy])

/-- Writing a memory cell. -/
theorem Rel.setMem (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  have hnonneg : 0 ≤ a := ha.1
  refine R.of_agreeOutside ((AgreeOutside.refl {a} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun x hx => by cell_read using R.loc x hx) fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · rw [Function.update_apply, if_pos (by omega)]
    simp
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])

/-- Reading a memory cell. -/
theorem Rel.read (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this

/-- The cell to which FP points is local variable 0. -/
theorem Rel.loc_zero (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) :=
  R.loc 0 hF

end Rel

/-- The memory m represents the state σ in the frame q, and the frame lies within the stack: after
stack cell 0 and before stack cell Q. -/
structure Framed (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q

/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩

/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using steps_bltz hcode hneg hr

/-- The two instructions that put the content v of the cell c into the local variable x. -/
theorem steps_setVar {x : ℕ} {c v : ℤ} (I : Framed Z σ q m) (hx : x < Z.F)
    (hcode : CodeAt code pos (.sub cADDR cFP (cPool (2 * x)) :: .store cADDR c :: rest))
    (hc : m c = wd W v) (hne : c ≠ cADDR) :
    ∃ m', Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      AgreeOutside (Writable Z q) m m' := by
  have hN := Z.offsets_le
  have hQ := I.high
  -- ADDR := FP - 2 x
  have run₁ := steps_sub (i := cADDR) hcode I.rel.fp (I.rel.pool (2 * x) (by omega))
  rw [cStack_sub] at run₁
  have A₁ := (AgreeOutside.refl (Scratch Z.F) m).update (a := cADDR) (by cells)
    (wd W (cStack (q + x)))
  -- the cell at ADDR := c
  have run₂ := run₁.trans (steps_store hcode.tail (Function.update_self _ _ _)
    (Z.inRange_stack (by omega)))
  rw [Function.update_of_ne hne, hc] at run₂
  exact ⟨_, run₂, (I.rel.same A₁).setLoc I.low x v,
    (A₁.mono scratch_subset_writable).update (by cells) _⟩

end code

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/Conditions.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/Conditions.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/Conditions.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Expressions
import TCSlib.Programs.Light.RunsStayInLimits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr)

variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

/-! ## Two expressions -/

/-- What follows the code of two expressions. -/
theorem codeAt_after_pair (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, length_compileExpr, length_compileExpr])

/-- The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
scratch cells only. -/
theorem steps_pair (I : Framed Z σ q m)
    (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧
      AgreeOutside (Scratch Z.F) m m' := by
  obtain ⟨va, Aa⟩ := effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have Aa' := Aa.mono temps_subset_scratch
  obtain ⟨vb, Ab⟩ := effects_compileExpr_of_width (I.same Aa') b 1 hwb hsb (by omega)
  have run := steps_straight _ pos m hcode.left
    (List.forall_mem_append.2 ⟨straight_compileExpr a 0, straight_compileExpr b 1⟩)
  rw [List.length_append, length_compileExpr, length_compileExpr, effects_append] at run
  exact ⟨_, run, Ab.read (by cells) va, vb, Aa'.trans (Ab.mono temps_subset_scratch)⟩

/-! ## Tests -/

/-- What the code of a test does, if it has size instructions, begins at pos, and tests p: in at
most size steps the machine reaches the position after the code if p holds, and the position l if
not.  Only scratch cells change. -/
def Decides (code : List Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
    (p → Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → Steps code n ⟨pos, m⟩ ⟨l, m'⟩)

/-- The test holds. -/
theorem Decides.of_holds {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- The test fails. -/
theorem Decides.of_fails {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : ¬ p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨l, m'⟩ :=
  let ⟨m', n, le, A, _, run⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- No overflow: the difference of two values fits in a word, and so does one less. -/
private theorem inRange_sub (Z : Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word)
    (hy : |y| ≤ Z.lim.word) : InRange W (x - y) ∧ InRange W (x - y - 1) := by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]

/-- The test a < b. -/
private theorem decides_lt (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.lt a b) l)) (hw : (Cond.lt a b).width ≤ Z.F)
    (hs : (Cond.lt a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.lt a b).size l m (a.val σ < b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := b - a
  have run₂ := run₁.trans (steps_sub restCode vb va)
  -- D := D - 1
  have run₃ := run₂.trans (steps_sub restCode.tail (Function.update_self _ _ _)
    (by cell_read using (I.rel.same A₁).one))
  -- leave if D < 0
  have run₄ := run₃.trans (steps_bltz restCode.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z (Expr.abs_val_le hσ b hsb) (Expr.abs_val_le hσ a hsa)).2)
  exact ⟨_, _, by rw [Cond.size], (A₁.update (by cells) _).update (by cells) _,
    run₄.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The test a = b. -/
private theorem decides_eq (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.eq a b) l)) (hw : (Cond.eq a b).width ≤ Z.F)
    (hs : (Cond.eq a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.eq a b).size l m (a.val σ = b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := Expr.abs_val_le hσ a hsa
  have hb := Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := a - b
  have run₂ := run₁.trans (steps_sub restCode va vb)
  have A₂ := A₁.update (a := cD) (by cells) (wd W (a.val σ - b.val σ))
  -- leave if D < 0
  have run₃ := run₂.trans (steps_bltz restCode.tail (Function.update_self _ _ _)
    (inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  -- D := 0 - D
  have run₄ := run₃.trans (steps_sub restCode.tail.tail
    (by cell_read using (I.rel.same A₁).zero)
    (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  -- leave if D < 0
  have run₅ := run₄.trans (steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z hb ha).1)
  exact ⟨_, _, by rw [Cond.size], A₂.update (by cells) _,
    run₅.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The code of a test decides the test. -/
theorem decides_compileCond (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact decides_lt I hσ hcode hw hs
  | eq a b => exact decides_eq I hσ hcode hw hs

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/Dispatcher.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/Dispatcher.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/Dispatcher.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Cells

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The dispatcher

The machine has no indirect jump.  A return loads the position r to return to into the register RR
and jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, ….  It
arrives at position r after 2 (r + 1) steps and changes no cell but RR (`steps_dispatcher`).

The proof runs one pair of instructions (`steps_dispatcher_pair`) and then counts down: from the
j-th pair on, with k in RR, the machine arrives at position j + k (`steps_dispatcher_from`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr)

variable {W : ℕ} {code : List Instr} {disp n : ℕ}

/-- The dispatcher for one more position. -/
private theorem dispatcher_succ (n : ℕ) :
    dispatcher (n + 1) = dispatcher n ++ [.sub cRR cRR cONE, .bltz cRR n] := by
  simp [dispatcher, List.range_succ, List.flatMap_append]

/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (dispatcher n).length = 2 * n := by
  simp [dispatcher, List.length_flatMap, Nat.mul_comm]

/-- A shorter dispatcher is the beginning of a longer one. -/
private theorem dispatcher_prefix {j n : ℕ} (h : j ≤ n) : dispatcher j <+: dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (dispatcher_succ n ▸ List.prefix_append _ _)

/-- The two instructions for the position j. -/
private theorem codeAt_dispatcher {j : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) :
    CodeAt code (disp + 2 * j) [.sub cRR cRR cONE, .bltz cRR j] := by
  have upToPairCode : CodeAt code disp (dispatcher j ++ [.sub cRR cRR cONE, .bltz cRR j]) :=
    dispatcher_succ j ▸ (dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [length_dispatcher])

/-- The two instructions for the position j, when RR holds v: RR goes down by one, and the machine
goes to j if that is negative and to the next pair if not. -/
private theorem steps_dispatcher_pair {j : ℕ} (hcode : CodeAt code disp (dispatcher n))
    (hj : j < n) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) {v : ℤ} (hv : InRange W (v - 1)) :
    Steps code 2 ⟨disp + 2 * j, Function.update m cRR (wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m cRR (wd W (v - 1))⟩ := by
  have pairCode := codeAt_dispatcher hcode hj
  -- RR := RR - 1
  have run₁ := steps_sub pairCode (Function.update_self cRR (wd W v) m)
    (by cell_read using hone)
  rw [Function.update_idem] at run₁
  -- if RR < 0 go to j
  exact run₁.trans (steps_bltz pairCode.tail (Function.update_self _ _ _) hv)

/-- The dispatcher from its j-th pair of instructions on, when RR holds k: it arrives at position
j + k.  The positions fit in a word (hn). -/
private theorem steps_dispatcher_from (hcode : CodeAt code disp (dispatcher n))
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (k j : ℕ)
    (hjk : j + k < n) :
    Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m cRR (wd W k)⟩
      ⟨j + k, Function.update m cRR (wd W (-1))⟩ := by
  induction k generalizing j with
  | zero =>
    simpa using steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0)
      (by constructor <;> omega)
  | succ k ih =>
    have run := steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1)
      (by constructor <;> omega)
    rw [if_neg (by omega), add_sub_cancel_right] at run
    rw [Nat.cast_succ]
    -- 2 + 2 (k + 1) steps lead to the position j + 1 + k
    exact ((run.trans (ih (j + 1) (by omega))).cast_count (by ring)).cast_pos (by ring)

/-- From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
word (hn). -/
theorem steps_dispatcher {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1)
    (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ := by
  have := steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.mul_zero, Nat.add_zero, Nat.zero_add, ← hRR, Function.update_eq_self] at this

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/Expressions.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/Expressions.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/Expressions.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Cells

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

variable {W : ℕ} {F : ℕ}

/-- Every expression uses at least one temporary. -/
private theorem _root_.Light.Expr.height_pos (e : Expr) : 0 < e.height := by
  induction e with
  | const n => simp [Expr.height]
  | var x => simp [Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
private theorem cT_mem_temps_of_height (e : Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    cT k ∈ Temps k F := by
  have := e.height_pos
  cells

/-! ## Constants -/

private theorem straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ digitsCode c L, Straight i
  | [] => by simp [digitsCode, Straight]
  | d :: L => by
    have := straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [digitsCode, hd, Straight, or_imp, forall_and] using this

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
private theorem effects_digitsCode {c : ℤ} (hc : cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) :
    effects (digitsCode c L) m c = wd W (Nat.ofDigits 2 L : ℕ) ∧
      AgreeOutside {c} m (effects (digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [digitsCode, effects_cons, effects_nil,
      effect_sub c (wd_toInt (m c)).symm (wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [digitsCode, effects_append, effects_append, effects_cons, effects_nil, effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, effects_cons, effects_nil, effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring

/-! ## Expressions -/

private theorem straight_instr (o : Op) (i j k : ℤ) : Straight (o.instr i j k) := by
  cases o <;> trivial

/-- The code of an expression only changes the memory. -/
theorem straight_compileExpr : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  | .const _, _ => straight_digitsCode _ _
  | .var _, _ => by simp [compileExpr, Straight]
  | .op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨straight_compileExpr a k, straight_compileExpr b (k + 1)⟩, by simp [straight_instr]⟩
  | .load a, k => List.forall_mem_append.2 ⟨straight_compileExpr a k, by simp [Straight]⟩

/-- The instruction of an operation, on cells that hold known numbers. -/
private theorem effect_instr (o : Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = wd W a)
    (hk : m k = wd W b) : effect (o.instr i j k) m = Function.update m i (wd W (o.eval a b)) := by
  cases o
  exacts [effect_add i hj hk, effect_sub i hj hk, effect_mul i hj hk]

variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
private theorem effects_compileExpr (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := effects_digitsCode (c := cT k) (by cells) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [compileExpr, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), cStack_sub,
      effect_load (cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((AgreeOutside.refl _ m).update (by cells) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by cells), I.rel.loc x hx, Expr.val]
  | op o a b iha ihb =>
    have hk := cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [compileExpr, effects_append, effects_append, effects_cons, effects_nil,
      effect_instr o (cT k) (Ab.read (by cells) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by cells))).update hk _⟩
  | load a ih =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have hnonneg : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [compileExpr, effects_append, effects_cons, effects_nil,
      effect_load (cT k) va (Z.inRange_addr haddr), Aa.cell (by cells), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩

/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  effects_compileExpr I e k (Expr.width_le_iff.1 hw).1 hs
    (by have := (Expr.width_le_iff.1 hw).2; omega)

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/ProgramCode.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/ProgramCode.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/ProgramCode.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Dispatcher

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr)

/-! ## The number read off the text -/

/-- The number of local variables of every frame: the width of the text, and at least 3 for the
outermost frame. -/
def frameSize (P : Program) : ℕ := max 3 (maxOf Stmt.width P)

/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : Program) : 3 ≤ frameSize P := le_max_left _ _

/-- Every body fits into a frame. -/
theorem width_le_frameSize {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P :=
  (maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)

/-! ## The parts of the code -/

/-- The outermost statement: procedure p0 is called on the local variables 1 and 2 of the outermost
frame, and its result goes to local variable 0. -/
def _root_.Light.mainStmt (p0 : ℕ) : Stmt := .call p0 [.var 1, .var 2] 0

/-- What follows the outermost statement, from position pos on: the result, which is local
variable 0 of the outermost frame, goes to the cell `cRESULT`; then the machine accepts, or, if dec
is set, it accepts if the result is positive and rejects if not. -/
def tailCode (dec : Bool) (pos : ℕ) : List Instr :=
  .add cRESULT (cStack mainFrame) cZERO ::
    (if dec then [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept]
      else [.accept])

/-- The position of the outermost statement: after the four instructions of `headCode`. -/
def mainPos : ℕ := 4

/-- The position of the code that follows the outermost statement. -/
def tailPos (F : ℕ) : ℕ := mainPos + (mainStmt 0).size F

/-- The position of the first body: after the outermost statement and what follows it. -/
def firstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length

/-- The positions of the bodies, the first of them at pos.  A body is followed by the return
sequence. -/
def entries (F : ℕ) : List Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + epilogueSize)

/-- The position after the bodies, the first of them at pos. -/
def endPos (F : ℕ) : List Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + epilogueSize)

/-- The position after the last body, which is the position of the dispatcher.  It is also the
largest number in the pool. -/
def dispPos (P : Program) (dec : Bool) : ℕ := endPos (frameSize P) P (firstBody (frameSize P) dec)

/-- What the code of the statements of P needs to know about the whole code. -/
def codeLayout (P : Program) (dec : Bool) : CodeLayout :=
  ⟨frameSize P, entries (frameSize P) P (firstBody (frameSize P) dec), dispPos P dec⟩

/-- The bodies with their return sequences, the first of them at pos. -/
def bodiesCode (G : CodeLayout) : List Stmt → ℕ → List Instr
  | [], _ => []
  | b :: bs, pos =>
    (compileStmt G b pos ++ epilogue G) ++ bodiesCode G bs (pos + b.size G.F + epilogueSize)

/-- The first three instructions: the numbers 1, 0, -1. -/
def headStraight : List Instr := [.one cONE, .sub cZERO cONE cONE, .sub cNEG cZERO cONE]

/-- The code that fills the pool with the numbers 0, …, N. -/
def poolCode (N : ℕ) : List Instr :=
  .sub (cPool 0) cONE cONE :: (List.range N).map fun n => .add (cPool (n + 1)) (cPool n) cONE

/-- The code that puts zeros into the local variables of the outermost frame. -/
def zeroCode (F : ℕ) : List Instr :=
  (List.range F).map fun x => .sub (cStack (mainFrame + x)) cONE cONE

/-- The code that sets up the outermost frame: FP, zeros in its local variables, and then the two
arguments in its local variables 1 and 2. -/
def frameCode (F : ℕ) : List Instr :=
  .sub cFP cZERO (cPool (2 * mainFrame)) ::
    (zeroCode F ++
      [.add (cStack (mainFrame + 1)) cARG1 cZERO, .add (cStack (mainFrame + 2)) cARG2 cZERO])

/-- The start-up code without its last jump. -/
def startStraight (F N : ℕ) : List Instr := poolCode N ++ frameCode F

/-- The first part: the numbers 1, 0, -1, and the jump to the start-up code. -/
def headCode (P : Program) (dec : Bool) : List Instr :=
  headStraight ++ [.bltz cNEG (3 * dispPos P dec)]

/-- The second part: the outermost statement and the verdict. -/
def mainCode (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  compileStmt (codeLayout P dec) (mainStmt p0) mainPos ++ tailCode dec (tailPos (frameSize P))

/-- The last part: the start-up code and the jump back to the outermost statement. -/
def startCode (P : Program) (dec : Bool) : List Instr :=
  startStraight (frameSize P) (dispPos P dec) ++ [.bltz cNEG mainPos]

/-- **The code of a program.**  With dec = false the machine accepts at the end of the run; with
dec = true it accepts if the result of procedure p0 is positive and rejects if not. -/
def _root_.Light.compileProgram (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  headCode P dec ++ mainCode P p0 dec ++ bodiesCode (codeLayout P dec) P
      (firstBody (frameSize P) dec) ++
    dispatcher (dispPos P dec) ++ startCode P dec

/-! ## Lengths and positions -/

private theorem le_endPos (F : ℕ) : ∀ (bs : List Stmt) (pos : ℕ), pos ≤ endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (le_endPos F bs (pos + b.size F + epilogueSize))

/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [mainStmt, Stmt.size, callSize, argsSize, Expr.size]

/-- The outermost statement uses the local variables 0, 1, 2. -/
theorem width_mainStmt (p0 : ℕ) : (mainStmt p0).width = 3 := rfl

private theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl

/-- The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
pointer, and it reaches further down than the 2 F + 1 temporaries. -/
theorem two_mul_frameSize_add_le_dispPos (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by
  have : firstBody (frameSize P) dec ≤ dispPos P dec := le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [firstBody, tailPos, mainPos, size_mainStmt, length_tailCode] at this
  omega

private theorem length_bodiesCode (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), pos + (bodiesCode G bs pos).length = endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := length_bodiesCode G bs (pos + b.size G.F + epilogueSize)
    simp only [bodiesCode, endPos, List.length_append, length_compileStmt, length_epilogue]
    omega

section parts

variable (P : Program) (p0 : ℕ) (dec : Bool)

private theorem length_through_mainCode :
    (headCode P dec ++ mainCode P p0 dec).length = firstBody (frameSize P) dec := by
  simp only [headCode, headStraight, mainCode, List.length_append, length_compileStmt,
    size_mainStmt, length_tailCode, firstBody, tailPos, mainPos, codeLayout, List.length_cons,
    List.length_nil]
  omega

private theorem length_through_bodiesCode :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)).length = dispPos P dec := by
  rw [List.length_append, length_through_mainCode]
  exact length_bodiesCode (codeLayout P dec) P _

private theorem length_through_dispatcher :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec) ++
      dispatcher (dispPos P dec)).length = 3 * dispPos P dec := by
  rw [List.length_append, length_through_bodiesCode, length_dispatcher]
  omega

/-- The first part is at position 0. -/
theorem codeAt_headCode : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) :=
  (codeAt_self _).left.left.left.left

private theorem codeAt_mainCode : CodeAt (compileProgram P p0 dec) mainPos (mainCode P p0 dec) :=
  (codeAt_self _).left.left.left.right

/-- The outermost statement is at `mainPos`. -/
theorem codeAt_mainStmt :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) :=
  (codeAt_mainCode P p0 dec).left

/-- The code for the verdict follows the outermost statement. -/
theorem codeAt_tailCode :
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) :=
  (codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [length_compileStmt, size_mainStmt, tailPos, codeLayout])

/-- The bodies begin at `firstBody`. -/
theorem codeAt_bodiesCode :
    CodeAt (compileProgram P p0 dec) (firstBody (frameSize P) dec)
      (bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)) :=
  (codeAt_self _).left.left.right.cast_pos (by rw [length_through_mainCode, Nat.zero_add])

/-- The dispatcher is at `dispPos`. -/
theorem codeAt_dispatcher_dispPos :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) :=
  (codeAt_self _).left.right.cast_pos (by rw [length_through_bodiesCode, Nat.zero_add])

/-- The start-up code follows the dispatcher. -/
theorem codeAt_startCode :
    CodeAt (compileProgram P p0 dec) (3 * dispPos P dec) (startCode P dec) :=
  (codeAt_self _).right.cast_pos (by rw [length_through_dispatcher, Nat.zero_add])

end parts

/-- Every body is at its entry, followed by the return sequence, and ends at or before the position
after the bodies. -/
theorem codeAt_bodies {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    codeAt_bodies G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, length_compileStmt, length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/Simulation.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/Simulation.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/Simulation.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.CallFrames
import TCSlib.Programs.Light.Compiler.Dispatcher

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr)

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}

/-- The code of e, and the two instructions that store T₀ in x. -/
private theorem codeAt_set (h : CodeAt code pos (compileStmt G (.set x e) pos)) :
    CodeAt code pos (compileExpr e 0) ∧
      CodeAt code (pos + e.size) [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileExpr])⟩

/-- The code of s, and the code of t. -/
private theorem codeAt_seq (h : CodeAt code pos (compileStmt G (.seq s t) pos)) :
    CodeAt code pos (compileStmt G s pos) ∧
      CodeAt code (pos + s.size G.F) (compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileStmt])⟩

/-- The test, the first branch, the jump over the second branch, the second branch. -/
private theorem codeAt_ite (h : CodeAt code pos (compileStmt G (.ite c s t) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F)
        [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
      CodeAt code (pos + c.size + s.size G.F + 1)
        (compileStmt G t (pos + c.size + s.size G.F + 1)) := by
  rw [compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_,
    h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]

/-- The test, the body, the jump back. -/
private theorem codeAt_while (h : CodeAt code pos (compileStmt G (.while c s) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG pos] := by
  rw [compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_compileCond, length_compileStmt]

/-- The arguments and the new frame, the jump to the procedure, and the two instructions that store
the result. -/
private theorem codeAt_call (h : CodeAt code pos (compileStmt G (.call p args x) pos)) :
    CodeAt code pos (argsCode args 0 ++ newFrame G.F args.length (pos + callSize G.F args)) ∧
      CodeAt code (pos + (argsSize args + (2 * G.F + 4))) [.bltz cNEG (G.entry.getD p 0)] ∧
      CodeAt code (pos + callSize G.F args)
        [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET] := by
  rw [compileStmt, callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_argsCode, length_newFrame, callSize]

end layout

/-! ## The setting -/

/-- What the simulation assumes once and for all: the numbers are large enough (`Sizes`), and the
program and its code fit them. -/
structure Setting (W : ℕ) extends Sizes W where
  /-- The light program. -/
  P : Program
  /-- The code of the whole program. -/
  code : List Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    CodeAt code e (compileStmt toCodeLayout b e ++ epilogue toCodeLayout) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : CodeAt code disp (dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F

/-- An upper bound for the number of machine steps that match one step of the light language, if the
code before the dispatcher has n instructions.  Each rule of the semantics counts at least one step
and, calls apart, runs a piece of code once, which takes at most n machine steps.  A call counts two
steps, so it has 2 stepsPerStep = 4 n: at most n for its own code, n for the return sequence, 2 n
for the dispatcher. -/
def stepsPerStep (n : ℕ) : ℕ := 2 * n

/-- At most n machine steps are within the bound for c ≥ 1 steps of the language. -/
private theorem le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) :
    a ≤ stepsPerStep n * c :=
  calc a ≤ stepsPerStep n * 1 := by rw [stepsPerStep]; omega
    _ ≤ stepsPerStep n * c := Nat.mul_le_mul_left _ hc

/-- At most n machine steps, followed by b machine steps that are within the bound for k steps, are
within the bound for c + k steps if c ≥ 1. -/
private theorem add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c)
    (hb : b ≤ stepsPerStep n * k) : a + b ≤ stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (le_stepsPerStep_mul h hc) hb

/-- The count for a call whose code is at pos and has size + 2 instructions: size steps to enter, b
for the body, r + 2 (pos + size + 1) to leave, where r is the length of the return sequence, and 2
to store the result.  The cost a of the arguments is not needed. -/
private theorem call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n)
    (hr : r ≤ n) (hb : b ≤ stepsPerStep n * k) :
    size + b + (r + 2 * (pos + size + 1)) + 2 ≤ stepsPerStep n * (a + 2 + k) := by
  rw [Nat.mul_add (stepsPerStep n), Nat.mul_add (stepsPerStep n)]
  have hK : stepsPerStep n * 2 = 4 * n := by rw [stepsPerStep]; omega
  omega

variable {W : ℕ} (S : Setting W)

/-- The situation before the code of the statement s runs, at nesting depth d of calls: the memory m
represents the state σ in the frame q, and the following holds. -/
structure Start (d : ℕ) (s : Stmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : CodeAt S.code pos (compileStmt S.toCodeLayout s pos)
  /-- It ends at or before the dispatcher. -/
  below : pos + s.size S.F ≤ S.disp
  /-- F local variables and 2 F + 1 temporaries are enough for s. -/
  width : s.width ≤ S.F
  /-- The state holds words. -/
  bounded : σ.Bounded S.lim
  /-- The stack has room for this frame and for F + 1 cells for each further level of calls. -/
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q

/-- The code of s, started as in `Start`, has matched a run of c steps that ends in σ': it has
taken n machine steps and left the memory m'. -/
structure Finished (s : Stmt) (σ' : State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : AgreeOutside (Writable S.toSizes q) m m'

/-- The code of s matches the run of s from σ to σ' in c steps. -/
def Simulates (d : ℕ) (s : Stmt) (σ σ' : State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), Finished S s σ' c pos q m m' n

variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}

/-- The situation before a part t of the statement runs, in the same frame. -/
private theorem Start.sub (B : Start S d s σ pos q m) {t : Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : CodeAt S.code pos' (compileStmt S.toCodeLayout t pos'))
    (hpos : pos' + t.size S.F ≤ S.disp) (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim)
    (R : Rel S.toSizes σ' q m') : Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw,
    bounded := hσ, room := B.room }

/-- The room on the stack, seen from the frame of a procedure that is called. -/
private theorem Start.room_succ (B : Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q := by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega

/-- The test of an if or a while that is at pos. -/
private theorem Start.test (B : Start S d s σ pos q m) {c : Cond} {l : ℕ}
    (hcode : CodeAt S.code pos (compileCond c l)) (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) :
    Decides S.code S.F pos c.size l m (c.Holds σ) :=
  decides_compileCond B.toFramed B.bounded c hcode hw hs

/-! ## Statements without calls -/

/-- skip: no code, no step. -/
private theorem sim_skip : Simulates S d .skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := AgreeOutside.refl _ m }⟩

/-- x := e: the code of e leaves the value in T₀, and two instructions store it in x. -/
private theorem sim_set {x : ℕ} {e : Expr} (hs : e.Safe S.lim σ) :
    Simulates S d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) }
      (e.cost + 1) := by
  intro pos q m B
  obtain ⟨hx, he⟩ := Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := codeAt_set B.codeAt
  have hpos : pos + (e.size + 2) ≤ S.disp := B.below
  -- T₀ := e
  obtain ⟨val, A⟩ := effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono temps_subset_scratch
  have run₁ := steps_straight _ pos m exprCode (straight_compileExpr e 0)
  rw [length_compileExpr] at run₁
  -- x := T₀
  obtain ⟨m₂, run₂, R₂, A₂⟩ := steps_setVar (B.toFramed.same A₁) hx setCode val (by cells)
  exact ⟨m₂, _, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := R₂
    agree := (A₁.mono scratch_subset_writable).trans A₂ }⟩

/-- The cell at a := e: the code of a and e leaves the values in T₀ and T₁, and one instruction
stores. -/
private theorem sim_store {a e : Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ)
    (haddr : S.lim.Addr (a.val σ)) :
    Simulates S d (.store a e) σ
      { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } (a.cost + e.cost + 1) := by
  intro pos q m B
  obtain ⟨ha, he⟩ := Stmt.width_store_le_iff.1 B.width
  have hpos : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  -- T₀ := a; T₁ := e
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := steps_pair B.toFramed B.codeAt ha he hsa hse
  -- the cell at T₀ := T₁
  have run₂ := run₁.trans (steps_store (codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact ⟨_, _, {
    run := run₂.cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := (B.rel.same A₁).setMem B.low haddr _
    agree := (A₁.mono scratch_subset_writable).update (mem_writable_of_addr haddr) _ }⟩

/-- s₁; s₂: the code of s₁, then the code of s₂. -/
private theorem sim_seq {c₁ c₂ : ℕ} (h₁ : Exec S.lim S.P d s₁ σ σ₁ c₁)
    (ih₁ : Simulates S d s₁ σ σ₁ c₁) (ih₂ : Simulates S d s₂ σ₁ σ₂ c₂) :
    Simulates S d (.seq s₁ s₂) σ σ₂ (c₁ + c₂) := by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := codeAt_seq B.codeAt
  have hpos : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _
    (B.sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact ⟨m₂, n₁ + n₂, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
    rel := R₂
    agree := A₁.trans A₂ }⟩

/-- if c then s₁ else s₂, when c holds: the test goes on to the code of s₁, and a jump leads over
the code of s₂. -/
private theorem sim_iteTrue {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : Simulates S d s₁ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the first branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
  -- the jump over the second branch
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact ⟨m₁, n₀ + 1 + n₁, {
    run := (run₂.cast_count (by omega)).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- if c then s₁ else s₂, when c fails: the test jumps to the code of s₂. -/
private theorem sim_iteFalse {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ)
    (ih : Simulates S d s₂ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  -- the second branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact ⟨m₁, n₀ + n₁, {
    run := (run₀.trans run₁).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- while c do s, when c fails: the test jumps to the position after the loop. -/
private theorem sim_whileFalse {c : Cond} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ) :
    Simulates S d (.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  exact ⟨m₀, n₀, {
    run := run₀.cast_pos (by rw [Stmt.size]; omega)
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := B.rel.same A₀
    agree := A₀.mono scratch_subset_writable }⟩

/-- while c do s, when c holds: the test goes on to the code of s, a jump leads back to the test,
and the loop runs again. -/
private theorem sim_whileTrue {c : Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : Simulates S d s σ σ₁ k₁)
    (ih₂ : Simulates S d (.while c s) σ₁ σ₂ k₂) :
    Simulates S d (.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) := by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the body
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _
    (B.sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
  -- the jump back
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  -- the loop again
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _
    (B.sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact ⟨m₃, n₀ + 1 + n₁ + n₃, {
    run := (run₂.trans run₃).cast_count (by omega)
    le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (add_le_stepsPerStep_mul (by omega) (by omega) le₁)
        le₃
    rel := R₃
    agree := ((A₀.mono scratch_subset_writable).trans A₁).trans A₃ }⟩

/-! ## Calls -/

section call

variable {p x : ℕ} {args : List Expr}

/-- Entering a procedure: the arguments, the new frame with the position to return to, and the jump
to the entry e.  Afterwards the memory represents the state in which the procedure starts, in the
frame q + F + 1, and the stack cell before that frame holds the position after the jump.  Of the
stack, only cells from q + F on have changed. -/
private theorem steps_callEnter (B : Start S d (.call p args x) σ pos q m)
    (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hd : d < S.lim.depth) {e : ℕ}
    (he : S.entry[p]? = some e) :
    ∃ m₂, Steps S.code (callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
      Rel S.toSizes ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
      m₂ (cStack (q + S.F)) = wd W ((pos + callSize S.F args : ℕ) : ℤ) ∧
      AgreeOutside (Writable S.toSizes (q + S.F)) m m₂ := by
  obtain ⟨-, hlen, hwa⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  -- the arguments: there are at most F of them, each of width at most F
  obtain ⟨vals, A⟩ := effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono temps_subset_scratch
  -- the new frame
  obtain ⟨R₂, hret, A₂⟩ := effects_newFrame (B.toFramed.same A₁)
    ((Nat.le_add_right _ _).trans (B.room_succ hd)) args (by simpa using vals)
    (ret := pos + callSize S.F args) (by omega)
  have run₂ := steps_straight _ pos m frameCode
    (List.forall_mem_append.2 ⟨straight_argsCode _ _, straight_newFrame _ _ _⟩)
  rw [effects_append, List.length_append, length_argsCode, length_newFrame] at run₂
  -- the jump
  exact ⟨_, (run₂.trans (steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count
    (by rw [callSize]; omega), R₂, hret, (A₁.mono scratch_subset_writable).trans A₂⟩

/-- Leaving a procedure whose frame is q + F + 1, when the stack cell before that frame holds the
position ret: the return sequence and the dispatcher.  The machine arrives at ret; RET holds the
result (local variable 0), FP points to the frame q, and otherwise only scratch cells have
changed. -/
private theorem steps_callLeave (S : Setting W) {ret : ℕ} (R : Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : CodeAt S.code pos (epilogue S.toCodeLayout))
    (hret : m (cStack (q + S.F)) = wd W ret) (hlt : ret < S.disp) (hQ : q + S.F + 1 ≤ S.Q)
    (hF : 0 < S.F) :
    ∃ m', Steps S.code (epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
      m' cFP = wd W (cStack q) ∧ m' cRET = wd W (σ.loc 0) ∧
      AgreeOutside (insert cFP (Scratch S.F)) m m' := by
  have hN := S.offsets_le
  -- RET := the cell at FP, which is local variable 0
  have run₁ := steps_load (i := cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ := (AgreeOutside.refl (Scratch S.F) m).update (a := cRET) (by cells) (wd W (σ.loc 0))
  -- ADDR := FP + 2, the address of the stack cell before the frame
  have run₂ := run₁.trans (steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [cStack_succ_add] at run₂
  have A₂ := A₁.update (a := cADDR) (by cells) (wd W (cStack (q + S.F)))
  -- RR := the cell at ADDR, which holds ret
  have run₃ := run₂.trans (steps_load hcode.tail.tail (Function.update_self _ _ _)
    (S.inRange_stack (by omega)))
  rw [A₂.read (by cells) hret] at run₃
  have A₃ := A₂.update (a := cRR) (by cells) (wd W ret)
  -- FP := FP + 2 (F + 1), the frame of the caller
  have run₄ := run₃.trans (steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, cStack_add] at run₄
  -- the jump to the dispatcher
  have run₅ := run₄.trans (steps_jump hcode.tail.tail.tail.tail
    (by cell_read using (R.same A₃).neg) S.inRange_neg_one)
  -- the dispatcher, which leaves -1 in RR
  have run₆ := run₅.trans (steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
    (by cell_read using (R.same A₃).one) (by cell_read))
  exact ⟨_, run₆, by cell_read, by cell_read,
    ((A₃.mono (by cells)).update (by cells) _).update (by cells) _⟩

/-- x := p(args): enter, the body, leave, store the result. -/
private theorem sim_call {body : Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hp : S.P[p]? = some body) (hd : d < S.lim.depth)
    (ih : Simulates S (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    Simulates S d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
      ((args.map Expr.cost).sum + 2 + k) := by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.room_succ hd
  -- enter
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := steps_callEnter B hsa hd he
  -- the body, in the frame q + F + 1
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih e (q + S.F + 1) m₁
    { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
      width := S.width body (List.mem_of_getElem? hp),
      bounded := bounded_callFrame B.bounded args hsa, room := hroom }
  -- the body writes the stack only from its frame on, so the position to return to is still there
  have hret₂ := A₂.read (a := cStack (q + S.F)) (by cells) hret
  -- leave
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ := steps_callLeave S R₂
    (procCode.right.cast_pos (by rw [length_compileStmt])) hret₂ (by omega) (by omega)
    (Nat.zero_lt_of_lt hx)
  -- since the call began, the stack has changed only from cell q + F on: the local variables of the
  -- caller are as before, and the memory is as the procedure left it
  have A : AgreeOutside (Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (writable_subset_writable (by omega)))).trans
      (A₃.mono (Set.insert_subset (by cells) scratch_subset_writable))
  have I₃ : Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ := ⟨R₂.of_agreeOutside A₃ (by cells) hfp
    (fun y hy => A.read (by cells) (B.rel.loc y hy))
    fun a ha => A₃.read (by cells) (R₂.mem a ha), hq, B.high⟩
  -- store the result
  obtain ⟨m₄, run₄, R₄, A₄⟩ := steps_setVar I₃ hx resultCode hres (by cells)
  exact ⟨m₄, _, {
    run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := call_le_stepsPerStep_mul hpos (by omega) le₂
    rel := R₄
    agree := (A.mono (writable_subset_writable (by omega))).trans A₄ }⟩

end call

/-! ## The theorem -/

/-- **The simulation theorem.**  The code of a statement matches every run of the statement. -/
theorem sim (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) :
    Simulates S d s σ σ' c := by
  induction h with
  | skip => exact sim_skip
  | set hs => exact sim_set hs
  | store hsa hse haddr => exact sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact sim_iteFalse hs fails ih
  | whileFalse hs fails => exact sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact sim_call hsa hp hd ih

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/StartUp.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/StartUp.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/StartUp.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.ProgramCode

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

private theorem effects_headStraight (m : ℤ → BitVec W) :
    effects headStraight m =
      Function.update (Function.update (Function.update m cONE (wd W 1)) cZERO (wd W 0)) cNEG
        (wd W (-1)) := by
  simp only [headStraight, effects_cons, effects_nil]
  rw [effect_one, effect_sub cZERO (by cell_read) (by cell_read),
    effect_sub cNEG (by cell_read) (by cell_read)]
  rfl

/-- The three registers after the first three instructions. -/
private theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧ effects headStraight m cZERO = wd W 0 ∧
      effects headStraight m cNEG = wd W (-1) := by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> cell_read

/-! ## The pool -/

private theorem poolCode_succ (N : ℕ) :
    poolCode (N + 1) = poolCode N ++ [.add (cPool (N + 1)) (cPool N) cONE] := by
  simp [poolCode, List.range_succ]

private theorem agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Pool N) m (effects (poolCode N) m) := by
  refine agreeOutside_effects (l := poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show cPool 0 ∈ Pool N
    cells
  · have := List.mem_range.1 hn
    show cPool (n + 1) ∈ Pool N
    cells

/-- After `poolCode N` the pool holds the numbers 0, …, N. -/
private theorem effects_poolCode (hone : m cONE = wd W 1) (N : ℕ) :
    ∀ n ≤ N, effects (poolCode N) m (cPool n) = wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [poolCode, List.range_zero, List.map_nil, effects_cons, effects_nil]
    rw [effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [poolCode_succ, effects_append, effects_cons, effects_nil,
      effect_add _ (ih N le_rfl) ((agreeOutside_poolCode N m).read (by cells) hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne (by cells), ih n (by omega)]

/-- The memory after the first three instructions and the code for the pool. -/
private def poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (poolCode N) (effects headStraight m)

private theorem agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N) m (poolMem N m) := by
  refine AgreeOutside.trans_union ?_ (agreeOutside_poolCode N _)
  rw [effects_headStraight]
  exact (((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
private theorem poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    poolMem N m cONE = wd W 1 ∧ poolMem N m cZERO = wd W 0 ∧ poolMem N m cNEG = wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := effects_headStraight_consts m
  have keep := agreeOutside_poolCode N (effects headStraight m)
  exact ⟨keep.read (by cells) one, keep.read (by cells) zero, keep.read (by cells) neg⟩

private theorem poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) :
    poolMem N m (cPool n) = wd W n :=
  effects_poolCode (effects_headStraight_consts m).1 N n hn

/-! ## The outermost frame -/

private theorem zeroCode_succ (F : ℕ) :
    zeroCode (F + 1) = zeroCode F ++ [.sub (cStack (mainFrame + F)) cONE cONE] := by
  simp [zeroCode, List.range_succ]

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem writesIn_zeroCode (F : ℕ) : ∀ i ∈ zeroCode F, WritesIn (MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show cStack (mainFrame + x) ∈ MainFrame F
    cells

/-- The local variables of the outermost frame hold zeros. -/
private theorem effects_zeroCode (hone : m cONE = wd W 1) (F : ℕ) :
    ∀ x < F, effects (zeroCode F) m (cStack (mainFrame + x)) = wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' := (agreeOutside_effects (writesIn_zeroCode F) m).read (by cells) hone
    rw [zeroCode_succ, effects_append, effects_cons, effects_nil, effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by cells), ih x hlt]

private theorem agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    AgreeOutside ({cFP} ∪ MainFrame F) m (effects (frameCode F) m) := by
  refine agreeOutside_effects (l := frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show cStack (mainFrame + 1) ∈ _
    cells
  · -- local variable 2 := the second argument
    show cStack (mainFrame + 2) ∈ _
    cells

/-- The code for the outermost frame: FP, then zeros, then the two arguments. -/
private theorem effects_frameCode {i j : ℤ} (hzero : m cZERO = wd W 0)
    (hpool : m (cPool (2 * mainFrame)) = wd W (2 * mainFrame : ℕ)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) (F : ℕ) :
    effects (frameCode F) m =
      Function.update (Function.update
        (effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))))
        (cStack (mainFrame + 1)) (wd W i)) (cStack (mainFrame + 2)) (wd W j) := by
  -- what the last two instructions read has not been written since the beginning
  have read (a : ℤ) (ha : a ∉ MainFrame F) (hfp : a ≠ cFP) :
      effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))) a = m a :=
    ((agreeOutside_effects (writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero := (read cZERO (by cells) (by cells)).trans hzero
  have arg1 := (read cARG1 (by cells) (by cells)).trans hi
  have arg2 := (read cARG2 (by cells) (by cells)).trans hj
  simp only [frameCode, effects_cons, effects_append, effects_nil]
  -- FP := 0 - 2 mainFrame
  rw [effect_sub cFP hzero hpool, show (0 : ℤ) - (2 * mainFrame : ℕ) = cStack mainFrame from rfl]
  -- after the zeros: local variable 1 := the first argument + 0
  rw [effect_add _ arg1 zero, add_zero]
  -- local variable 2 := the second argument + 0
  rw [effect_add _ (by cell_read using arg2) (by cell_read using zero), add_zero]

/-! ## The memory in which the outermost statement starts -/

/-- The memory after the first three instructions and the start-up code. -/
def startMem (F N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (startStraight F N) (effects headStraight m)

private theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    startMem F N m = effects (frameCode F) (poolMem N m) := effects_append _ _ _

/-- The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
frame. -/
theorem agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N ∪ ({cFP} ∪ MainFrame F)) m (startMem F N m) :=
  startMem_eq F N m ▸ (agreeOutside_poolMem N m).trans_union (agreeOutside_frameCode h3 _)

/-- After the start-up code the memory represents the state in which the outermost statement
starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
the cells below -2 of the initial memory. -/
theorem rel_startMem (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) := by
  obtain ⟨one, zero, neg⟩ := poolMem_consts Z.disp m
  have keep₁ := agreeOutside_poolMem Z.disp m
  have keep₂ := agreeOutside_frameCode h3 (poolMem Z.disp m)
  have written := effects_frameCode zero (poolMem_pool m hpool) (keep₁.read (by cells) hi)
    (keep₁.read (by cells) hj) Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
      effects (frameCode Z.F) (poolMem Z.disp m) (cStack (mainFrame + x)) = wd W 0 := by
    rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells)]
    exact effects_zeroCode (by cell_read using one) Z.F x hx
  rw [startMem_eq]
  exact {
    one := keep₂.read (by cells) one
    zero := keep₂.read (by cells) zero
    neg := keep₂.read (by cells) neg
    pool := fun n hn => keep₂.read (by cells) (poolMem_pool m hn)
    fp := by
      rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells),
        (agreeOutside_effects (writesIn_zeroCode Z.F) _).cell (by cells), Function.update_self]
    loc := fun x hx => match x with
      | 0 => zeros 0 hx (by omega) (by omega)
      | 1 => by rw [written, Function.update_of_ne (by cells)]; exact Function.update_self ..
      | 2 => by rw [written]; exact Function.update_self ..
      | x + 3 => zeros (x + 3) hx (by omega) (by omega)
    mem := fun a ha => keep₂.read (by cells) (keep₁.read (by cells) (hm a ha)) }

/-! ## The run from the first instruction to the outermost statement -/

private theorem straight_headStraight : ∀ i ∈ headStraight, Straight i := by
  simp [headStraight, Straight]

private theorem straight_startStraight (F N : ℕ) : ∀ i ∈ startStraight F N, Straight i := by
  simp [startStraight, poolCode, frameCode, zeroCode, Straight, or_imp, forall_and]

private theorem length_startStraight (F N : ℕ) : (startStraight F N).length = N + F + 4 := by
  simp +arith [startStraight, poolCode, frameCode, zeroCode]

/-- From the first instruction to the outermost statement. -/
theorem steps_start (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1))
    (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ := by
  have head := codeAt_headCode P p0 dec
  have start := codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := poolMem_consts (dispPos P dec) m
  have neg₁ : startMem (frameSize P) (dispPos P dec) m cNEG = wd W (-1) := by
    rw [startMem_eq, (agreeOutside_frameCode (three_le_frameSize P) _).cell (by cells), neg]
  -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
  refine ((((steps_straight _ 0 m head.left straight_headStraight).trans
    (steps_jump head.right neg₀ hneg)).trans
    (steps_straight _ _ _ start.left (straight_startStraight _ _))).trans
    (steps_jump start.right neg₁ hneg)).cast_count ?_
  rw [length_startStraight, show headStraight.length = 3 from rfl]
  omega

end Light.Compiler
end
```

## ===== TCSlib/Programs/Light/Compiler/StatementCode.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/StatementCode.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/StatementCode.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Syntax
import TCSlib.Programs.WordRAM.Steps
import Mathlib.Data.Nat.Digits.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light.Compiler

open WordRAM (Instr)

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/

/-- The cell from which a whole program takes its first argument. -/
def cARG1 : ℤ := -1
/-- The cell from which a whole program takes its second argument. -/
def cARG2 : ℤ := -2
/-- The cell into which a whole program puts its result. -/
def cRESULT : ℤ := -3
/-- The register that holds 1. -/
def cONE : ℤ := -5
/-- The register that holds 0. -/
def cZERO : ℤ := -7
/-- The register that holds -1; an unconditional jump branches on it. -/
def cNEG : ℤ := -9
/-- The frame pointer FP: the address of local variable 0 of the running procedure. -/
def cFP : ℤ := -11
/-- The register ADDR: the address for the next load or store of a local variable. -/
def cADDR : ℤ := -13
/-- The register RET: the result of the procedure that has just returned. -/
def cRET : ℤ := -15
/-- The register RR: the position to return to, counted down by the dispatcher. -/
def cRR : ℤ := -17
/-- The register NFP: the frame pointer of the procedure that is about to be called. -/
def cNFP : ℤ := -19
/-- The register D: the difference that a test branches on. -/
def cD : ℤ := -21
/-- The temporaries. -/
def cT (k : ℕ) : ℤ := -(23 + 4 * (k : ℤ))
/-- The pool of numbers. -/
def cPool (n : ℕ) : ℤ := -(25 + 4 * (n : ℤ))
/-- The cell number j of the stack. -/
def cStack (j : ℕ) : ℤ := -(2 * (j : ℤ))
/-- The frame of the outermost statement of a whole program: the first whose cells lie beyond the
cells of the arguments and the result. -/
def mainFrame : ℕ := 4

/-! ## Expressions and tests -/

/-- The instruction of the machine for an operation. -/
def _root_.Light.Op.instr : Op → ℤ → ℤ → ℤ → Instr
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- Code that builds in the cell c the number with the given binary digits, least significant digit
first: the number of the higher digits, doubled, plus the lowest digit. -/
def digitsCode (c : ℤ) : List ℕ → List Instr
  | [] => [.sub c c c]
  | d :: L => digitsCode c L ++ [.add c c c] ++ (if d = 0 then [] else [.add c c cONE])

/-- The length of `digitsCode c L`. -/
def digitsLen : List ℕ → ℕ
  | [] => 1
  | d :: L => digitsLen L + 1 + (if d = 0 then 0 else 1)

/-- Code that leaves the value of the expression in the temporary T_k, using only T_k, T_{k+1}, …
and ADDR.  A constant is built from its binary digits, in at most 2 log₂ n + 3 instructions. -/
def compileExpr : Expr → ℕ → List Instr
  | .const n, k => digitsCode (cT k) (Nat.digits 2 n)
  | .var x, k => [.sub cADDR cFP (cPool (2 * x)), .load (cT k) cADDR]
  | .op o a b, k => compileExpr a k ++ compileExpr b (k + 1) ++ [o.instr (cT k) (cT k) (cT (k + 1))]
  | .load a, k => compileExpr a k ++ [.load (cT k) (cT k)]

/-- The length of the code of an expression. -/
def _root_.Light.Expr.size : Expr → ℕ
  | .const n => digitsLen (Nat.digits 2 n)
  | .var _ => 2
  | .op _ a b => a.size + b.size + 1
  | .load a => a.size + 1

/-- Code that goes on to the next position if the test holds and jumps to the position l if it does
not.  Both tests evaluate a into T₀ and b into T₁.  For a < b the code forms D = b - a - 1 and
leaves if D < 0.  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative. -/
def compileCond : Cond → ℕ → List Instr
  | .lt a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++ [.sub cD (cT 1) (cT 0), .sub cD cD cONE, .bltz cD l]
  | .eq a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++
      [.sub cD (cT 0) (cT 1), .bltz cD l, .sub cD cZERO cD, .bltz cD l]

/-- The length of the code of a test. -/
def _root_.Light.Cond.size : Cond → ℕ
  | .lt a b => a.size + b.size + 3
  | .eq a b => a.size + b.size + 4

/-! ## Statements -/

/-- What the code of a statement needs to know about the whole program. -/
structure CodeLayout : Type where
  /-- The number of local variables of every frame. -/
  F : ℕ
  /-- The positions of the procedures. -/
  entry : List ℕ
  /-- The position of the dispatcher. -/
  disp : ℕ

/-- The arguments of a call, evaluated into T_k, T_{k+1}, …. -/
def argsCode : List Expr → ℕ → List Instr
  | [], _ => []
  | e :: es, k => compileExpr e k ++ argsCode es (k + 1)

/-- The length of the code for the arguments of a call. -/
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es

/-- The local variables of the new frame: the first n from the temporaries, the others 0. -/
def frameInit (F n : ℕ) : List Instr :=
  (List.range F).flatMap fun i =>
    [.sub cADDR cNFP (cPool (2 * i)), .store cADDR (if i < n then cT i else cZERO)]

/-- The code of a call between the arguments and the jump to the procedure: the address of the new
frame into NFP, its local variables, the position ret to return to, and FP := NFP. -/
def newFrame (F n ret : ℕ) : List Instr :=
  [.sub cNFP cFP (cPool (2 * (F + 1)))] ++ frameInit F n ++
    [.add cADDR cNFP (cPool 2), .store cADDR (cPool ret), .add cFP cNFP cZERO]

/-- A call up to and including the jump to the procedure; ret is the position after the jump. -/
def callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) : List Instr :=
  argsCode args 0 ++ newFrame G.F args.length ret ++ [.bltz cNEG (G.entry.getD p 0)]

/-- The length of a call up to and including the jump. -/
def callSize (F : ℕ) (args : List Expr) : ℕ := argsSize args + 1 + 2 * F + 4

/-- The length of the code of a statement. -/
def _root_.Light.Stmt.size (F : ℕ) : Stmt → ℕ
  | .skip => 0
  | .set _ e => e.size + 2
  | .store a e => a.size + e.size + 1
  | .seq s t => s.size F + t.size F
  | .ite c s t => c.size + s.size F + 1 + t.size F
  | .while c s => c.size + s.size F + 1
  | .call _ args _ => callSize F args + 2

/-- The code of a statement, for the position pos. -/
def compileStmt (G : CodeLayout) : Stmt → ℕ → List Instr
  | .skip, _ => []
  | .set x e, _ => compileExpr e 0 ++ [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)]
  | .store a e, _ => compileExpr a 0 ++ compileExpr e 1 ++ [.store (cT 0) (cT 1)]
  | .seq s t, pos => compileStmt G s pos ++ compileStmt G t (pos + s.size G.F)
  | .ite c s t, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ++
      compileStmt G t (pos + c.size + s.size G.F + 1)
  | .while c s, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG pos]
  | .call p args x, pos =>
    callCode G p args (pos + callSize G.F args) ++
      [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET]

/-- The return sequence of a procedure: the result (local variable 0) into RET, the position to
return to into RR, the frame of the caller, and the jump to the dispatcher. -/
def epilogue (G : CodeLayout) : List Instr :=
  [.load cRET cFP, .add cADDR cFP (cPool 2), .load cRR cADDR,
    .add cFP cFP (cPool (2 * (G.F + 1))), .bltz cNEG G.disp]

/-- The length of the return sequence. -/
def epilogueSize : ℕ := 5

/-- The dispatcher for the positions below n. -/
def dispatcher (n : ℕ) : List Instr :=
  (List.range n).flatMap fun j => [.sub cRR cRR cONE, .bltz cRR j]

/-! ## Lengths -/

private theorem length_digitsCode (c : ℤ) (L : List ℕ) : (digitsCode c L).length = digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [digitsCode, digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl

/-- The code of an expression has the length defined on the text. -/
theorem length_compileExpr (e : Expr) (k : ℕ) : (compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [compileExpr, Expr.size, iha, ihb]
  | load a ih => simp [compileExpr, Expr.size, ih]

/-- The code of a test has the length defined on the text. -/
theorem length_compileCond (c : Cond) (l : ℕ) : (compileCond c l).length = c.size := by
  cases c <;> simp +arith [compileCond, Cond.size, length_compileExpr]

/-- The code for the arguments of a call has the length defined on the text. -/
theorem length_argsCode (es : List Expr) (k : ℕ) : (argsCode es k).length = argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [argsCode, argsSize, length_compileExpr, ih]

/-- Two instructions for each local variable of the new frame. -/
private theorem length_frameInit (F n : ℕ) : (frameInit F n).length = 2 * F := by
  simp [frameInit, List.length_flatMap, Nat.mul_comm]

/-- The code between the arguments and the jump has 2 F + 4 instructions. -/
theorem length_newFrame (F n ret : ℕ) : (newFrame F n ret).length = 2 * F + 4 := by
  simp +arith [newFrame, length_frameInit]

/-- A call up to its jump has the length defined on the text. -/
private theorem length_callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) :
    (callCode G p args ret).length = callSize G.F args := by
  simp +arith [callCode, callSize, length_argsCode, length_newFrame]

theorem length_epilogue (G : CodeLayout) : (epilogue G).length = epilogueSize := rfl

/-- The code of a statement has the length defined on the text. -/
theorem length_compileStmt (G : CodeLayout) (s : Stmt) (pos : ℕ) :
    (compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [compileStmt, Stmt.size, length_compileExpr]
  | store a e => simp +arith [compileStmt, Stmt.size, length_compileExpr]
  | seq s t ihs iht => simp [compileStmt, Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [compileStmt, Stmt.size, ihs, iht, length_compileCond]
  | «while» c s ih => simp +arith [compileStmt, Stmt.size, ih, length_compileCond]
  | call p args x => simp [compileStmt, Stmt.size, length_callCode]

end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/

/-- One more than the largest variable of an expression. -/
def Expr.vars : Expr → ℕ
  | .const _ => 0
  | .var x => x + 1
  | .op _ a b => max a.vars b.vars
  | .load a => a.vars

/-- The number of temporaries that the code of an expression uses. -/
def Expr.height : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => max a.height (b.height + 1)
  | .load a => a.height

/-- The width of an expression: at least its variables and its temporaries. -/
def Expr.width (e : Expr) : ℕ := max e.vars e.height

/-- The width of a test: that of its two sides. -/
def Cond.width : Cond → ℕ
  | .lt a b => max a.width b.width
  | .eq a b => max a.width b.width

/-- The largest value of f on a list. -/
def maxOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: l => max (f x) (maxOf f l)

/-- The width of a statement: at least the width of its expressions, one more than each variable
that it writes, and the number of arguments of each of its calls. -/
def Stmt.width : Stmt → ℕ
  | .skip => 0
  | .set x e => max (x + 1) e.width
  | .store a e => max a.width e.width
  | .seq s t => max s.width t.width
  | .ite c s t => max c.width (max s.width t.width)
  | .while c s => max c.width s.width
  | .call _ args x => max (x + 1) (max args.length (maxOf Expr.width args))

section width

variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem maxOf_le_iff {α : Type} {f : α → ℕ} {l : List α} : maxOf f l ≤ F ↔ ∀ y ∈ l, f y ≤ F := by
  induction l <;> simp [maxOf, *]

theorem Expr.vars_op_le_iff : (Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

theorem Cond.width_lt_le_iff : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Cond.width_eq_le_iff : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Stmt.width_set_le_iff : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff

theorem Stmt.width_store_le_iff : (Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff

theorem Stmt.width_seq_le_iff : (Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff

theorem Stmt.width_ite_le_iff :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [Stmt.width, max_le_iff]

theorem Stmt.width_while_le_iff : (Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff

theorem Stmt.width_call_le_iff :
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [Stmt.width, max_le_iff, maxOf_le_iff, Nat.succ_le_iff]

end width

end Light
end
```

## ===== TCSlib/Programs/Light/Compiler/WholeProgram.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Compiler/WholeProgram.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Compiler/WholeProgram.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Compiler.Simulation
import TCSlib.Programs.Light.Compiler.StartUp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open WordRAM

namespace Light.Compiler

open WordRAM (Instr exec)

variable {W : ℕ}

/-! ## The verdict -/

/-- The verdict: accept, or, if dec is set, accept exactly if the result is positive. -/
def _root_.Light.verdictOf (dec : Bool) (r : ℤ) : Bool := !dec || decide (0 < r)

/-- What the code that follows the outermost statement leaves, if it starts in the memory m and the
result is r: the machine is about to give the verdict, the cell `cRESULT` holds the result, and only
that cell and the register D have changed. -/
private structure Verdict (code : List Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : Cfg W) : Prop where
  verdict : step code cfg = .inr (verdictOf dec r)
  result : cfg.mem cRESULT = wd W r
  agree : AgreeOutside {cRESULT, cD} m cfg.mem

/-- The code that follows the outermost statement gets there in at most three steps. -/
private theorem steps_tail {code : List Instr} {pos : ℕ} {dec : Bool}
    (hcode : CodeAt code pos (tailCode dec pos)) {m : ℤ → BitVec W} {r : ℤ}
    (hres : m (cStack mainFrame) = wd W r) (hzero : m cZERO = wd W 0) (hr : InRange W (-r)) :
    ∃ (n : ℕ) (cfg : Cfg W), n ≤ 3 ∧ Steps code n ⟨pos, m⟩ cfg ∧ Verdict code dec r m cfg := by
  -- the cell for the result := the result
  have copy : Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m cRESULT (wd W r)⟩ :=
    add_zero r ▸ steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    have read : Function.update m cRESULT (wd W r) cRESULT = wd W r := Function.update_self ..
    exact ⟨1, _, by omega, copy, step_accept hcode.tail.head, read,
      (AgreeOutside.refl _ m).update (by simp) _⟩
  | true =>
    have rest : CodeAt code (pos + 1)
      [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept] := hcode.tail
    -- D := 0 - the result; go to accept if D < 0; reject
    have run := (copy.trans (steps_sub rest (by cell_read using hzero)
      (by cell_read using hres))).trans
      (steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep : AgreeOutside {cRESULT, cD} m
        (Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r))) :=
      ((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    have read : Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r)) cRESULT =
        wd W r := by
      cell_read
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_accept rest.tail.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_reject rest.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩

/-! ## Time and space of the compiled program -/

/-- A bound for the number of steps of the compiled program outside the outermost statement:
`dispPos` + `frameSize` + 9 before it (`steps_start`), at most three after it (`steps_tail`), and
the verdict. -/
def startCost (P : Program) (dec : Bool) : ℕ := dispPos P dec + frameSize P + 13

/-- A bound for the number of steps of the compiled program, for c steps of the light program. -/
def _root_.Light.ramSteps (P : Program) (dec : Bool) (c : ℕ) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) * c

/-- The number of cells of the stack that a run within the limits needs. -/
def stackCells (P : Program) (lim : Limits) : ℕ :=
  mainFrame + (frameSize P + 1) * (lim.depth + 1)

/-- A bound for the extent of the negative cells that the compiled program uses: the stack ends
before the cell -2 · stackCells, and the pool, which reaches further down than the temporaries, ends
at the cell -(25 + 4 · dispPos). -/
def lowCell (P : Program) (dec : Bool) (lim : Limits) : ℕ :=
  max (2 * stackCells P lim) (25 + 4 * dispPos P dec)

private theorem frame_le_stackCells (P : Program) (lim : Limits) :
    mainFrame + frameSize P + 1 ≤ stackCells P lim := by
  have := Nat.le_mul_of_pos_right (frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold stackCells
  omega

/-! ## The setting of the simulation theorem -/

section setting

variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}

/-- The compiled program, with its numbers, satisfies what the simulation theorem assumes once and
for all. -/
private def setting (P : Program) (p0 : ℕ) (dec : Bool)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) : Setting W where
  toCodeLayout := codeLayout P dec
  lim := lim
  Q := stackCells P lim
  fits := hfit
  offsets_le := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [codeLayout]
    omega
  P := P
  code := compileProgram P p0 dec
  bodyAt := codeAt_bodies (codeLayout P dec) P _ (codeAt_bodiesCode P p0 dec)
  dispatcherAt := codeAt_dispatcher_dispPos P p0 dec
  width _ hb := width_le_frameSize hb

variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))

/-- The outermost statement is at `mainPos` and runs in the frame `mainFrame`. -/
private theorem start_mainStmt {σ : State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : Rel (setting P p0 dec hfit).toSizes σ mainFrame m) :
    Start (setting P p0 dec hfit) 0 (mainStmt p0) σ mainPos mainFrame m where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (frame_le_stackCells P lim)
  codeAt := codeAt_mainStmt P p0 dec
  below := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [size_mainStmt, setting, codeLayout, mainPos]
    omega
  width := (width_mainStmt p0).trans_le (three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [setting, codeLayout, stackCells, Nat.sub_zero, Nat.mul_succ]
    omega

/-- The cells below `-lowCell` and the cells from `lim.space` on are not among those that the
start-up code, the outermost statement or the code for the verdict may change. -/
private theorem not_mem_of_far {a : ℤ}
    (ha : a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a) :
    a ∉ Constants (dispPos P dec) ∪ ({cFP} ∪ MainFrame (frameSize P)) ∪
      Writable (setting P p0 dec hfit).toSizes mainFrame ∪ {cRESULT, cD} := by
  have hframe := frame_le_stackCells P lim
  have htemps := two_mul_frameSize_add_le_dispPos P dec
  have hstack : 2 * stackCells P lim ≤ lowCell P dec lim := le_max_left _ _
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec lim := le_max_right _ _
  simp only [Writable, setting, codeLayout]
  rcases ha with ha | ha <;> cells

end setting

/-! ## The theorem -/

/-- The cells 0, 1, 2, … of the memory m of the machine hold the memory μ of the light language,
and μ holds words. -/
structure Holds (W : ℕ) (lim : Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word

/-- What a run of a compiled program needs in the memory m: the memory μ of the light language, and
the arguments i and j, which are words, in their two cells. -/
structure Input (lim : Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends Holds W lim μ m where
  arg1 : m cARG1 = wd W i
  arg2 : m cARG2 = wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word

/-- What a run of a compiled program from the memory m leaves in the memory m', if the light run
ends in σ'. -/
structure Outcome (lim : Limits) (P : Program) (dec : Bool) (m : ℤ → BitVec W) (σ' : State)
    (m' : ℤ → BitVec W) : Prop where
  /-- The cells 0, 1, 2, … hold the final memory. -/
  holds : Holds W lim σ'.mem m'
  /-- The cell for the result holds the result. -/
  result : (m' cRESULT).toInt = σ'.loc 0
  /-- The first argument is still there. -/
  arg1 : m' cARG1 = m cARG1
  /-- The second argument is still there. -/
  arg2 : m' cARG2 = m cARG2
  /-- The cells far below 0 and the cells from lim.space on are unchanged. -/
  far : ∀ a : ℤ, a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a

/-- **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps.  Then
the cell -3 holds the result of the procedure and the cells `a ≥ 0` hold the final memory.  The
cells -1 and -2, the cells below `-lowCell` and the cells from `lim.space` on are unchanged.  The
two constants of the time depend on the text of P and on dec only. -/
theorem compileProgram_correct {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : State} {c : ℕ} {m : ℤ → BitVec W}
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m
        = some (verdictOf dec (σ'.loc 0), m') ∧ Outcome lim P dec m σ' m' := by
  have hF := three_le_frameSize P
  have hdisp := two_mul_frameSize_add_le_dispPos P dec
  have hσ : State.Bounded lim ⟨frame [0, i, j], μ⟩ :=
    bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  -- the start-up code
  have run₁ := steps_start P p0 dec (setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := agreeOutside_startMem hF (dispPos P dec) m
  -- the outermost statement
  obtain ⟨m', n, fin⟩ := sim (setting P p0 dec hfit) h mainPos mainFrame _ (start_mainStmt hfit hσ
    (rel_startMem _ hF (by simp only [setting, codeLayout, mainFrame]; omega)
      (fun a _ => hm.rep a) hm.arg1 hm.arg2))
  have hn : n ≤ stepsPerStep (dispPos P dec) * c := fin.le
  have run₂ := fin.run.cast_pos (p' := tailPos (frameSize P))
    (by simp only [tailPos, size_mainStmt, setting, codeLayout])
  -- the verdict
  obtain ⟨k, cfg, hk, run₃, tail⟩ := steps_tail (codeAt_tailCode P p0 dec)
    (fin.rel.loc 0 (show 0 < frameSize P by omega)) fin.rel.zero
    (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  have far (a : ℤ) ha : cfg.mem a = m a := keep.cell (not_mem_of_far hfit ha)
  refine ⟨cfg.mem, exec_mono (c := ⟨0, m⟩) (exec_of_steps run tail.verdict) ?_,
    { holds := ⟨fun a => ?_, hσ'.2⟩
      result := tail.result ▸ toInt_wd (hfit.inRange (hσ'.1 0))
      arg1 := keep.cell (by cells)
      arg2 := keep.cell (by cells)
      far := far }⟩
  · simp only [ramSteps, startCost]
    omega
  · by_cases ha : a < lim.space
    · exact tail.agree.read (by cells) (fin.rel.mem a ha)
    · rw [far _ (Or.inr (by exact_mod_cast not_lt.1 ha)), h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a

end Light.Compiler
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
* added the repository-standard `set_option` header;
* appended reading lemmas (`rfl`/`Iff.rfl` restatements of definitions) for TCSlib's own
  proofs, which do not unfold vendored definitions.
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

/-! ## Equations for reading blocks -/

/-- The resulting state of the skip block. -/
theorem Stmt.after_skip (σ : State)  :
    Stmt.after .skip σ = σ := rfl

/-- The safety condition of the skip block. -/
theorem Stmt.blockSafe_skip_iff (lim : Limits) (σ : State)  :
    Stmt.BlockSafe lim .skip σ ↔ True := Iff.rfl

/-- The resulting state of the set block. -/
theorem Stmt.after_set (σ : State) (x : ℕ) (e : Expr) :
    Stmt.after (.set x e) σ = { σ with loc := Function.update σ.loc x (e.val σ) } := rfl

/-- The safety condition of the set block. -/
theorem Stmt.blockSafe_set_iff (lim : Limits) (σ : State) (x : ℕ) (e : Expr) :
    Stmt.BlockSafe lim (.set x e) σ ↔ e.Safe lim σ := Iff.rfl

/-- The resulting state of the store block. -/
theorem Stmt.after_store (σ : State) (a e : Expr) :
    Stmt.after (.store a e) σ = { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } := rfl

/-- The safety condition of the store block. -/
theorem Stmt.blockSafe_store_iff (lim : Limits) (σ : State) (a e : Expr) :
    Stmt.BlockSafe lim (.store a e) σ ↔ a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ) := Iff.rfl

end Light
end
```

## ===== TCSlib/Programs/Light/RunsStayInLimits.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/RunsStayInLimits.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/RunsStayInLimits.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Syntax
import TCSlib.Programs.Util.List
import Mathlib.Tactic.SplitIfs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Writing a bounded number into a bounded function. -/
private theorem abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]

/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨Light.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by
  refine bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact Expr.abs_val_le hσ e (ha e he)

/-- A run that starts with words in all variables and cells ends with words in all of them. -/
theorem Exec.bounded {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨abs_update_le hσ.1 (Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, abs_update_le hσ.2 (Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (bounded_callFrame hσ _ ha)
    exact ⟨abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩

/-- A run does not change the cells from lim.space on. -/
theorem Exec.mem_outside {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by
  induction h with
  | skip => rfl
  | set _ => rfl
  | store _ _ haddr =>
    obtain ⟨h0, hlt⟩ := haddr
    exact Function.update_of_ne (by omega) _ _
  | seq _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | call _ _ _ _ ih => exact ih

end Light
end
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
* added the repository-standard `set_option` header;
* appended reading lemmas (`rfl`/`Iff.rfl` restatements of definitions) for TCSlib's own
  proofs, which do not unfold vendored definitions.
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

/-! ## Equations for reading expressions and tests -/

/-- The add operation evaluates its two integer operands. -/
theorem Op.eval_add (a b : ℤ) :
    Op.eval .add a b = a + b := rfl

/-- The sub operation evaluates its two integer operands. -/
theorem Op.eval_sub (a b : ℤ) :
    Op.eval .sub a b = a - b := rfl

/-- The mul operation evaluates its two integer operands. -/
theorem Op.eval_mul (a b : ℤ) :
    Op.eval .mul a b = a * b := rfl

/-- Expression evaluation reads the const constructor. -/
theorem Expr.val_const (σ : State) (n : ℕ) :
    Expr.val σ (.const n) = (n : ℤ) := rfl

/-- Expression evaluation reads the var constructor. -/
theorem Expr.val_var (σ : State) (x : ℕ) :
    Expr.val σ (.var x) = σ.loc x := rfl

/-- Expression evaluation reads the op constructor. -/
theorem Expr.val_op (σ : State) (o : Op) (a b : Expr) :
    Expr.val σ (.op o a b) = o.eval (a.val σ) (b.val σ) := rfl

/-- Expression evaluation reads the load constructor. -/
theorem Expr.val_load (σ : State) (a : Expr) :
    Expr.val σ (.load a) = σ.mem (a.val σ).toNat := rfl

/-- The cost of the const expression constructor. -/
theorem Expr.cost_const (n : ℕ) :
    Expr.cost (.const n) = 1 := rfl

/-- The cost of the var expression constructor. -/
theorem Expr.cost_var (x : ℕ) :
    Expr.cost (.var x) = 1 := rfl

/-- The cost of the op expression constructor. -/
theorem Expr.cost_op (o : Op) (a b : Expr) :
    Expr.cost (.op o a b) = a.cost + b.cost + 1 := rfl

/-- Address safety means nonnegativity and strict containment in the memory. -/
theorem Limits.addr_iff (lim : Limits) (a : ℤ) :
    lim.Addr a ↔ 0 ≤ a ∧ a < lim.space := Iff.rfl

/-- Safety of the const expression constructor. -/
theorem Expr.safe_const_iff (lim : Limits) (σ : State) (n : ℕ) :
    Expr.Safe lim σ (.const n) ↔ (n : ℤ) ≤ lim.word := Iff.rfl

/-- Safety of the var expression constructor. -/
theorem Expr.safe_var_iff (lim : Limits) (σ : State) (x : ℕ) :
    Expr.Safe lim σ (.var x) ↔ True := Iff.rfl

/-- Safety of the op expression constructor. -/
theorem Expr.safe_op_iff (lim : Limits) (σ : State) (o : Op) (a b : Expr) :
    Expr.Safe lim σ (.op o a b) ↔ a.Safe lim σ ∧ b.Safe lim σ ∧ |o.eval (a.val σ) (b.val σ)| ≤ lim.word := Iff.rfl

/-- Safety of the load expression constructor. -/
theorem Expr.safe_load_iff (lim : Limits) (σ : State) (a : Expr) :
    Expr.Safe lim σ (.load a) ↔ a.Safe lim σ ∧ lim.Addr (a.val σ) := Iff.rfl

/-- The lt test holds when its evaluated operands satisfy the comparison. -/
theorem Cond.holds_lt_iff (σ : State) (a b : Expr) :
    Cond.Holds σ (.lt a b) ↔ a.val σ < b.val σ := Iff.rfl

/-- The lt test costs its two operands and one comparison. -/
theorem Cond.cost_lt (a b : Expr) :
    Cond.cost (.lt a b) = a.cost + b.cost + 1 := rfl

/-- The lt test is safe exactly when both operands are safe. -/
theorem Cond.safe_lt_iff (lim : Limits) (σ : State) (a b : Expr) :
    Cond.Safe lim σ (.lt a b) ↔ a.Safe lim σ ∧ b.Safe lim σ := Iff.rfl

/-- The eq test holds when its evaluated operands satisfy the comparison. -/
theorem Cond.holds_eq_iff (σ : State) (a b : Expr) :
    Cond.Holds σ (.eq a b) ↔ a.val σ = b.val σ := Iff.rfl

/-- The eq test is safe exactly when both operands are safe. -/
theorem Cond.safe_eq_iff (lim : Limits) (σ : State) (a b : Expr) :
    Cond.Safe lim σ (.eq a b) ↔ a.Safe lim σ ∧ b.Safe lim σ := Iff.rfl

/-- A called procedure's local is the corresponding argument, or zero if absent. -/
theorem frame_apply (args : List ℤ) (i : ℕ) :
    frame args i = args.getD i 0 := rfl

end Light
end
```

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
import TCSlib.Programs.Light.Lib.Pass
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

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

/-! ## Private encoding and placement lemmas -/

/-- A signed work-tape position has an even code on the nonnegative side and an odd code on
its negative side. This is the direct-address layout used for the work tapes. -/
private def tmCell (z : ℤ) : ℕ :=
  if z < 0 then 2 * (-z).toNat + 1 else 2 * z.toNat

/-- Distinct signed positions have distinct cell codes. -/
private theorem tmCell_injective : Function.Injective tmCell := by
  intro z w h
  unfold tmCell at h
  split_ifs at h <;> omega

/-- Positions within radius `n` use cell codes at most `2 * n + 1`. -/
private theorem tmCell_le {z : ℤ} {n : ℕ} (h : |z| ≤ (n : ℤ)) :
    tmCell z ≤ 2 * n + 1 := by
  rw [abs_le] at h
  unfold tmCell
  split_ifs <;> omega

/-- The first `2 * i` cell codes are exactly the signed positions of absolute value below `i`. -/
private theorem tmCell_lt_iff (z : ℤ) (i : ℕ) :
    tmCell z < 2 * i ↔ |z| < (i : ℤ) := by
  rw [abs_lt]
  unfold tmCell
  split_ifs <;> omega

/-- Tape `j` uses the corresponding residue class in an interleaved scratch array. -/
private def tmAddr (sc tapes : ℕ) (j : Fin tapes) (z : ℤ) : ℕ :=
  sc + tmCell z * tapes + j.val

/-- Quotient and remainder uniquely identify a bank number and its finite index. -/
private theorem tmIndex_injective {k q r : ℕ} {j l : Fin k}
    (h : q * k + j.val = r * k + l.val) : q = r ∧ j = l := by
  have hk : 0 < k := by have := j.isLt; omega
  have hq := (Nat.div_mod_unique (a := q * k + j.val) (b := k) (d := q) (c := j.val) hk).mpr
    ⟨by rw [Nat.mul_comm k q, Nat.add_comm], j.isLt⟩
  have hr := (Nat.div_mod_unique (a := r * k + l.val) (b := k) (d := r) (c := l.val) hk).mpr
    ⟨by rw [Nat.mul_comm k r, Nat.add_comm], l.isLt⟩
  exact ⟨hq.1.symm.trans ((congrArg (fun n => n / k) h).trans hr.1),
    Fin.ext (hq.2.symm.trans ((congrArg (fun n => n % k) h).trans hr.2))⟩

/-- Two static local-bank indices differ if their banks or finite indices differ. -/
private theorem tmLocal_ne {k r s : ℕ} {j l : Fin k} (h : r ≠ s ∨ j ≠ l) :
    10 + r * k + j.val ≠ 10 + s * k + l.val := by
  intro he
  have he' : r * k + j.val = s * k + l.val := by omega
  obtain ⟨hrs, hjl⟩ := tmIndex_injective he'
  rcases h with h | h
  · exact h hrs
  · exact h hjl

/-- The interleaved address identifies both the tape and its signed position.

**Proof sketch.** Cancel the scratch base. `tmIndex_injective`, through `Nat.div_mod_unique`,
identifies the cell code and the finite tape index. `tmCell_injective` identifies the signed
positions. -/
private theorem tmAddr_injective {sc tapes : ℕ} {j l : Fin tapes} {z w : ℤ}
    (h : tmAddr sc tapes j z = tmAddr sc tapes l w) : j = l ∧ z = w := by
  unfold tmAddr at h
  obtain ⟨hc, hj⟩ := tmIndex_injective (show tmCell z * tapes + j.val = tmCell w * tapes + l.val by omega)
  exact ⟨hj, tmCell_injective hc⟩

/-- A cell in radius `n` lies in the first `tapes * (2 * n + 2)` scratch cells. -/
private theorem tmAddr_lt {sc tapes n : ℕ} (j : Fin tapes) {z : ℤ}
    (hz : |z| ≤ (n : ℤ)) : tmAddr sc tapes j z < sc + tapes * (2 * n + 2) := by
  have hc := tmCell_le hz
  have hm := Nat.mul_le_mul_right tapes hc
  have hj := j.isLt
  unfold tmAddr
  nlinarith

/-- Before step `i`, every work head is within radius `i` of the origin. -/
private theorem tmHead_abs_le (M : Turing.FinTM Bool) (x : List Bool) (i : ℕ)
    (j : Fin M.k) :
    |(M.tm.runFrom (M.tm.initCfg x) i).workTapePos j| ≤ (i : ℤ) := by
  have h := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) i j
  rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_workTapePos] at h
  rw [Turing.MultiTapeTM.initCfg_eq, abs_le]
  simpa only [Finset.mem_Icc, zero_sub, zero_add] using h

/-- At time `i`, cells at distance at least `i` are still blank. A simulator may initialize
these cells as it expands its scratch region, without a time bound supplied to the program.

**Proof sketch.** Induct on `i`. The initial tapes are blank by `Cfg.init_workTapes`. A live
step writes only at its current head (`Action.apply_workTapes`), which has distance at most
`i` by `tmHead_abs_le`; a cell at distance at least `i + 1` is different. A halted step is
stationary (`MultiTapeTM.step_of_halt`). -/
private theorem tmTape_blank (M : Turing.FinTM Bool) (x : List Bool) (i : ℕ)
    (j : Fin M.k) (z : ℤ) (hz : (i : ℤ) ≤ |z|) :
    (M.tm.runFrom (M.tm.initCfg x) i).workTapes j z = none := by
  induction i with
  | zero =>
    rw [Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
      Turing.Cfg.init_workTapes]
  | succ i ih =>
    have hi : (i : ℤ) ≤ |z| := by omega
    have hb := tmHead_abs_le M x i j
    have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) i).workTapePos j := by
      intro he
      rw [he] at hz
      omega
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (M.tm.runFrom (M.tm.initCfg x) i).state with
    | none =>
      rw [Turing.MultiTapeTM.step_of_halt hs]
      exact ih hi
    | some q =>
      rw [Turing.MultiTapeTM.step_of_some hs, Turing.Action.apply_workTapes,
        Function.update_of_ne hne]
      exact ih hi

/-- A completed computation has a positive first halting time no greater than its deadline,
with the prescribed output and live states at every earlier time. -/
private theorem tmFirstHalt (M : Turing.FinTM Bool) {x out : List Bool} {t : ℕ}
    (h : M.ComputesInTime x out t) :
    ∃ u ≤ t, 0 < u ∧
      (M.tm.runFrom (M.tm.initCfg x) u).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) u).output = out ∧
      ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none := by
  obtain ⟨hh, ho⟩ := (Turing.FinTM.computesInTime_iff M x out t).mp h
  obtain ⟨u, hu, hlive, he⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hh
  have hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none := by rw [he]; exact hh
  have hpos : 0 < u := by
    by_contra hn
    have hz : u = 0 := by omega
    rw [hz, Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
      Turing.Cfg.init_state] at hhalt
    cases hhalt
  exact ⟨u, hu, hpos, hhalt, by rw [he]; exact ho, hlive⟩

/-- Relocating a procedure and appending other procedures preserves its specification. -/
private theorem tmMeets_behind {lim : Limits} {Q : Program} {p d T : ℕ}
    {args : List ℤ} {μ : ℕ → ℤ} {R : ℤ → (ℕ → ℤ) → Prop}
    (h : Meets lim Q p d args μ T R) (Pre Post : Program) :
    Meets lim (Program.behind Pre Q ++ Post) (p + Pre.length) d args μ T R := by
  obtain ⟨body, hp, he⟩ := (meets_iff).mp h
  exact Meets.of_body (getElem?_append_of_eq_some (Program.getElem?_behind_right Pre hp) Post)
    (he.shift_append Pre Post)

/-! ## Private primitive block rules -/

/-- A safe assignment with a known expression value has the displayed exact local update. -/
private theorem tmSet_runs {lim : Limits} {σ : State} {dst : ℕ} {e : Expr} {z : ℤ}
    (hs : e.Safe lim σ) (hv : e.val σ = z) :
    (Stmt.set dst e).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc dst z } := by
  refine ⟨(Stmt.blockSafe_set_iff _ _ _ _).mpr hs, ?_⟩
  rw [Stmt.after_set, hv]

/-- A safe store with a known in-range natural address and value has the displayed exact
memory update and preserves the local variables. -/
private theorem tmStore_runs {lim : Limits} {σ : State} {addr value : Expr} {b : ℕ} {z : ℤ}
    (ha : addr.Safe lim σ) (he : value.Safe lim σ) (haddr : addr.val σ = (b : ℤ))
    (hv : value.val σ = z) (hb : b < lim.space) :
    (Stmt.store addr value).Runs lim σ fun τ =>
      τ = { σ with mem := Function.update σ.mem b z } := by
  refine ⟨(Stmt.blockSafe_store_iff _ _ _ _).mpr ⟨ha, he, ?_⟩, ?_⟩
  · rw [haddr, Limits.addr_iff]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hb⟩
  · rw [Stmt.after_store, haddr, hv, Int.toNat_natCast]

/-! ## Private finite branch selection -/

/-- The listed locals have the listed natural values. -/
private def tmMatches (tests : List (ℕ × ℕ)) (σ : State) : Prop :=
  ∀ pair ∈ tests, σ.loc pair.1 = (pair.2 : ℤ)

/-- Test a fixed finite list of local values, choosing `yes` only when all agree. -/
private def tmSelect : List (ℕ × ℕ) → Stmt → Stmt → Stmt
  | [], yes, _ => yes
  | pair :: rest, yes, no =>
      .ite (.eq (.var pair.1) (.const pair.2)) (tmSelect rest yes no) no

/-- Finite branch selection preserves any common postcondition of its two alternatives.

**Proof sketch.** Induct on the tests. `Stmt.Runs.ite_pos` removes a matching head test,
and `Stmt.Runs.ite_neg` selects the failure alternative as soon as a local differs. The
constructor readers of `Expr` and `Cond` discharge the safe comparison and its value. -/
private theorem tmSelect_runs {lim : Limits} {σ : State} {tests : List (ℕ × ℕ)}
    {yes no : Stmt} {R : State → Prop}
    (hs : ∀ pair ∈ tests, (pair.2 : ℤ) ≤ lim.word)
    (hy : tmMatches tests σ → yes.Runs lim σ R)
    (hn : ¬tmMatches tests σ → no.Runs lim σ R) :
    (tmSelect tests yes no).Runs lim σ R := by
  induction tests with
  | nil => exact hy (by simp only [tmMatches, List.not_mem_nil, false_implies, implies_true])
  | cons pair rest ih =>
    have hsafe : (Cond.eq (.var pair.1) (.const pair.2)).Safe lim σ := by
      rw [Cond.safe_eq_iff, Expr.safe_var_iff, Expr.safe_const_iff]
      exact ⟨trivial, hs pair (List.mem_cons_self ..)⟩
    have hholds : (Cond.eq (.var pair.1) (.const pair.2)).Holds σ ↔
        σ.loc pair.1 = (pair.2 : ℤ) := by
      rw [Cond.holds_eq_iff, Expr.val_var, Expr.val_const]
    by_cases hp : σ.loc pair.1 = (pair.2 : ℤ)
    · apply Stmt.Runs.ite_pos (c := .eq (.var pair.1) (.const pair.2))
        (ih (fun p h => hs p (List.mem_cons_of_mem _ h)) ?_ ?_) (hholds.mpr hp) hsafe
      · intro hr
        apply hy
        intro p h
        rcases List.mem_cons.mp h with he | he
        · subst p; exact hp
        · exact hr p he
      · intro hr
        apply hn
        intro hall
        exact hr fun p h => hall p (List.mem_cons_of_mem _ h)
    · apply Stmt.Runs.ite_neg (c := .eq (.var pair.1) (.const pair.2))
        (hn ?_) (fun hh => hp (hholds.mp hh)) hsafe
      intro hall
      exact hp (hall pair (List.mem_cons_self ..))

/-- A finite table compiled as code branches, with no transition table stored in memory. -/
private def tmDispatch {α : Type} (tests : α → List (ℕ × ℕ)) (body : α → Stmt) : List α → Stmt
  | [] => .skip
  | row :: rest => tmSelect (tests row) (body row) (tmDispatch tests body rest)

/-- A compiled finite table executes the selected row whenever that row occurs in the table.

**Proof sketch.** Induct on the rows and use `tmSelect_runs` for the first row. A successful
test identifies that row with `actual`. A failed test excludes it, so the occurrence of
`actual` is in the tail, where the induction hypothesis applies. -/
private theorem tmDispatch_runs {α : Type} {lim : Limits} {σ : State}
    {tests : α → List (ℕ × ℕ)} {body : α → Stmt} {rows : List α} {actual : α}
    {R : State → Prop} (ha : actual ∈ rows)
    (hs : ∀ row ∈ rows, ∀ pair ∈ tests row, (pair.2 : ℤ) ≤ lim.word)
    (hm : ∀ row ∈ rows, tmMatches (tests row) σ ↔ row = actual)
    (hr : (body actual).Runs lim σ R) :
    (tmDispatch tests body rows).Runs lim σ R := by
  induction rows with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons row rest ih =>
    apply tmSelect_runs (hs row (List.mem_cons_self ..))
    · intro ht
      have he := (hm row (List.mem_cons_self ..)).mp ht
      subst row
      exact hr
    · intro hn
      have hat : actual ∈ rest := by
        rcases List.mem_cons.mp ha with he | he
        · exact False.elim (hn ((hm row (List.mem_cons_self ..)).mpr he.symm))
        · exact he
      exact ih hat (fun r hh => hs r (List.mem_cons_of_mem _ hh))
        (fun r hh => hm r (List.mem_cons_of_mem _ hh))

/-! ## Private simulator program -/

/-- Blank, false, and true have codes zero, one, and two. -/
private def tmSym : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The nonblank symbol code is the bit value plus one. -/
private theorem tmSym_some_eq (bit : Bool) : tmSym (some bit) = bit.toNat + 1 := by
  cases bit <;> rfl

/-- Every encoded work symbol is at most two. -/
private theorem tmSym_le_two (sym : Option Bool) : tmSym sym ≤ 2 := by
  cases sym with
  | none => decide
  | some bit =>
    rw [tmSym_some_eq]
    exact Nat.add_le_add_right (Bool.toNat_le bit) 1

/-- A bit string represented as one integer word per bit in memory. -/
private def tmBits (bits : List Bool) : List ℤ := bits.map fun bit => (bit.toNat : ℤ)

/-- Zero the next pair of cell-code rows, leaving all previously initialized rows alone. -/
private def tmRingMemory (sc tapes i : ℕ) (μ : ℕ → ℤ) : ℕ → ℤ :=
  wrote μ (sc + 2 * i * tapes) (fun _ => 0) (2 * tapes)

/-- Initializing the next ring preserves every earlier represented cell. -/
private theorem tmRingMemory_old {sc tapes i : ℕ} (μ : ℕ → ℤ) (j : Fin tapes) (z : ℤ)
    (hz : tmCell z < 2 * i) :
    tmRingMemory sc tapes i μ (tmAddr sc tapes j z) = μ (tmAddr sc tapes j z) := by
  have hm := Nat.mul_le_mul_right tapes (show tmCell z + 1 ≤ 2 * i by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hj := j.isLt
  apply wrote_rest
  left
  unfold tmAddr
  omega

/-- Every cell in the new pair of cell-code rows is initialized to blank. -/
private theorem tmRingMemory_new {sc tapes i : ℕ} (μ : ℕ → ℤ) (j : Fin tapes) (z : ℤ)
    (hlo : 2 * i ≤ tmCell z) (hhi : tmCell z < 2 * i + 2) :
    tmRingMemory sc tapes i μ (tmAddr sc tapes j z) = 0 := by
  have hj := j.isLt
  have hlow : sc + 2 * i * tapes ≤ tmAddr sc tapes j z := by
    unfold tmAddr
    nlinarith
  have hhigh : tmAddr sc tapes j z < sc + 2 * i * tapes + 2 * tapes := by
    unfold tmAddr
    nlinarith
  have hoff : tmAddr sc tapes j z - (sc + 2 * i * tapes) < 2 * tapes := by omega
  have he : sc + 2 * i * tapes + (tmAddr sc tapes j z - (sc + 2 * i * tapes)) =
      tmAddr sc tapes j z := Nat.add_sub_of_le hlow
  exact he ▸ (wrote_done (μ := μ) (f := fun _ => (0 : ℤ)) hoff)

/-- The three symbol codes distinguish blank and the two bits. -/
private theorem tmSym_injective : Function.Injective tmSym := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> simp only [tmSym, Nat.reduceEqDiff] at h
  | some a => cases b with
    | none => cases a <;> simp only [tmSym, Nat.reduceEqDiff] at h
    | some b => cases a <;> cases b <;> simp_all only [tmSym, Nat.reduceEqDiff]

/-- Clearing the next ring extends a correct tape encoding from strict radius `i` to radius `i`. -/
private theorem tmRingMemory_tapes (M : Turing.FinTM Bool) (x : List Bool) (i sc : ℕ)
    (μ : ℕ → ℤ)
    (hμ : ∀ (j : Fin M.k) (z : ℤ), |z| < (i : ℤ) →
      μ (tmAddr sc M.k j z) = (tmSym ((M.tm.runFrom (M.tm.initCfg x) i).workTapes j z) : ℤ)) :
    ∀ (j : Fin M.k) (z : ℤ), |z| ≤ (i : ℤ) →
      tmRingMemory sc M.k i μ (tmAddr sc M.k j z) =
        (tmSym ((M.tm.runFrom (M.tm.initCfg x) i).workTapes j z) : ℤ) := by
  intro j z hz
  by_cases hc : tmCell z < 2 * i
  · rw [tmRingMemory_old μ j z hc]
    exact hμ j z ((tmCell_lt_iff z i).mp hc)
  · have hlarge : (i : ℤ) ≤ |z| := by
      have hn : ¬ |z| < (i : ℤ) := fun hh => hc ((tmCell_lt_iff z i).mpr hh)
      omega
    have hhi : tmCell z < 2 * i + 2 := by have := tmCell_le hz; omega
    rw [tmRingMemory_new μ j z (by omega) hhi, tmTape_blank M x i j z hlarge]
    rfl

/-- The live states have positive indices in a fixed enumeration; zero denotes halt. -/
private noncomputable def tmStateCode (M : Turing.FinTM Bool) : Option M.State → ℕ
  | none => 0
  | some q => 1 + (Finset.univ.toList : List M.State).idxOf q

/-- Distinct optional machine states have distinct control-state codes. -/
private theorem tmStateCode_injective (M : Turing.FinTM Bool) :
    Function.Injective (tmStateCode M) := by
  classical
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => simp only [tmStateCode] at h; omega
  | some a => cases b with
    | none => simp only [tmStateCode] at h; omega
    | some b =>
      have ha : a ∈ (Finset.univ.toList : List M.State) :=
        Finset.mem_toList.mpr (Finset.mem_univ a)
      have hb : b ∈ (Finset.univ.toList : List M.State) :=
        Finset.mem_toList.mpr (Finset.mem_univ b)
      simp only [tmStateCode] at h
      exact congrArg some ((List.idxOf_inj ha hb).mp (by omega))

/-- All control-state codes are bounded by the size of the fixed state enumeration plus one. -/
private theorem tmStateCode_le (M : Turing.FinTM Bool) (q : Option M.State) :
    tmStateCode M q ≤ (Finset.univ.toList : List M.State).length + 1 := by
  classical
  cases q with
  | none => exact Nat.zero_le _
  | some q =>
    simpa only [tmStateCode, Nat.add_comm] using
      Nat.add_le_add_left (List.idxOf_le_length (a := q)
        (l := (Finset.univ.toList : List M.State))) 1

/-- A transition row specifies a live state and the input and work symbols it scans. -/
private abbrev TMRow (M : Turing.FinTM Bool) :=
  M.State × (Option Bool × (Fin M.k → Option Bool))

/-- All transition rows of a finite binary machine, enumerated once when generating the code. -/
private noncomputable def tmRows (M : Turing.FinTM Bool) : List (TMRow M) :=
  Finset.univ.toList

/-- Sequential composition of a fixed list of statements. -/
private def tmSeq : List Stmt → Stmt
  | [] => .skip
  | s :: rest => .seq s (tmSeq rest)

/-- A static bank preserves its invariant, establishes the property of every visited index,
and preserves that property at any index where it already held.

**Proof sketch.** Induct over the statically generated statement list and compose with
`Stmt.Runs.seq`. Each single block preserves the invariant and all previously established
index properties; the tail therefore preserves the head's property as well as its own. -/
private theorem tmSeq_accumulate {α : Type} {lim : Limits} {body : α → Stmt}
    {I : State → Prop} {F : α → State → Prop} {rows : List α} {σ : State}
    (hi : I σ)
    (hr : ∀ j ∈ rows, ∀ τ, I τ → (body j).Runs lim τ fun τ' =>
      I τ' ∧ F j τ' ∧ ∀ l, F l τ → F l τ') :
    (tmSeq (rows.map body)).Runs lim σ fun τ =>
      I τ ∧ (∀ j ∈ rows, F j τ) ∧ ∀ j, F j σ → F j τ := by
  induction rows generalizing σ with
  | nil =>
    constructor
    · exact (Stmt.blockSafe_skip_iff lim σ).mpr trivial
    · simp only [List.map_nil, tmSeq, Stmt.after_skip]
      exact ⟨hi, fun _ hh => False.elim (List.not_mem_nil hh), fun _ hh => hh⟩
  | cons j rest ih =>
    apply Stmt.Runs.seq
    apply (hr j (List.mem_cons_self ..) σ hi).mono
    intro τ hτ
    apply (ih hτ.1 (fun l hl => hr l (List.mem_cons_of_mem _ hl))).mono
    intro τ' hτ'
    refine ⟨hτ'.1, ?_, fun l hl => hτ'.2.2 l (hτ.2.2 l hl)⟩
    intro l hl
    rcases List.mem_cons.mp hl with he | he
    · subst l
      exact hτ'.2.2 j hτ.2.1
    · exact hτ'.2.1 l he

/-- One statically generated block per work tape. -/
private def tmBank (M : Turing.FinTM Bool) (body : Fin M.k → Stmt) : Stmt :=
  tmSeq ((List.finRange M.k).map body)

/-- Local numbers for work heads, scanned work symbols, and computed tape addresses. The first
ten locals hold the arguments, input position, control state, output length, and round number. -/
private def tmHead (j : ℕ) : ℕ := 10 + j
private def tmScan (tapes j : ℕ) : ℕ := 10 + tapes + j
private def tmAddress (tapes j : ℕ) : ℕ := 10 + 2 * tapes + j
private def tmOldHead (tapes j : ℕ) : ℕ := 10 + 3 * tapes + j

/-! ## Private representation invariant -/

/-- The stable locals describing one simulated configuration. The temporary locals for
addresses, frozen heads, scans, and scratch initialization are deliberately unconstrained. -/
private structure TMFrame (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (a b sc i : ℕ) (σ : State) : Prop where
  src : σ.loc 0 = (a : ℤ)
  len : σ.loc 1 = (x.length : ℤ)
  dst : σ.loc 2 = (b : ℤ)
  scratch : σ.loc 3 = (sc : ℤ)
  inputPos : σ.loc 4 = (c.inputPos.val : ℤ)
  control : σ.loc 5 = (tmStateCode M c.state : ℤ)
  outputLen : σ.loc 6 = (c.output.length : ℤ)
  round : σ.loc 7 = (i : ℤ)
  heads : ∀ j : Fin M.k, σ.loc (tmHead j.val) = c.workTapePos j

/-- The frozen work heads and their direct addresses for one simulated configuration. -/
private structure TMLocated (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc : ℕ) (σ : State) : Prop where
  oldHeads : ∀ j : Fin M.k, σ.loc (tmOldHead M.k j.val) = c.workTapePos j
  addresses : ∀ j : Fin M.k,
    σ.loc (tmAddress M.k j.val) = (tmAddr sc M.k j (c.workTapePos j) : ℤ)

/-- The scanned input and work symbols captured before the transition writes any tape. -/
private structure TMScanned (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (σ : State) : Prop where
  input : σ.loc 9 = (tmSym c.inputSymbol : ℤ)
  work : ∀ j : Fin M.k, σ.loc (tmScan M.k j.val) = (tmSym (c.workTapeSymbols j) : ℤ)

/-- The represented cells of all work tapes within a strict radius. -/
private def TMTapes (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc radius : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
    μ (tmAddr sc M.k j z) = (tmSym (c.workTapes j z) : ℤ)

/-- The represented work cells away from the old head on each tape; old head cells may be
rewritten while a transition's static tape bank is executing. -/
private def TMTapesAway (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc radius : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) → z ≠ c.workTapePos j →
    μ (tmAddr sc M.k j z) = (tmSym (c.workTapes j z) : ℤ)

/-- Writing at an old work head preserves every represented cell away from all old heads.
The address injectivity theorem separates both different tapes and different signed cells. -/
private theorem tmTapesAway_write {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {sc radius : ℕ} {μ : ℕ → ℤ} (j : Fin M.k)
    (h : TMTapesAway M c sc radius μ) (value : ℤ) :
    TMTapesAway M c sc radius
      (Function.update μ (tmAddr sc M.k j (c.workTapePos j)) value) := by
  intro l z hz hne
  have haddr : tmAddr sc M.k l z ≠ tmAddr sc M.k j (c.workTapePos j) := by
    intro he
    obtain ⟨hjl, hp⟩ := tmAddr_injective he
    subst l
    exact hne hp
  rw [Function.update_of_ne haddr]
  exact h l z hz hne

/-- The locals constrained by `TMFrame`: the eight scalar locals and the current work heads. -/
private def tmKeyLocal (M : Turing.FinTM Bool) (v : ℕ) : Prop :=
  v < 8 ∨ ∃ j : Fin M.k, v = tmHead j.val

/-- Preserving the stable locals other than the round counter, and assigning a new counter,
preserves the configuration frame at that new round. -/
private theorem tmFrame_transfer {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i i' : ℕ} {σ τ : State}
    (hf : TMFrame M c a b sc i σ)
    (he : ∀ v, tmKeyLocal M v → v ≠ 7 → τ.loc v = σ.loc v)
    (hround : τ.loc 7 = (i' : ℤ)) : TMFrame M c a b sc i' τ := by
  constructor
  · exact (he 0 (Or.inl (by decide)) (by decide)).trans hf.src
  · exact (he 1 (Or.inl (by decide)) (by decide)).trans hf.len
  · exact (he 2 (Or.inl (by decide)) (by decide)).trans hf.dst
  · exact (he 3 (Or.inl (by decide)) (by decide)).trans hf.scratch
  · exact (he 4 (Or.inl (by decide)) (by decide)).trans hf.inputPos
  · exact (he 5 (Or.inl (by decide)) (by decide)).trans hf.control
  · exact (he 6 (Or.inl (by decide)) (by decide)).trans hf.outputLen
  · exact hround
  · intro j
    exact (he (tmHead j.val) (Or.inr ⟨j, rfl⟩) (by unfold tmHead; omega)).trans (hf.heads j)

/-- Assigning the round local changes only the round index of the represented frame. -/
private theorem tmFrame_round {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i : ℕ} {σ : State}
    (hf : TMFrame M c a b sc i σ) (i' : ℕ) :
    TMFrame M c a b sc i' ⟨Function.update σ.loc 7 (i' : ℤ), σ.mem⟩ := by
  apply tmFrame_transfer hf
  · intro v _ hv
    exact Function.update_of_ne hv (i' : ℤ) σ.loc
  · change Function.update σ.loc 7 (i' : ℤ) 7 = (i' : ℤ)
    exact Function.update_self ..

/-- Changing a temporary local outside the scalar and head banks preserves the frame,
with no restriction on the replacement memory. -/
private theorem tmFrame_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i r : ℕ} {σ : State} {z : ℤ}
    (hf : TMFrame M c a b sc i σ) (hr : 8 ≤ r) (hgap : r < 10 ∨ 10 + M.k ≤ r)
    (ν : ℕ → ℤ) : TMFrame M c a b sc i ⟨Function.update σ.loc r z, ν⟩ := by
  apply tmFrame_transfer hf
  · intro v hv _
    change Function.update σ.loc r z v = σ.loc v
    apply Function.update_of_ne
    intro he
    rcases hv with hv | ⟨j, hj⟩
    · omega
    · have hjlt := j.isLt
      unfold tmHead at hj
      rcases hgap with hgap | hgap <;> omega
  · change Function.update σ.loc r z 7 = (i : ℤ)
    rw [Function.update_of_ne (by omega)]
    exact hf.round

/-- A local update outside the frozen-head/address interval preserves the located data,
independently of the replacement memory. -/
private theorem tmLocated_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {sc r : ℕ} {σ : State} {z : ℤ}
    (hl : TMLocated M c sc σ) (hr : r < 10 + 2 * M.k ∨ 10 + 4 * M.k ≤ r)
    (ν : ℕ → ℤ) : TMLocated M c sc ⟨Function.update σ.loc r z, ν⟩ := by
  have he (v : ℕ) (hlo : 10 + 2 * M.k ≤ v) (hhi : v < 10 + 4 * M.k) :
      Function.update σ.loc r z v = σ.loc v := by
    apply Function.update_of_ne
    intro hv
    rcases hr with hr | hr <;> omega
  constructor
  · intro j
    exact (he _ (by unfold tmOldHead; omega)
      (by have := j.isLt; unfold tmOldHead; omega)).trans (hl.oldHeads j)
  · intro j
    exact (he _ (by unfold tmAddress; omega)
      (by have := j.isLt; unfold tmAddress; omega)).trans (hl.addresses j)

/-- Updating a local outside the captured input/work scan slots preserves their old symbol
codes, independently of the replacement memory. -/
private theorem tmScanned_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {r : ℕ} {σ : State} {z : ℤ}
    (hs : TMScanned M c σ) (hr9 : r ≠ 9) (hr : r < 10 + M.k ∨ 10 + 2 * M.k ≤ r)
    (ν : ℕ → ℤ) : TMScanned M c ⟨Function.update σ.loc r z, ν⟩ := by
  constructor
  · exact (Function.update_of_ne hr9.symm z σ.loc).trans hs.input
  · intro j
    have hne : tmScan M.k j.val ≠ r := by
      have hj := j.isLt
      unfold tmScan
      rcases hr with hr | hr <;> omega
    exact (Function.update_of_ne hne z σ.loc).trans (hs.work j)

/-- The scratch address of the nonnegative cell code `code` on tape `j`. -/
private def tmAddrExpr (tapes j : ℕ) (code : Expr) : Expr :=
  .op .add (.var 3) (.op .add (.op .mul code (.const tapes)) (.const j))

/-- A natural cell-code expression gives the corresponding safe interleaved address whenever
its code, the two constants, and the resulting address fit the limits. -/
private theorem tmAddrExpr_read {lim : Limits} {σ : State} {tapes j sc n : ℕ}
    (code : Expr) (hsc : σ.loc 3 = (sc : ℤ)) (hc : code.Safe lim σ)
    (hv : code.val σ = (n : ℤ)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hk : (tapes : ℤ) ≤ lim.word) (hj : (j : ℤ) ≤ lim.word)
    (hs : sc + n * tapes + j ≤ lim.space) :
    (tmAddrExpr tapes j code).Safe lim σ ∧
      (tmAddrExpr tapes j code).val σ = ((sc + n * tapes + j : ℕ) : ℤ) := by
  have hsZ : (sc : ℤ) + (n : ℤ) * tapes + j ≤ (lim.space : ℤ) := by exact_mod_cast hs
  have hp : 0 ≤ (n : ℤ) * tapes := by positivity
  constructor
  · simp only [tmAddrExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_mul,
      hsc, hv, hc, true_and, abs_le]
    omega
  · simp only [tmAddrExpr, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
      Op.eval_mul, hsc, hv, Nat.cast_add, Nat.cast_mul, add_assoc]

/-- Initialize the next two interleaved cell-code rows using the existing pass routine.
Locals eight and nine hold its destination and length; its counter is beyond the tape locals. -/
private def tmClearRing (M : Turing.FinTM Bool) : Stmt :=
  tmSeq [.set 8 (tmAddrExpr M.k 0 (.op .mul (.const 2) (.var 7))),
    .set 9 (.const (2 * M.k)), pass (10 + 4 * M.k) (.var 9) (.var 8) (.const 0)]

/-- Clearing one newly reachable ring costs `26 * M.k + 18` steps, leaves the represented
memory `tmRingMemory`, and changes only the pass's three temporary locals.

**Proof sketch.** Compute the ring destination and its constant length in locals eight and
nine. Apply `Ends.pass` with the constant-zero expression, using the published expression
readers for its safety and cost. `wrote` is exactly `tmRingMemory`; the pass changes only its
counter, and `Function.update_of_ne` preserves the other locals. -/
private theorem tmClearRing_ends (M : Turing.FinTM Bool) {lim : Limits} {P : Program} {d : ℕ}
    (σ : State) (sc i : ℕ) (hsc : σ.loc 3 = (sc : ℤ)) (hi : σ.loc 7 = (i : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hs : sc + 2 * (i + 1) * M.k ≤ lim.space)
    (hi2 : (2 : ℤ) * ((i : ℤ) + 1) ≤ lim.word)
    (hk2 : (2 : ℤ) * M.k ≤ lim.word) :
    Ends lim P d (tmClearRing M) σ (26 * M.k + 18) fun τ =>
      τ.mem = tmRingMemory sc M.k i σ.mem ∧
      ∀ v, v ≠ 8 → v ≠ 9 → v ≠ 10 + 4 * M.k → τ.loc v = σ.loc v := by
  let dst := sc + 2 * i * M.k
  have hsZ : (sc : ℤ) + 2 * ((i : ℤ) + 1) * M.k ≤ (lim.space : ℤ) := by
    exact_mod_cast hs
  have hdst : dst + 2 * M.k ≤ lim.space := by dsimp only [dst]; nlinarith
  have hzero : (0 : ℤ) ≤ lim.word := by nlinarith [Int.natCast_nonneg M.k]
  have hc : (Expr.op .mul (.const 2) (.var 7)).Safe lim σ := by
    simp only [Expr.safe_op_iff, Expr.safe_const_iff, Expr.safe_var_iff, Expr.val_const,
      Expr.val_var, Op.eval_mul, hi, Nat.cast_ofNat, true_and, abs_le]
    omega
  have hvc : (Expr.op .mul (.const 2) (.var 7)).val σ = ((2 * i : ℕ) : ℤ) := by
    simp only [Expr.val_op, Expr.val_const, Expr.val_var, Op.eval_mul, hi,
      Nat.cast_mul, Nat.cast_ofNat]
  obtain ⟨hsafe, hv⟩ := tmAddrExpr_read (.op .mul (.const 2) (.var 7)) hsc hc hvc hw
    (show (M.k : ℤ) ≤ lim.word by omega) hzero
    (show sc + (2 * i) * M.k + 0 ≤ lim.space by dsimp only [dst] at hdst; omega)
  change (tmAddrExpr M.k 0 (.op .mul (.const 2) (.var 7))).val σ = (dst : ℤ) at hv
  unfold tmClearRing tmSeq
  refine Ends.seq 10 (26 * M.k + 8) (Ends.set hsafe ?_ ?_) (by omega)
  · simp only [tmAddrExpr, Expr.cost_op, Expr.cost_var, Expr.cost_const]
    omega
  · rw [hv]
    refine Ends.seq 2 (26 * M.k + 6) (Ends.set ?_ ?_ ?_) (by omega)
    · rw [Expr.safe_const_iff, Nat.cast_mul, Nat.cast_ofNat]
      exact hk2
    · rw [Expr.cost_const]
    · rw [Expr.val_const]
      refine Ends.seq (26 * M.k + 6) 0 ?_ (by omega)
      refine Ends.pass (c := 10 + 4 * M.k) (x := 9) (y := 8) (n := 2 * M.k)
        (dst := dst) (fun _ => (0 : ℤ)) ?_ ?_ hw hdst ?_ ?_
        (by omega) (by omega) ?_
      · intro j hj
        exact ⟨(Expr.safe_const_iff _ _ 0).mpr hzero, Expr.val_const _ 0⟩
      · apply Ends.skip
        refine ⟨rfl, ?_⟩
        intro v h8 h9 hc
        simp only [Function.update_of_ne hc, Function.update_of_ne h9,
          Function.update_of_ne h8]
      · change Function.update (Function.update σ.loc 8 (dst : ℤ)) 9 ((2 * M.k : ℕ) : ℤ) 9 =
          ((2 * M.k : ℕ) : ℤ)
        exact Function.update_self ..
      · change Function.update (Function.update σ.loc 8 (dst : ℤ)) 9 ((2 * M.k : ℕ) : ℤ) 8 =
          (dst : ℤ)
        rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 9)]
        exact Function.update_self ..
      · rw [Expr.cost_const]
        omega

/-- The two arithmetic branches computing a signed tape position's cell code. -/
private def tmCodeExpr (src : ℕ) : Bool → Expr
  | false => .op .mul (.const 2) (.var src)
  | true => .op .add (.op .mul (.const 2) (.op .sub (.const 0) (.var src))) (.const 1)

/-- The selected sign branch safely computes the signed cell code using only linear
arithmetic in the head position.

**Proof sketch.** Split on the sign branch and read each arithmetic constructor through its
published equations. `tmCell` has the same two branches; the sign hypothesis identifies
`Int.toNat` with the corresponding nonnegative position. The code bound controls every
intermediate value, and the separate bound on two controls the constants. -/
private theorem tmCodeExpr_read {lim : Limits} {σ : State} {src : ℕ} {z : ℤ}
    (negative : Bool) (hz : σ.loc src = z) (h2 : (2 : ℤ) ≤ lim.word)
    (hc : (tmCell z : ℤ) ≤ lim.word) (hside : if negative then z < 0 else 0 ≤ z) :
    (tmCodeExpr src negative).Safe lim σ ∧
      (tmCodeExpr src negative).val σ = (tmCell z : ℤ) := by
  cases negative with
  | false =>
    change 0 ≤ z at hside
    have hn : ¬z < 0 := by omega
    simp only [tmCodeExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_mul, hz, tmCell, if_neg hn,
      Nat.cast_mul, Nat.cast_ofNat, true_and, abs_le] at hc ⊢
    omega
  | true =>
    change z < 0 at hside
    simp only [tmCodeExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_mul, Op.eval_sub,
      hz, tmCell, if_pos hside, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, true_and, abs_le] at hc ⊢
    omega

/-- Compute a head's direct scratch address by branching on its sign. -/
private def tmLocate (M : Turing.FinTM Bool) (j : Fin M.k) : Stmt :=
  .seq (.set (tmOldHead M.k j.val) (.var (tmHead j.val)))
    (.ite (.lt (.var (tmHead j.val)) (.const 0))
      (.set (tmAddress M.k j.val) (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) true)))
      (.set (tmAddress M.k j.val) (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) false))))

/-- Locating one tape freezes its head and records its direct scratch address, changing no
memory and no other locals.

**Proof sketch.** The first assignment freezes the work head. Its temporary local is distinct
from both the current head and scratch base. The guard therefore reads the original sign.
In either branch, `tmCodeExpr_read` computes the signed cell code and `tmAddrExpr_read`
computes the interleaved address; the two assignments give the displayed exact state. -/
private theorem tmLocate_runs (M : Turing.FinTM Bool) {lim : Limits} (σ : State)
    (j : Fin M.k) (sc : ℕ) (z : ℤ) (hsc : σ.loc 3 = (sc : ℤ))
    (hz : σ.loc (tmHead j.val) = z) (hw : (lim.space : ℤ) ≤ lim.word)
    (h2 : (2 : ℤ) ≤ lim.word) (hc : (tmCell z : ℤ) ≤ lim.word)
    (hk : (M.k : ℤ) ≤ lim.word) (hj : (j.val : ℤ) ≤ lim.word)
    (ha : sc + tmCell z * M.k + j.val ≤ lim.space) :
    (tmLocate M j).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update (Function.update σ.loc (tmOldHead M.k j.val) z) (tmAddress M.k j.val) (tmAddr sc M.k j z : ℤ) } := by
  unfold tmLocate
  apply Stmt.Runs.seq
  refine ⟨(Stmt.blockSafe_set_iff _ _ _ _).mpr ((Expr.safe_var_iff _ _ _).mpr trivial), ?_⟩
  rw [Stmt.after_set, Expr.val_var, hz]
  let σ₁ : State := { σ with loc := Function.update σ.loc (tmOldHead M.k j.val) z }
  have hs₁ : σ₁.loc 3 = (sc : ℤ) := by
    change Function.update σ.loc (tmOldHead M.k j.val) z 3 = (sc : ℤ)
    rw [Function.update_of_ne (by unfold tmOldHead; omega)]
    exact hsc
  have hz₁ : σ₁.loc (tmHead j.val) = z := by
    change Function.update σ.loc (tmOldHead M.k j.val) z (tmHead j.val) = z
    rw [Function.update_of_ne (by have := j.isLt; unfold tmHead tmOldHead; omega)]
    exact hz
  have hbranch (negative : Bool) (hside : if negative then z < 0 else 0 ≤ z) :
      (Stmt.set (tmAddress M.k j.val)
        (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) negative))).Runs lim σ₁ fun τ =>
          τ = { σ with loc := Function.update (Function.update σ.loc (tmOldHead M.k j.val) z) (tmAddress M.k j.val) (tmAddr sc M.k j z : ℤ) } := by
    obtain ⟨hcode, hval⟩ := tmCodeExpr_read negative hz₁ h2 hc hside
    obtain ⟨haddr, hvaladdr⟩ := tmAddrExpr_read _ hs₁ hcode hval hw hk hj ha
    simpa only [σ₁, tmAddr] using (tmSet_runs (dst := tmAddress M.k j.val) haddr hvaladdr)
  have hguard : (Cond.lt (.var (tmHead j.val)) (.const 0)).Holds σ₁ ↔ z < 0 := by
    rw [Cond.holds_lt_iff, Expr.val_var, Expr.val_const, hz₁, Nat.cast_zero]
  have hsafe : (Cond.lt (.var (tmHead j.val)) (.const 0)).Safe lim σ₁ := by
    rw [Cond.safe_lt_iff, Expr.safe_var_iff, Expr.safe_const_iff]
    exact ⟨trivial, by omega⟩
  by_cases hn : z < 0
  · exact Stmt.Runs.ite_pos (hbranch true hn) (hguard.mpr hn) hsafe
  · have hznonneg : 0 ≤ z := le_of_not_gt hn
    exact Stmt.Runs.ite_neg (hbranch false hznonneg) (fun hh => hn (hguard.mp hh)) hsafe

/-- Locating the whole work-head bank preserves the frame and memory and records every frozen
head and direct address.

**Proof sketch.** Apply `tmSeq_accumulate` to the static tape list. `tmLocate_runs` gives each
pair of local assignments. `tmFrame_tmp` preserves the stable frame through them, while
`tmLocal_ne` separates different banks and different tape indices. Thus every existing
frozen-head/address property survives and the visited tape's property is established. -/
private theorem tmLocateBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hw : (lim.space : ℤ) ≤ lim.word)
    (h2 : (2 : ℤ) ≤ lim.word) (hk : (M.k : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (ha : ∀ j : Fin M.k, sc + tmCell (c.workTapePos j) * M.k + j.val ≤ lim.space) :
    (tmBank M (tmLocate M)).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ τ.mem = σ.mem ∧ TMLocated M c sc τ := by
  let I : State → Prop := fun τ => TMFrame M c a b sc i τ ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmOldHead M.k j.val) = c.workTapePos j ∧
      τ.loc (tmAddress M.k j.val) = (tmAddr sc M.k j (c.workTapePos j) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmLocate M j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hft, hmt⟩
    have hj : (j.val : ℤ) ≤ lim.word := by have := j.isLt; omega
    apply (tmLocate_runs M τ j sc (c.workTapePos j) hft.scratch (hft.heads j)
      hw h2 (hc j) hk hj (ha j)).mono
    rintro ν rfl
    let ν : State := { τ with loc := Function.update (Function.update τ.loc (tmOldHead M.k j.val) (c.workTapePos j)) (tmAddress M.k j.val) (tmAddr sc M.k j (c.workTapePos j) : ℤ) }
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hf₁ := tmFrame_tmp (r := tmOldHead M.k j.val) (z := c.workTapePos j) hft
      (by unfold tmOldHead; omega) (Or.inr (by unfold tmOldHead; omega)) τ.mem
    have hf₂ := tmFrame_tmp (r := tmAddress M.k j.val)
      (z := (tmAddr sc M.k j (c.workTapePos j) : ℤ)) hf₁
      (by unfold tmAddress; omega) (Or.inr (by unfold tmAddress; omega)) τ.mem
    have hda : tmOldHead M.k j.val ≠ tmAddress M.k j.val := by
      simpa only [tmOldHead, tmAddress] using
        (tmLocal_ne (r := 3) (s := 2) (j := j) (l := j) (Or.inl (by decide)))
    have hfresh : F j ν := by
      simp only [F, ν, Function.update_self, Function.update_of_ne hda, true_and]
    refine ⟨⟨hf₂, hmt⟩, hfresh, ?_⟩
    intro l hl
    by_cases he : l = j
    · subst l
      exact hfresh
    · have hoo : tmOldHead M.k l.val ≠ tmOldHead M.k j.val := by
        simpa only [tmOldHead] using
          (tmLocal_ne (r := 3) (s := 3) (j := l) (l := j) (Or.inr he))
      have hoa : tmOldHead M.k l.val ≠ tmAddress M.k j.val := by
        simpa only [tmOldHead, tmAddress] using
          (tmLocal_ne (r := 3) (s := 2) (j := l) (l := j) (Or.inl (by decide)))
      have hao : tmAddress M.k l.val ≠ tmOldHead M.k j.val := by
        simpa only [tmOldHead, tmAddress] using
          (tmLocal_ne (r := 2) (s := 3) (j := l) (l := j) (Or.inl (by decide)))
      have haa : tmAddress M.k l.val ≠ tmAddress M.k j.val := by
        simpa only [tmAddress] using
          (tmLocal_ne (r := 2) (s := 2) (j := l) (l := j) (Or.inr he))
      dsimp only [F, ν] at hl ⊢
      simpa only [Function.update_of_ne hoo, Function.update_of_ne hoa,
        Function.update_of_ne hao, Function.update_of_ne haa] using hl
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k) ⟨hf, rfl⟩ hr
  apply hbank.mono
  rintro τ ⟨hI, hF, _⟩
  exact ⟨hI.1, hI.2, ⟨fun j => (hF j (List.mem_finRange j)).1,
    fun j => (hF j (List.mem_finRange j)).2⟩⟩

/-- Read the symbol at one previously computed work-tape address into its scan local. -/
private def tmReadTape (M : Turing.FinTM Bool) (j : Fin M.k) : Stmt :=
  .set (tmScan M.k j.val) (.load (.var (tmAddress M.k j.val)))

/-- Reading all work symbols preserves the frame, located data, input code, and memory.

**Proof sketch.** Use `tmSeq_accumulate` for the static tape list. Each load reads the address
from `TMLocated` and its value from the supplied memory encoding. `tmSet_runs` changes only the
corresponding scan local. `tmFrame_tmp`, `tmLocated_tmp`, and `tmLocal_ne` preserve the stable
and located data and all other established scan values. -/
private theorem tmScanBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hl : TMLocated M c sc σ)
    (hi : σ.loc 9 = (tmSym c.inputSymbol : ℤ))
    (hread : ∀ j : Fin M.k, σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ))
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmBank M (tmReadTape M)).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧ TMScanned M c τ ∧ τ.mem = σ.mem := by
  let I : State → Prop := fun τ => TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧
    τ.loc 9 = (tmSym c.inputSymbol : ℤ) ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmScan M.k j.val) = (tmSym (c.workTapeSymbols j) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmReadTape M j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hft, hlt, hit, hmt⟩
    have hs : (Expr.load (.var (tmAddress M.k j.val))).Safe lim τ := by
      rw [Expr.safe_load_iff, Expr.safe_var_iff, Expr.val_var, hlt.addresses j, Limits.addr_iff]
      exact ⟨trivial, Int.natCast_nonneg _, by exact_mod_cast hrange j⟩
    have hv : (Expr.load (.var (tmAddress M.k j.val))).val τ =
        (tmSym (c.workTapeSymbols j) : ℤ) := by
      rw [Expr.val_load, Expr.val_var, hlt.addresses j, Int.toNat_natCast, hmt, hread j]
    apply (tmSet_runs (dst := tmScan M.k j.val) hs hv).mono
    rintro ν rfl
    let ν : State := { τ with loc := Function.update τ.loc (tmScan M.k j.val) (tmSym (c.workTapeSymbols j) : ℤ) }
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hf' := tmFrame_tmp (r := tmScan M.k j.val)
      (z := (tmSym (c.workTapeSymbols j) : ℤ)) hft
      (by unfold tmScan; omega) (Or.inr (by unfold tmScan; omega)) τ.mem
    have hl' := tmLocated_tmp (r := tmScan M.k j.val)
      (z := (tmSym (c.workTapeSymbols j) : ℤ)) hlt
      (Or.inl (by have := j.isLt; unfold tmScan; omega)) τ.mem
    have hi' : ν.loc 9 = (tmSym c.inputSymbol : ℤ) := by
      change Function.update τ.loc (tmScan M.k j.val) (tmSym (c.workTapeSymbols j) : ℤ) 9 = _
      rw [Function.update_of_ne (by unfold tmScan; omega)]
      exact hit
    refine ⟨⟨hf', hl', hi', hmt⟩, ?_, ?_⟩
    · simp only [F, ν, Function.update_self]
    · intro l hlold
      by_cases he : l = j
      · subst l
        simp only [F, ν, Function.update_self]
      · have hne : tmScan M.k l.val ≠ tmScan M.k j.val := by
          simpa only [tmScan, Nat.one_mul] using
            (tmLocal_ne (r := 1) (s := 1) (j := l) (l := j) (Or.inr he))
        dsimp only [F, ν] at hlold ⊢
        simpa only [Function.update_of_ne hne] using hlold
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k)
    ⟨hf, hl, hi, rfl⟩ hr
  apply hbank.mono
  rintro τ ⟨⟨hft, hlt, hit, hmt⟩, hF, _⟩
  exact ⟨hft, hlt, ⟨hit, fun j => hF j (List.mem_finRange j)⟩, hmt⟩

/-- The zero-position test is safe and identifies exactly the left input end marker. -/
private theorem tmInputZeroTest {n : ℕ} {lim : Limits} {σ : State}
    (p : Fin (n + 2)) (hp : σ.loc 4 = (p.val : ℤ)) (h0 : (0 : ℤ) ≤ lim.word) :
    (Cond.eq (.var 4) (.const 0)).Safe lim σ ∧
      ((Cond.eq (.var 4) (.const 0)).Holds σ ↔ p = 0) := by
  constructor
  · rw [Cond.safe_eq_iff, Expr.safe_var_iff, Expr.safe_const_iff]
    exact ⟨trivial, h0⟩
  · rw [Cond.holds_eq_iff, Expr.val_var, Expr.val_const, hp, Nat.cast_zero]
    constructor
    · intro he
      exact Fin.val_eq_zero_iff.mp (by exact_mod_cast he)
    · intro he
      have hv := Fin.val_eq_zero_iff.mpr he
      exact_mod_cast hv

/-- The expression for the right input end marker is safe and has value `n + 1`. -/
private theorem tmInputEnd_read {n : ℕ} {lim : Limits} {σ : State}
    (hn : σ.loc 1 = (n : ℤ)) (hL : (n : ℤ) + 1 ≤ lim.word) :
    (Expr.op .add (.var 1) (.const 1)).Safe lim σ ∧
      (Expr.op .add (.var 1) (.const 1)).val σ = (n : ℤ) + 1 := by
  constructor
  · simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_var, Expr.val_const, Op.eval_add, hn, Nat.cast_one, true_and, abs_le]
    omega
  · rw [Expr.val_op, Op.eval_add, Expr.val_var, Expr.val_const, hn, Nat.cast_one]

/-- Read the input in place, encoding either end marker as blank. -/
private def tmReadInput : Stmt :=
  .ite (.eq (.var 4) (.const 0)) (.set 9 (.const 0))
    (.ite (.eq (.var 4) (.op .add (.var 1) (.const 1))) (.set 9 (.const 0))
      (.set 9 (.op .add
        (.load (.op .add (.var 0) (.op .sub (.var 4) (.const 1)))) (.const 1))))

/-- Reading the input changes only the scanned-input local, and returns the machine's actual
input symbol under the blank/bit encoding.

**Proof sketch.** The two end-marker branches use `Cfg.inputSymbol_of_zero` and
`Cfg.inputSymbol_of_end`. In the interior, `inputSymbolInner` identifies the bit at the
one-shifted head position. Its memory cell is inside the input region; loading its bit value
and adding one gives `tmSym_some_eq`. The word bounds control the address subtraction, address
addition, and final symbol code. -/
private theorem tmReadInput_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} (σ : State) (a : ℕ)
    (hsrc : σ.loc 0 = (a : ℤ)) (hlen : σ.loc 1 = (x.length : ℤ))
    (hpos : σ.loc 4 = (c.inputPos.val : ℤ))
    (hread : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2 : (2 : ℤ) ≤ lim.word) (hL : (x.length : ℤ) + 1 ≤ lim.word) :
    tmReadInput.Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 9 (tmSym c.inputSymbol : ℤ) } := by
  have hblank : (Stmt.set 9 (.const 0)).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 9 (0 : ℤ) } := by
    constructor
    · rw [Stmt.blockSafe_set_iff, Expr.safe_const_iff]
      omega
    · rw [Stmt.after_set, Expr.val_const, Nat.cast_zero]
  obtain ⟨hs0, hg0⟩ := tmInputZeroTest c.inputPos hpos (show (0 : ℤ) ≤ lim.word by omega)
  obtain ⟨hendsafe, hendval⟩ := tmInputEnd_read hlen hL
  have hgend : (Cond.eq (.var 4) (.op .add (.var 1) (.const 1))).Holds σ ↔
      c.inputPos.val = x.length + 1 := by
    rw [Cond.holds_eq_iff, Expr.val_var, hpos, hendval]
    constructor <;> intro he <;> exact_mod_cast he
  have hsend : (Cond.eq (.var 4) (.op .add (.var 1) (.const 1))).Safe lim σ :=
    (Cond.safe_eq_iff _ _ _ _).mpr ⟨(Expr.safe_var_iff _ _ _).mpr trivial, hendsafe⟩
  unfold tmReadInput
  by_cases hleft : c.inputPos = 0
  · apply Stmt.Runs.ite_pos ?_ (hg0.mpr hleft) hs0
    simpa only [Turing.Cfg.inputSymbol_of_zero hleft, tmSym, Nat.cast_zero] using hblank
  · apply Stmt.Runs.ite_neg ?_ (fun hh => hleft (hg0.mp hh)) hs0
    by_cases hend : c.inputPos.val = x.length + 1
    · apply Stmt.Runs.ite_pos ?_ (hgend.mpr hend) hsend
      simpa only [Turing.Cfg.inputSymbol_of_end hend, tmSym, Nat.cast_zero] using hblank
    · apply Stmt.Runs.ite_neg ?_ (fun hh => hend (hgend.mp hh)) hsend
      let u := c.inputPos.val - 1
      have hp0 : c.inputPos.val ≠ 0 := by
        intro he
        exact hleft (Fin.ext he)
      have hu : u < x.length := by
        have := c.inputPos.isLt
        dsimp only [u]
        omega
      have hpu : c.inputPos.val = 1 + u := by dsimp only [u]; omega
      have hsym : c.inputSymbol = some (x.getD u false) := by
        rw [Turing.inputSymbolInner u hpu hu, List.getD_eq_getElem _ _ hu]
      let ea : Expr := .op .add (.var 0) (.op .sub (.var 4) (.const 1))
      have hpuZ : (c.inputPos.val : ℤ) = 1 + (u : ℤ) := by exact_mod_cast hpu
      have haddrlt : a + u < lim.space := by omega
      have haddrZ : (a : ℤ) + (u : ℤ) < (lim.space : ℤ) := by exact_mod_cast haddrlt
      have hvaladdr : ea.val σ = ((a + u : ℕ) : ℤ) := by
        simp only [ea, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
          Op.eval_sub, hsrc, hpos, Nat.cast_one, Nat.cast_add]
        omega
      have hsafeaddr : ea.Safe lim σ := by
        simp only [ea, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
          Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_sub,
          hsrc, hpos, Nat.cast_one, true_and, abs_le]
        omega
      have hloadval : (Expr.load ea).val σ = ((x.getD u false).toNat : ℤ) := by
        rw [Expr.val_load, hvaladdr, Int.toNat_natCast, hread u hu]
      have hloadsafe : (Expr.load ea).Safe lim σ := by
        rw [Expr.safe_load_iff, hvaladdr, Limits.addr_iff]
        exact ⟨hsafeaddr, Int.natCast_nonneg _, by exact_mod_cast haddrlt⟩
      let e : Expr := .op .add (.load ea) (.const 1)
      have hv : e.val σ = (tmSym c.inputSymbol : ℤ) := by
        simp only [e, Expr.val_op, Op.eval_add, hloadval, Expr.val_const, Nat.cast_one,
          hsym, tmSym_some_eq, Nat.cast_add]
      have hsafe : e.Safe lim σ := by
        simp only [e, Expr.safe_op_iff, hloadsafe, Expr.safe_const_iff, hloadval,
          Expr.val_const, Op.eval_add, Nat.cast_one, true_and, abs_le]
        have hbit := Bool.toNat_le (x.getD u false)
        omega
      exact tmSet_runs hsafe hv

/-- The read-only preparation of a transition: locate the work heads and read all symbols. -/
private def tmPrepare (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmBank M (tmLocate M)) (.seq tmReadInput (tmBank M (tmReadTape M)))

/-- Transition preparation preserves memory and the stable frame and captures all addresses,
frozen heads, and scanned symbols.

**Proof sketch.** Compose `tmLocateBank_runs`, `tmReadInput_runs`, and `tmScanBank_runs`.
The input read changes only temporary local nine, which preserves both the frame and located
data by `tmFrame_tmp` and `tmLocated_tmp`. The two bank rules preserve memory, so the supplied
input and work-cell encodings remain valid throughout. -/
private theorem tmPrepare_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hin : a + x.length ≤ lim.space) (h2 : (2 : ℤ) ≤ lim.word)
    (hL : (x.length : ℤ) + 1 ≤ lim.word) (hk : (M.k : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (hinput : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hwork : ∀ j : Fin M.k, σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ))
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmPrepare M).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧ TMScanned M c τ ∧ τ.mem = σ.mem := by
  unfold tmPrepare
  apply Stmt.Runs.seq
  apply (tmLocateBank_runs M c σ hf hw h2 hk hc
    (fun j => by simpa only [tmAddr] using (hrange j).le)).mono
  rintro τ ⟨hft, hmt, hlt⟩
  apply Stmt.Runs.seq
  have hinputτ : ∀ u < x.length, τ.mem (a + u) = ((x.getD u false).toNat : ℤ) := by
    intro u hu
    rw [hmt]
    exact hinput u hu
  apply (tmReadInput_runs M c τ a hft.src hft.len hft.inputPos hinputτ hw hin h2 hL).mono
  rintro ν rfl
  let ν : State := { τ with loc := Function.update τ.loc 9 (tmSym c.inputSymbol : ℤ) }
  have hf' := tmFrame_tmp (r := 9) (z := (tmSym c.inputSymbol : ℤ)) hft
    (by decide) (Or.inl (by decide)) τ.mem
  have hl' := tmLocated_tmp (r := 9) (z := (tmSym c.inputSymbol : ℤ)) hlt
    (Or.inl (by omega)) τ.mem
  have hi' : ν.loc 9 = (tmSym c.inputSymbol : ℤ) := by
    change Function.update τ.loc 9 (tmSym c.inputSymbol : ℤ) 9 = _
    exact Function.update_self ..
  have hworkν : ∀ j : Fin M.k, ν.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ) := by
    intro j
    change τ.mem _ = _
    rw [hmt]
    exact hwork j
  apply (tmScanBank_runs M c ν hf' hl' hi' hworkν hrange).mono
  rintro ρ ⟨hfρ, hlρ, hsρ, hmρ⟩
  exact ⟨hfρ, hlρ, hsρ, hmρ.trans hmt⟩

/-- A fixed transition displacement applied to a frozen work-head local. -/
private def tmDisplace (src : ℕ) : SignType → Expr
  | .neg => .op .sub (.var src) (.const 1)
  | .zero => .var src
  | .pos => .op .add (.var src) (.const 1)

/-- A displacement expression is safe under its unit and result bounds and returns the
signed head position plus the transition displacement. -/
private theorem tmDisplace_read {lim : Limits} {σ : State} {src : ℕ} {z : ℤ} (m : SignType)
    (hz : σ.loc src = z) (h1 : (1 : ℤ) ≤ lim.word)
    (hm : |z + (m.cast : ℤ)| ≤ lim.word) :
    (tmDisplace src m).Safe lim σ ∧ (tmDisplace src m).val σ = z + (m.cast : ℤ) := by
  cases m <;>
    simp only [tmDisplace, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_sub, Op.eval_add, hz,
      Nat.cast_one, SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.coe_neg_one, SignType.coe_zero, SignType.coe_one, sub_eq_add_neg,
      add_zero, eq_self, true_and, and_true] at hm ⊢
  all_goals exact ⟨h1, hm⟩

/-- Move a work head from its frozen position. The frozen locals make all tape updates
independent, so the static bank implements simultaneous work-tape actions. -/
private def tmMoveWork (dst src : ℕ) (m : SignType) : Stmt :=
  .set dst (tmDisplace src m)

/-- A work-head update changes only its destination local and returns the prescribed signed
position; its expression safety is `tmDisplace_read`. -/
private theorem tmMoveWork_runs {lim : Limits} {σ : State} {dst src : ℕ} {z : ℤ}
    (m : SignType) (hz : σ.loc src = z) (h1 : (1 : ℤ) ≤ lim.word)
    (hm : |z + (m.cast : ℤ)| ≤ lim.word) :
    (tmMoveWork dst src m).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc dst (z + (m.cast : ℤ)) } := by
  obtain ⟨hs, hv⟩ := tmDisplace_read m hz h1 hm
  exact tmSet_runs hs hv

/-- Move the input head, clamping outward moves at the two end markers. -/
private def tmMoveInput : SignType → Stmt
  | .neg => .ite (.eq (.var 4) (.const 0)) .skip
      (.set 4 (.op .sub (.var 4) (.const 1)))
  | .zero => .skip
  | .pos => .ite (.lt (.var 4) (.op .add (.var 1) (.const 1)))
      (.set 4 (.op .add (.var 4) (.const 1))) .skip

/-- Input-head motion changes only its local and agrees with the machine's clamped movement.

**Proof sketch.** `tmInputZeroTest` handles the left boundary and `tmInputEnd_read` supplies
the right-boundary expression. A stationary or clamped move leaves the state unchanged.
The interior decrement and increment use `moveInputPos_neg_of_ne_left` and
`moveInputPos_pos_of_ne_right`, with the right-end bound controlling their arithmetic. -/
private theorem tmMoveInput_runs {n : ℕ} {lim : Limits} (σ : State) (p : Fin (n + 2))
    (m : SignType) (hp : σ.loc 4 = (p.val : ℤ)) (hn : σ.loc 1 = (n : ℤ))
    (hL : (n : ℤ) + 1 ≤ lim.word) :
    (tmMoveInput m).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 4 ((Turing.moveInputPos p m).val : ℤ) } := by
  have hskip (r : Fin (n + 2)) (he : r = p) : Stmt.skip.Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 4 (r.val : ℤ) } := by
    subst r
    constructor
    · exact (Stmt.blockSafe_skip_iff _ _).mpr trivial
    · rw [Stmt.after_skip, ← hp, Function.update_eq_self]
  cases m with
  | zero =>
    simpa only [tmMoveInput, SignType.zero_eq_zero, Turing.moveInputPos_zero] using hskip p rfl
  | neg =>
    obtain ⟨hs0, hg0⟩ := tmInputZeroTest p hp (show (0 : ℤ) ≤ lim.word by omega)
    unfold tmMoveInput
    by_cases hz : p = 0
    · have hm : Turing.moveInputPos p .neg = p := by
        rw [hz, SignType.neg_eq_neg_one, Turing.moveInputPos_leftBoundary]
      exact Stmt.Runs.ite_pos (hskip _ hm) (hg0.mpr hz) hs0
    · apply Stmt.Runs.ite_neg ?_ (fun hh => hz (hg0.mp hh)) hs0
      have hp0 : p.val ≠ 0 := fun hh => hz (Fin.val_eq_zero_iff.mp hh)
      have hplt := p.isLt
      constructor
      · simp only [Stmt.blockSafe_set_iff, Expr.safe_op_iff, Expr.safe_var_iff,
          Expr.safe_const_iff, Expr.val_var, Expr.val_const, Op.eval_sub,
          hp, Nat.cast_one, true_and, abs_le]
        omega
      · simp only [Stmt.after_set, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_sub,
          hp, Nat.cast_one, Turing.moveInputPos_neg_of_ne_left p hz]
        have he : (p.val : ℤ) - 1 = ((p.val - 1 : ℕ) : ℤ) := by omega
        rw [he]
  | pos =>
    obtain ⟨hendsafe, hendval⟩ := tmInputEnd_read hn hL
    have hg : (Cond.lt (.var 4) (.op .add (.var 1) (.const 1))).Holds σ ↔
        p.val < n + 1 := by
      rw [Cond.holds_lt_iff, Expr.val_var, hp, hendval]
      constructor <;> intro he <;> exact_mod_cast he
    have hs : (Cond.lt (.var 4) (.op .add (.var 1) (.const 1))).Safe lim σ :=
      (Cond.safe_lt_iff _ _ _ _).mpr ⟨(Expr.safe_var_iff _ _ _).mpr trivial, hendsafe⟩
    have hplt := p.isLt
    unfold tmMoveInput
    by_cases hi : p.val < n + 1
    · apply Stmt.Runs.ite_pos ?_ (hg.mpr hi) hs
      have hne : p.val ≠ n + 1 := by omega
      constructor
      · simp only [Stmt.blockSafe_set_iff, Expr.safe_op_iff, Expr.safe_var_iff,
          Expr.safe_const_iff, Expr.val_var, Expr.val_const, Op.eval_add,
          hp, Nat.cast_one, true_and, abs_le]
        omega
      · simp only [Stmt.after_set, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
          hp, Turing.moveInputPos_pos_of_ne_right p hne, Nat.cast_add, Nat.cast_one]
    · have he : p = (⟨n + 1, by omega⟩ : Fin (n + 2)) :=
        Fin.ext (show p.val = n + 1 from by omega)
      have hm : Turing.moveInputPos p .pos = p := by
        rw [he, SignType.pos_eq_one, Turing.moveInputPos_rightBoundary]
      exact Stmt.Runs.ite_neg (hskip _ hm) (fun hh => hi (hg.mp hh)) hs

/-- One tape's transition writes the chosen symbol, or writes back the scanned symbol when
there is no write, then moves the head. -/
private def tmWriteMove (M : Turing.FinTM Bool) (action : Turing.Action M.k Bool M.State)
    (j : Fin M.k) : Stmt :=
  .seq (.store (.var (tmAddress M.k j.val))
    (match (action.workTapes j).1 with
      | none => .var (tmScan M.k j.val)
      | some sym => .const (tmSym sym)))
    (tmMoveWork (tmHead j.val) (tmOldHead M.k j.val) (action.workTapes j).2)

/-- One tape's write and head movement have the normalized optional-write effect used by
`Action.apply_workTapes` and change only that tape cell and head local.

**Proof sketch.** Choose the stored symbol from the optional write, defaulting to the captured
scanned symbol. Its expression is either a scan local or a bounded symbol constant.
`tmStore_runs` writes it to the frozen address. The store preserves locals, so
`tmMoveWork_runs` then reads the frozen head and establishes the prescribed displacement. -/
private theorem tmWriteMove_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} (σ : State) (sc : ℕ) (j : Fin M.k)
    (hl : TMLocated M c sc σ) (hs : TMScanned M c σ) (h2 : (2 : ℤ) ≤ lim.word)
    (hm : |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (ha : tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmWriteMove M action j).Runs lim σ fun τ =>
      τ = ⟨Function.update σ.loc (tmHead j.val) (c.workTapePos j + ((action.workTapes j).2.cast : ℤ)),
        Function.update σ.mem (tmAddr sc M.k j (c.workTapePos j))
          (tmSym ((action.workTapes j).1.getD (c.workTapeSymbols j)) : ℤ)⟩ := by
  let e : Expr := match (action.workTapes j).1 with
    | none => .var (tmScan M.k j.val)
    | some sym => .const (tmSym sym)
  let w := (action.workTapes j).1.getD (c.workTapeSymbols j)
  have he : e.Safe lim σ ∧ e.val σ = (tmSym w : ℤ) := by
    cases hwrite : (action.workTapes j).1 with
    | none =>
      simp only [e, w, hwrite, Option.getD_none]
      exact ⟨(Expr.safe_var_iff _ _ _).mpr trivial,
        (Expr.val_var _ _).trans (hs.work j)⟩
    | some sym =>
      simp only [e, w, hwrite, Option.getD_some]
      refine ⟨(Expr.safe_const_iff _ _ _).mpr ?_, Expr.val_const _ _⟩
      have hsym := tmSym_le_two sym
      omega
  have haddr : (Expr.var (tmAddress M.k j.val)).val σ =
      (tmAddr sc M.k j (c.workTapePos j) : ℤ) :=
    (Expr.val_var _ _).trans (hl.addresses j)
  unfold tmWriteMove
  apply Stmt.Runs.seq
  apply (tmStore_runs ((Expr.safe_var_iff _ _ _).mpr trivial) he.1 haddr he.2 ha).mono
  rintro τ rfl
  let σ₁ : State := { σ with mem := Function.update σ.mem (tmAddr sc M.k j (c.workTapePos j)) (tmSym w : ℤ) }
  have hh : σ₁.loc (tmOldHead M.k j.val) = c.workTapePos j := hl.oldHeads j
  simpa only [σ₁, w] using
    (tmMoveWork_runs (dst := tmHead j.val) (src := tmOldHead M.k j.val)
      (action.workTapes j).2 hh (show (1 : ℤ) ≤ lim.word by omega) hm)

/-- The complete tape-action bank preserves the eight scalar locals and old output, updates
all heads and represented tape cells as the action prescribes, and keeps the external memory.

**Proof sketch.** `tmSeq_accumulate` visits the tape bank. Its invariant keeps the scalar,
located, and scanned locals, all tape cells away from old heads, the output segment, and the
external-memory promise. `tmWriteMove_runs` gives each exact store/head update. The store
preserves away cells by `tmTapesAway_write`, output by `Seg.update_out`, and external memory by
`SameOutside2.update`. For the visited tape, `Action.apply_workTapes` and
`Action.apply_workTapePos` identify the full new tape and head. `tmAddr_injective` and
`tmLocal_ne` preserve the properties already established for different tapes. -/
private theorem tmWriteBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} {b sc radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hl : TMLocated M c sc σ) (hs : TMScanned M c σ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits c.output))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen) (h2 : (2 : ℤ) ≤ lim.word)
    (hm : ∀ j : Fin M.k, |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space)
    (hinside : ∀ j : Fin M.k, Inside sc scratchLen (tmAddr sc M.k j (c.workTapePos j)))
    (houtside : ∀ j : Fin M.k, Outside b c.output.length (tmAddr sc M.k j (c.workTapePos j))) :
    (tmBank M (tmWriteMove M action)).Runs lim σ fun τ =>
      (∀ v < 8, τ.loc v = σ.loc v) ∧
      (∀ j : Fin M.k, τ.loc (tmHead j.val) = (action.apply c).workTapePos j) ∧
      TMTapes M (action.apply c) sc radius τ.mem ∧ Seg τ.mem b (tmBits c.output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  let I : State → Prop := fun τ => (∀ v < 8, τ.loc v = σ.loc v) ∧
    TMLocated M c sc τ ∧ TMScanned M c τ ∧ TMTapesAway M c sc radius τ.mem ∧
    Seg τ.mem b (tmBits c.output) ∧ SameOutside2 μ₀ τ.mem b outLen sc scratchLen
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmHead j.val) = (action.apply c).workTapePos j ∧
    ∀ z : ℤ, |z| < (radius : ℤ) →
      τ.mem (tmAddr sc M.k j z) = (tmSym ((action.apply c).workTapes j z) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmWriteMove M action j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hscalar, hlt, hst, haway, houtτ, hkeepτ⟩
    apply (tmWriteMove_runs M c action τ sc j hlt hst h2 (hm j) (hrange j)).mono
    rintro ν rfl
    let addr := tmAddr sc M.k j (c.workTapePos j)
    let value : ℤ := tmSym ((action.workTapes j).1.getD (c.workTapeSymbols j))
    let pos : ℤ := c.workTapePos j + ((action.workTapes j).2.cast : ℤ)
    let ν : State := ⟨Function.update τ.loc (tmHead j.val) pos, Function.update τ.mem addr value⟩
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hscalar' : ∀ v < 8, ν.loc v = σ.loc v := by
      intro v hv
      change Function.update τ.loc (tmHead j.val) pos v = _
      rw [Function.update_of_ne (by unfold tmHead; omega)]
      exact hscalar v hv
    have hl' := tmLocated_tmp (r := tmHead j.val) (z := pos) hlt
      (Or.inl (by have := j.isLt; unfold tmHead; omega)) (Function.update τ.mem addr value)
    have hs' := tmScanned_tmp (r := tmHead j.val) (z := pos) hst
      (by unfold tmHead; omega) (Or.inl (by have := j.isLt; unfold tmHead; omega))
      (Function.update τ.mem addr value)
    have haway' := tmTapesAway_write j haway value
    have hout' := Seg.update_out houtτ
      (show addr < b ∨ b + (tmBits c.output).length ≤ addr from by
        simpa only [tmBits, List.length_map] using houtside j) value
    have hkeep' := SameOutside2.update hkeepτ (Or.inr (hinside j)) value
    have hI : I ν := ⟨hscalar', hl', hs', haway', hout', hkeep'⟩
    have hfresh : F j ν := by
      constructor
      · change Function.update τ.loc (tmHead j.val) pos (tmHead j.val) = _
        rw [Function.update_self, Turing.Action.apply_workTapePos]
      · intro z hz
        rw [Turing.Action.apply_workTapes]
        by_cases he : z = c.workTapePos j
        · subst z
          change Function.update τ.mem addr value addr =
            (tmSym (Function.update (c.workTapes j) (c.workTapePos j)
              ((action.workTapes j).1.getD (c.workTapeSymbols j)) (c.workTapePos j)) : ℤ)
          rw [Function.update_self, Function.update_self]
        · have haddr : tmAddr sc M.k j z ≠ addr := by
            intro heq
            exact he (tmAddr_injective heq).2
          change Function.update τ.mem addr value (tmAddr sc M.k j z) =
            (tmSym (Function.update (c.workTapes j) (c.workTapePos j)
              ((action.workTapes j).1.getD (c.workTapeSymbols j)) z) : ℤ)
          rw [Function.update_of_ne haddr, Function.update_of_ne he]
          exact haway j z hz he
    refine ⟨hI, hfresh, ?_⟩
    intro l hlold
    by_cases he : l = j
    · subst l
      exact hfresh
    · constructor
      · have hhead : tmHead l.val ≠ tmHead j.val := by
          simpa only [tmHead, Nat.zero_mul, Nat.add_zero] using
            (tmLocal_ne (r := 0) (s := 0) (j := l) (l := j) (Or.inr he))
        change Function.update τ.loc (tmHead j.val) pos (tmHead l.val) = _
        rw [Function.update_of_ne hhead]
        exact hlold.1
      · intro z hz
        have haddr : tmAddr sc M.k l z ≠ addr := by
          intro heq
          exact he (tmAddr_injective heq).1
        change Function.update τ.mem addr value (tmAddr sc M.k l z) = _
        rw [Function.update_of_ne haddr]
        exact hlold.2 z hz
  have hI : I σ := ⟨fun _ _ => rfl, hl, hs, fun j z hz _ => ht j z hz, hout, hkeep⟩
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k) hI hr
  apply hbank.mono
  rintro τ ⟨⟨hscalar, _, _, _, houtτ, hkeepτ⟩, hF, _⟩
  refine ⟨hscalar, fun j => (hF j (List.mem_finRange j)).1, ?_, houtτ, hkeepτ⟩
  intro j z hz
  exact (hF j (List.mem_finRange j)).2 z hz

/-- Append the optional output bit and advance the output length. -/
private def tmEmit : Option Bool → Stmt
  | none => .skip
  | some bit => .seq (.store (.op .add (.var 2) (.var 6)) (.const bit.toNat))
      (.set 6 (.op .add (.var 6) (.const 1)))

/-- The exact state after an optional output emission. -/
private def tmEmitState (σ : State) (b o : ℕ) : Option Bool → State
  | none => σ
  | some bit => ⟨Function.update σ.loc 6 ((o + 1 : ℕ) : ℤ),
      Function.update σ.mem (b + o) (bit.toNat : ℤ)⟩

/-- The output cursor is the only local changed by emission, with absent emission leaving
its existing value unchanged. -/
private theorem tmEmitState_locals (σ : State) (b o : ℕ) (v : Option Bool)
    (ho : σ.loc 6 = (o : ℤ)) :
    (tmEmitState σ b o v).loc = Function.update σ.loc 6 ((o + v.toList.length : ℕ) : ℤ) := by
  cases v with
  | none =>
    simp only [tmEmitState, Option.toList_none, List.length_nil, Nat.add_zero]
    rw [← ho, Function.update_eq_self]
  | some bit =>
    simp only [tmEmitState, Option.toList_some, List.length_singleton]

/-- Emission extends the output segment and keeps represented work tapes and external memory
when the final output region is apart from scratch.

**Proof sketch.** No emission changes no memory. For a bit, its cursor lies inside the final
output region. Every represented work cell lies in scratch, so `Apart` separates it from that
cursor and `Function.update_of_ne` preserves its encoding. `Seg.snoc` extends the bit segment,
and `SameOutside2.update` preserves memory outside the two allowed regions. -/
private theorem tmEmitState_data (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (σ : State) (bits : List Bool)
    (b sc radius outLen scratchLen : ℕ) (v : Option Bool) (μ₀ : ℕ → ℤ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits bits))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hbound : bits.length + v.toList.length ≤ outLen) (hsep : Apart b outLen sc scratchLen)
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z)) :
    TMTapes M c sc radius (tmEmitState σ b bits.length v).mem ∧
      Seg (tmEmitState σ b bits.length v).mem b (tmBits (bits ++ v.toList)) ∧
      SameOutside2 μ₀ (tmEmitState σ b bits.length v).mem b outLen sc scratchLen := by
  cases v with
  | none =>
    simpa only [tmEmitState, Option.toList_none, List.append_nil] using ⟨ht, hout, hkeep⟩
  | some bit =>
    have hb : bits.length + 1 ≤ outLen := by
      simpa only [Option.toList_some, List.length_singleton] using hbound
    refine ⟨?_, ?_, ?_⟩
    · intro j z hz
      have hcell := hinside j z hz
      have hne : tmAddr sc M.k j z ≠ b + bits.length := by
        rcases hcell with ⟨hlo, hhi⟩
        rcases hsep with hsep | hsep <;> omega
      change Function.update σ.mem (b + bits.length) (bit.toNat : ℤ) (tmAddr sc M.k j z) = _
      rw [Function.update_of_ne hne]
      exact ht j z hz
    · simpa only [tmEmitState, tmBits, List.length_map, Option.toList_some,
        List.map_append, List.map_cons, List.map_nil] using hout.snoc (bit.toNat : ℤ)
    · exact SameOutside2.update hkeep
        (Or.inl ⟨by omega, by omega⟩) (bit.toNat : ℤ)

/-- Output emission appends the optional bit at the output cursor, advances its length,
and leaves every other local and memory cell unchanged.

**Proof sketch.** The absent-bit branch is `skip`. In the present-bit branch, `tmStore_runs`
writes the bounded bit at the in-range output cursor. Its exact state keeps the length local
unchanged, so `tmSet_runs` increments that local safely. The two exact updates are
`tmEmitState`. -/
private theorem tmEmit_runs {lim : Limits} (σ : State) (b o : ℕ) (v : Option Bool)
    (hb : σ.loc 2 = (b : ℤ)) (ho : σ.loc 6 = (o : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hs : b + o + v.toList.length ≤ lim.space) :
    (tmEmit v).Runs lim σ fun τ => τ = tmEmitState σ b o v := by
  cases v with
  | none =>
    exact ⟨(Stmt.blockSafe_skip_iff _ _).mpr trivial, Stmt.after_skip _⟩
  | some bit =>
    have hs1 : b + o + 1 ≤ lim.space := by
      simpa only [Option.toList_some, List.length_singleton] using hs
    have hsZ : (b : ℤ) + (o : ℤ) + 1 ≤ (lim.space : ℤ) := by exact_mod_cast hs1
    have haddrlt : b + o < lim.space := by omega
    let ea : Expr := .op .add (.var 2) (.var 6)
    have hvaladdr : ea.val σ = ((b + o : ℕ) : ℤ) := by
      simp only [ea, Expr.val_op, Expr.val_var, Op.eval_add, hb, ho, Nat.cast_add]
    have hsafeaddr : ea.Safe lim σ := by
      simp only [ea, Expr.safe_op_iff, Expr.safe_var_iff, Expr.val_var, Op.eval_add,
        hb, ho, true_and, abs_le]
      omega
    have hbit := Bool.toNat_le bit
    have hsafebit : (Expr.const bit.toNat).Safe lim σ :=
      (Expr.safe_const_iff _ _ _).mpr (by omega)
    unfold tmEmit
    apply Stmt.Runs.seq
    apply (tmStore_runs hsafeaddr hsafebit hvaladdr (Expr.val_const _ _) haddrlt).mono
    rintro τ rfl
    let σ₁ : State := { σ with mem := Function.update σ.mem (b + o) (bit.toNat : ℤ) }
    have ho₁ : σ₁.loc 6 = (o : ℤ) := ho
    have hsafe : (Expr.op .add (.var 6) (.const 1)).Safe lim σ₁ := by
      simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff, Expr.val_var,
        Expr.val_const, Op.eval_add, ho₁, Nat.cast_one, true_and, abs_le]
      omega
    have hv : (Expr.op .add (.var 6) (.const 1)).val σ₁ = ((o + 1 : ℕ) : ℤ) := by
      simp only [Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, ho₁,
        Nat.cast_add, Nat.cast_one]
    simpa only [tmEmitState, σ₁] using (tmSet_runs (dst := 6) hsafe hv)

/-- Finish a transition after the work-tape bank: move the input head, emit output, and
install the next control state, as an exact-state description. -/
private noncomputable def tmFinishState (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    (b : ℕ) (σ : State) : State :=
  let moved : State := { σ with loc := Function.update σ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  let emitted := tmEmitState moved b c.output.length action.output
  { emitted with loc := Function.update emitted.loc 5 (tmStateCode M action.state : ℤ) }

/-- Finishing the scalar updates after a correct tape bank gives the complete next frame.

**Proof sketch.** `tmEmitState_locals` expresses both output cases by one cursor update.
The resulting locals are three updates of the bank's locals, at input position four, output
length six, and control state five. The other scalar locals and every head are preserved.
The published field equations `Action.apply_inputPos`, `apply_output`, and `apply_state`
identify the three new frame fields. -/
private theorem tmFinishState_frame (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {a b sc i : ℕ} (σ ρ : State) (hf : TMFrame M c a b sc i σ)
    (he : ∀ v < 8, ρ.loc v = σ.loc v)
    (hh : ∀ j : Fin M.k, ρ.loc (tmHead j.val) = (action.apply c).workTapePos j) :
    TMFrame M (action.apply c) a b sc i (tmFinishState M c action b ρ) := by
  let moved : State := { ρ with loc := Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  have ho : moved.loc 6 = (c.output.length : ℤ) := by
    change Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) 6 = _
    rw [Function.update_of_ne (by decide : (6 : ℕ) ≠ 4)]
    exact (he 6 (by decide)).trans hf.outputLen
  have hl : (tmFinishState M c action b ρ).loc =
      Function.update (Function.update (Function.update ρ.loc 4
        ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ)) 6
          ((c.output.length + action.output.toList.length : ℕ) : ℤ)) 5
            (tmStateCode M action.state : ℤ) := by
    change Function.update (tmEmitState moved b c.output.length action.output).loc 5
      (tmStateCode M action.state : ℤ) = _
    rw [tmEmitState_locals moved b c.output.length action.output ho]
  have hsame (v : ℕ) (hne : v ≠ 4 ∧ v ≠ 5 ∧ v ≠ 6) :
      (tmFinishState M c action b ρ).loc v = ρ.loc v := by
    rw [hl, Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2,
      Function.update_of_ne hne.1]
  have hscalar (v : ℕ) (hv : v < 4 ∨ v = 7) :
      (tmFinishState M c action b ρ).loc v = σ.loc v :=
    (hsame v (by omega)).trans (he v (by omega))
  constructor
  · exact (hscalar 0 (by decide)).trans hf.src
  · exact (hscalar 1 (by decide)).trans hf.len
  · exact (hscalar 2 (by decide)).trans hf.dst
  · exact (hscalar 3 (by decide)).trans hf.scratch
  · rw [hl, Function.update_of_ne (by decide : (4 : ℕ) ≠ 5),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self,
      Turing.Action.apply_inputPos]
  · rw [hl, Function.update_self, Turing.Action.apply_state]
  · rw [hl, Function.update_of_ne (by decide : (6 : ℕ) ≠ 5), Function.update_self,
      Turing.Action.apply_output, List.length_append]
  · exact (hscalar 7 (by decide)).trans hf.round
  · intro j
    exact (hsame (tmHead j.val) (by unfold tmHead; omega)).trans (hh j)

/-- The executable block for one fixed action. -/
private noncomputable def tmActionBody (M : Turing.FinTM Bool)
    (action : Turing.Action M.k Bool M.State) : Stmt :=
  .seq (tmBank M (tmWriteMove M action)) (.seq (tmMoveInput action.inputTape)
    (.seq (tmEmit action.output) (.set 5 (.const (tmStateCode M action.state)))))

/-- A fixed transition action updates the complete configuration representation, output, and
external-memory promise within the supplied word and region bounds.

**Proof sketch.** Run `tmWriteBank_runs`, then the verified input motion and emission blocks.
The tape bank preserves all scalar arguments needed by those two blocks. `tmEmitState_data`
preserves the new work tapes, appends output, and keeps external memory. Assign the bounded
next-state code; `tmFinishState_frame` identifies the resulting complete frame. -/
private theorem tmActionBody_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} {a b sc i radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hf : TMFrame M c a b sc i σ) (hl : TMLocated M c sc σ) (hs : TMScanned M c σ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits c.output))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hw : (lim.space : ℤ) ≤ lim.word) (h2 : (2 : ℤ) ≤ lim.word)
    (hL : (x.length : ℤ) + 1 ≤ lim.word) (hc : (tmStateCode M action.state : ℤ) ≤ lim.word)
    (hm : ∀ j : Fin M.k, |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hhead : ∀ j : Fin M.k, |c.workTapePos j| < (radius : ℤ))
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z))
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsep : Apart b outLen sc scratchLen)
    (hprefix : c.output.length + action.output.toList.length ≤ outLen) :
    (tmActionBody M action).Runs lim σ fun τ =>
      TMFrame M (action.apply c) a b sc i τ ∧ TMTapes M (action.apply c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits (action.apply c).output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  have hinsideHead (j : Fin M.k) := hinside j (c.workTapePos j) (hhead j)
  have hrange (j : Fin M.k) : tmAddr sc M.k j (c.workTapePos j) < lim.space := by
    have hcell := hinsideHead j
    omega
  have houtside (j : Fin M.k) : Outside b c.output.length (tmAddr sc M.k j (c.workTapePos j)) := by
    have hcell := hinsideHead j
    rcases hsep with hsep | hsep <;> omega
  unfold tmActionBody
  apply Stmt.Runs.seq
  apply (tmWriteBank_runs M c action σ μ₀ hl hs ht hout hkeep h2 hm hrange
    hinsideHead houtside).mono
  rintro ρ ⟨hscalar, hheads, htρ, houtρ, hkeepρ⟩
  apply Stmt.Runs.seq
  have hpρ : ρ.loc 4 = (c.inputPos.val : ℤ) := (hscalar 4 (by decide)).trans hf.inputPos
  have hnρ : ρ.loc 1 = (x.length : ℤ) := (hscalar 1 (by decide)).trans hf.len
  apply (tmMoveInput_runs ρ c.inputPos action.inputTape hpρ hnρ hL).mono
  rintro σ₁ rfl
  let σ₁ : State := { ρ with loc := Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  have hmoved (v : ℕ) (hv : v < 8) (hne : v ≠ 4) : σ₁.loc v = σ.loc v := by
    change Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) v = _
    rw [Function.update_of_ne hne]
    exact hscalar v hv
  have hb₁ : σ₁.loc 2 = (b : ℤ) := (hmoved 2 (by decide) (by decide)).trans hf.dst
  have ho₁ : σ₁.loc 6 = (c.output.length : ℤ) :=
    (hmoved 6 (by decide) (by decide)).trans hf.outputLen
  apply Stmt.Runs.seq
  apply (tmEmit_runs σ₁ b c.output.length action.output hb₁ ho₁ hw
    (show (1 : ℤ) ≤ lim.word by omega) (show b + c.output.length + action.output.toList.length ≤ lim.space by omega)).mono
  rintro σ₂ rfl
  let σ₂ := tmEmitState σ₁ b c.output.length action.output
  have hdata := tmEmitState_data M (action.apply c) σ₁ c.output b sc radius outLen scratchLen
    action.output μ₀ htρ houtρ hkeepρ hprefix hsep hinside
  have hsafe : (Expr.const (tmStateCode M action.state)).Safe lim σ₂ :=
    (Expr.safe_const_iff _ _ _).mpr hc
  apply (tmSet_runs (dst := 5) hsafe (Expr.val_const _ _)).mono
  rintro σ₃ rfl
  refine ⟨tmFinishState_frame M c action σ ρ hf hscalar hheads, hdata.1, ?_, hdata.2.2⟩
  rw [Turing.Action.apply_output]
  exact hdata.2.1

/-- The block implementing one fixed row of the machine's transition function. -/
private noncomputable def tmRowBody (M : Turing.FinTM Bool) (row : TMRow M) : Stmt :=
  tmActionBody M (M.tm.tr row.1 row.2.1 row.2.2)

/-- The local-value tests identifying a transition row. -/
private noncomputable def tmRowTests (M : Turing.FinTM Bool) (row : TMRow M) : List (ℕ × ℕ) :=
  (5, tmStateCode M (some row.1)) :: (9, tmSym row.2.1) ::
    (List.finRange M.k).map (fun j => (tmScan M.k j.val, tmSym (row.2.2 j)))

/-- Reading a row's tests gives exactly its control state and scanned symbols. -/
private theorem tmRowTests_matches_iff (M : Turing.FinTM Bool) (row : TMRow M) (σ : State) :
    tmMatches (tmRowTests M row) σ ↔
      σ.loc 5 = (tmStateCode M (some row.1) : ℤ) ∧
      σ.loc 9 = (tmSym row.2.1 : ℤ) ∧
      ∀ j : Fin M.k, σ.loc (tmScan M.k j.val) = (tmSym (row.2.2 j) : ℤ) := by
  simp only [tmMatches, tmRowTests, List.forall_mem_cons, List.forall_mem_map,
    List.mem_finRange, forall_true_left]

/-- If the scanned locals encode `actual`, a row's tests succeed exactly for that row. -/
private theorem tmRowTests_unique (M : Turing.FinTM Bool) (actual row : TMRow M) (σ : State)
    (ha : tmMatches (tmRowTests M actual) σ) :
    tmMatches (tmRowTests M row) σ ↔ row = actual := by
  constructor
  · intro hr
    obtain ⟨haq, hai, haw⟩ := (tmRowTests_matches_iff M actual σ).mp ha
    obtain ⟨hrq, hri, hrw⟩ := (tmRowTests_matches_iff M row σ).mp hr
    have hq : some row.1 = some actual.1 :=
      tmStateCode_injective M (by exact_mod_cast hrq.symm.trans haq)
    have hi : row.2.1 = actual.2.1 :=
      tmSym_injective (by exact_mod_cast hri.symm.trans hai)
    have hw : row.2.2 = actual.2.2 := by
      funext j
      exact tmSym_injective (by exact_mod_cast (hrw j).symm.trans (haw j))
    exact Prod.ext (Option.some.inj hq) (Prod.ext hi hw)
  · intro he
    subst row
    exact ha

/-- The block after scratch initialization: read the old configuration, execute its
transition row, and advance the round count. -/
private noncomputable def tmTail (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmPrepare M) (.seq (tmDispatch (tmRowTests M) (tmRowBody M) (tmRows M))
    (.set 7 (.op .add (.var 7) (.const 1))))

/-- The transition selected by a live configuration. -/
private def tmAction (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (q : M.State) : Turing.Action M.k Bool M.State :=
  M.tm.tr q c.inputSymbol c.workTapeSymbols

/-- Reading a live configuration, selecting its row, and advancing the counter simulates
exactly one machine step under the given word and region bounds.

**Proof sketch.** `tmPrepare_runs` freezes the old heads and reads the scanned symbols without
changing memory. The row for the live state and those symbols belongs to `tmRows`, and
`tmRowTests_unique` excludes every other row. Apply `tmDispatch_runs` with
`tmActionBody_runs` as its selected-row rule. The last assignment advances only the round
counter, so `tmFrame_round` gives the next complete frame. -/
private theorem tmTail_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (q : M.State) (hq : c.state = some q)
    {lim : Limits} {a b sc i radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hf : TMFrame M c a b sc i σ) (ht : TMTapes M c sc radius σ.mem)
    (hout : Seg σ.mem b (tmBits c.output)) (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2 : (2 : ℤ) ≤ lim.word) (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hk : (M.k : ℤ) ≤ lim.word) (hi : (i : ℤ) + 1 ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (hinput : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hm : ∀ j : Fin M.k,
      |c.workTapePos j + (((tmAction M c q).workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hhead : ∀ j : Fin M.k, |c.workTapePos j| < (radius : ℤ))
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z))
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsep : Apart b outLen sc scratchLen)
    (hprefix : c.output.length + (tmAction M c q).output.toList.length ≤ outLen) :
    (tmTail M).Runs lim σ fun τ =>
      TMFrame M (M.tm.step c) a b sc (i + 1) τ ∧ TMTapes M (M.tm.step c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits (M.tm.step c).output) ∧ SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  classical
  have hstep : M.tm.step c = (tmAction M c q).apply c := Turing.MultiTapeTM.step_of_some hq
  rw [hstep]
  have hrange (j : Fin M.k) : tmAddr sc M.k j (c.workTapePos j) < lim.space := by
    have hcell := hinside j (c.workTapePos j) (hhead j)
    omega
  have hwork (j : Fin M.k) : σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ) := by
    rw [Turing.Cfg.workTapeSymbols_eq]
    exact ht j (c.workTapePos j) (hhead j)
  unfold tmTail
  apply Stmt.Runs.seq
  apply (tmPrepare_runs M c σ hf hw hin h2 hL hk hc hinput hwork hrange).mono
  rintro ρ ⟨hfρ, hlρ, hsρ, hmem⟩
  apply Stmt.Runs.seq
  let actual : TMRow M := (q, c.inputSymbol, c.workTapeSymbols)
  have hactual : tmMatches (tmRowTests M actual) ρ := by
    apply (tmRowTests_matches_iff M actual ρ).mpr
    exact ⟨by simpa only [hq] using hfρ.control, hsρ.input, hsρ.work⟩
  have htests (row : TMRow M) (_ : row ∈ tmRows M) :
      ∀ pair ∈ tmRowTests M row, (pair.2 : ℤ) ≤ lim.word := by
    simp only [tmRowTests, List.forall_mem_cons, List.forall_mem_map,
      List.mem_finRange, forall_true_left]
    refine ⟨hstates _, ?_, fun j => ?_⟩
    · have := tmSym_le_two row.2.1
      omega
    · have := tmSym_le_two (row.2.2 j)
      omega
  have hrow : (tmRowBody M actual).Runs lim ρ fun τ =>
      TMFrame M ((tmAction M c q).apply c) a b sc i τ ∧
      TMTapes M ((tmAction M c q).apply c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits ((tmAction M c q).apply c).output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen :=
    tmActionBody_runs M c (tmAction M c q) ρ μ₀ hfρ hlρ hsρ
      (by rw [hmem]; exact ht) (by rw [hmem]; exact hout) (by rw [hmem]; exact hkeep)
      hw h2 hL (hstates _) hm hhead hinside hscratch hspace hsep hprefix
  apply (tmDispatch_runs (actual := actual)
    (show actual ∈ tmRows M from Finset.mem_toList.mpr (Finset.mem_univ actual)) htests
    (fun row _ => tmRowTests_unique M actual row ρ hactual) hrow).mono
  rintro ν ⟨hfν, htν, houtν, hkeepν⟩
  have hsafe : (Expr.op .add (.var 7) (.const 1)).Safe lim ν := by
    simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_var, Expr.val_const, Op.eval_add, hfν.round, Nat.cast_one, true_and]
    exact ⟨by omega, by rw [abs_of_nonneg (by positivity)]; exact hi⟩
  have hval : (Expr.op .add (.var 7) (.const 1)).val ν = ((i + 1 : ℕ) : ℤ) := by
    rw [Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, hfν.round, Nat.cast_add,
      Nat.cast_one]
  apply (tmSet_runs (dst := 7) hsafe hval).mono
  rintro τ rfl
  exact ⟨tmFrame_round hfν (i + 1), htν, houtν, hkeepν⟩

/-- One simulator round initializes its newly reachable cells, then executes the transition. -/
private noncomputable def tmRound (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmClearRing M) (tmTail M)

/-! ## Private bounded-run invariant -/

/-- Before round `i`, the stable frame, initialized work cells, output prefix, and untouched
external memory encode the machine after exactly `i` steps. -/
private structure TMRunInv (M : Turing.FinTM Bool) (x : List Bool)
    (a b sc outLen scratchLen : ℕ) (μ₀ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop where
  frame : TMFrame M (M.tm.runFrom (M.tm.initCfg x) i) a b sc i σ
  tapes : TMTapes M (M.tm.runFrom (M.tm.initCfg x) i) sc i σ.mem
  output : Seg σ.mem b (tmBits (M.tm.runFrom (M.tm.initCfg x) i).output)
  keep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen

/-- A simulator round preserves the run invariant when its next initialized ring and all
intermediate words fit the supplied limits.

**Proof sketch.** `tmClearRing_ends` changes only the initialization temporaries and the next
scratch ring. Its `SameOutside` contract preserves the output and composes with the external
memory promise. `tmRingMemory_tapes` extends the represented tapes to radius `i + 1`.
The unchanged-memory promise and region separation recover the input words. Head envelopes
bound cell codes and next head values. `tmTail_runs` then performs the live step; the published
successor-run equation identifies its result with round `i + 1`. -/
private theorem tmRound_ends (M : Turing.FinTM Bool) (x : List Bool)
    {lim : Limits} {P : Program} {d a b sc outLen scratchLen i : ℕ}
    (σ : State) (μ₀ : ℕ → ℤ) (hI : TMRunInv M x a b sc outLen scratchLen μ₀ i σ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2i : (2 : ℤ) * ((i : ℤ) + 1) ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hring : 2 * (i + 1) * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsepIO : Apart a x.length b outLen) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b outLen sc scratchLen)
    (hinput : ∀ u < x.length, μ₀ (a + u) = ((x.getD u false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hlive : (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none)
    (hnext : (M.tm.runFrom (M.tm.initCfg x) (i + 1)).output.length ≤ outLen) :
    Ends lim P d (tmRound M) σ (26 * M.k + 18 + (tmTail M).blockCost)
      (TMRunInv M x a b sc outLen scratchLen μ₀ (i + 1)) := by
  let c := M.tm.runFrom (M.tm.initCfg x) i
  obtain ⟨q, hq⟩ : ∃ q, c.state = some q := Option.ne_none_iff_exists'.mp hlive
  have hstep : M.tm.step c = (tmAction M c q).apply c := Turing.MultiTapeTM.step_of_some hq
  have hprefix : c.output.length + (tmAction M c q).output.toList.length ≤ outLen := by
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step'] at hnext
    change (M.tm.step c).output.length ≤ outLen at hnext
    rw [hstep, Turing.Action.apply_output, List.length_append] at hnext
    exact hnext
  have hend : sc + 2 * i * M.k + 2 * M.k ≤ sc + scratchLen := by nlinarith
  unfold tmRound
  refine Ends.seq (26 * M.k + 18) (tmTail M).blockCost ?_ (Nat.le_refl _)
  apply (tmClearRing_ends M σ sc i hI.frame.scratch hI.frame.round hw
    (by omega) h2i hk2).mono (Nat.le_refl _)
  rintro ρ ⟨hmem, hloc⟩
  have hfρ : TMFrame M c a b sc i ρ := by
    apply tmFrame_transfer hI.frame
    · intro v hv _
      apply hloc v
      · rcases hv with hv | ⟨j, hj⟩ <;> (try unfold tmHead at hj) <;> omega
      · rcases hv with hv | ⟨j, hj⟩ <;> (try unfold tmHead at hj) <;> omega
      · rcases hv with hv | ⟨j, hj⟩
        · omega
        · have := j.isLt
          unfold tmHead at hj
          omega
    · exact (hloc 7 (by decide) (by decide) (by omega)).trans hI.frame.round
  have hclear : SameOutside σ.mem ρ.mem sc scratchLen := by
    rw [hmem]
    exact SameOutside.mono (sameOutside_wrote (μ := σ.mem)
      (dst := sc + 2 * i * M.k) (f := fun _ => (0 : ℤ)) (j := 2 * M.k)
      (n := 2 * M.k) (Nat.le_refl _)) (by omega) hend
  have hkeepρ : SameOutside2 μ₀ ρ.mem b outLen sc scratchLen :=
    SameOn.then hI.keep hclear (fun _ h => ⟨h, h.2⟩)
  have houtρ : Seg ρ.mem b (tmBits c.output) := by
    have hout0 : Seg σ.mem b (tmBits c.output) := hI.output
    apply hout0.of_sameOutside hclear
    simp only [tmBits, List.length_map]
    rcases hsepOS with hsepOS | hsepOS <;> omega
  have htρ : TMTapes M c sc (i + 1) ρ.mem := by
    intro j z hz
    rw [hmem]
    exact tmRingMemory_tapes M x i sc σ.mem hI.tapes j z (by omega)
  have hhead (j : Fin M.k) : |c.workTapePos j| < ((i + 1 : ℕ) : ℤ) := by
    have hb := tmHead_abs_le M x i j
    change |c.workTapePos j| ≤ (i : ℤ) at hb
    omega
  have hinside (j : Fin M.k) (z : ℤ) (hz : |z| < ((i + 1 : ℕ) : ℤ)) :
      Inside sc scratchLen (tmAddr sc M.k j z) := by
    have haddr := tmAddr_lt (sc := sc) (tapes := M.k) (n := i) j (show |z| ≤ (i : ℤ) by omega)
    have hs : M.k * (2 * i + 2) ≤ scratchLen := by nlinarith
    exact ⟨by unfold tmAddr; omega, by omega⟩
  have hc (j : Fin M.k) : (tmCell (c.workTapePos j) : ℤ) ≤ lim.word := by
    have hn := tmCell_le (tmHead_abs_le M x i j)
    have hnZ : (tmCell (c.workTapePos j) : ℤ) ≤ 2 * (i : ℤ) + 1 := by exact_mod_cast hn
    omega
  have hinputρ (u : ℕ) (hu : u < x.length) :
      ρ.mem (a + u) = ((x.getD u false).toNat : ℤ) := by
    have he : ρ.mem (a + u) = μ₀ (a + u) :=
      SameOn.cell (hkeepρ.mono (by
        intro v hv
        subst v
        constructor
        · rcases hsepIO with h | h <;> omega
        · rcases hsepIS with h | h <;> omega))
    exact he.trans (hinput u hu)
  have hm (j : Fin M.k) :
      |c.workTapePos j + (((tmAction M c q).workTapes j).2.cast : ℤ)| ≤ lim.word := by
    have hb := tmHead_abs_le M x (i + 1) j
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step'] at hb
    change |(M.tm.step c).workTapePos j| ≤ ((i + 1 : ℕ) : ℤ) at hb
    rw [hstep, Turing.Action.apply_workTapePos] at hb
    omega
  refine Ends.block ?_ (Nat.le_refl _)
  apply (tmTail_runs M c q hq ρ μ₀ hfρ htρ houtρ hkeepρ hw hin
    (by omega) hL (by omega) (by omega) hstates hc hinputρ hm hhead hinside
    hscratch hspace hsepOS hprefix).mono
  rintro τ ⟨hfτ, htτ, houtτ, hkeepτ⟩
  constructor
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using hfτ
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using htτ
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using houtτ
  · exact hkeepτ

/-- Initialize the scalar configuration locals and the work-head bank. -/
private noncomputable def tmSetup (M : Turing.FinTM Bool) : Stmt :=
  .seq (.set 4 (.const 1)) (.seq (.set 5 (.const (tmStateCode M (some M.tm.q₀))))
    (.seq (.set 6 (.const 0)) (.seq (.set 7 (.const 0))
      (tmBank M (fun j => .set (tmHead j.val) (.const 0))))))

/-- Zeroing the static head bank preserves all scalar locals and memory.

**Proof sketch.** Apply `tmSeq_accumulate` to the finite tape list. Every assignment changes
only its own head local, which is above all eight scalar locals. It sets that head to zero
and preserves any head already known to be zero, even when the two indices coincide. -/
private theorem tmZeroHeads_runs (M : Turing.FinTM Bool) {lim : Limits} (σ : State)
    (h0 : (0 : ℤ) ≤ lim.word) :
    (tmBank M (fun j => .set (tmHead j.val) (.const 0))).Runs lim σ fun τ =>
      (∀ v < 8, τ.loc v = σ.loc v) ∧ τ.mem = σ.mem ∧
      ∀ j : Fin M.k, τ.loc (tmHead j.val) = 0 := by
  let I : State → Prop := fun τ => (∀ v < 8, τ.loc v = σ.loc v) ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ => τ.loc (tmHead j.val) = 0
  have hr : (tmBank M (fun j => .set (tmHead j.val) (.const 0))).Runs lim σ fun τ =>
      I τ ∧ (∀ j ∈ List.finRange M.k, F j τ) ∧ ∀ j, F j σ → F j τ := by
    apply tmSeq_accumulate (I := I) (F := F) ⟨fun _ _ => rfl, rfl⟩
    intro j _ τ hτ
    apply (tmSet_runs (dst := tmHead j.val) ((Expr.safe_const_iff _ _ _).mpr h0)
      (Expr.val_const _ 0)).mono
    rintro τ' rfl
    refine ⟨⟨?_, hτ.2⟩, ?_, ?_⟩
    · intro v hv
      exact (Function.update_of_ne (show v ≠ tmHead j.val by unfold tmHead; omega)
        (0 : ℤ) τ.loc).trans (hτ.1 v hv)
    · exact Function.update_self ..
    · intro l hl
      change Function.update τ.loc (tmHead j.val) (0 : ℤ) (tmHead l.val) = 0
      by_cases he : tmHead l.val = tmHead j.val
      · rw [he, Function.update_self]
      · exact (Function.update_of_ne he (0 : ℤ) τ.loc).trans hl
  exact hr.mono fun τ hτ => ⟨hτ.1.1, hτ.1.2, fun j => hτ.2.1 j (List.mem_finRange j)⟩

/-- Setup produces the initial machine frame and preserves the argument memory.

**Proof sketch.** Perform the four safe scalar assignments, then use `tmZeroHeads_runs` for
the head bank. The bank preserves the scalar assignments and the original arguments. The
published initialization field equations identify these values with `M.tm.initCfg x`. -/
private theorem tmSetup_runs (M : Turing.FinTM Bool) (x : List Bool)
    {lim : Limits} {a b sc : ℕ} (σ : State)
    (ha : σ.loc 0 = (a : ℤ)) (hn : σ.loc 1 = (x.length : ℤ))
    (hb : σ.loc 2 = (b : ℤ)) (hsc : σ.loc 3 = (sc : ℤ))
    (h1 : (1 : ℤ) ≤ lim.word) (hq : (tmStateCode M (some M.tm.q₀) : ℤ) ≤ lim.word) :
    (tmSetup M).Runs lim σ fun τ => TMFrame M (M.tm.initCfg x) a b sc 0 τ ∧ τ.mem = σ.mem := by
  have h0 : (0 : ℤ) ≤ lim.word := by omega
  unfold tmSetup
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 4) ((Expr.safe_const_iff _ _ _).mpr h1) (Expr.val_const _ 1)).mono
  rintro σ₁ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 5) ((Expr.safe_const_iff _ _ _).mpr hq) (Expr.val_const _ _)).mono
  rintro σ₂ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 6) ((Expr.safe_const_iff _ _ _).mpr h0) (Expr.val_const _ 0)).mono
  rintro σ₃ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 7) ((Expr.safe_const_iff _ _ _).mpr h0) (Expr.val_const _ 0)).mono
  rintro σ₄ rfl
  apply (tmZeroHeads_runs M _ h0).mono
  rintro τ ⟨hscalar, hmem, hheads⟩
  have harg (v : ℕ) (hv : v < 4) : τ.loc v = σ.loc v := by
    simpa only [Function.update_of_ne (show v ≠ 7 by omega),
      Function.update_of_ne (show v ≠ 6 by omega), Function.update_of_ne (show v ≠ 5 by omega),
      Function.update_of_ne (show v ≠ 4 by omega)] using hscalar v (by omega)
  refine ⟨?_, hmem⟩
  constructor
  · exact (harg 0 (by decide)).trans ha
  · exact (harg 1 (by decide)).trans hn
  · exact (harg 2 (by decide)).trans hb
  · exact (harg 3 (by decide)).trans hsc
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_inputPos]
    simpa only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 7),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 5), Function.update_self] using hscalar 4 (by decide)
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_state]
    simpa only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),
      Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), Function.update_self] using hscalar 5 (by decide)
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_output]
    simpa only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7),
      Function.update_self, List.length_nil, Nat.cast_zero] using hscalar 6 (by decide)
  · simpa only [Function.update_self, Nat.cast_zero] using hscalar 7 (by decide)
  · intro j
    rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_workTapePos]
    exact hheads j

/-- The loop guard is safe when zero fits, and it holds exactly for a live encoded state. -/
private theorem tmGuard_read (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} (σ : State)
    (hc : σ.loc 5 = (tmStateCode M c.state : ℤ)) (h0 : (0 : ℤ) ≤ lim.word) :
    (Cond.lt (.const 0) (.var 5)).Safe lim σ ∧
      ((Cond.lt (.const 0) (.var 5)).Holds σ ↔ c.state ≠ none) := by
  constructor
  · rw [Cond.safe_lt_iff, Expr.safe_const_iff, Expr.safe_var_iff]
    exact ⟨h0, trivial⟩
  · rw [Cond.holds_lt_iff, Expr.val_const, Expr.val_var, hc, Nat.cast_zero]
    cases hs : c.state with
    | none => simp only [tmStateCode, Nat.cast_zero, lt_self_iff_false, ne_self_iff_false]
    | some q =>
      simp only [tmStateCode, Nat.cast_add, Nat.cast_one, ne_eq, Option.some_ne_none, not_false_eq_true,
        iff_true]
      positivity

/-- The verified rounds run until the first halting time, with a constant cost per round.

**Proof sketch.** Apply `Ends.whileConst` to `TMRunInv`. `tmGuard_read` makes the guard true
before the supplied first halt and false at it. Each live iteration uses `tmRound_ends`;
the initialized-head envelope and the total scratch bound supply its ring bounds. The output
prefix theorem bounds every intermediate emission by the final output. -/
private theorem tmLoop_ends (M : Turing.FinTM Bool) (x out : List Bool) (u : ℕ)
    {lim : Limits} {P : Program} {d a b sc scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hI : TMRunInv M x a b sc out.length scratchLen μ₀ 0 σ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2u : (2 : ℤ) * u ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hrings : 2 * u * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + out.length ≤ lim.space)
    (hsepIO : Apart a x.length b out.length) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b out.length sc scratchLen)
    (hinput : ∀ j < x.length, μ₀ (a + j) = ((x.getD j false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none)
    (hout : (M.tm.runFrom (M.tm.initCfg x) u).output = out)
    (hlive : ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none) :
    Ends lim P d (.while (.lt (.const 0) (.var 5)) (tmRound M)) σ
      (u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 4)
      (TMRunInv M x a b sc out.length scratchLen μ₀ u) := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg _) hw
  refine Ends.whileConst (TMRunInv M x a b sc out.length scratchLen μ₀) u
    (26 * M.k + 18 + (tmTail M).blockCost) hI ?_ ?_ ?_
  · intro i τ hi hτ
    have hg := tmGuard_read M _ τ hτ.frame.control h0
    refine ⟨hg.1, hg.2.mpr (hlive i hi), ?_⟩
    have hr : 2 * (i + 1) * M.k ≤ scratchLen :=
      (Nat.mul_le_mul_right M.k (show 2 * (i + 1) ≤ 2 * u by omega)).trans hrings
    have hn : (M.tm.runFrom (M.tm.initCfg x) (i + 1)).output.length ≤ out.length := by
      have hp := M.tm.output_prefix (M.tm.initCfg x) (t := i + 1) (t' := u) (by omega)
      rw [hout] at hp
      exact hp.length_le
    exact tmRound_ends M x τ μ₀ hτ hw hin (by omega) hk2 hstates hr hscratch hspace
      hsepIO hsepIS hsepOS hinput hL (hlive i hi) hn
  · intro τ hτ
    have hg := tmGuard_read M _ τ hτ.frame.control h0
    exact ⟨hg.1, fun hh => (hg.2.mp hh) hhalt, hτ⟩
  · simp only [Cond.cost_lt, Expr.cost_const, Expr.cost_var]
    exact Nat.le_refl _

/-- The generated simulator has one procedure and no calls. The loop observes the encoded
halting state, and local zero receives the final output length only after the loop. -/
private noncomputable def tmBody (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmSetup M) (.seq (.while (.lt (.const 0) (.var 5)) (tmRound M)) (.set 0 (.var 6)))

/-- Read a bit segment in the exact default-index form used by the procedure specification. -/
private theorem tmBits_read {μ : ℕ → ℤ} {b : ℕ} {out : List Bool}
    (h : Seg μ b (tmBits out)) {j : ℕ} (hj : j < out.length) :
    μ (b + j) = ((out.getD j false).toNat : ℤ) := by
  have hj' : j < (tmBits out).length := by simpa only [tmBits, List.length_map] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simpa only [tmBits, List.getElem_map] using h.get hj'

/-- Setup, the finite simulation loop, and the final return give the complete body contract.

**Proof sketch.** The read-only setup produces the initial frame; its empty tape radius and
empty output establish `TMRunInv` at zero. Run `tmLoop_ends` to the supplied first halt. Its
frame records the final output length and its output segment is the prescribed output. A last
safe variable assignment copies that length into the return local, preserving memory. -/
private theorem tmBody_ends (M : Turing.FinTM Bool) (x out : List Bool) (u : ℕ)
    {lim : Limits} {P : Program} {d a b sc scratchLen : ℕ} (σ : State)
    (ha : σ.loc 0 = (a : ℤ)) (hn : σ.loc 1 = (x.length : ℤ))
    (hb : σ.loc 2 = (b : ℤ)) (hsc : σ.loc 3 = (sc : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2u : (2 : ℤ) * u ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hrings : 2 * u * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + out.length ≤ lim.space)
    (hsepIO : Apart a x.length b out.length) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b out.length sc scratchLen)
    (hinput : ∀ j < x.length, σ.mem (a + j) = ((x.getD j false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none)
    (hout : (M.tm.runFrom (M.tm.initCfg x) u).output = out)
    (hlive : ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none) :
    Ends lim P d (tmBody M) σ
      ((tmSetup M).blockCost + u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 6)
      fun τ => τ.loc 0 = (out.length : ℤ) ∧ Seg τ.mem b (tmBits out) ∧
        SameOutside2 σ.mem τ.mem b out.length sc scratchLen := by
  let loopCost := u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 4
  unfold tmBody
  refine Ends.seq (tmSetup M).blockCost (loopCost + 2) ?_ (by dsimp only [loopCost]; omega)
  refine Ends.block ?_ (Nat.le_refl _)
  apply (tmSetup_runs M x σ ha hn hb hsc (by omega) (hstates _)).mono
  rintro ρ ⟨hfρ, hmem⟩
  have hI : TMRunInv M x a b sc out.length scratchLen σ.mem 0 ρ := by
    constructor
    · simpa only [Turing.MultiTapeTM.runFrom_zero] using hfρ
    · intro j z hz
      have := abs_nonneg z
      omega
    · rw [Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
        Turing.Cfg.init_output]
      exact Seg.nil
    · rw [hmem]
      exact SameOutside2.refl
  refine Ends.seq loopCost 2 ?_ (by omega)
  apply (tmLoop_ends M x out u ρ σ.mem hI hw hin h2u hk2 hstates hrings hscratch hspace
    hsepIO hsepIS hsepOS hinput hL hhalt hout hlive).mono (Nat.le_refl _)
  intro τ hτ
  have hlen : τ.loc 6 = (out.length : ℤ) := by rw [hτ.frame.outputLen, hout]
  have houtτ : Seg τ.mem b (tmBits out) := by rw [← hout]; exact hτ.output
  refine Ends.set ((Expr.safe_var_iff _ _ _).mpr trivial) ?_ ?_
  · rw [Expr.cost_var]
  · rw [Expr.val_var]
    refine ⟨?_, houtτ, hτ.keep⟩
    change Function.update τ.loc 0 (τ.loc 6) 0 = (out.length : ℤ)
    rw [Function.update_self, hlen]

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
- **Encoding.** `tmStateCode` assigns zero to halt and positive indices from a fixed finite
  enumeration to live states. `tmSym` assigns zero, one, and two to blank, false, and true.
  `tmCell` and `tmAddr` interleave the signed cells of the work tapes in scratch memory;
  `tmAddr_injective` separates the cells and `tmAddr_lt` bounds the memory needed at a radius.
  `TMFrame` records the stable locals.
- **One step.** `tmRound` first clears its next ring with the existing `pass` routine.
  `tmClearRing_ends` bounds that initialization and `tmRingMemory_tapes` extends the valid tape
  representation. `tmLocate_runs` freezes each old head and computes its direct address;
  `tmReadInput_runs` reads the input in place. The finite code branches generated by
  `tmDispatch` choose exactly the row identified by `tmRowTests_unique`. The row writes each
  tape, moves the heads, appends the optional output bit, and updates the control state.
- **The run.** `TMRunInv` couples each round to `M.tm.runFrom (M.tm.initCfg x) i`, and
  `tmRound_ends` preserves its configuration, tapes, output prefix, and memory promise.
  `tmSetup_runs` initializes the frame. `tmFirstHalt` supplies the first halting time at most
  `t`; `tmLoop_ends` applies `Ends.whileConst`, and `tmBody_ends` returns the output length.
  Choose `A` as the sum of setup cost, per-round cost, the state-code bound, twice the tape
  count, and ten. It bounds time, scratch, and intermediate words. `tmBits_read` recovers
  the specified individual output bits.
- **Placement.** Build the procedure specification for its singleton program and use
  `tmMeets_behind` to carry it to `Program.behind Pre Q ++ Post`. -/
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
  classical
  let setup := (tmSetup M).blockCost
  let step := 4 + (26 * M.k + 18 + (tmTail M).blockCost)
  let states := (Finset.univ.toList : List M.State).length + 1
  let A := setup + step + states + 2 * M.k + 10
  refine ⟨[tmBody M], 0, A, 0, ?_⟩
  intro Pre Post lim d a len b sc μ x out t hlen hinput ht hw hin hspace hscratch
    hsepIO hsepIS hsepOS _
  subst len
  obtain ⟨u, hu, _, hhalt, hout, hlive⟩ := tmFirstHalt M ht
  let S := t + x.length + 1
  let N := A * S
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have huS : u + 1 ≤ S := by dsimp only [S]; omega
  have hA1 : 1 ≤ A := by dsimp only [A]; omega
  have hA2 : 2 ≤ A := by omega
  have hAk : 2 * M.k ≤ A := by dsimp only [A]; omega
  have hAstates : states ≤ A := by dsimp only [A]; omega
  have hAstep : step ≤ A := by dsimp only [A]; omega
  have hAsetup : setup + 6 ≤ A := by dsimp only [A]; omega
  have hAN : A ≤ N := by dsimp only [N]; nlinarith
  have hNspace : N ≤ lim.space := by
    change sc + N ≤ lim.space at hscratch
    omega
  have hNword : (N : ℤ) ≤ lim.word :=
    (show (N : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast hNspace).trans hw
  have h2uN : 2 * u ≤ N := Nat.mul_le_mul hA2 (show u ≤ S by omega)
  have hkN : 2 * M.k ≤ N := hAk.trans hAN
  have hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word := by
    intro s
    have hsN : tmStateCode M s ≤ N := (tmStateCode_le M s).trans (hAstates.trans hAN)
    exact (show (tmStateCode M s : ℤ) ≤ (N : ℤ) by exact_mod_cast hsN).trans hNword
  have hrings : 2 * u * M.k ≤ N := by
    calc
      2 * u * M.k = (2 * M.k) * u := by ring
      _ ≤ A * S := Nat.mul_le_mul hAk (by omega)
  have hLN : x.length + 1 ≤ N := by
    have hLS : x.length + 1 ≤ S := by dsimp only [S]; omega
    dsimp only [N]
    nlinarith
  have hL : (x.length : ℤ) + 1 ≤ lim.word :=
    (show (x.length : ℤ) + 1 ≤ (N : ℤ) by exact_mod_cast hLN).trans hNword
  have htime : setup + u * step + 6 ≤ N := by
    calc
      setup + u * step + 6 ≤ A + u * A := by
        have := Nat.mul_le_mul_left u hAstep
        omega
      _ = A * (u + 1) := by ring
      _ ≤ A * S := Nat.mul_le_mul_left A huS
  refine tmMeets_behind (Meets.of_body (p := 0)
    (show ([tmBody M] : Program)[0]? = some (tmBody M) from rfl) ?_) Pre Post
  apply (tmBody_ends M x out u (State.mk (frame [(a : ℤ), x.length, b, sc]) μ)
    (by change frame [(a : ℤ), x.length, b, sc] 0 = (a : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 1 = (x.length : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 2 = (b : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 3 = (sc : ℤ); rw [frame_apply]; rfl)
    hw hin
    ((show (2 : ℤ) * u ≤ (N : ℤ) by exact_mod_cast h2uN).trans hNword)
    ((show (2 : ℤ) * M.k ≤ (N : ℤ) by exact_mod_cast hkN).trans hNword)
    hstates hrings hscratch hspace hsepIO hsepIS hsepOS hinput hL hhalt hout hlive).mono htime
  rintro τ ⟨hret, hseg, hkeep⟩
  exact ⟨hret, fun j hj => tmBits_read hseg hj, hkeep⟩


end Light
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

## ===== TCSlib/Programs/Light/Lib/ArrayAt.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/ArrayAt.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/ArrayAt.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
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
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

open Light

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}

/-- The list `l` stands at address `a`: it has `N` entries, and its cells lie below `top`. -/
structure ListAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  below : a + N ≤ top := by light_arith

/-- The list `l` stands at address `a`: it has `N` entries, each of absolute value at most `U`, and
its cells lie below `top`. -/
structure ArrayAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N : ℕ) (U : ℤ) (top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  bound : AbsLe l U
  below : a + N ≤ top := by light_arith

namespace ListAt

/-- A list stays in place when its cells do not change.  That they lie below `top` is said again in
the description of the cells: so the promise `Kept μ μ' top` of a callee is enough as it stands. -/
theorem keep (h : ListAt μ a l N top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) : ListAt μ' a l N top :=
  { h with seg := h.seg.congr fun i hi => hs _ (by have := h.len; have := h.below; omega) }

/-- The address `top` may grow. -/
theorem mono (h : ListAt μ a l N top) (ht : top ≤ top' := by light_arith) : ListAt μ a l N top' :=
  { h with below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ListAt μ a l N top) (hk : k + n ≤ N) :
    ListAt μ (a + k) ((l.drop k).take n) n top where
  len := by rw [List.length_take, List.length_drop, h.len]; omega
  seg := (h.seg.drop k).take n
  below := by have := h.below; omega

end ListAt

namespace ArrayAt

/-- An array without the bound on its entries. -/
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }

/-- An array stays in place when its cells do not change. -/
theorem keep (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) :
    ArrayAt μ' a l N U top :=
  { h with seg := (h.listAt.keep hs).seg }

/-- The bound `U` on the entries and the address `top` may grow. -/
theorem mono (h : ArrayAt μ a l N U top) (hU : U ≤ U' := by light_arith)
    (ht : top ≤ top' := by light_arith) : ArrayAt μ a l N U' top' :=
  { h with bound := fun x hx => (h.bound x hx).trans hU, below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi

/-- A cell of an array holds a number of absolute value at most `U`. -/
theorem abs_read_le (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by
  rw [h.seg i (h.len ▸ hi)]
  exact h.bound.getElem _

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ArrayAt μ a l N U top) (hk : k + n ≤ N) :
    ArrayAt μ (a + k) ((l.drop k).take n) n U top :=
  { h.listAt.drop_take hk with
    bound := fun x hx => h.bound x (List.mem_of_mem_drop (List.mem_of_mem_take hx)) }

end ArrayAt

/-- The list `l` of natural numbers stands at address `a`: it has `N` entries, each below `p`, and
its cells lie below `top`. -/
structure IndexAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) (N p top : ℕ) : Prop where
  len : l.length = N
  seg : SegN μ a l
  lt : ∀ x ∈ l, x < p
  below : a + N ≤ top := by light_arith

namespace IndexAt

variable {l : List ℕ} {p : ℕ}

/-- A list of natural numbers stays in place when its cells do not change. -/
theorem keep (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) :
    IndexAt μ' a l N p top :=
  { h with
    seg := Seg.congr h.seg fun i hi => hs _ (by
      have := h.len
      have := h.below
      rw [List.length_map] at hi
      omega) }

/-- Reading a cell. -/
theorem read (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) :=
  h.seg.read (h.len ▸ hi)

/-- An entry is below `p`. -/
theorem getD_lt (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by
  have hl : i < l.length := h.len ▸ hi
  rw [List.getD_eq_getElem _ 0 hl]
  exact h.lt _ (List.getElem_mem hl)

end IndexAt

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

## ===== TCSlib/Programs/Light/Lib/CountSort.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/CountSort.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/CountSort.lean`, with imports remapped;
* v4.25 proof repair (beta: loop invariant applied to its round);
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Tactics
import TCSlib.Programs.Util.CountingSort

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counting sort of a list of items by a key that is read through the item

countSort(n, src, dst, key, stride, off, nb, cnt) sorts the n items at src stably by their keys and
writes them to dst.  The key of the item x is the number in the cell key + x · stride + off, a
natural number below nb.  cnt is a scratch area of nb + 1 cells, of arbitrary content on entry; on
exit cnt[t] is the number of items with a key below t, which is where bucket t starts.

The routine has five phases, each of them one loop:
* `csZero` sets the cells of cnt to 0 (`csZero_ends`);
* `csCount` counts the items with key t in cnt[t + 1] (`csCount_ends`);
* `csPrefix` adds up, so that cnt[t] is the start of bucket t (`csPrefix_ends`);
* `csPlace` writes each item to the next free place of its bucket, which it reads from cnt and moves
  on by one (`csPlace_ends`);
* `csShift` moves the contents of cnt up by one cell, so that cnt[t] is again the start of bucket t
  (`csShift_ends`).

Each phase has an invariant, a structure about the memory, with two lemmas: `start` says that it
holds before the first round, and `succ` says what a round does to the memory.  Three numbers
describe the memory, where kf j is the key of item number j: `cntLt kf t n` is the number of items
with a key below t, the start of bucket t; `cntEq kf t i` is the number of items before item number
i with key t; and `sortPos kf n j`, their sum at t = kf j and i = j, is the place of item number j.
What is assumed is `CountSort.Pre`, what is achieved is `CountSort.Post`, and the result is
`countSort_meets`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open Light

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace CountSort

/-- The local variables of countSort: the arguments n (Len), src, dst, key (Keys), stride, off
(Offset), nb (Buckets), cnt; the counter of the loops (Idx); the address of a cell of cnt (Cell); a
place in dst (Place). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Dst : ℕ := 2
@[inherit_doc Len] abbrev Keys : ℕ := 3
@[inherit_doc Len] abbrev Stride : ℕ := 4
@[inherit_doc Len] abbrev Offset : ℕ := 5
@[inherit_doc Len] abbrev Buckets : ℕ := 6
@[inherit_doc Len] abbrev Cnt : ℕ := 7
@[inherit_doc Len] abbrev Idx : ℕ := 8
@[inherit_doc Len] abbrev Cell : ℕ := 9
@[inherit_doc Len] abbrev Place : ℕ := 10

end CountSort

open CountSort in
/-- The key of item number i, where i is the value of the counter:
mem[key + src[i] · stride + off]. -/
def csKey : Expr := M (v Keys +' M (v Src +' v Idx) *' v Stride +' v Offset)

@[simp] theorem csKey_cost : csKey.cost = 11 := rfl

open CountSort in
/-- cnt[t] := 0 for t ≤ nb. -/
def csZero : Stmt := .for Idx (v Buckets +' k 1) (.store (v Cnt +' v Idx) (k 0))

open CountSort in
/-- cnt[(key of item i) + 1] += 1 for i < n. -/
def csCount : Stmt :=
  .for Idx (v Len) (.set Cell (v Cnt +' csKey +' k 1) ;; .store (v Cell) (M (v Cell) +' k 1))

open CountSort in
/-- cnt[t + 1] += cnt[t] for t < nb. -/
def csPrefix : Stmt :=
  .for Idx (v Buckets)
    (.store (v Cnt +' v Idx +' k 1) (M (v Cnt +' v Idx +' k 1) +' M (v Cnt +' v Idx)))

open CountSort in
/-- dst[cnt[key of item i]] := item i, cnt[key of item i] += 1, for i < n. -/
def csPlace : Stmt :=
  .for Idx (v Len) (
    .set Cell (v Cnt +' csKey) ;;
    .set Place (M (v Cell)) ;;
    .store (v Dst +' v Place) (M (v Src +' v Idx)) ;;
    .store (v Cell) (v Place +' k 1))

open CountSort in
/-- cnt[t] := cnt[t - 1] for t = nb, …, 1, and cnt[0] := 0. -/
def csShift : Stmt :=
  .set Idx (v Buckets) ;;
  .while (k 0 <' v Idx) (
    .store (v Cnt +' v Idx) (M (v Cnt +' v Idx -' k 1)) ;;
    .set Idx (v Idx -' k 1)) ;;
  .store (v Cnt) (k 0)

/-- countSort(n, src, dst, key, stride, off, nb, cnt). -/
def countSortBody : Stmt := csZero ;; csCount ;; csPrefix ;; csPlace ;; csShift

/-! ## What is assumed, and the state between the phases -/

namespace CountSort

/-- The arguments of countSort. -/
structure Args where
  /-- the number of items -/
  n : ℕ
  /-- where the items stand -/
  src : ℕ
  /-- where the sorted items go -/
  dst : ℕ
  /-- the key of the item x is in the cell key + x · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells of scratch space -/
  cnt : ℕ

/-- The cell that holds the key of the item x. -/
def Args.keyCell (A : Args) (x : ℕ) : ℕ := A.key + x * A.stride + A.off

/-- A state of countSort: the arguments, the counter i, the scratch variables c and p, and the
memory. -/
abbrev Args.state (A : Args) (i c p : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt, i, c, p], μ'⟩

/-- Only dst and cnt have changed. -/
abbrev Args.Same (A : Args) (μ μ' : ℕ → ℤ) : Prop := SameOutside2 μ μ' A.dst A.n A.cnt (A.nb + 1)

end CountSort

open CountSort

/-- What countSort assumes: where the arrays lie, that what is read is not overwritten, and what the
items (it) and their keys (kf) are. -/
structure CountSort.Pre (lim : Limits) (μ : ℕ → ℤ) (A : Args) (it kf : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  srcB : A.src + A.n ≤ lim.space
  dstB : A.dst + A.n ≤ lim.space
  cntB : A.cnt + (A.nb + 1) ≤ lim.space
  items : ∀ i < A.n, μ (A.src + i) = it i
  keyB : ∀ i < A.n, A.keyCell (it i) < lim.space
  keys : ∀ i < A.n, μ (A.keyCell (it i)) = kf i
  keyLt : ∀ i < A.n, kf i < A.nb
  srcDst : Apart A.src A.n A.dst A.n
  srcCnt : Apart A.src A.n A.cnt (A.nb + 1)
  dstCnt : Apart A.dst A.n A.cnt (A.nb + 1)
  keyDst : ∀ i < A.n, Outside A.dst A.n (A.keyCell (it i))
  keyCnt : ∀ i < A.n, Outside A.cnt (A.nb + 1) (A.keyCell (it i))

/-- What countSort achieves: item number j stands at dst[sortPos kf n j], cnt[t] is the number of
items with a key below t, and nothing else has changed. -/
structure CountSort.Post (μ : ℕ → ℤ) (A : Args) (it kf : ℕ → ℕ) (μ' : ℕ → ℤ) : Prop where
  placed : ∀ j < A.n, μ' (A.dst + sortPos kf A.n j) = it j
  starts : ∀ t ≤ A.nb, μ' (A.cnt + t) = cntLt kf t A.n
  same : A.Same μ μ'

variable {μ μ' : ℕ → ℤ} {A : Args} {it kf : ℕ → ℕ} {σ : State}

/-- The items are still there after writing to dst and cnt. -/
theorem CountSort.Pre.item (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ') {i : ℕ}
    (hi : i < A.n) : μ' (A.src + i) = it i := by
  light_facts pre
  exact (same _ ⟨by omega, by omega⟩).trans (pre.items i hi)

/-- Reading the key of item number i: the expression stays within the limits and gives kf i. -/
theorem csKey_gives (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ') {i : ℕ} (hi : i < A.n)
    (c p : ℤ) : csKey.Gives lim (A.state i c p μ') (kf i) := by
  light_facts pre
  have hcell := pre.keyB i hi
  have hitem := pre.item same hi
  have hkey : μ' (A.keyCell (it i)) = kf i :=
    (same _ ⟨pre.keyDst i hi, pre.keyCnt i hi⟩).trans (pre.keys i hi)
  unfold Args.keyCell at hcell hkey
  have haddr : ((A.key : ℤ) + (it i : ℤ) * A.stride + A.off).toNat
      = A.key + it i * A.stride + A.off := by
    rw [← Int.toNat_natCast (A.key + it i * A.stride + A.off)]
    push_cast
    rfl
  simp [csKey, Limits.Addr, abs_le, hitem, haddr, hkey]
  omega

/-- The state between two phases, and before a round of a phase: the counter is i, only dst and cnt
have changed since the start, and R holds of the memory. -/
def CsState (μ : ℕ → ℤ) (A : Args) (i : ℤ) (R : (ℕ → ℤ) → Prop) (σ : State) : Prop :=
  ∃ (c p : ℤ) (μ' : ℕ → ℤ), σ = A.state i c p μ' ∧ A.Same μ μ' ∧ R μ'

/-- A weaker fact about the memory. -/
theorem CsState.imp {entry : ℤ} {R R' : (ℕ → ℤ) → Prop} (h : CsState μ A entry R σ)
    (hR : ∀ μ', R μ' → R' μ') : CsState μ A entry R' σ := by
  obtain ⟨c, p, μ', rfl, same, h⟩ := h
  exact ⟨c, p, μ', rfl, same, hR _ h⟩

/-- **The loop rule for the phases.**  The loop has m rounds, the value of hi.  The body is a block
that keeps the arguments and the counter.  R j holds of the memory before round j; afterwards the
counter is m and R m holds. -/
theorem Ends.csFor {entry : ℤ} {hi : Expr} {body : Stmt} {T : ℕ} (R : ℕ → (ℕ → ℤ) → Prop) (m : ℕ)
    (start : CsState μ A entry (R 0) σ)
    (round : ∀ (j : ℕ) (c p : ℤ) (μ' : ℕ → ℤ), j < m → A.Same μ μ' → R j μ' →
      Ends lim P d body (A.state j c p μ') body.blockCost (CsState μ A j (R (j + 1))))
    (bound : ∀ (j : ℕ) (c p : ℤ) (μ' : ℕ → ℤ), hi.Gives lim (A.state j c p μ') m := by
      intros; light_side)
    (hm : (m : ℤ) ≤ lim.word := by omega)
    (hT : m * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (.for Idx hi body) σ T (CsState μ A m (R m)) := by
  obtain ⟨c, p, μ', rfl, same, h⟩ := start
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => A.state j s.1 s.2 μ')
    (fun j μ' => A.Same μ μ' ∧ R j μ') m body.blockCost (c, p) ⟨same, h⟩ ?round
    (fun s μ' h => ⟨s.1, s.2, μ', rfl, h.1, h.2⟩) (bound := fun j s μ' _ _ => bound j s.1 s.2 μ')
    (hn := hm) (hT := hT)
  intro j s μ' hj h
  refine (round j s.1 s.2 μ' hj h.1 h.2).mono le_rfl ?_
  rintro _ ⟨c, p, μ', rfl, same, h⟩
  exact ⟨(c, p), μ', rfl, same, h⟩

/-! ## The first phase: the counters are set to 0 -/

/-- The first j cells of cnt are 0. -/
def CsZeroed (A : Args) (j : ℕ) (μ' : ℕ → ℤ) : Prop := ∀ t < j, μ' (A.cnt + t) = 0

/-- One more cell is set to 0. -/
theorem CsZeroed.succ {j : ℕ} (h : CsZeroed A j μ') :
    CsZeroed A (j + 1) (Function.update μ' (A.cnt + j) 0) := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h t ht)
  · exact Function.update_self ..

/-- `csZero`: the nb + 1 cells of cnt are 0 afterwards. -/
theorem csZero_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (fun _ => True) σ) :
    Ends lim P d csZero σ (15 * A.nb + 23)
      (CsState μ A (A.nb + 1 : ℕ) (CsZeroed A (A.nb + 1))) := by
  light_facts pre
  -- for t < nb + 1
  refine Ends.csFor (CsZeroed A) (A.nb + 1) (h.imp fun _ _ t ht => absurd ht (by omega)) ?round
  case round =>
    intro t c p μ' ht same zero
    -- cnt[t] := 0
    light_store (A.cnt + t) 0
    exact ⟨c, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, zero.succ⟩

/-! ## The second phase: the sizes of the buckets -/

/-- The items before item number i have been counted: the cell t + 1 of cnt holds the number of
those with key t, and the cell 0 holds 0. -/
structure CsCounted (A : Args) (kf : ℕ → ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  first : μ' A.cnt = 0
  sizes : ∀ t < A.nb, μ' (A.cnt + (t + 1)) = cntEq kf t i

/-- Nothing has been counted yet, and all cells are 0. -/
theorem CsCounted.start (h : CsZeroed A (A.nb + 1) μ') : CsCounted A kf 0 μ' :=
  ⟨h 0 (by omega), fun t ht => by simpa using h (t + 1) (by omega)⟩

/-- Item number i is counted. -/
theorem CsCounted.succ {i : ℕ} (h : CsCounted A kf i μ') :
    CsCounted A kf (i + 1)
      (Function.update μ' (A.cnt + (kf i + 1)) (cntEq kf (kf i) i + 1 : ℕ)) := by
  refine ⟨(Function.update_of_ne (by omega) _ _).trans h.first, fun t ht => ?_⟩
  rw [cntEq_succ]
  by_cases e : kf i = t
  · subst e
    rw [if_pos rfl, Function.update_self]
  · rw [if_neg e, Function.update_of_ne (by omega)]
    exact h.sizes t ht

/-- `csCount`: cnt[t + 1] is the number of items with key t afterwards. -/
theorem csCount_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsZeroed A (A.nb + 1)) σ) :
    Ends lim P d csCount σ (30 * A.n + 6) (CsState μ A A.n (CsCounted A kf A.n)) := by
  light_facts pre
  -- for i < n
  refine Ends.csFor (CsCounted A kf) A.n (h.imp fun _ => .start) ?round (hT := by simp; omega)
  case round =>
    intro i c p μ' hi same counted
    obtain ⟨hsafe, hval⟩ := csKey_gives pre same hi c p
    have hlt := pre.keyLt i hi
    have hcell := counted.sizes _ hlt
    have hle : cntEq kf (kf i) i ≤ i := Nat.count_le _
    have haddr : ((A.cnt : ℤ) + ((kf i : ℤ) + 1)).toNat = A.cnt + (kf i + 1) := by omega
    -- cell := cnt + key + 1
    light_set (A.cnt + (kf i + 1) : ℕ) using hsafe, hval
    -- mem[cell] := mem[cell] + 1
    light_store (A.cnt + (kf i + 1)) (cntEq kf (kf i) i + 1 : ℕ) using haddr, hcell
    exact ⟨_, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, counted.succ⟩

/-! ## The third phase: the starts of the buckets -/

/-- The first r sizes have been added up: the cells t ≤ r of cnt hold the starts of their buckets,
and a cell t + 1 after them still holds the size of bucket t. -/
structure CsSummed (A : Args) (kf : ℕ → ℕ) (r : ℕ) (μ' : ℕ → ℤ) : Prop where
  starts : ∀ t ≤ r, μ' (A.cnt + t) = cntLt kf t A.n
  sizes : ∀ t < A.nb, r ≤ t → μ' (A.cnt + (t + 1)) = cntEq kf t A.n

/-- What `csCount` leaves: the cell 0 holds 0, the start of bucket 0, and the others the sizes. -/
theorem CsSummed.start (h : CsCounted A kf A.n μ') : CsSummed A kf 0 μ' := by
  refine ⟨fun t ht => ?_, fun t ht _ => h.sizes t ht⟩
  obtain rfl : t = 0 := by omega
  simpa using h.first

/-- The cell r + 1 receives the start of bucket r + 1. -/
theorem CsSummed.succ {r : ℕ} (h : CsSummed A kf r μ') :
    CsSummed A kf (r + 1) (Function.update μ' (A.cnt + (r + 1)) (cntLt kf (r + 1) A.n : ℕ)) := by
  refine ⟨fun t ht => ?_,
    fun t ht hrt => (Function.update_of_ne (by omega) _ _).trans (h.sizes t ht (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h.starts t (by omega))
  · exact Function.update_self ..

/-- `csPrefix`: cnt[t] is the number of items with a key below t afterwards. -/
theorem csPrefix_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsCounted A kf A.n) σ) :
    Ends lim P d csPrefix σ (25 * A.nb + 6) (CsState μ A A.nb (CsSummed A kf A.nb)) := by
  light_facts pre
  -- for t < nb
  refine Ends.csFor (CsSummed A kf) A.nb (h.imp fun _ => .start) ?round
  case round =>
    intro t c p μ' ht same summed
    have hprev := summed.starts t le_rfl
    have hcell := summed.sizes t ht le_rfl
    have hle : cntLt kf (t + 1) A.n ≤ A.n := cntLt_le _ _ _
    -- The start of bucket t + 1 is the start of bucket t plus its size.
    have hsum := cntLt_succ_left kf t A.n
    have haddr : ((A.cnt : ℤ) + t + 1).toNat = A.cnt + (t + 1) := by omega
    -- cnt[t + 1] := cnt[t + 1] + cnt[t]
    light_store (A.cnt + (t + 1)) (cntLt kf (t + 1) A.n : ℕ) using haddr, hprev, hcell
    exact ⟨c, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, summed.succ⟩

/-! ## The fourth phase: the items go to their places -/

/-- The items before item number i have been placed: they stand at their places in dst, and the
cell t of cnt holds the next free place of bucket t. -/
structure CsPlaced (A : Args) (it kf : ℕ → ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  next : ∀ t < A.nb, μ' (A.cnt + t) = (cntLt kf t A.n + cntEq kf t i : ℕ)
  done : ∀ j < i, μ' (A.dst + sortPos kf A.n j) = it j

/-- What `csPrefix` leaves: no item has been placed, and the next free places are the starts. -/
theorem CsPlaced.start (h : CsSummed A kf A.nb μ') : CsPlaced A it kf 0 μ' :=
  ⟨fun t ht => by simpa using h.starts t (by omega), fun j hj => absurd hj (by omega)⟩

/-- **Item number i is placed**: it is written to its place, and the next free place of its bucket
moves on. -/
theorem CsPlaced.succ (pre : CountSort.Pre lim μ A it kf) {i : ℕ} (hi : i < A.n)
    (h : CsPlaced A it kf i μ') :
    CsPlaced A it kf (i + 1) (Function.update (Function.update μ'
      (A.dst + sortPos kf A.n i) (it i)) (A.cnt + kf i) (sortPos kf A.n i + 1 : ℕ)) := by
  have hapart := pre.dstCnt
  have hk := pre.keyLt i hi
  have hpos := sortPos_lt kf hi
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rw [cntEq_succ]
    by_cases e : kf i = t
    · subst e
      rw [Function.update_self, if_pos rfl, sortPos, Nat.add_assoc]
    · rw [if_neg e, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.next t ht
  · have hlt := sortPos_lt kf (show j < A.n by omega)
    rw [Function.update_of_ne (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : sortPos kf A.n j ≠ sortPos kf A.n i := fun e =>
        absurd (eq_of_sortPos_eq (by omega) hi e) (by omega)
      exact (Function.update_of_ne (by omega) _ _).trans (h.done j hj)
    · exact Function.update_self ..

/-- `csPlace`: item number j is written to dst[sortPos kf n j], and cnt[t] moves on to the start of
bucket t + 1. -/
theorem csPlace_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsSummed A kf A.nb) σ) :
    Ends lim P d csPlace σ (38 * A.n + 6) (CsState μ A A.n (CsPlaced A it kf A.n)) := by
  light_facts pre
  -- for i < n
  refine Ends.csFor (CsPlaced A it kf) A.n (h.imp fun _ => .start) ?round (hT := by simp; omega)
  case round =>
    intro i c p μ' hi same placed
    obtain ⟨hsafe, hval⟩ := csKey_gives pre same hi c p
    have hlt := pre.keyLt i hi
    have hpos : sortPos kf A.n i < A.n := sortPos_lt kf hi
    have hcell : μ' (A.cnt + kf i) = (sortPos kf A.n i : ℕ) := placed.next _ hlt
    have hitem := pre.item same hi
    -- cell := cnt + key
    light_set (A.cnt + kf i : ℕ) using hsafe, hval
    -- place := mem[cell]
    light_set (sortPos kf A.n i : ℕ) using hcell
    -- dst[place] := src[i]
    light_store (A.dst + sortPos kf A.n i) (it i) using hitem
    -- mem[cell] := place + 1
    light_store (A.cnt + kf i) (sortPos kf A.n i + 1 : ℕ)
    exact ⟨_, _, _, rfl, (same.update (Or.inl ⟨by omega, by omega⟩) _).update
        (Or.inr ⟨by omega, by omega⟩) _, placed.succ pre hi⟩

/-! ## The fifth phase: the contents of cnt move up by one cell -/

/-- While the contents of cnt move up, with the counter at s: the items stand at their places, the
cells after s of cnt hold the starts of their buckets, and the cells before s still the starts of
the next buckets.  Nothing is said about the cell s: the next write goes there. -/
structure CsShifted (A : Args) (it kf : ℕ → ℕ) (s : ℕ) (μ' : ℕ → ℤ) : Prop where
  placed : ∀ j < A.n, μ' (A.dst + sortPos kf A.n j) = it j
  moved : ∀ t ≤ A.nb, s < t → μ' (A.cnt + t) = cntLt kf t A.n
  waiting : ∀ t < s, μ' (A.cnt + t) = cntLt kf (t + 1) A.n

/-- What `csPlace` leaves, with the counter at nb: every bucket is full, so that its next free place
is the start of the next bucket. -/
theorem CsShifted.start (h : CsPlaced A it kf A.n μ') : CsShifted A it kf A.nb μ' :=
  ⟨h.done, fun t ht hlt => absurd hlt (by omega),
    fun t ht => by rw [cntLt_succ_left]; exact h.next t ht⟩

/-- A write to a cell of cnt leaves the items at their places. -/
theorem CsShifted.placed_update (pre : CountSort.Pre lim μ A it kf) {s t : ℕ}
    (h : CsShifted A it kf s μ') (ht : t ≤ A.nb) (x : ℤ) :
    ∀ j < A.n, Function.update μ' (A.cnt + t) x (A.dst + sortPos kf A.n j) = it j := by
  intro j hj
  have hapart := pre.dstCnt
  have hlt := sortPos_lt kf hj
  exact (Function.update_of_ne (by omega) _ _).trans (h.placed j hj)

/-- The cell s + 1 receives what the cell s holds. -/
theorem CsShifted.succ (pre : CountSort.Pre lim μ A it kf) {s : ℕ} (hs : s < A.nb)
    (h : CsShifted A it kf (s + 1) μ') :
    CsShifted A it kf s (Function.update μ' (A.cnt + (s + 1)) (cntLt kf (s + 1) A.n : ℕ)) := by
  refine ⟨h.placed_update pre hs _, fun t ht hst => ?_,
    fun t ht => (Function.update_of_ne (by omega) _ _).trans (h.waiting t (by omega))⟩
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hst) with hst | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h.moved t ht hst)
  · exact Function.update_self ..

/-- The cell 0 of cnt is set to 0, the start of bucket 0. -/
theorem CsShifted.last (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ')
    (h : CsShifted A it kf 0 μ') : CountSort.Post μ A it kf (Function.update μ' A.cnt 0) := by
  refine ⟨h.placed_update pre (Nat.zero_le _) 0, fun t ht => ?_,
    same.update (Or.inr ⟨le_rfl, by omega⟩) _⟩
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp
  · exact (Function.update_of_ne (by omega) _ _).trans (h.moved t ht hpos)

/-- `csShift`: from cnt[t] = start of bucket t + 1 to cnt[t] = start of bucket t. -/
theorem csShift_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsPlaced A it kf A.n) σ) :
    Ends lim P d csShift σ (18 * A.nb + 9) fun σ' => CountSort.Post μ A it kf σ'.mem := by
  obtain ⟨c, p, μ', rfl, same, placed⟩ := h
  light_facts pre
  -- t := nb
  light_set A.nb
  -- while 0 < t; before round r the counter is nb - r
  refine Ends.next _ (Ends.whileBlock
    (fun r => CsState μ A (A.nb - r : ℕ) (CsShifted A it kf (A.nb - r))) A.nb
    ⟨c, p, μ', rfl, same, .start placed⟩ ?round ?done (hT := le_rfl))
  case round =>
    rintro r _ hr ⟨c, p, μ', rfl, same, shifted⟩
    obtain ⟨s, hs⟩ : ∃ s, A.nb - r = s + 1 := ⟨A.nb - r - 1, by omega⟩
    beta_reduce
    rw [show A.nb - (r + 1) = s by omega]
    rw [hs] at shifted ⊢
    have hread := shifted.waiting s (by omega)
    have haddr : ((A.cnt : ℤ) + ((s : ℤ) + 1)).toNat = A.cnt + (s + 1) := by omega
    have hfrom : ((A.cnt : ℤ) + ((s : ℤ) + 1) - 1).toNat = A.cnt + s := by omega
    -- cnt[t] := cnt[t - 1]; t := t - 1
    refine ⟨by light_side, by light_side, by light_side, c, p, _, ?_,
      same.update (Or.inr ⟨by omega, by omega⟩) _, shifted.succ pre (by omega)⟩
    simp [update_frame_setLocal, haddr, hfrom, hread]
  case done =>
    rintro _ ⟨c, p, μ', rfl, same, shifted⟩
    rw [Nat.sub_self] at shifted
    -- cnt[0] := 0
    exact ⟨by light_side, by light_side, Ends.storeTo A.cnt 0 (shifted.last pre same)⟩

/-! ## The routine -/

/-- The time of countSort, for n items and keys below nb. -/
@[simp] def countSortTime (n nb : ℕ) : ℕ := 68 * n + 58 * nb + 52

/-- **countSort** sorts the items stably by their keys: the five phases, one after the other. -/
theorem countSort_meets {q : ℕ} (hq : P[q]? = some countSortBody)
    (pre : CountSort.Pre lim μ A it kf) :
    Meets lim P q d [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt] μ
      (countSortTime A.n A.nb) fun _ μ' => CountSort.Post μ A it kf μ' := by
  have start : CsState μ A 0 (fun _ => True)
      ⟨frame [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt], μ⟩ :=
    ⟨0, 0, μ, by rw [← frame_append_zeros _ 3]; rfl, .refl, trivial⟩
  refine .of_body hq ?_
  unfold countSortTime
  refine Ends.next _ ((csZero_ends pre start).mono le_rfl fun _ zeroed => ?_)
  refine Ends.next _ ((csCount_ends pre zeroed).mono le_rfl fun _ counted => ?_)
  refine Ends.next _ ((csPrefix_ends pre counted).mono le_rfl fun _ summed => ?_)
  refine Ends.next _ ((csPlace_ends pre summed).mono le_rfl fun _ placed => ?_)
  light_piece (csShift_ends pre placed)

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Emod.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Emod.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Emod.lean`, with imports remapped;
* v4.25 proof repair (beta: loop invariant applied to its round);
* v4.25 proof repair (beta: as above);
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod

/-- The local variables of emod: the arguments x, M and fr (the result replaces x), what is left
of |x|, the number of entries of the table, and the next multiple of M. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Modulus : ℕ := 1
@[inherit_doc Arg] abbrev Free : ℕ := 2
@[inherit_doc Arg] abbrev Rest : ℕ := 3
@[inherit_doc Arg] abbrev Count : ℕ := 4
@[inherit_doc Arg] abbrev Mult : ℕ := 5

end Emod

open Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : Stmt :=
  .store (v Free +' v Count) (v Mult) ;;
  .set Count (v Count +' k 1) ;;
  .set Mult (v Mult +' v Mult)

open Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : Stmt := .while (v Mult ≤' v Rest) emodTableRound

open Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .ite (M (v Free +' v Count) ≤' v Rest) (.set Rest (v Rest -' M (v Free +' v Count))) .skip

open Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : Stmt := .while (k 0 <' v Count) emodReduceRound

open Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : Stmt :=
  .ite (v Arg <' k 0)
    (.ite (v Rest =' k 0) (.set Arg (k 0)) (.set Arg (v Modulus -' v Rest)))
    (.set Arg (v Rest))

open Emod in
/-- emod(x, M, fr). -/
def emodBody : Stmt :=
  .ite (v Arg <' k 0) (.set Rest (k 0 -' v Arg)) (.set Rest (v Arg)) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  emodReduce ;;
  emodSign

/-- The number of doublings: the least k with a < M 2^k. -/
def emodRounds (a M : ℕ) : ℕ := Nat.size (a / M)

/-- The time of emod, for a = |x|. -/
@[simp] def emodTime (a M : ℕ) : ℕ := 43 * emodRounds a M + 34

/-- The multiple M 2^i is at most a exactly for i below the number of doublings. -/
theorem mul_two_pow_le_iff {a M i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < emodRounds a M := by
  rw [emodRounds, Nat.lt_size, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]

/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

/-- The remainder of a negative number. -/
theorem neg_emod_nat (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by
  have h : (a : ℤ) = (M : ℤ) * ((a / M : ℕ) : ℤ) + ((a % M : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a M).symm
  have hlt : a % M < M := Nat.mod_lt _ (by omega)
  split_ifs with h0
  · rw [h0] at h
    rw [h, Nat.cast_zero, add_zero, ← mul_neg]
    exact Int.mul_emod_right _ _
  · have e : -(a : ℤ) = ((M : ℤ) - ((a % M : ℕ) : ℤ)) + (M : ℤ) * (-((a / M : ℕ) : ℤ) - 1) := by
      rw [h]
      push_cast
      ring
    rw [e, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
namespace Emod

/-- What emod asks of the limits, for a modulus M ≥ 1, numbers up to V and the free pointer fr. -/
structure Pre (lim : Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space

/-- The first i entries of the table are in place, and no cell below the free pointer has changed.
-/
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ Kept μ μ' fr

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}

/-- **The table.**  With K doublings, the K multiples M 2^j ≤ a are written. -/
theorem table_ends (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Ends lim P d emodTable ⟨frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨frame [x, Mo, fr, a, emodRounds a Mo, ((Mo * 2 ^ emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        Table μ μ' Mo fr (emodRounds a Mo) := by
  light_facts F
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  refine Ends.whileConst (fun i σ => ∃ μ',
    σ = ⟨frame [x, Mo, fr, a, i, ((Mo * 2 ^ i : ℕ) : ℤ)], μ'⟩ ∧ Table μ μ' Mo fr i)
    (emodRounds a Mo) emodTableRound.blockCost ?start ?round ?done
    (by simp [emodTableRound]; omega)
  case start => exact ⟨μ, by simp, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
  case done =>
    rintro _ ⟨μ', rfl, tab⟩
    have hgt : ¬ Mo * 2 ^ emodRounds a Mo ≤ a := fun h =>
      absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
    generalize Mo * 2 ^ emodRounds a Mo = t at hgt
    exact ⟨by light_side, by simp; omega, μ', rfl, tab⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, tab, below⟩
    have hle : Mo * 2 ^ i ≤ a := (mul_two_pow_le_iff F.mod_pos).2 hi
    have hnext : Mo * 2 ^ (i + 1) = Mo * 2 ^ i + Mo * 2 ^ i := by ring
    beta_reduce
    rw [hnext]
    generalize ht : Mo * 2 ^ i = t at hle
    refine ⟨by light_side, by simp; omega, ?_⟩
    unfold emodTableRound
    -- table[count] := mult; count := count + 1; mult := mult + mult
    light_store (fr + i) t
    light_set (i + 1 : ℕ)
    light_set (t + t : ℕ)
    refine ⟨_, rfl, fun j hj => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · rw [Function.update_of_ne (by omega)]
        exact tab j h
      · rw [Function.update_self, ht]
    · rw [Function.update_of_ne (by omega)]
      exact below b hb

/-- **The subtractions.**  What is left of a after the multiples M 2^j have been subtracted, from
the largest down, where possible, is the remainder of a. -/
theorem reduce_ends (F : Pre lim Mo V fr) (haV : a ≤ V) {μ' : ℕ → ℤ} {t : ℤ}
    (tab : Table μ μ' Mo fr (emodRounds a Mo)) :
    Ends lim P d emodReduce ⟨frame [x, Mo, fr, a, emodRounds a Mo, t], μ'⟩
      (24 * emodRounds a Mo + 4) fun σ' => σ' = ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ := by
  light_facts F
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  have hgt : a < Mo * 2 ^ emodRounds a Mo := not_le.1 fun h =>
    absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
  refine Ends.whileConst (fun i σ => ∃ r : ℕ,
    σ = ⟨frame [x, Mo, fr, r, (emodRounds a Mo - i : ℕ), t], μ'⟩ ∧
      r < Mo * 2 ^ (emodRounds a Mo - i) ∧ r % Mo = a % Mo) (emodRounds a Mo)
    emodReduceRound.blockCost ?start ?round ?done (by simp [emodReduceRound]; omega)
  case start => exact ⟨a, by simp, by simpa using hgt, rfl⟩
  case done =>
    rintro _ ⟨r, rfl, hr, hmod⟩
    rw [Nat.sub_self] at hr ⊢
    have hra : r = a % Mo := by rw [← hmod, Nat.mod_eq_of_lt (by simpa using hr)]
    exact ⟨by simp; omega, by simp, by rw [hra]; rfl⟩
  case round =>
    rintro i _ hi ⟨r, rfl, hr, hmod⟩
    obtain ⟨c, hc⟩ : ∃ c, emodRounds a Mo - i = c + 1 := ⟨emodRounds a Mo - i - 1, by omega⟩
    beta_reduce
    rw [show emodRounds a Mo - (i + 1) = c by omega]
    rw [hc] at hr ⊢
    have hcell : μ' (fr + c) = ((Mo * 2 ^ c : ℕ) : ℤ) := tab.1 c (by omega)
    have hle : Mo * 2 ^ c ≤ a := (mul_two_pow_le_iff F.mod_pos).2 (by omega)
    have hsub : ∀ r' : ℕ, Mo * 2 ^ c ≤ r' → (r' - Mo * 2 ^ c) % Mo = r' % Mo :=
      fun r' h => Nat.sub_mul_mod h
    rw [show Mo * 2 ^ (c + 1) = Mo * 2 ^ c + Mo * 2 ^ c by ring] at hr
    generalize Mo * 2 ^ c = m at hr hcell hle hsub ⊢
    refine ⟨by light_side, by light_side, ?_⟩
    unfold emodReduceRound
    -- count := count - 1; if table[count] ≤ rest then rest := rest - table[count]
    light_set (c : ℕ)
    refine Ends.iteLast (fun h => ?_) (fun h => ?_)
    · have hmr : m ≤ r := by
        simp [hcell] at h
        omega
      exact Ends.setTo (r - m : ℕ) ⟨r - m, rfl, by omega, by rw [hsub r hmr, hmod]⟩
        (by light_side [hcell])
    · have hrm : r < m := by
        simp [hcell] at h
        omega
      exact Ends.skip ⟨r, rfl, hrm, hmod⟩

/-- **The sign.** -/
theorem sign_ends (F : Pre lim Mo V fr) (hax : (a : ℤ) = |x|) {μ' : ℕ → ℤ} {t : ℤ} :
    Ends lim P d emodSign ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ 12 fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ σ'.mem = μ' := by
  have hword := F.word
  have hr : a % Mo < Mo := Nat.mod_lt _ F.mod_pos
  generalize hrem : a % Mo = r at hr
  refine Ends.iteLast (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    have hmod := neg_emod_nat a Mo F.mod_pos
    rw [hrem, show -(a : ℤ) = x by rw [hax, abs_of_neg hneg]; ring] at hmod
    refine Ends.iteLast (fun hz => ?_) (fun hz => ?_)
    · have hz : r = 0 := by simpa using hz
      exact Ends.setTo 0 ⟨by rw [hmod, if_pos hz]; rfl, rfl⟩
    · have hz : ¬ r = 0 := by simpa using hz
      exact Ends.setTo ((Mo : ℤ) - r) ⟨by rw [hmod, if_neg hz]; rfl, rfl⟩
  · have hpos : 0 ≤ x := by simpa using hpos
    refine Ends.setTo (r : ℤ) ⟨?_, rfl⟩
    rw [← abs_of_nonneg hpos, ← hax, ← hrem]
    exact (Int.natCast_mod a Mo)

/-- **emod(x, M, fr)** returns the remainder of x modulo M and changes no cell below the free
pointer. -/
theorem _root_.Light.emod_meets {p : ℕ} (hp : P[p]? = some emodBody) (F : Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    Meets lim P p d [x, Mo, fr] μ (emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ Kept μ μ' fr := by
  have hword := F.word
  have hax : ((x.natAbs : ℕ) : ℤ) = |x| := Int.natCast_natAbs x
  have haV : x.natAbs ≤ V := by omega
  refine .of_body hp ?_
  unfold emodTime
  generalize x.natAbs = a at hax haV ⊢
  -- count := 0; mult := M; the table; the subtractions; the sign
  have tail : Ends lim P d (.set Count (k 0) ;; .set Mult (v Modulus) ;; emodTable ;;
      emodReduce ;; emodSign) ⟨frame [x, Mo, fr, a], μ⟩ (43 * emodRounds a Mo + 26) fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ Kept μ σ'.mem fr := by
    refine Ends.setToThen (0 : ℕ) (Ends.setToThen (Mo : ℕ) ?_)
    refine Ends.next _ ((table_ends F haV).mono le_rfl ?_)
    rintro _ ⟨μ', rfl, tab⟩
    refine Ends.next _ ((reduce_ends F haV tab).mono le_rfl ?_)
    rintro _ rfl
    exact (sign_ends F hax).mono (by light_time) fun σ' h =>
      ⟨h.1, fun b hb => by rw [h.2]; exact tab.2 b hb⟩
  -- rest := |x|
  refine Ends.iteThen (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    rw [abs_of_neg hneg] at hax
    exact Ends.setToThen (a : ℕ) (tail.mono (by light_time) fun _ h => h)
  · have hpos : 0 ≤ x := by simpa using hpos
    rw [abs_of_nonneg hpos] at hax
    exact Ends.setToThen (a : ℕ) (tail.mono (by light_time) fun _ h => h)

end Emod

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Logs.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Logs.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Logs.lean`, with imports remapped;
* v4.25 proof repair (beta: v4.25 leaves the loop rule's invariant applied to its round unreduced);
* v4.25 proof repair (beta: as above);
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs

/-- The local variables of the routines: the argument, which the result replaces, the candidate,
and a power of two. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Power : ℕ := 2

end Logs

open Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 2) ;;
  .while (v Power ≤' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of log2. -/
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12

/-- **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is. -/
theorem log2_meets {p x : ℕ} (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  refine .of_body hp ?_
  unfold log2Body log2Time
  -- L := 0; p := 2
  light_set 0
  light_set 2
  -- while p ≤ x.  Before round i, L = i and p = 2^(i + 1).
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ (i + 1) : ℕ)], μ⟩)
    (Nat.log 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hi
    have hle : 2 ^ (i + 1) ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 2 hx)
    have hix : i < x := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hle)
    beta_reduce
    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]
    generalize 2 ^ (i + 1) = q at hle
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ (Nat.log 2 x + 1) = q at hlt
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.log 2 x)
    exact ⟨rfl, rfl⟩

/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power <' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of clog2. -/
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10

/-- **clog2(x)** returns ⌈log₂ x⌉ and leaves the memory as it is. -/
theorem clog2_meets {p x : ℕ} (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ := by
  have hle : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  refine .of_body hp ?_
  unfold clog2Body clog2Time
  -- L := 0; p := 1
  light_set 0
  light_set 1
  -- while p < x.  Before round i, L = i and p = 2^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ i : ℕ)], μ⟩)
    (Nat.clog 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : 2 ^ i < x := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hix : i < x := lt_trans (Nat.lt_pow_self (by norm_num)) hlt
    beta_reduce
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    generalize 2 ^ i = q at hlt
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ Nat.clog 2 x = q at hle
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.clog 2 x)
    exact ⟨rfl, rfl⟩

/-! ## The cube root, rounded up -/

/-- Some cube is at least n. -/
theorem exists_le_cube (n : ℕ) : ∃ s, n ≤ s ^ 3 := ⟨n, Nat.le_self_pow (by norm_num) n⟩

/-- The least s with s³ ≥ n. -/
def cbrtLeast (n : ℕ) : ℕ := Nat.find (exists_le_cube n)

theorem le_cbrtLeast_pow (n : ℕ) : n ≤ cbrtLeast n ^ 3 := Nat.find_spec (exists_le_cube n)

theorem pow_lt_of_lt_cbrtLeast {n s : ℕ} (h : s < cbrtLeast n) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)

theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' (exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n :=
  cbrtLeast_le (Nat.le_self_pow (by norm_num) n)

/-- The number ⌈n^{1/3}⌉ is at least 1 for n ≥ 1. -/
theorem one_le_cbrtLeast {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by
  by_contra h
  have hpow := le_cbrtLeast_pow n
  rw [show cbrtLeast n = 0 by omega] at hpow
  omega

/-- The cube of the rounded cube root is at most 8 n. -/
theorem cbrtLeast_pow_le (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp [h]
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := ⟨cbrtLeast n - 1, by omega⟩
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast (by omega)
  rw [hs]
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    omega
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega

/-- The squares and cubes of the candidates fit in a word. -/
private theorem abs_cube_le {n i : ℕ} (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word)
    (hi : i ≤ cbrtLeast n) : |(i : ℤ) * i| ≤ lim.word ∧ |(i : ℤ) * i * i| ≤ lim.word := by
  have hcube : i * i * i ≤ 8 * n :=
    calc i * i * i = i ^ 3 := by ring
      _ ≤ cbrtLeast n ^ 3 := Nat.pow_le_pow_left hi 3
      _ ≤ 8 * n := cbrtLeast_pow_le n
  have hsquare : i * i ≤ i * i * i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    · exact Nat.le_mul_of_pos_right _ h
  have hcube' : (i : ℤ) * i * i ≤ 8 * n := by exact_mod_cast hcube
  have hsquare' : (i : ℤ) * i ≤ 8 * n := by exact_mod_cast hsquare.trans hcube
  have h2 : (0 : ℤ) ≤ (i : ℤ) * i := by positivity
  have h3 : (0 : ℤ) ≤ (i : ℤ) * i * i := by positivity
  push_cast at hword
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- cbrtCeil(n): the candidate is s. -/
def cbrtCeilBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand *' v Cand *' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of cbrtCeil. -/
@[simp] def cbrtCeilTime (n : ℕ) : ℕ := 12 * cbrtLeast n + 12

/-- **cbrtCeil(n)** returns the least s with s³ ≥ n and leaves the memory as it is. -/
theorem cbrtCeil_meets {p n : ℕ} (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ := by
  have hsn : cbrtLeast n ≤ n := cbrtLeast_le_self n
  refine .of_body hp ?_
  unfold cbrtCeilBody cbrtCeilTime
  -- s := 0
  light_set 0
  -- while s³ < n.  Before round i, s = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, i], μ⟩) (cbrtLeast n) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : (i : ℤ) * i * i < n := by
      have := pow_lt_of_lt_cbrtLeast hi
      rw [show i ^ 3 = i * i * i by ring] at this
      exact_mod_cast this
    -- The test is safe and holds.  s := s + 1 is safe and leads to the next state.
    exact ⟨by simpa using abs_cube_le hword hi.le, by simpa using hlt, by light_side,
      by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hle : (n : ℤ) ≤ (cbrtLeast n : ℤ) * cbrtLeast n * cbrtLeast n := by
      have := le_cbrtLeast_pow n
      rw [show cbrtLeast n ^ 3 = cbrtLeast n * cbrtLeast n * cbrtLeast n by ring] at this
      exact_mod_cast this
    refine ⟨by simpa using abs_cube_le hword le_rfl, by simpa using hle, ?_⟩
    -- the result is s
    light_set (cbrtLeast n)
    exact ⟨rfl, rfl⟩

/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand +' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of half. -/
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10

/-- **half(h)** returns ⌈h/2⌉ and leaves the memory as it is. -/
theorem half_meets {p h : ℕ} (hp : P[p]? = some halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [h] μ (halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by
  refine .of_body hp ?_
  unfold halfBody halfTime
  -- r := 0
  light_set 0
  -- while r + r < h.  Before round i, r = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [h, i], μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    -- The test is safe and holds.  r := r + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is r
    light_set ((h + 1) / 2 : ℕ)
    exact ⟨rfl, rfl⟩

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Merge.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Merge.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Merge.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Tactics

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}

theorem step_left (hi : i < l.length) (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [h]

theorem step_right (hi : i < l.length) (hj : j < r.length) (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [not_le.2 h]

theorem step_left_end (hi : i < l.length) (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_nil_of_le hj, List.merge_right, List.merge_right, List.drop_eq_getElem_cons hi]

theorem step_right_end (hi : l.length ≤ i) (hj : j < r.length) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_nil_of_le hi, List.nil_merge, List.nil_merge, List.drop_eq_getElem_cons hj]

end Merge

/-! ## The program -/

namespace Merge

/-- The local variables of merge: the arguments a, na, b, nb, dst, and the numbers i and j of cells
already taken from the first and the second list. -/
abbrev ListA : ℕ := 0
@[inherit_doc ListA] abbrev LenA : ℕ := 1
@[inherit_doc ListA] abbrev ListB : ℕ := 2
@[inherit_doc ListA] abbrev LenB : ℕ := 3
@[inherit_doc ListA] abbrev Dest : ℕ := 4
@[inherit_doc ListA] abbrev DoneA : ℕ := 5
@[inherit_doc ListA] abbrev DoneB : ℕ := 6

end Merge

open Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListA +' v DoneA)) ;;
  .set DoneA (v DoneA +' k 1)

open Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListB +' v DoneB)) ;;
  .set DoneB (v DoneB +' k 1)

open Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : Stmt :=
  .set DoneA (k 0) ;;
  .set DoneB (k 0) ;;
  .while (v DoneA +' v DoneB <' v LenA +' v LenB) (
    .ite (v DoneA <' v LenA)
      (.ite (v DoneB <' v LenB)
        (.ite (M (v ListB +' v DoneB) <' M (v ListA +' v DoneA)) mergeTakeRight mergeTakeLeft)
        mergeTakeLeft)
      mergeTakeRight)

namespace Merge

/-- What merge assumes: the two lists lie in the memory, and the output region is within the memory
and meets neither of them. -/
structure Pre (lim : Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : Seg μ a l
  segR : Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : Apart a l.length dst (l.length + r.length)
  sepR : Apart b r.length dst (l.length + r.length)

/-- The state after i cells of the first list and j cells of the second have been taken: they stand,
merged, in the first i + j cells of dst, and no cell outside dst has changed. -/
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r

/-- The invariant of the loop: t cells have been taken. -/
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ

variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

/-- dst[i + j] := a[i]; i := i + 1. -/
theorem takeLeft (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hi : i < l.length)
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, -, hj, same, hlen, seg, hout⟩ := h
  light_facts C
  have hread : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get hi)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by light_side [mergeTakeLeft], i + 1, j, by omega,
    Function.update μ' (dst + out.length) l[i], out ++ [l[i]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeLeft, update_frame_setLocal, haddr, hread]

/-- dst[i + j] := b[j]; j := j + 1. -/
theorem takeRight (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  light_facts C
  have hread : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get hj)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by light_side [mergeTakeRight], i, j + 1, by omega,
    Function.update μ' (dst + out.length) r[j], out ++ [r[j]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeRight, update_frame_setLocal, haddr, hread]

/-- The time of merge, for n = na + nb numbers. -/
@[simp] def _root_.Light.mergeTime (n : ℕ) : ℕ := 40 * n + 12

/-- **merge(a, na, b, nb, dst)** writes `List.merge` of the two lists to dst and changes nothing
else. -/
theorem _root_.Light.merge_meets {p : ℕ} (hp : P[p]? = some mergeBody)
    (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) := by
  light_facts C
  refine .of_body hp ?_
  unfold mergeTime
  -- i := 0; j := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while i + j < na + nb
  refine Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
    (by simp [mergeTakeLeft, mergeTakeRight]; omega)
  case start =>
    exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, by simp⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact ⟨by light_side, by simp; omega, by simpa [← hout] using seg, same⟩
  case round =>
    rintro _ σ ht ⟨i, j, rfl, hI⟩
    have left := takeLeft C hI
    have right := takeRight C hI
    obtain ⟨μ', out, rfl, hi, hj, same, -⟩ := hI
    refine ⟨by light_side, by simp; omega, ?_⟩
    -- The next output is the head of the first list unless the head of the second list is smaller.
    by_cases c1 : i < l.length
    · refine .ite_pos ?_
      by_cases c2 : j < r.length
      · have hreadL : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get c1)
        have hreadR : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (right c2 (step_right c1 c2 c3)) (by simpa [hreadL, hreadR] using c3)
        · exact .ite_neg (left c1 (step_left c1 c2 (not_lt.1 c3)))
            (by simpa [hreadL, hreadR] using c3)
      · exact .ite_neg (left c1 (step_left_end c1 (by omega)))
    · exact .ite_neg (right (by omega) (step_right_end (by omega) (by omega)))

end Merge

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/MergeSort.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/MergeSort.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/MergeSort.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* imports `TCSlib.Programs.Compat` for names that differ at our Mathlib pin;
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Copy
import TCSlib.Programs.Light.Lib.Logs
import TCSlib.Programs.Light.Lib.Merge
import TCSlib.Programs.Compat

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort

/-- The local variables of sort: the arguments n, a and fr; h = ⌈n/2⌉; and a local that takes the
results of the calls, which are not used. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Start : ℕ := 1
@[inherit_doc Len] abbrev Free : ℕ := 2
@[inherit_doc Len] abbrev Half : ℕ := 3
@[inherit_doc Len] abbrev Unused : ℕ := 4

end MergeSort

open MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : Stmt :=
  .call pMerge [v Start, v Half, v Start +' v Half, v Len -' v Half, v Free] Unused ;;
  .call pCopy [v Free, v Start, v Len] Unused

open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (
    .call pHalf [v Len] Half ;;
    .call pSort [v Half, v Start, v Free] Unused ;;
    .call pSort [v Len -' v Half, v Start +' v Half, v Free] Unused ;;
    sortJoin pMerge pCopy) .skip

/-- The time of sort. -/
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4

namespace MergeSort

/-- The recursion for n ⌈log₂ n⌉. -/
theorem clog_split {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
  have h2 : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hh : (n + 1) / 2 ≤ n := by omega
  rw [h1]
  generalize (n + 1) / 2 = h at *
  generalize Nat.clog 2 h = c at *
  have a1 : (n - h) * Nat.clog 2 (n - h) ≤ (n - h) * c := Nat.mul_le_mul_left _ h2
  have a2 : h * c + (n - h) * c = n * c := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have a3 : n * (c + 1) = n * c + n := by ring
  omega

/-- The program holds the four procedures. -/
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody

/-- The recursion for the number of steps. -/
theorem time_split {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega

/-- What sort leaves: a sorted permutation of the list L at a; of the cells below fr only those of
the list may have changed. -/
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length

/-- A list of at most one number is sorted. -/
theorem sorted_refl {μ : ℕ → ℤ} {a fr : ℕ} {L : List ℤ} (hseg : Seg μ a L) (hL : L.length ≤ 1) :
    Sorted μ a fr L μ := by
  refine ⟨⟨L, hseg, .refl _, ?_⟩, .refl⟩
  match L, hL with
  | [], _ => exact .nil
  | [x], _ => exact List.pairwise_singleton _ _

/-- The two halves are sorted one after the other, merged into the cells from fr, and copied
back. -/
theorem sorted_merge {μ μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {a fr h m : ℕ} {L S₁ S₂ : List ℤ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by
  refine ⟨⟨S₁.merge S₂, hS₄, ?_, hO₁.merge hO₂⟩, fun c hc => ?_⟩
  · calc (S₁.merge S₂).Perm (S₁ ++ S₂) := List.merge_perm_append _
      _ |>.Perm (L.take h ++ L.drop h) := hP₁.append hP₂
      _ = L := List.take_append_drop h L
  · have hl₁ : (L.take h).length = h := by simp; omega
    have hl₂ : (L.drop h).length = L.length - h := by simp
    have := hc.2
    rw [hk₄ c hc.2, hk₃ c (Or.inl hc.1), hk₂ c ⟨hc.1, by omega⟩, hk₁ c ⟨hc.1, by omega⟩]

variable {pSort pHalf pMerge pCopy : ℕ}

/-- Two lists, one after the other in the memory, are merged into the cells from fr and copied
back. -/
theorem join_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) {d a fr h n : ℕ} {r : ℤ} {S₁ S₂ : List ℤ} {μ : ℕ → ℤ}
    (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n) (hS₁ : Seg μ a S₁)
    (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧
        SameOutside μ' σ'.mem a n := by
  have hlm : (S₁.merge S₂).length = n := by rw [List.length_merge]; omega
  -- merge(a, h, a + h, n - h, fr)
  have hmerge := merge_meets (d := d + 1) C.merge (a := a) (b := a + h) (dst := fr) (l := S₁)
    (r := S₂) ⟨hw, hS₁, hS₂, by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  rw [hl₁, hl₂, show h + (n - h) = n by omega] at hmerge
  light_call hmerge with _ μ₁ ⟨hseg, hk₁⟩
  -- copy(fr, a, n)
  light_call (copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega)
    (by omega)) with _ μ₂ ⟨hcopy, hk₂⟩
  exact ⟨μ₁, hk₁, fun i hi => (hcopy i (by omega)).trans (hseg i hi), hk₂⟩

/-- The body of sort, given that the procedure sorts the lists of at most half the length, rounded
up. -/
theorem body_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {d a fr : ℕ} {L : List ℤ}
    {μ : ℕ → ℤ} (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space)
    (hd : d < lim.depth)
    (ih : ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ), 1 < L.length → 2 * L'.length ≤ L.length + 1 →
      Seg μ' a' L' → a' + L'.length ≤ fr →
      Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (sortTime L'.length) fun _ =>
        Sorted μ' a' fr L') :
    Ends lim P d (sortBody pSort pHalf pMerge pCopy) ⟨frame [L.length, a, fr], μ⟩
      (sortTime L.length) fun σ' => Sorted μ a fr L σ'.mem := by
  -- if 1 < n
  refine Ends.iteLast (fun hc => ?_) (fun hc => Ends.skip (sorted_refl hseg (by simpa using hc)))
    (hT := by simp [sortTime])
  have hn : 1 < L.length := by simpa using hc
  have htime := time_split hn
  have hhalf := half_meets (d := d + 1) C.half μ (h := L.length)
    (le_trans (by exact_mod_cast (by omega : L.length + 1 ≤ lim.space)) hw)
  have hlt : (L.length + 1) / 2 < L.length := by omega
  have hpos : 1 ≤ (L.length + 1) / 2 := by omega
  have htwice : 2 * ((L.length + 1) / 2) ≤ L.length + 1 := by omega
  have htwice' : L.length ≤ 2 * ((L.length + 1) / 2) := by omega
  generalize (L.length + 1) / 2 = h at *
  have hl₁ : (L.take h).length = h := by simp; omega
  have hl₂ : (L.drop h).length = L.length - h := by simp
  -- h := half(n)
  light_call hhalf with _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl : μ = μ₀ := hμ₀.symm
  -- sort(h, a, fr)
  have hsort₁ := ih a (L.take h) μ hn (by omega) (hseg.take h) (by omega)
  rw [hl₁] at hsort₁
  light_call hsort₁ with _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩
  have hseg₂ : Seg μ₁ (a + h) (L.drop h) :=
    (hseg.drop h).congr fun i hi => hk₁ _ ⟨by omega, Or.inr (by omega)⟩
  -- sort(n - h, a + h, fr)
  have hsort₂ := ih (a + h) (L.drop h) μ₁ hn (by omega) hseg₂ (by omega)
  rw [hl₂] at hsort₂
  light_call hsort₂ with _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩
  have hlS₁ := hP₁.length_eq
  have hS₁' : Seg μ₂ a S₁ := hS₁.congr fun i hi => hk₂ _ ⟨by omega, Or.inl (by omega)⟩
  -- merge and copy
  refine (join_ends C hw (hP₁.length_eq.trans hl₁) (hP₂.length_eq.trans hl₂) hlt.le hn.le hS₁' hS₂
    haf hfr hd).mono (by light_time) ?_
  rintro _ ⟨μ₃, hk₃, hS₄, hk₄⟩
  exact sorted_merge hlt.le hP₁ hO₁ hk₁ hP₂ hO₂ hk₂ hk₃ hS₄ hk₄

/-- **sort(n, a, fr)** leaves a sorted permutation of the list at a.  Of the cells below fr only the
n cells from a may change; the n cells from fr are used. -/
theorem _root_.Light.sort_meets (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by
  induction hn : L.length using Nat.strong_induction_on generalizing a L μ with
  | _ n ih =>
    subst hn
    intro d hd
    refine Meets.of_body C.sort (body_ends C hw h1 hseg haf hfr (by omega)
      fun a' L' μ' hn hhalf hseg' haf' =>
        ih L'.length (by omega) hseg' haf' (by omega) rfl (d + 1) ?_)
    -- one level of calls fewer for half the length
    have hclog : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
      simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
    have := Nat.clog_mono_right 2 (by omega : L'.length ≤ (L.length + 1) / 2)
    omega

end MergeSort

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/NextPair.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/NextPair.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/NextPair.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Frames
import TCSlib.Programs.Util.Index

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- b := b + 1; if b = n then b := 0; a := a + 1.  The locals A, B and N hold a, b and n. -/
def nextPair (A B N : ℕ) : Stmt :=
  .set B (v B +' k 1) ;; .ite (v B =' v N) (.set B (k 0) ;; .set A (v A +' k 1)) .skip

/-- **From the pair number t to the pair number t + 1.** -/
theorem Ends.nextPair {A B N n t T : ℕ} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop}
    (h : Q ⟨frame (setLocal (setLocal l B ((t + 1) % n : ℕ)) A ((t + 1) / n : ℕ)), μ⟩)
    (hn : 0 < n) (ht : ((t + 1 : ℕ) : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word)
    (hA : frame l A = (t / n : ℕ)) (hB : frame l B = (t % n : ℕ)) (hN : frame l N = n)
    (hAB : A ≠ B := by decide) (hBN : N ≠ B := by decide) (hT : 14 ≤ T := by light_time) :
    Ends lim P d (nextPair A B N) ⟨frame l, μ⟩ T Q := by
  have hmod := Nat.mod_lt t hn
  have hdiv := Nat.div_le_self t n
  have hlast := Nat.succ_div_mod_of_eq (n := n) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (i := t) hn
  generalize t / n = a at *
  generalize t % n = b at *
  -- b := b + 1
  refine Ends.setToThen (b + 1 : ℕ) ?_ (by light_norm [Expr.Gives, hB, abs_le]; omega)
    (by simp; omega)
  -- if b = n then b := 0; a := a + 1
  refine Ends.iteLast (fun he => ?_) (fun he => ?_) ⟨trivial, trivial⟩ (by simp; omega)
  · have he : b + 1 = n := by
      have : ((b + 1 : ℕ) : ℤ) = n := by
        simpa only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN] using he
      exact_mod_cast this
    rw [(hlast he).1, (hlast he).2] at h
    refine Ends.setToThen (0 : ℕ) (Ends.setTo (a + 1 : ℕ) ?_
      (by light_norm [Expr.Gives, frame_setLocal, if_neg hAB, hA, abs_le]; omega)
      (by simp; omega)) (by light_norm [Expr.Gives]; omega) (by simp; omega)
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs <;> rfl
  · have he : b + 1 ≠ n := fun e => he (by
      simp only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN]
      exact_mod_cast e)
    rw [(hinner he).1, (hinner he).2] at h
    refine Ends.skip ?_
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) hAB
    · rfl
    · rw [h2, hA]
    · rfl

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Odometer.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Odometer.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Odometer.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Tactics
import TCSlib.Programs.Util.Odometer

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An odometer in the memory

`incStmt vb vn j len` adds 1 to the number whose len digits in base n, least significant first, are
in the cells base + j, base + j + 1, …; a carry out of the last digit is dropped (`incStmt_ends`).
Local vb holds base and local vn holds n.  The number of digits is known when the program is
written, so the statement has no loop: it is a chain of len tests, and the proof is an induction on
the list of the digits.  The pure model is `Light.incDigits`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Add 1 to the number with the digits at base + j, …, base + j + len - 1. -/
def incStmt (vb vn : ℕ) : ℕ → ℕ → Stmt
  | _, 0 => .skip
  | j, len + 1 =>
    .ite (M (v vb +' k j) +' k 1 <' v vn)
      (.store (v vb +' k j) (M (v vb +' k j) +' k 1))
      (.store (v vb +' k j) (k 0) ;; incStmt vb vn (j + 1) len)

/-- **incStmt** replaces the digits l by `Light.incDigits n l`, changes nothing else, and
takes at
most 14 len + 5 steps. -/
theorem incStmt_ends {vb vn base n j : ℕ} {l : List ℕ} {μ loc : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : (n : ℤ) ≤ lim.word) (eb : loc vb = base)
    (en : loc vn = n) (hspace : base + j + l.length ≤ lim.space) (hlt : ∀ x ∈ l, x < n)
    (hseg : SegN μ (base + j) l) :
    Ends lim P d (incStmt vb vn j l.length) ⟨loc, μ⟩ (14 * l.length + 5) fun σ' =>
      σ'.loc = loc ∧ SegN σ'.mem (base + j) (Light.incDigits n l) ∧
      SameOutside μ σ'.mem (base + j) l.length := by
  induction l generalizing j μ with
  | nil => exact Ends.skip ⟨rfl, by simpa [Light.incDigits] using hseg, .refl⟩
  | cons x l ih =>
    simp only [List.length_cons] at hspace ⊢
    have hx : x < n := hlt x (by simp)
    obtain ⟨hread, hrest⟩ : μ (base + j) = x ∧ SegN μ (base + j + 1) l := seg_cons.1 hseg
    have haddr : ((base : ℤ) + j).toNat = base + j := by omega
    rw [incStmt, Light.incDigits]
    -- if digit + 1 < n
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
      (by light_side [eb, haddr, hread])
    · have hc' : x + 1 < n := by
        have : (x : ℤ) + 1 < n := by simpa [eb, en, haddr, hread] using hc
        omega
      rw [if_pos hc']
      -- digit := digit + 1
      refine Ends.storeLast ⟨rfl, ?_, ?_⟩ (by light_side [eb, haddr, hread])
      · simp only [Expr.val, Op.eval, eb, haddr, hread]
        exact seg_cons.2 ⟨by simp, hrest.update_out (Or.inl (by omega)) _⟩
      · simp only [Expr.val, Op.eval, eb, haddr]
        exact SameOutside.refl.update ⟨le_rfl, by omega⟩ _
    · have hc' : ¬ x + 1 < n := fun h =>
        hc (by simpa [eb, en, haddr, hread] using (by omega : (x : ℤ) + 1 < n))
      rw [if_neg hc']
      -- digit := 0, and the carry goes to the next digit
      refine Ends.storeThen ?_ (by light_side [eb])
      simp only [Expr.val, Op.eval, eb, haddr]
      light_piece (ih (j := j + 1) (by omega) (fun y hy => hlt y (by simp [hy]))
        (hrest.update_out (Or.inl (by omega)) _)) with σ' ⟨hloc, hseg', hsame⟩
      refine ⟨hloc, seg_cons.2 ⟨?_, hseg'⟩, fun b hb => ?_⟩
      · rw [hsame _ (Or.inl (by omega))]
        simp
      · rw [hsame b (by omega), Function.update_of_ne (by omega)]

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

## ===== TCSlib/Programs/Light/Lib/PowTable.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/PowTable.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/PowTable.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Tactics
import Mathlib.Data.Int.SuccPred

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The pure model: the powers 1, b, …, b^(L-1). -/
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)

@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable

/-- The local variables of powTable: the arguments dst, L and b, the exponent j, and the power b^j.
-/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Len : ℕ := 1
@[inherit_doc Dest] abbrev Base : ℕ := 2
@[inherit_doc Dest] abbrev Expo : ℕ := 3
@[inherit_doc Dest] abbrev Power : ℕ := 4

end PowTable

open PowTable

/-- One round: dst[j] := p; p := p * b. -/
def powTableRound : Stmt :=
  .store (v Dest +' v Expo) (v Power) ;;
  .set Power (v Power *' v Base)

/-- powTable(dst, L, b): p := 1; for j < L: dst[j] := p; p := p * b. -/
def powTableBody : Stmt :=
  .set Power (k 1) ;;
  .for Expo (v Len) powTableRound

/-- The time of powTable. -/
def powTableTime (L : ℕ) : ℕ := 17 * L + 8

/-- The state before round j: p = b^j, the first j cells hold the powers up to b^(j-1), and no cell
outside the L cells from dst has changed.  The list t holds the local variables after the five of
powTable. -/
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L

/-- The body of powTable writes the powers of b and changes nothing else, whatever its local
variables hold apart from the three arguments. -/
theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
  light_set 1
  -- for j < L
  refine Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound
    (hT := by light_time [powTableRound])
  case start => exact ⟨μ, by simp [update_frame_setLocal], fun i hi => absurd hi (by omega), .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by rw [getElem_powList]; exact powers i (by simpa using hi), same⟩
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have hfits : (b : ℤ) ^ (j + 1) ≤ lim.word := by exact_mod_cast hpow (j + 1) (by omega)
    have hnonneg : 0 ≤ (b : ℤ) ^ (j + 1) := by positivity
    unfold powTableRound
    -- dst[j] := p
    light_store (dst + j) (b ^ j : ℕ)
    -- p := p * b
    light_set (b ^ (j + 1) : ℕ) using ← pow_succ
    refine ⟨by simp, Function.update μ' (dst + j) (b ^ j : ℕ), by simp [update_frame_setLocal],
      fun i hi => ?_, by light_keep⟩
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
    · rw [Function.update_of_ne (by omega)]
      exact powers i hi
    · exact Function.update_self ..

/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  .of_body hp (frame_append_zeros [(dst : ℤ), L, b] 2 ▸ powTable_ends 0 0 [] hw hdst hpow)

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/RadixPass.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/RadixPass.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/RadixPass.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Lib.Copy
import TCSlib.Programs.Light.Lib.CountSort
import TCSlib.Programs.Util.StablePass

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One pass of a radix sort on a list of indices

The pass sorts the list of indices at perm stably by a key that is read through the index: countSort
writes the sorted list into the w cells after the list, and copy brings it back.  What countSort
leaves is the result of a stable pass on lists (`exists_stablePass`), and `radixPass_ends` puts the
two calls together.  The pass is used with different expressions for the place of the keys, so these
are parameters.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

open Light

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- What countSort leaves at dst is a list, and it is the result of a stable pass. -/
theorem exists_stablePass {μ' : ℕ → ℤ} {dst : ℕ} {π : List ℕ} {kd : ℕ → ℕ}
    (h : ∀ j (hj : j < π.length), μ' (dst + sortPos (keyAt kd π) π.length j) = (π[j] : ℤ)) :
    ∃ π', IsStablePass kd π π' ∧ SegN μ' dst π' := by
  refine ⟨(readSeg μ' dst π.length).map Int.toNat, ⟨by simp, fun j hj => ?_⟩, fun q hq => ?_⟩
  · have hp := sortPos_lt (keyAt kd π) hj
    rw [List.getD_eq_getElem _ _ (by simpa using hp)]
    simp [h j hj]
  · have hq' : q < π.length := by simpa using hq
    obtain ⟨j, hj, rfl⟩ := exists_sortPos_eq (keyAt kd π) hq'
    simp [h j hj]

namespace RadixPass

/-- The local variables that the pass uses: w, perm, and a local that takes the results of the two
calls, which are not used. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Perm : ℕ := 5
@[inherit_doc Num] abbrev Unused : ℕ := 7

/-- The pass: procedure pc is countSort, procedure pp is copy. -/
def _root_.Light.radixPass (pc pp : ℕ) (ekey estride eoff enb ecnt : Expr) : Stmt :=
  .call pc [v Num, v Perm, v Perm +' v Num, ekey, estride, eoff, enb, ecnt] Unused ;;
  .call pp [v Perm +' v Num, v Perm, v Num] Unused

/-- Where the data of a pass lie. -/
structure Args where
  /-- the number of indices -/
  w : ℕ
  /-- where the list of indices stands; the w cells after it are scratch space -/
  perm : ℕ
  /-- the key of the index i is in the cell key + i · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells for the counters -/
  cnt : ℕ
  /-- only the R cells from perm on may change -/
  R : ℕ

/-- The arguments of the call of countSort. -/
abbrev Args.sort (A : Args) : CountSort.Args :=
  ⟨A.w, A.perm, A.perm + A.w, A.key, A.stride, A.off, A.nb, A.cnt⟩

end RadixPass

/-- What a pass assumes: the list π of indices below w stands at perm, the keys lie before the list,
and the counters after the list and its scratch space, within the R cells that may change. -/
structure RadixPass.Pre (lim : Limits) (μ : ℕ → ℤ) (A : RadixPass.Args) (π : List ℕ)
    (kd : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  len : π.length = A.w
  lt : ∀ i ∈ π, i < A.w
  seg : SegN μ A.perm π
  keyBefore : ∀ i < A.w, A.key + i * A.stride + A.off < A.perm
  keys : ∀ i < A.w, μ (A.key + i * A.stride + A.off) = kd i
  keyLt : ∀ i < A.w, kd i < A.nb
  cntAfter : A.perm + 2 * A.w ≤ A.cnt
  cntIn : A.cnt + (A.nb + 1) ≤ A.perm + A.R
  space : A.perm + A.R ≤ lim.space

/-- What a pass achieves: the list at perm is the result of a stable pass by the key kd, cnt[t] is
the number of indices with a key below t, and only the R cells from perm on have changed. -/
structure RadixPass.Post (μ : ℕ → ℤ) (A : RadixPass.Args) (π : List ℕ) (kd : ℕ → ℕ)
    (μ' : ℕ → ℤ) : Prop where
  same : SameOutside μ μ' A.perm A.R
  starts : ∀ t ≤ A.nb, μ' (A.cnt + t) = cntLt (keyAt kd π) t A.w
  sorted : ∃ π', IsStablePass kd π π' ∧ SegN μ' A.perm π'

variable {μ : ℕ → ℤ} {A : RadixPass.Args} {π : List ℕ} {kd : ℕ → ℕ}

/-- What countSort assumes holds for the pass: the items are the list at perm, and they go to the w
cells after it. -/
theorem RadixPass.Pre.sort (pre : RadixPass.Pre lim μ A π kd) :
    CountSort.Pre lim μ A.sort (fun j => π.getD j 0) (keyAt kd π) := by
  obtain ⟨hw, len, lt, seg, keyBefore, keys, keyLt, cntAfter, cntIn, space⟩ := pre
  have hit : ∀ i < A.w, π.getD i 0 < A.w := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact lt _ (List.getElem_mem _)
  have hbefore : ∀ i < A.w, A.key + π.getD i 0 * A.stride + A.off < A.perm :=
    fun i hi => keyBefore _ (hit i hi)
  exact
    { hw := hw
      srcB := by dsimp only; omega
      dstB := by dsimp only; omega
      cntB := by dsimp only; omega
      items := fun i hi => seg.read (by dsimp only at hi; omega)
      keyB := fun i hi => (hbefore i hi).trans_le (by omega)
      keys := fun i hi => keys _ (hit i hi)
      keyLt := fun i hi => keyLt _ (hit i hi)
      srcDst := Or.inl le_rfl
      srcCnt := Or.inl (by dsimp only; omega)
      dstCnt := Or.inl (by dsimp only; omega)
      keyDst := fun i hi => Or.inl ((hbefore i hi).trans_le (by dsimp only; omega))
      keyCnt := fun i hi => Or.inl ((hbefore i hi).trans_le (by dsimp only; omega)) }

/-- The memory after countSort (μ₁) and after the copy (μ₂). -/
theorem RadixPass.Post.of_sorted_copied {μ₁ μ₂ : ℕ → ℤ} (pre : RadixPass.Pre lim μ A π kd)
    (sorted : CountSort.Post μ A.sort (fun j => π.getD j 0) (keyAt kd π) μ₁)
    (copied : ∀ i < A.w, μ₂ (A.perm + i) = μ₁ (A.perm + A.w + i))
    (same₂ : SameOutside μ₁ μ₂ A.perm A.w) : RadixPass.Post μ A π kd μ₂ := by
  obtain ⟨placed, starts, (same₁ : SameOutside2 μ μ₁ (A.perm + A.w) A.w A.cnt (A.nb + 1))⟩ := sorted
  dsimp only at placed starts
  have len := pre.len
  light_facts pre
  refine ⟨fun b hb => (same₂ b (by omega)).trans (same₁ b ⟨by omega, by omega⟩),
    fun t ht => (same₂ (A.cnt + t) (by omega)).trans (starts t ht), ?_⟩
  -- What stands after the list is the result of a stable pass, and it has been copied back.
  obtain ⟨π', stable, seg⟩ := exists_stablePass (μ' := μ₁) (dst := A.perm + A.w) (π := π)
    fun j hj => by rw [len, placed j (by omega), List.getD_eq_getElem _ _ hj]
  have len' : π'.length = π.length := stable.1
  refine ⟨π', stable, fun i hi => ?_⟩
  rw [← seg i hi]
  exact copied i (by simpa [len', len] using hi)

/-- **pass**: the list π of indices at perm is replaced by the result of a stable pass by the key
kd.  The five expressions give the place of the keys, the number of buckets and the place of the
counters.  Of the local variables only `Unused` changes. -/
theorem radixPass_ends {pc pp T : ℕ} {ekey estride eoff enb ecnt : Expr} {loc : ℕ → ℤ}
    (hpc : P[pc]? = some countSortBody) (hpp : P[pp]? = some copyBody)
    (pre : RadixPass.Pre lim μ A π kd)
    (hlen : loc RadixPass.Num = A.w := by light_side)
    (hperm : loc RadixPass.Perm = A.perm := by light_side)
    (hkey : ekey.Gives lim ⟨loc, μ⟩ A.key := by light_side)
    (hstride : estride.Gives lim ⟨loc, μ⟩ A.stride := by light_side)
    (hoff : eoff.Gives lim ⟨loc, μ⟩ A.off := by light_side)
    (hnb : enb.Gives lim ⟨loc, μ⟩ A.nb := by light_side)
    (hcnt : ecnt.Gives lim ⟨loc, μ⟩ A.cnt := by light_side)
    (hd : d < lim.depth := by omega)
    (hT : 84 * A.w + 58 * A.nb + 72 +
      (ekey.cost + estride.cost + eoff.cost + enb.cost + ecnt.cost) ≤ T := by light_time) :
    Ends lim P d (radixPass pc pp ekey estride eoff enb ecnt) ⟨loc, μ⟩ T fun σ' =>
      (∃ r, σ'.loc = Function.update loc RadixPass.Unused r) ∧ RadixPass.Post μ A π kd σ'.mem := by
  have hw := pre.hw
  light_facts pre
  -- countSort(w, perm, perm + w, key, stride, off, nb, cnt)
  refine Ends.callThen (countSort_meets hpc pre.sort) ?_
    (by simp [abs_le, hlen, hperm, hkey.1, hkey.2, hstride.1, hstride.2, hoff.1, hoff.2, hnb.1,
      hnb.2, hcnt.1, hcnt.2]; omega) hd (by simp; omega)
  intro _ μ₁ sorted
  -- copy(perm + w, perm, w)
  refine Ends.callLast (copy_meets (src := A.perm + A.w) (dst := A.perm) (n := A.w) hpp hw
    (hsrc := by omega) (hdst := by omega) (hsep := Or.inr le_rfl)) ?_
    (by light_side [hlen, hperm]) hd (by simp; omega)
  rintro r μ₂ ⟨copied, same₂⟩
  exact ⟨⟨r, by simp⟩, .of_sorted_copied pre sorted copied same₂⟩

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Seg.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Seg.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Seg.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Logic
import TCSlib.Programs.Light.Regions
import TCSlib.Programs.Util.Index
import TCSlib.Programs.Util.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

open Light

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The list held by the n cells from address a. -/
def readSeg (μ : ℕ → ℤ) (a n : ℕ) : List ℤ := (List.range n).map fun i => μ (a + i)

variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

@[simp] theorem length_readSeg : (readSeg μ a n).length = n := by simp [readSeg]

@[simp] theorem getElem_readSeg {i : ℕ} (h : i < (readSeg μ a n).length) :
    (readSeg μ a n)[i] = μ (a + i) := by
  simp [readSeg]

theorem getD_readSeg {i : ℕ} (hi : i < n) : (readSeg μ a n).getD i 0 = μ (a + i) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), getElem_readSeg]

theorem seg_readSeg : Seg μ a (readSeg μ a n) := fun i h => by simp

@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi

/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

/-- A segment determines its list. -/
theorem Seg.eq_readSeg (h : Seg μ a l) : l = readSeg μ a l.length :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by rw [getElem_readSeg, h i h₁]

theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by light_keep) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

/-- Writing into a segment. -/
theorem Seg.update_in (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  have hj' : j < l.length := by simpa using hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h j hj']

/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

theorem SameOutside2.refl {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl

/-- Writing into one of the two regions. -/
theorem SameOutside2.update {m c : ℕ} (h : SameOutside2 μ μ' a n b m)
    (hc : (a ≤ c ∧ c < a + n) ∨ (b ≤ c ∧ c < b + m)) (x : ℤ) :
    SameOutside2 μ (Function.update μ' c x) a n b m :=
  h.write (by omega) x

/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)

/-- One more entry of a list of natural numbers is written behind its first k entries. -/
theorem SegN.take_succ {l : List ℕ} {k : ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  rwa [List.length_take, Nat.min_eq_left hk.le, ← List.take_succ_getD l hk 0] at hsnoc

/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by light_keep) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)

/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)

/-- The cells from a on hold the matrix A, row by row. -/
def MatAt {n k : ℕ} (μ : ℕ → ℤ) (a : ℕ) (A : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.keep {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hs : SameOn (Inside a (n * k)) μ μ' := by light_keep) : MatAt μ' a A :=
  h.congr fun b h₁ h₂ => hs b ⟨h₁, h₂⟩

/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)

/-- The cells from a on hold the indices I 0, I 1, …. -/
def VecAt {t n : ℕ} (μ : ℕ → ℤ) (a : ℕ) (I : Fin t → Fin n) : Prop :=
  ∀ k : Fin t, μ (a + k.val) = ((I k).val : ℤ)

/-- A vector of indices that has been written as a list. -/
theorem vecAt_of_seg {t n : ℕ} {I : Fin t → Fin n}
    (h : Seg μ a (List.ofFn fun k => ((I k).val : ℤ))) : VecAt μ a I := fun k => by
  rw [h k.val (by simp)]
  simp

/-- A vector of indices stays where it is if its cells do not change. -/
theorem VecAt.keep {t n : ℕ} {I : Fin t → Fin n} (h : VecAt μ a I)
    (hs : SameOn (Inside a t) μ μ' := by light_keep) : VecAt μ' a I :=
  fun k => (hs _ ⟨by omega, by omega⟩).trans (h k)

end Light
end
```

## ===== TCSlib/Programs/Light/Lib/Sqrt.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Lib/Sqrt.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Lib/Sqrt.lean`, with imports remapped;
* v4.25 proof repair (beta: loop invariant applied to its round);
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Tactics
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt

/-- The local variables of sqrt: the argument K, which the result replaces, the candidate k, and the
square (k + 1)². -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Square : ℕ := 2

end Sqrt

open Sqrt in
/-- sqrt(K). -/
def sqrtBody : Stmt :=
  .set Cand (k 0) ;;
  .set Square (k 1) ;;
  .while (v Square ≤' v Arg) (
    .set Square (v Square +' k 2 *' v Cand +' k 3) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of sqrt. -/
@[simp] def sqrtTime (K : ℕ) : ℕ := 18 * Nat.sqrt K + 12

/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  -- k := 0; sq := 1
  light_set 0
  light_set 1
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    beta_reduce
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is k
    light_set (Nat.sqrt K)
    exact ⟨rfl, rfl⟩

end Light
end
```
