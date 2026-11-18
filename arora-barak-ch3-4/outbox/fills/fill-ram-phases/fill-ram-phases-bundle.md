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

## ===== campaign/items/ram-tm/briefs/fill-ram-phases.md =====

# RAM fill (Codex), tier 2 job D: the instruction phases (`Sim/Phases`, 2 admissions)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-phases`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/Sim/Phases.lean` states one phase per instruction of the
extended word RAM (`WordRAM.XInstr`, `Programs/WordRAM/Extended`). A phase is a machine on the
eight tapes of `WordRAM.Sim.Encodes` (`Sim/Encoding`). From tapes encoding `c`, whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep P x ρ c`, and
exits at `next` or `jump`. **This job proves the two statements:**
1. **`WordRAM.Sim.exists_phase`** (every non-verdict instruction): a nondeterministic machine
   whose two transitions differ only at a `coin` phase's entry, which is never re-entered. Its
   run is stated for each fixed choice `b` (`Turing.NDTM.fixChoice`), within
   `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
   `C·((|T| + 1)·(W + 1) + log |x| + 1)`.
2. **`WordRAM.Sim.exists_verdictPhase`**: in verdict mode emit `v`, then halt.

Job E builds the phase host and the induction from these. Gate 162's auditor checked both
(G162-21, G162-22).

## Route

**Build each phase from the rows, by cases on `ins`.** Place five-tape rows on the eight tapes
with `Turing.Contract.embed` (`Build/Contract/Embed`) or `Turing.embedEmitTM`. Turn
`ReachesWithin` rows into contracts with `Turing.Contract.ofReaches`, and sequence them with
`Turing.Contract.seq` (`Build/Contract/Seam`).
- **Key of a written address `i`:** `Turing.exists_wordIntTM i a` into tape `1`.
- **Key of a computed address `[j]`:** look `j` up into a register, then
  `Turing.exists_wordSignExtendTM a` into tape `1`.
- **Operands** are looked up into registers `2` and `3` (`Turing.exists_keyLookupTM`). The result
  is computed into register `4` and stored back (`Turing.exists_keyAssignTM`).

| Instruction | Compute |
|---|---|
| `one i` | `exists_wordIntTM 1 0` |
| `add`, `sub`, `mul` | `exists_wordAddTM`, `exists_wordSubTM`, `exists_wordMulTM` |
| `load i j` | look up `[j]`, sign-extend it to a key, look that up |
| `store i j` | look up `[i]`, sign-extend it as the key, assign `[j]` |
| `half i j` | `exists_wordHalfTM` |
| `rdIn i j` | look up `[j]`, then `Turing.exists_inputBitTM` (with tape `5`) |
| `bltz i l` | look up `[i]`, `Turing.exists_wordSignTM`, exit at `jump` or `next` |
| `emit i` | look up `[i]`, `Turing.exists_wordNonzeroTM`; in function mode emit the bit in one step (in verdict mode, nothing) |
| `coin i` | one choice step at the entry: transition `b` remembers `b` in the state; then `exists_wordIntTM b 0` into register `4`, and assign |

The semantics come through `WordRAM.xstep_def`, `WordRAM.effect_def`, `WordRAM.inBitWord_def`,
`WordRAM.coinWord_def` and `WordRAM.XInstr.touches_def`, never by unfolding.

**The invariant.** `TableOf` is kept because:
- every key written is that of a cell of `T ∪ touches` in range: `ImmBound` for written
  addresses, and a word's signed value is in range (`WordRAM.toInt_wd` and the range lemmas of
  `Programs/WordRAM/Steps`);
- keys of distinct cells in range are distinct (`bvBits_injective`, and `BitVec.ofInt` injective
  on the range).

Lookups are correct for every read. Write these as lemmas once, about `TableOf`, `keyLookup` and
`keyAssign`, in a new file (below), and use them in every case.

**Nondeterminism.** Build each phase as a deterministic machine, made an `NDTM` by
`MultiTapeTM.toNDTM` (equal transitions). The coin phase is the exception: a fresh entry state
whose transitions under `false` and `true` go to two deterministic continuations. Its
`fixChoice b` is then the continuation for `b`, prefixed by one step. Make the entry a state that
no transition targets.

**Bounds.** The table has at most `|T|` entries of `O(W + a)` cells, so every lookup and
assignment costs `O((|T| + 1)·(W + 1))`. `mul` adds `O(W²)`; `rdIn` adds `O(W + |x|)` steps and
`O(W + log |x|)` radius. `C` depends on `a` and `ins`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/Sim/Phases.lean`: the two statements, byte-identical.
- **New files** under `TCSlib/Complexity/RAMSimulation/Sim/`, named `Phase*.lean` (for example
  `PhaseTable.lean` for the `TableOf` lemmas and `PhaseRows.lean` for the placed rows). Their
  declarations are public in `WordRAM.Sim`, per the tier 2 addendum. `Phases.lean` imports them.
  Add each to the `RAMSimulation.lean` facade's imports and contents: you may edit the facade
  for that only.

## Admitted dependencies allowed

The statements of `Build/WordArith` (job A), `Build/KeyTable` (job B) and `Build/InputBit` (job C).
Nothing else.

## Downstream check

`RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facades.

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

## ===== campaign/items/ram-tm/TIER2-DESIGN.md =====

# Tier 2 design note: the word RAM on Turing machines (`exists_simulation`, `exists_ndSimulation`)

2026-11-18 (maintainer, at Seyoon's request). Base: `complexity/ram-simulation` after #371
(`adb694d2`; snapshot `oleans-cl161-cl160`). **Seyoon ruled on D1–D5 the same day** (§6). The jobs
are §5's regrouped table.

## 1. What is left, and what the statements ask

After #371 the RAM work has 11 admissions: `Simulation` 2 (this tier) and `Classes` 9 (tier 3,
dispatched). The two targets were gated on 2026-10-14 and are frozen. The re-read of
2026-11-18 found them sound. It checked word size `W = 0`, the immediate addresses, the range
of `rdIn`, `HaltsWithin`'s `n < t` and the matching of choice words to coin streams both ways.

The proof builds one machine, `M : FinTM Bool`, depending on `P` and `fn` only. Per input
`x`, with `n = |x|` and `W = W n`:

- **Time:** `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`. `ComputesInTime` means halted by then,
  with exactly `outputOf fn v o` on the output.
- **Space:** `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells. The input and output tapes
  do not count, so the input must be read in place.
- **Nondeterministic form:** the same machine, with each `coin` a choice step. Bounds are
  uniform over branches. A branch is accepting when its output is `[true]`
  (`FinNDTM.AcceptsWithin`).

## 2. What the library already gives (surveys of 2026-11-18)

All of these are public and proved unless marked otherwise.

| Need | Exists | Gap |
|---|---|---|
| Composition | `Turing.Contract` (exact time, endpoint, no earlier exit, head envelopes), `trans`, `seq` (seams), `inPhase` (phase host), `branch`, `embed`, `mapState`, counter-loop rounds | `inPhase` cannot redirect a phase to itself and cannot end in a halt (see §4) |
| Dispatch on the program counter | `phaseHostTM` (`Build/Seam.lean:886`) with its run lemmas | no space lemmas; space comes from contract envelopes |
| Nondeterministic dispatch | `NDTM.phaseHostND` and `phaseHostND_fixChoice` (`Build/NDHost.lean`): the host of fixed-choice phases *is* `phaseHostTM` | none |
| Choice slices | `runWith_eq_fixChoice_runFrom`, `spaceUsedWith_eq_fixChoice_spaceUsed`, `runWith_mapState_of_agreeOn(_det)`; the NARM compiler's `ndtm_runWith_eq_runFrom` (PATH ∈ NL): choice at `choose` states only, deterministic elsewhere | none; the NARM proof is the template for the coin phase |
| Word size start-up | `embedSilentTM` (output captured on a work tape), `expandTM` (binary `W` to a unary ruler of `W` cells), `exists_inputLengthTM` (`Nat.bits n` in `O(n)`) | the start-up composite |
| Input | `exists_inputSeekTM` (seek position `p ≤ n + 1` in `C·(|w| + pos + p + 1)`, scratch tape blank, restores the work tapes) | the range test `p < n` before it; contract wrappers (the row states `∃ t ≤ …`, contracts need an exact time) |
| Word rows | `copyTM`, `compareTM` (equality), `clearTM`, increment and decrement, `scanTM` (one-tape finite-state transducer: sign, shift, negation as instances), `writeConstTM`, the seek, skip and walk family | **no two-tape row with a carry** (add, subtract, less-than); **no multiplication** |
| The memory table | `RecordTable`'s layout (`tableFields`, `TableAt`, `TableWF`) and `exists_fieldsCopyTM` | **no keyed find** (the key on another tape), **no in-place overwrite**. `exists_tableFindTM` (finite-state predicate, not keyed) and `exists_tableAppendTM` are **admitted** on `main`, and tier 2 must not cite them |
| Output | any action may emit one bit | a one-step `emit` phase and the final "write `[v]`, halt" phase (trivial) |

## 3. The construction

**Tapes** (a fixed number, independent of `W`):
- the word-size machine's tapes, frozen after start-up (`SW n`);
- the ruler, `W` cells;
- the length tape, `Nat.bits n`;
- the table;
- three word registers: two operands and the result;
- a multiplication accumulator;
- the seek scratch tape, kept blank;
- the output, used only in function mode.

**Encoding:**
- *Words* are `W`-bit little-endian two's complement, measured against the ruler. A
  ruler-bounded lockstep scan handles `W = 0` (zero cells), where blank-delimited fields would
  not.
- *Keys* are addresses sign-extended to width `W + a`, where `a` covers `P`'s immediate
  addresses. So an immediate address and an equal computed address get the same key.
- *An entry* is the key, then the value, each with a leading marker bit, so that no field is
  empty and the table's end is a blank.
- *The invariant:* the tapes encode `XCfg` `c` when the phase is `c.pc` and the table lists
  exactly the cells written so far, plus `-1`, with their values. Every other cell reads 0.
  `HaltsWithin`'s footprint `K` then bounds the table by `|K| + 1 ≤ f + 1` entries.

**Start-up:**
1. Run the word-size machine silently. Its run lemma starts at the initial configuration.
2. Expand `Nat.bits W` into the ruler.
3. Rewind the input and count `n` onto the length tape.
4. Write the entry `-1 ↦ n mod 2^W`, truncating or padding `Nat.bits n` against the ruler.

Cost: `TW n + O(n + W²)` time and `SW n + O(W + logSpace n)` space. This fits the bound because
`t ≥ 1`.

**One phase per instruction position, in a phase host.** Each instruction is a short sequence of
rows:
- *find:* find the operand keys and copy the values into the registers;
- *compute:* apply the instruction to the registers;
- *write back:* overwrite the entry in place, or append it if absent;
- then dispatch to `pc + 1` or to `l`.

| Instruction | Compute |
|---|---|
| `one` | write the word `1` against the ruler |
| `add`, `sub` | two-tape scan with a carry |
| `mul` | shift-and-add, `W` rounds, `O(W²)` |
| `load`, `store` | sign-extend the address register into a key, then find |
| `bltz` | sign test (the top bit) |
| `half` | arithmetic shift |
| `rdIn` | range test `0 ≤ p < n` against the length tape, then seek and read |
| `emit` | zero test, then emit one bit (function mode only) |
| `coin` | write `0` (deterministic) or the choice bit (nondeterministic) |
| `accept`, `reject` | write `[v]` in verdict mode, then halt |

Every step costs at most `A·(f·(W + 1) + W² + n + 1)`:
- a table scan over at most `f + 1` entries of `W + O(1)` cells;
- `W` rounds of an `O(W)` scan for multiplication;
- `O(W + n)` for the seek.

**One induction, for both forms.** Build the host as an `NDTM` with `phaseHostND`. The coin phase
is the only state whose two transitions differ.
- *The master lemma:* by induction on the `XStepsIn` run, the branch with choice word `w`
  simulates `P` with the coin stream read off `w` at the coin steps. Between coin steps, it
  applies the deterministic contracts slice by slice (`phaseHostND_fixChoice`,
  `runWith_eq_fixChoice_runFrom`).
- *Deterministic form:* take `M = N.fixChoice false` and the all-`false` word. Its stream reads
  like `ρ = []`, so the deterministic form is a corollary.
- *Nondeterministic form:*
  - every branch is the run of some stream, so the uniform bounds bound every branch;
  - an accepting stream gives a branch that places its bits at the coin steps;
  - an accepting branch gives a stream whose run accepts, by `HaltsWithin.unique` (tier 0).

## 4. Hazards found in the survey

1. **`Contract.inPhase` forbids redirecting into the same phase** (`q.1 ≠ p`), but `bltz i l`
   with `l = pc` is a legal self-loop. Fix: index phases by (position, parity) and flip the
   parity at every dispatch. It costs nothing.
2. **`inPhase` cannot end in a halt** (`none ∉ X`). The verdict phase uses
   `phaseHostTM_run_le` instead, which is built for the last phase.
3. **The admitted table rows.** `exists_tableFindTM` and `exists_tableAppendTM` are `sorry` on
   `main`. A tier 2 route through them would leave `exists_simulation` resting on admissions. The
   keyed rows must be proved, and must not cite them.
4. **`W = 0`** gives empty words, so the layout must not rely on blank-delimited fields (§3).
5. **Existential rows.** `exists_inputSeekTM` and `exists_inputLengthTM` give `∃ t ≤ …`. A
   contract needs an exact time, chosen with `Classical.choose`, through a small adapter per row.
6. **The seek's scratch tape** must be blank everywhere (`∀ q, … = none`), so it is a dedicated
   tape that no other row writes.
7. **Private declarations do not cross files.** The simulation is 3,000–5,000 lines, and the
   policy's file size of at most about 1,000 lines forces several files. Their shared lemmas
   must then be public, in an internal namespace (decision D1).
8. **Stale line references** in `Simulation.lean`'s docstrings: `phaseHostTM` is at
   `Seam.lean:886`, not 813; `exists_inputSeekTM` is at `InputCall.lean:291`, not 294;
   `embedSilentTM` is at `Embed.lean:253`, not 241. These are repaired with the fill that
   rewrites the sketches.

## 5. The pieces, PRs and fills

The policy's **Hosts come first** rule decides the order. The keyed table is a dispatcher over a
data structure, so it is a host. Its public contract is stated and gated before any fill uses
it. The arithmetic rows are leaf rows, but `scanTM` almost covers them, so the general
two-tape form goes into the shared layer rather than into a private copy.

| # | Piece | Home (proposed) | Public? | Estimate (lines) |
|---|---|---|---|---|
| L1 | Lockstep transducer row: `r` source tapes and one destination, finite-state carry, bounded by a ruler tape. Instances: add, subtract, less-than, sign-extend, sign, zero test, arithmetic shift, copy | `Build/Lockstep.lean` (new) | yes: row plus instance lemmas | 800–1,500 |
| L2 | Multiplication mod `2^W`: a phase loop over the multiplier's bits, built from L1 | `Build/WordMul.lean` (new) | yes | 500–900 |
| L3 | Keyed table host: layout, find by a key on another tape, read value, overwrite value, append, rewind, with time and envelope clauses | `Build/KeyTable.lean` (new), reusing `RecordTable`'s layout | yes, statement-gated first | 1,500–2,500 |
| L4 | Contract adapters for the seek and length rows; the range test | `Build/InputContract.lean` (new) | yes | 300–600 |
| S1 | Start-up | `RAMSimulation/Sim/Startup.lean` | internal (D1) | 500–900 |
| S2 | The encoding invariant; the instruction phases and their contracts; the parity phase host | `RAMSimulation/Sim/Phases*.lean` | internal | 1,500–2,500 |
| S3 | The master induction; the bounds; the deterministic corollary | `RAMSimulation/Sim/Run.lean`, then `Simulation.lean` | internal; targets public (frozen) | 600–1,200 |
| S4 | The nondeterministic form: coin phase, slices, matching choice words to coin streams | `RAMSimulation/Sim/ND.lean`, then `Simulation.lean` | internal | 500–1,000 |

**Total: about 6,200–11,100 lines.** This agrees with the itemized 6,100–10,500 of 2026-10-12.

**The jobs** (Seyoon, D4: Codex in the local checkout, larger jobs than tiers 0–1, run in
parallel):

| Job | Pieces | Estimate (lines) | Can start |
|---|---|---|---|
| A | L1 and L2: the lockstep row with its instances, and multiplication | 1,300–2,400 | after the statement gate |
| B | L3: the keyed table host | 1,500–2,500 | after the statement gate |
| C | L4 and S1: the input contracts, the range test and the start-up | 800–1,500 | after the statement gate |
| D | S2: the encoding invariant, the instruction phases and the parity phase host | 1,500–2,500 | after the statement gate, against A–C's gated statements |
| E | S3 and S4: the master induction, the bounds, both targets | 1,100–2,200 | after the statement gate, against D's gated statements |

All five can run at once. Each cites the others' gated statements under the proved-modulo
rule, and lands once what it cites is proved.

**Sequence:**
1. **Statements PR** (maintainer):
   - sorried public statements of L1–L4;
   - S1–S3's internal interfaces, especially the encoding invariant, which every phase shares;
   - a statement gate (Codex audit).
2. **Jobs A–E in parallel** (table above), each against the gated statements.
4. **Landing:** each delivery through the gate kit, as with #371. `Simulation.lean` drops its last
   two admissions only when every piece below it is proved.

## 5a. The statements PR (#372, gate 162)

The statements landed as drafted here with one simplification. **There is no unary ruler.**
Words keep one width throughout the run, so an operand's own blank delimiters bound every scan,
and `W = 0` (empty words) needs no special case. The table's fields carry a marker bit, so no
field is empty. The interfaces are:
- `ReachesWithin` and `Contract.ofReaches` (proved);
- the word rows, the keyed table and the input bit (`Build/WordArith`, `KeyTable`, `InputBit`);
- `WordRAM.Sim.Encodes` (proved);
- `exists_startup`, `exists_phase` and `exists_verdictPhase`.

PR #372's description and gate 162's pack give the details.

## 6. Decisions (Seyoon, 2026-11-18)

- **D1. New public homes. Approved as proposed.** The four new `Build/` modules L1–L4 with public contracts, and the
  simulation split over `RAMSimulation/Sim/*.lean` with public lemmas in an internal namespace
  (`WordRAM.Sim`), so that they can cross files. *Recommended:* yes. The alternative, one
  `Simulation.lean` of 3,000–5,000 private lines, breaks the file-size policy, and hosts-first
  forbids a private table.
- **D2. The table layout. Reuse `RecordTable`'s layout.** Reuse `RecordTable`'s `TableAt` layout with new keyed rows in
  `Build/KeyTable.lean` (*recommended*: one table layout in the library), or a separate layout
  tuned to the RAM.
- **D3. One master induction. Approved.** on the nondeterministic host, with the deterministic form as its
  `fixChoice false` corollary (*recommended*: one induction instead of two), or two separate
  machines.
- **D4. Fill routing.** Proposed: Codex fills, one piece per fill. **Ruled:** "codex in local
  checkout, but 600-1200 lines per job is too little. we can bite off more than that per job (in
  addition to running the jobs in parallel)". So the work goes as five larger jobs, A–E (§5), in
  parallel, through the exchange (Seyoon, 2026-11-17).
- **D5. The statement gate. A Codex statement audit.** for step 1: a Codex audit, as for the 2026-10-14 statement gate
  (*recommended*: these are new public APIs).

## ===== campaign/gates/162-ram-tier2-statements/pack.md =====

# Gate 162 · RAM tier 2: the statements (PR #372)

**A statement gate** (design note `items/ram-tm/TIER2-DESIGN.md`, decision D5; Seyoon,
2026-11-18). PR #372 is a draft into `complexity/ram-simulation`. It adds the public statements
that five fill jobs, A–E, will prove in parallel, and the internal interfaces of the simulation.
Together they prove the two frozen targets `WordRAM.exists_simulation` and
`WordRAM.exists_ndSimulation`. No fill starts before this gate clears. Seyoon dispatches and
merges.

- **Lean head:** `e1325c96cf035f0ed6710443d89c3fcb6026a5c4` (branch `ram/tier2-statements`): one
  commit on the RAM branch's Lean `adb694d2` (#371 merged).
- **Approvals** (Seyoon, 2026-11-18): D1–D5 of the design note:
  - the new public `Build/` modules;
  - the simulation split under `RAMSimulation/Sim/` with public lemmas in the internal namespace
    `WordRAM.Sim`;
  - reuse of `RecordTable`'s layout;
  - one induction for both forms;
  - this audit.

  Also two edits to frozen files: readers in `Programs/WordRAM/Extended.lean`, and two imports in
  `RAMSimulation/Simulation.lean`.

## What it adds

| Module | Content | Proved? | Job |
|---|---|---|---|
| `Build/Contract/Reach` | `Turing.ReachesWithin` (endpoint within `B` steps, no exit earlier, heads within radius `E`); `ReachesWithin.mono`; `Turing.Contract.ofReaches`, the contract of such a row, with `ofReaches_time_le` | **all proved** | — |
| `Build/WordArith` | `bvBits`, `WordAt`, `wordWrite`, `ScratchBlank`, with readers (proved); `bvBits_injective` and nine five-tape rows: add, sub, mul, half, sign extension, integer constant, sign test, zero test (sorried) | readers yes | A |
| `Build/KeyTable` | `keyFields`, `keyTableLength`, `KeyTableAt`, `keyTableWrite`, `keyLookup`, `keyAssign`, with readers (proved); `exists_keyLookupTM`, `exists_keyAssignTM` (sorried) | readers yes | B |
| `Build/InputBit` | `exists_inputBitTM` (sorried) | — | C |
| `RAMSimulation/Sim/Encoding` | `keyBits`, `immediates`, `ImmBound`, `TableOf`, `Encodes`, with readers | **all proved** | — |
| `RAMSimulation/Sim/Startup` | `exists_startup` (sorried) | — | C |
| `RAMSimulation/Sim/Phases` | `isCoin`, `isVerdict`, `jumpTarget`, with readers (proved); `exists_phase`, `exists_verdictPhase` (sorried) | readers yes | D |
| `Programs/WordRAM/Extended` | 12 readers (`inBitWord_def`, `coinWord_def`, `xstep_def`, `XSteps.zero_iff`/`succ_iff`, `baseTouches_def`, `XInstr.touches_def`, `XStepsIn.zero_iff`/`succ_iff`, `initMem_def`, `XCfg.init_def`, `haltsWithin_iff`), each `rfl` | **all proved** | — |
| `RAMSimulation/Simulation` | imports `Sim/Startup` and `Sim/Phases`; the two targets unchanged | — | E |
| facades | `Build/Contract`, `TuringMachine`, `RAMSimulation`: imports and contents lines | — | — |

Job E proves the two targets from `exists_startup`, `exists_phase` and `exists_verdictPhase`, in
files of its own under `RAMSimulation/Sim/`.

### The design, in brief

- **Words** of `W` bits are held least significant first, delimited by blanks (`WordAt`). Every
  row of `Build/WordArith` is a five-tape machine: operands on tapes `0` and `1`, the
  destination on `2`, blank scratch on `3` and `4`. It writes only the destination's word
  interval and returns every head. Words keep one width, so an operand's own delimiters bound
  each scan and `W = 0` needs no case. The design note's unary ruler is therefore dropped (a
  deviation from the note's §3, recorded here).
- **The memory** is a keyed table (`Build/KeyTable`) in `RecordTable`'s layout (D2), under the
  header `[true]`. Each entry is the two fields `true :: key` and `true :: value`; the marker
  keeps every field nonempty, so the layout is well formed even for `W = 0`. The rows look up
  and assign by a key held on another tape. They do not use the admitted
  `exists_tableFindTM` and `exists_tableAppendTM`, which select by a finite-state predicate.
- **Keys** are `W + a` bits of two's complement (`keyBits`). A computed address is a word's
  signed value, in range for `W` bits. An immediate is in range for `a` bits (`ImmBound`). In the
  range of `W + a` bits, distinct cells have distinct keys.
- **`Encodes`:** eight tapes (table, key register, three word registers, `Nat.bits |x|`, two
  scratch tapes), heads at fixed origins, output `c.out` in function mode and empty in verdict
  mode. `TableOf` ties the table to the memory over a cell set `T`: distinct keys; each entry is
  a cell of `T` in range with its word; every nonzero cell in range has an entry. So the table
  has at most `|T|` entries.
- **Phases** are nondeterministic machines whose transitions differ only at a `coin` phase's
  entry, and that entry is never re-entered. Each is stated for each fixed choice `b`. The
  deterministic simulation fixes `false`, which matches the stream `ρ = []`.

### How the interfaces give the frozen bounds (job E's argument)

Let `n = |x|`. Take `t`, `f`, `K` from `HaltsWithin` (`s < t` non-verdict steps, `|K| ≤ f`), and
`T_i = {-1} ∪` the cells touched in the first `i` steps. Then `T_i ⊆ {-1} ∪ K`, so
`|T_i| ≤ f + 1`.

- **Time.**
  - The start-up takes at most `tw + C₀·(n + W² + 1)` steps, with `tw ≤ TW n`.
  - Each of the `s < t` phases takes at most `C₁·((f + 2)·(W + 1) + W² + n + 1)` steps, plus one
    dispatch step of the phase host.
  - The verdict phase takes at most `C₂` steps, plus its dispatch.
  - Since `(f + 2)·(W + 1) ≤ 2·(f·(W + 1) + W² + n + 1)` and `t ≥ 1`, the sum is at most
    `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` for a constant `A`.
- **Space.**
  - The start-up visits at most `sw + C₀·(W + |bits n| + 1)` cells, with `sw ≤ SW n`.
  - After it, each of the eight tapes stays within its origin `± C₁·((f + 2)·(W + 1) + |bits n| + 1)`.
    The phases' radius is relative to their start, and every phase starts at the origins.
  - The extra tapes never move after the start-up (they are outside the embedded phases).
  - Since `|bits n| ≤ logSpace n`, the total is at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)`.
- **The nondeterministic form.**
  - A branch with choice word `w` runs the stream of `w`'s bits at the coin phases' entries. The
    phases agree elsewhere, so `Turing.NDTM.runWith_eq_fixChoice_runFrom` applies slice by slice.
  - The uniform hypothesis bounds every branch.
  - Acceptance matches by `HaltsWithin.unique`.

## Brief for the auditor

1. **Truth.** Check that every sorried statement is true and provable as stated, at the
   boundaries too: `W = 0`, `n = 0`, `a = 0` where allowed, empty keys and tables, `c` negative,
   an input position off the input or negative, and `bltz` to its own position. Check the bounds:
   that each time and radius bound is achievable by the sketched machine.
2. **Sufficiency.** Check that the statements suffice for the two frozen targets, by the argument
   above: the bounds, the dispatch, the embedding of the eight tapes among the start-up's, and the
   nondeterministic slicing (`exists_phase`'s agreement and no-re-entry clauses). Report any
   missing clause that job E would need.
3. **The encoding.** Check `keyBits`, `ImmBound`, `TableOf` and `Encodes`. Lookups must be
   correct for every address a step reads, and the table must stay within `|T|` entries.
4. **Readers and the freeze.** Check that the 12 `Extended` readers restate their definitions
   exactly and that no existing statement changed (`SOURCE.json`: 69 declarations added, no
   header or definition change).
5. **Library fit.** Check the homes (D1, D2). Check that the rows do not duplicate published
   ones (`copyTM`, `compareTM`, `scanTM`, the `RecordTable` rows, `exists_inputSeekTM`). Check the
   docstrings and proof sketches, and the proved parts (`Contract.ofReaches`).

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the 12 owners' downstream closure on
  `oleans-cl161-cl160`, the branch's build after #371. 88 modules: 88 passed, 0 failed.
  - 30 admissions in the replayed sources: this PR's 15 statements (WordArith 9, KeyTable 2,
    InputBit 1, Startup 1, Phases 2), and 15 inherited: RecordTable 4 (not used here),
    Simulation 2 (the targets) and Classes 9 (proved by #373, gate 163; the two PRs share no
    file).
  - Pool 3; 547 s.
- **`SOURCE.json`:** 12 owners, 69 declarations added; none removed; no header or definition
  change to an existing declaration.
- **Seals:** the 49 changed or added proofs pass with every foreign definition they reach sealed
  (24 heads). They include the proved adapter, readers and definitions, and the statements'
  types.
- **Controls:** 32 definitions and 64 identities, each native-PASS and sealed-FAIL.
- **The metadata check** admits `sorryAx` only for the 15 statements named in `gate.json`
  (`inherited_admissions`), which are this PR's sorried statements. This allowance is the kit
  change made at gate 163.
- **Sweeps:** the proof-syntax sweep finds 49 roots and 0 read candidates. Citation homes are in
  `CITATION-HOMES.json`.
- **Copy screen** (population: the 12 owners): 7 pairs at the head and 7 at the base, the same
  pairs; 0 new.
- **Pre-ship:** each new module and `Extended`, `Simulation`, `Classes` and the facades
  elaborated on `oleans-cl161-cl160` before the PR was opened. No new name clashes with an
  existing declaration.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate162-ram-tier2-statements-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.

## ===== campaign/gates/162-ram-tier2-statements/findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| G162-01 | minor | `RAMSimulation/Sim/Encoding.lean:106–110` · `TableOf` docstring | Absence is sufficient for a zero value, but zero does not imply absence. | Set `a = W = 1`, `T = {-1}`, and use `initMem 1 0`, which is zero everywhere. The singleton entry `([true, true], [false])` satisfies `TableOf`, yet lookup at `-1` returns `some [false]`. Thus “nothing exactly when the word is 0” overstates the invariant; start-up itself permits stored zeros. | Say that lookup returns the stored word when present, and absence implies the word is zero. Keep the definition unchanged. |
| G162-02 | minor | `Build/KeyTable.lean:139–143` · `exists_keyLookupTM` sketch | Copying the value after its marker needs a delimiter adapter. | Immediately before the payload is `some true`, whereas `copyTM_run_ofCfg` requires a blank at source offset `-1`. Applied directly, its rewind traverses the marker and returns both heads one cell too far left; empty payloads have the same problem. Raw-key comparison after the marker needs the same care. The existential statements remain achievable within their bounds. | Describe constant-step marker clearing and restoration around payload copy/comparison, or an equivalent framed adapter. Include the intermediate delimiter facts in job B’s route. |
| G162-03 | minor | `Programs/WordRAM/Extended.lean:702–706` · reader-section introduction | New public module prose contains dated campaign provenance. | The added introduction includes “policy rule 10; Seyoon, 2026-11-18”. This conflicts with the standing rule excluding dated rulings and campaign provenance from public Lean text. The mathematical readers are unaffected. | Move the approval provenance to campaign records and retain the mathematical introduction. |
| G162-04 | note | Exchange README, `SHA256SUMS`, bundle and pinned sources | Integrity and source provenance checked. | The bundle is 3,458,398 bytes, with SHA-256 `a3517e78a3bb1cfacc1b238783991816d3232fad218fc5a1a31df110eba4013a`; the README checksum also matches. All 46 sections occur in `BUNDLE-FILES.txt` order and reproduce Git blob hashes at Lean head `e1325c96cf035f0ed6710443d89c3fcb6026a5c4` or records commit `6164f5d1a50a38d0932baa4cef294226dcd37457`, as appropriate. All 471 recovered evidence files pass their recorded size and SHA-256 checks. | None. |
| G162-05 | note | `Build/Contract/Reach.lean` · `ReachesWithin`, `Contract.ofReaches` | The bounded endpoint predicate and contract adapter have the intended meaning. | `ReachesWithin` asserts an endpoint at some time at most `B`, avoidance of the exit set strictly earlier, and head displacement at most `E` through the endpoint. `ofReaches` selects that time under the entry/precondition, uses zero otherwise, retains the prescribed endpoint, and takes intervals from initial head minus `E` to initial head plus `E`; its exit-membership hypothesis supplies the contract’s remaining obligation. Zero time is allowed consistently, and `mono` and `ofReaches_time_le` match these meanings. | None. |
| G162-06 | note | `Build/WordArith.lean` · word definitions; `bvBits_injective` | Word representations, updates and injectivity are sound. | `bvBits` lists exactly the `W` low bits; `WordAt` fixes the word and its two delimiters while allowing an arbitrary outer frame. `wordWrite` changes only the destination interval, and `ScratchBlank` requires tapes 3 and 4 blank everywhere. Equal bit lists give equality at every bit position and hence equality of the words. At `W = 0`, the word type is a singleton, so injectivity still holds. | None. |
| G162-07 | note | `Build/KeyTable.lean` · six layout/operation definitions | The layout and list operations support empty keys, empty values and duplicate keys. | `keyFields` prefixes each key/value with `true`; `keyTableLength` counts the joined layout. `KeyTableAt` requires the existing table layout and an entirely blank right tail, while `keyTableWrite` changes only the new layout interval. `keyLookup` selects the first match; `keyAssign` replaces every matching value or appends when none matches. Marker fields are nonempty even when their payloads are empty; assignment’s equal-value-length premise prevents shrinking an existing layout. | None. |
| G162-08 | note | `RAMSimulation/Sim/Encoding.lean`, `Sim/Phases.lean` · encoding/control definitions | The address and tape invariants cover every instruction read. | `keyBits` encodes an integer modulo `2^(W+a)`; `immediates` lists cell operands and excludes jump labels; `ImmBound` places those operands in the signed `a`-bit range. `TableOf` requires distinct keys, sound entries from `T`, and coverage of nonzero memory in range, giving correct zero-default lookup and at most `T.card` entries. `Encodes` fixes the eight heads, table, register widths, input-length word, blank scratch and mode-dependent output, leaving program position and coin count to the run invariant. `isCoin`, `isVerdict` and `jumpTarget` select exactly their stated instruction cases; at `a = W = 0` the allowed address range is `{0}`, so empty keys cause no collision within range. | None beyond G162-01. |
| G162-09 | note | `Turing.exists_wordAddTM` | The linear bounds and exact frame are achievable. | A lockstep ripple-carry scan writes the low `W` sum bits, followed by a return scan; neither source nor either scratch tape needs changing. Discarding the final carry gives addition modulo `2^W`, with empty scans handling `W = 0`. | None. |
| G162-10 | note | `Turing.exists_wordSubTM` | The linear bounds include underflow. | The same scan with a borrow bit writes subtraction modulo `2^W`, then restores the heads. In particular, subtracting one from zero produces the all-one word at positive width and the unique empty word at width zero. | None. |
| G162-11 | note | `Turing.exists_wordMulTM` | Quadratic time and linear radius are achievable on five tapes. | Shift-and-add uses at most `W` rounds of linear scans, with the shifted multiplicand and temporary sum on the two scratch tapes, subsequently erased. Originals are preserved, all heads return, and width zero has no rounds. | Prove a reusable internal carry lemma with an arbitrary frame: the exported add row’s blank-scratch precondition does not directly cover multiplication’s occupied scratch tapes. |
| G162-12 | note | `Turing.exists_wordHalfTM` | Arithmetic right shift has the stated result and bounds. | A scan writes each next-higher source bit and repeats the sign bit at the top, then returns the heads. This preserves a negative one-bit word and writes nothing at width zero. | None. |
| G162-13 | note | `Turing.exists_wordSignExtendTM` | Sign extension is uniform in `W`, including zero. | Copy the source and append its sign bit `a` times, using false for the empty source. Since `a` is fixed before the machine and constant are chosen, the additional time and radius are absorbed in `C*(W+1)`. | None. |
| G162-14 | note | `Turing.exists_wordIntTM` | Integer constants, including negative constants, fit the linear bounds. | A finite controller emits the finitely many exceptional low bits of the fixed integer, then its eventual sign bit until the destination delimiter. It therefore writes precisely the truncated two’s-complement representation; fixed `a` is absorbed into `C`, and an empty destination remains unchanged. | None. |
| G162-15 | note | `Turing.exists_wordSignTM` | The sign test preserves the entire configuration except its exit state. | Instantiate `scanTM` with unchanged symbols and a flag remembering the last forward bit, initially false. Returning without changing that flag gives the sign, including false at width zero, within linear time and radius. | Reuse `scanTM_run_ofCfg`. |
| G162-16 | note | `Turing.exists_wordNonzeroTM` | The nonzero test has the required distinct exits and frame. | Instantiate the same scan with a flag recording whether any source bit is true. Its final flag is equivalent to nonzero by bit injectivity, including the empty zero word, and the scan leaves tapes, heads, input and output unchanged. | Reuse `scanTM_run_ofCfg`. |
| G162-17 | note | `Turing.exists_keyLookupTM` | First-match lookup and zero-default lookup fit the linear bound. | Comparing only through the first mismatch charges each unsuccessful comparison and rewind to that entry’s key length, rather than charging the entire query per entry. Searching, copying a matching value or writing default zeros, rewinding and restoring the frame therefore cost `O(table + key + value)`; empty tables and payloads are covered by the markers. | Apply G162-02’s delimiter adaptation. |
| G162-18 | note | `Turing.exists_keyAssignTM` | Assignment’s duplicate-key behavior and growth are achievable. | Scan all entries, replacing every matching value with the equally long supplied value; the total copied length is bounded by the old layout length. If absent, append one marked key/value pair into the blank tail, then rewind; this gives the stated exact endpoint and linear bound even for empty keys or values. | Apply G162-02’s delimiter adaptation to the search. |
| G162-19 | note | `Turing.exists_inputBitTM` | Signed, out-of-range and empty-input cases fit both bounds. | Reject negative positions and positions at least the input length before seeking; otherwise an unsigned counter for position plus one lets `exists_inputSeekTM` read the input in place. The input head starts within `x.length+1`, so time is linear in `W+x.length+1`, while scratch width is linear in `W+bits(x.length).length+1`. At width zero the result word is empty regardless of the bit. | None. |
| G162-20 | note | `WordRAM.Sim.exists_startup` | Start-up preserves the word-size witness’s leading time/space costs. | Silent embedding runs the witness one step per source step and captures only its final binary output, whose length is at most `W`. Register preparation, length counting and installing `-1` then fit the additional quadratic-width time and linear-width/logarithmic space allowances. The hypothesis `a >= 1` puts `-1` in key range even when `W = 0`; empty input and empty words still admit a marked table entry. | None. |
| G162-21 | note | `WordRAM.Sim.exists_phase` | The instruction interface has the required semantic and resource clauses. | Immediate addresses are in range by `ImmBound`, and computed addresses are signed word values, so lookup is correct for every read. Each instruction uses a bounded number of table/word rows, updates only touched memory, and restores the eight origins; the table remains a `TableOf` over the enlarged footprint. For nondeterminism, handle the entry choice explicitly, then use transition agreement and no re-entry to justify deterministic slices through every remaining prefix. | None. |
| G162-22 | note | `WordRAM.Sim.exists_verdictPhase` | The constant-time verdict interface is sufficient. | One stationary step halts, emitting `v` only in verdict mode. `Encodes` already gives empty output in that mode and `c.out` in function mode, so the required output and fixed-head clauses follow for arbitrary encoded configurations. | None. |
| G162-23 | note | `Sim/Startup`, `Sim/Phases` → two frozen simulation targets | The interfaces suffice for the stated time, space and acceptance bounds. | Use program-position/parity phases for self-jumps, a separate halting verdict phase, and R1 embedding on the first eight start-up tapes. There are fewer than `t` ordinary phases; each footprint has at most `f+1` cells, and dispatch adds one step. For space, `(f+2)*(W+1) <= 2*(f*(W+1)+W+1)` and fixed origins bound the union of all phase visits; extra start-up tapes stay fixed. Entry choices realize coin streams in both directions, while transition agreement, halting absorption and `HaltsWithin.unique` provide all-branch bounds and the acceptance equivalence. | None. |
| G162-24 | note | `Programs/WordRAM/Extended.lean`, `RAMSimulation/Simulation.lean`, `SOURCE.json` | Reader fidelity and the statement freeze are respected. | Direct comparison with base `adb694d2d73a253977522b26a8d79e852dac08f5` shows only documentation and the 12 readers added to `Extended`; each reader reproduces its defining equation. `Simulation` changes only by its two authorized imports, leaving both targets identical. An independent source census recounts 69 added public declarations. | None beyond G162-03. |
| G162-25 | note | Library homes and recovered verification evidence | Library fit and the supplied verification claims support this statement gate. | The table reuses `RecordTable`’s layout; keyed tape-driven lookup/assignment and two-source carry arithmetic fill genuine gaps, while the simpler rows can reuse the catalog. Recounted archived evidence gives 88 passing replay logs, zero error lines, and 30 expected admission warnings, including exactly the 15 new statements; 43 sealed declarations plus six without foreign boundaries and all 64 native-PASS/sealed-FAIL controls reconcile. No new copied proved-material pair was identified in the supplied owner screen. These are checks of archived evidence and source, not a fresh local Lean replay. | Retain the stated reuse routes in the fill briefs and repair the three minor items. |

Verdict: CLEAR

## ===== campaign/gates/162-ram-tier2-statements/resolutions.md =====

# Gate 162 resolutions

## Round 1: CLEAR (0 blockers, 0 majors, 3 minors, 22 notes; `findings.md`, verbatim)

A statement gate. The auditor found every sorried statement true and achievable within its
bounds, at the boundaries (G162-09 to G162-22). It found the interfaces sufficient for both
frozen targets by the pack's argument (G162-23), and the readers faithful with the freeze held
(G162-24).

**The three minors are repaired at `80e762e9`**, in docstrings only, with no statement or proof
changed:
- **G162-01, repaired.** `TableOf`'s docstring: a lookup finds the stored word when the cell has
  an entry, and finds nothing only when the word is `0`. An entry may hold `0`, as the start-up's
  `-1` entry can. The definition is unchanged.
- **G162-02, repaired.** The proof sketches of `exists_keyLookupTM` and `exists_keyAssignTM` now
  describe the marker adapter. Blank the marker cell, run the delimited word row on the payload,
  and write the marker back; an empty payload is then an empty delimited word. Job B's brief
  carries the intermediate delimiter facts.
- **G162-03, repaired.** The introduction to `Extended`'s reader section drops "policy rule 10;
  Seyoon, 2026-11-18". The provenance stays in these records and the HANDOFF. The PR adds no other
  dated provenance to Lean text.

**Notes carried into the job briefs:**
- **G162-11 (job A):** prove a reusable internal carry lemma with an arbitrary frame. The
  exported adder's blank-scratch precondition does not cover multiplication's occupied scratch
  tapes.
- **G162-15, G162-16 (job A):** reuse `Turing.scanTM_run_ofCfg` for the sign and zero tests.
- **G162-17, G162-18 (job B):** the marker adapter (G162-02) in lookup and assignment.
- **G162-21, G162-23 (jobs D, E):**
  - handle the coin's entry choice explicitly, then slice the rest deterministically;
  - use phases indexed by position and parity for self-jumps, and a separate halting verdict
    phase;
  - use the R1 embedding of the eight tapes.

## Merge

**Run 2 of the gate kit on the repaired head `80e762e9`** gives the same results as run 1 on the audited head: replay 88/88 (30 admissions, the same), 49 proofs sealed, controls 32/64, 0 read candidates, 7 copy pairs as at the base (0 new); `SOURCE.json` again gives 69 declarations added and no header or definition change. Seyoon
merges #372. After the merge the branch's build is the replay output of whichever PR merges
second, checked on the merged tree.

## ===== TCSlib/Complexity/RAMSimulation/Sim/Phases.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.InputBit
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: one phase per instruction

The simulating machine runs one phase for each instruction it executes. A phase is a machine on
the eight tapes of `WordRAM.Sim.Encodes`: from tapes encoding a configuration `c` whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep … c`, and its exit
tells the host where the program goes next. The host (a phase host over the program's positions)
and the induction over a run are built from these phases.

Every phase is a nondeterministic machine whose two transitions agree everywhere except at the
entry of a `coin` phase, where the choice is the coin. Fixing the choice gives a deterministic
machine (`Turing.NDTM.fixChoice`), and the phase's run is stated for each fixed choice; the
deterministic simulation fixes it to `false`, so that coins read `0`.

## Main definitions

* `WordRAM.Sim.isCoin`, `WordRAM.Sim.isVerdict`, `WordRAM.Sim.jumpTarget`.

## Main results

* `WordRAM.Sim.exists_phase`: the phase of an instruction other than `accept` and `reject`.
* `WordRAM.Sim.exists_verdictPhase`: the phase of `accept` and `reject`, which writes the output
  and halts.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2: nondeterministic machines.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- Whether an instruction is a `coin`. -/
def isCoin : XInstr → Bool
  | .coin _ => true
  | _ => false

/-- Whether an instruction is a `coin`, as an equation. -/
theorem isCoin_def (ins : XInstr) :
    isCoin ins = match ins with
      | .coin _ => true
      | _ => false := by
  cases ins <;> rfl

/-- Whether an instruction gives a verdict: `accept` or `reject`. -/
def isVerdict : XInstr → Bool
  | .base .accept => true
  | .base .reject => true
  | _ => false

/-- Whether an instruction gives a verdict, as an equation. -/
theorem isVerdict_def (ins : XInstr) :
    isVerdict ins = match ins with
      | .base .accept => true
      | .base .reject => true
      | _ => false := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- The position a taken jump goes to: the label of `bltz`, and `0` for any other instruction
(which never jumps). -/
def jumpTarget : XInstr → ℕ
  | .base (.bltz _ l) => l
  | _ => 0

/-- The position a taken jump goes to, as an equation. -/
theorem jumpTarget_def (ins : XInstr) :
    jumpTarget ins = match ins with
      | .base (.bltz _ l) => l
      | _ => 0 := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **The phase of an instruction.** For `a`, an output mode `fn` and an instruction `ins` that is
not a verdict and whose addresses are below `2^(a-1)` in absolute value, there is a
nondeterministic machine `N` on eight tapes, with an entry and two exits `next` and `jump`, and a
constant `C`, such that:
* the entry is never re-entered, and the two transitions of `N` agree at every state except the
  entry, and at the entry too unless `ins` is a `coin`;
* for each choice `b`: whenever the instruction at `c.pc` of a program `P` is `ins` (and, for a
  `coin`, the coin `ρ.getD c.rd false` is `b`), and `d`, at the entry, encodes `c` over the cells
  `T` with origins `o`, then `xstep P x ρ c` is a configuration `c'`, and the machine with the
  choice fixed to `b` reaches, within `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
  `C·((|T| + 1)·(W + 1) + log |x| + 1)`, a configuration `d'` encoding `c'` over the cells
  `T ∪ touches` with the same origins, at `next` if the program goes on to `c.pc + 1` and at
  `jump` if it jumps to `jumpTarget ins`.

[AB09, Exercise 1.9; §2.1.2]

**Proof sketch.** By cases on `ins`, each phase a sequence of the rows of
`Build/WordArith`, `Build/KeyTable` and `Build/InputBit`, placed on the eight tapes by
`Turing.embedEmitTM` and composed by `Turing.Contract.ofReaches` and `Turing.Contract.seq`:
* an address `i` written in `ins` is written as a key on tape `1` (`Turing.exists_wordIntTM`
  with `c = i`); a computed address `[j]` is looked up into a register and sign-extended into tape
  `1` (`Turing.exists_wordSignExtendTM`);
* operands are looked up into registers `2` and `3` (`Turing.exists_keyLookupTM`), the result is
  computed into register `4` by the arithmetic rows (`one`, `add`, `sub`, `mul`, `half`), read
  from the input (`rdIn`, `Turing.exists_inputBitTM`) or written from the coin (`coin`: one
  choice step, then `Turing.exists_wordIntTM` with `c = 0` or `1`), and stored back
  (`Turing.exists_keyAssignTM`);
* `bltz` looks up its cell and branches on `Turing.exists_wordSignTM`; `emit` looks up its cell,
  tests it with `Turing.exists_wordNonzeroTM`, and in function mode emits the bit.
The table stays a `TableOf` because every key written is that of a cell of `T ∪ touches` in
range (`ImmBound`; a word's signed value is in range), and keys of cells in range are distinct.
The table has at most `|T|` entries of `O(W + a)` cells, which gives the bounds; the seek adds
`O(|x|)` steps and the multiplication `O(W²)`. -/
theorem exists_phase (a : ℕ) (fn : Bool) (ins : XInstr) (hins : ImmBound a ins)
    (hv : isVerdict ins = false) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : NDTM 8 Bool S) (entry next jump : S)
      (C : ℕ), next ≠ jump ∧
      (∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry) ∧
      (∀ q : S, q ≠ entry ∨ isCoin ins = false → N.tr false q = N.tr true q) ∧
      ∀ (b : Bool) {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool) (T : Finset ℤ)
        (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x),
        P.getD c.pc (.base .reject) = ins → (isCoin ins = true → ρ.getD c.rd false = b) →
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ (c' : XCfg W) (d' : Turing.Cfg 8 Bool S x), xstep P x ρ c = .inl c' ∧
          Encodes a fn (T ∪ ins.touches c.mem) c' (Function.Embedding.refl _) o d' ∧
          ((d'.state = some next ∧ c'.pc = c.pc + 1) ∨
            (d'.state = some jump ∧ c'.pc = jumpTarget ins)) ∧
          ReachesWithin (N.fixChoice b) d {some next, some jump}
            (C * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1))
            (C * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1)) d' := by
  sorry

/-- **The phase of a verdict.** For an output mode `fn` and a verdict `v`, there is a deterministic
machine on eight tapes, with an entry, and a constant `C`, such that from tapes at the entry
encoding `c`, the machine halts within `C` steps with the output `c.out` in function mode and
`[v]` in verdict mode, every head fixed. [AB09, Exercise 1.9]

**Proof sketch.** One step: in verdict mode emit `v` (the output was empty, `Encodes`), and halt.
-/
theorem exists_verdictPhase (fn v : Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 8 Bool S) (entry : S)
      (C : ℕ),
      ∀ (a : ℕ) {x : List Bool} {W : ℕ} (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
        (d : Turing.Cfg 8 Bool S x),
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ t ≤ C, (M.runFrom d t).state = none ∧
          (M.runFrom d t).output = (if fn then c.out else [v]) ∧
          ∀ s ≤ t, (M.runFrom d s).workTapePos = d.workTapePos := by
  sorry

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/Encoding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.TuringMachine.Build.KeyTable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: how tapes encode a configuration of the extended word RAM

The simulating machine of `WordRAM.exists_simulation` keeps a configuration `c : XCfg W` of the
extended word RAM on eight work tapes, its program position in its finite control. This file
defines that encoding, `WordRAM.Sim.Encodes`, shared by the start-up (`Sim/Startup`), the
instruction phases (`Sim/Phases`) and the simulation's induction. The declarations of the
`WordRAM.Sim` namespace are the simulation's internal interfaces: public so that the pieces can
live in separate files, not meant for other consumers.

**The eight tapes.**
* `0`: the memory, a keyed table (`Turing.KeyTableAt`) of the written cells and their words.
* `1`: the key register, `W + a` cells.
* `2`, `3`, `4`: three word registers of `W` cells.
* `5`: the input length in binary, `Nat.bits |x|`.
* `6`, `7`: blank scratch tapes.

**Keys.** The memory is indexed by integers. A cell `z` is stored under the `W + a` bits of
`z` in two's complement, `keyBits a W z`. Every address the program touches is in that range:
a computed address is a word's signed value, and the program's own addresses (its immediates)
are below `2^(a-1)` in absolute value (`WordRAM.Sim.ImmBound`). In that range distinct cells
have distinct keys.

## Main definitions

* `WordRAM.Sim.keyBits`, `WordRAM.Sim.immediates`, `WordRAM.Sim.ImmBound`.
* `WordRAM.Sim.TableOf`: a list of entries stores a memory over a set of cells.
* `WordRAM.Sim.Encodes`: the tapes encode a configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- **The key of a cell**: the `W + a` bits of the integer `z` in two's complement, least
significant first. -/
def keyBits (a W : ℕ) (z : ℤ) : List Bool := bvBits (BitVec.ofInt (W + a) z)

/-- The key of a cell, as an equation. -/
theorem keyBits_def (a W : ℕ) (z : ℤ) : keyBits a W z = bvBits (BitVec.ofInt (W + a) z) := rfl

/-- **The addresses written in an instruction**: its integer arguments, which name cells (the
label of `bltz` is a position, not a cell, and is not one of them). -/
def immediates : XInstr → List ℤ
  | .base (.one i) => [i]
  | .base (.add i j k) => [i, j, k]
  | .base (.sub i j k) => [i, j, k]
  | .base (.mul i j k) => [i, j, k]
  | .base (.load i j) => [i, j]
  | .base (.store i j) => [i, j]
  | .base (.bltz i _) => [i]
  | .base .accept => []
  | .base .reject => []
  | .rdIn i j => [i, j]
  | .emit i => [i]
  | .coin i => [i]
  | .half i j => [i, j]

/-- The addresses written in an instruction, as an equation. -/
theorem immediates_def (ins : XInstr) :
    immediates ins =
      match ins with
      | .base (.one i) => [i]
      | .base (.add i j k) => [i, j, k]
      | .base (.sub i j k) => [i, j, k]
      | .base (.mul i j k) => [i, j, k]
      | .base (.load i j) => [i, j]
      | .base (.store i j) => [i, j]
      | .base (.bltz i _) => [i]
      | .base .accept => []
      | .base .reject => []
      | .rdIn i j => [i, j]
      | .emit i => [i]
      | .coin i => [i]
      | .half i j => [i, j] := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **Small immediates**: every address written in `ins` is in the signed range of `a` bits
(`WordRAM.InRange a`), so that it has a key of `W + a` bits for every `W`. -/
def ImmBound (a : ℕ) (ins : XInstr) : Prop := ∀ z ∈ immediates ins, InRange a z

/-- `ImmBound`, as an equivalence with its definition. -/
theorem immBound_iff (a : ℕ) (ins : XInstr) :
    ImmBound a ins ↔ ∀ z ∈ immediates ins, InRange a z := Iff.rfl

/-- **A table stores a memory over a set of cells.** `TableOf a W T m es`: the keys of `es` are
distinct; every entry is the key of some cell `z ∈ T` in the range of `W + a` bits, with `m z`'s
bits as its value; and every cell in that range where `m` is nonzero has an entry. So a lookup of
a cell in range finds its word when it has an entry, and finds nothing only when the word is `0`
(an entry may still hold the word `0`); and `es` has at most `|T|` entries. -/
def TableOf (a W : ℕ) (T : Finset ℤ) (m : ℤ → BitVec W) (es : List (List Bool × List Bool)) :
    Prop :=
  (es.map Prod.fst).Nodup ∧
    (∀ e ∈ es, ∃ z ∈ T, InRange (W + a) z ∧ e = (keyBits a W z, bvBits (m z))) ∧
    ∀ z : ℤ, InRange (W + a) z → m z ≠ 0 → keyBits a W z ∈ es.map Prod.fst

/-- `TableOf`, as an equivalence with its definition. -/
theorem tableOf_iff (a W : ℕ) (T : Finset ℤ) (m : ℤ → BitVec W)
    (es : List (List Bool × List Bool)) :
    TableOf a W T m es ↔ (es.map Prod.fst).Nodup ∧
      (∀ e ∈ es, ∃ z ∈ T, InRange (W + a) z ∧ e = (keyBits a W z, bvBits (m z))) ∧
      ∀ z : ℤ, InRange (W + a) z → m z ≠ 0 → keyBits a W z ∈ es.map Prod.fst :=
  Iff.rfl

/-- **The tapes encode a configuration.** `Encodes a fn T c σ o d`, for the eight tapes placed in
`d`'s tapes by `σ`, with origins `o`:
* every one of the eight heads is at its origin;
* tape `0` holds a keyed table that stores `c.mem` over the cells `T` (`TableOf`);
* tape `1` holds a word of `W + a` cells, tapes `2` to `4` words of `W` cells;
* tape `5` holds `Nat.bits |x|`;
* tapes `6` and `7` are blank;
* the output is `c.out` in function mode (`fn = true`) and empty in verdict mode.

The program position `c.pc` and the coin count `c.rd` are not on the tapes: the position is the
phase of the machine's finite control, and the coin count is a property of the run. -/
def Encodes {K : ℕ} {S : Type} (a : ℕ) (fn : Bool) {x : List Bool} {W : ℕ} (T : Finset ℤ)
    (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x) : Prop :=
  (∀ j : Fin 8, d.workTapePos (σ j) = o j) ∧
    (∃ es, KeyTableAt d (σ 0) (o 0) es ∧ TableOf a W T c.mem es) ∧
    (∃ w, WordAt d (σ 1) w ∧ w.length = W + a) ∧
    (∀ r : Fin 8, 2 ≤ r.val → r.val ≤ 4 → ∃ w, WordAt d (σ r) w ∧ w.length = W) ∧
    WordAt d (σ 5) (Nat.bits x.length) ∧
    (∀ r : Fin 8, 6 ≤ r.val → ∀ q : ℤ, d.workTapes (σ r) q = none) ∧
    d.output = if fn then c.out else []

/-- `Encodes`, as an equivalence with its definition. -/
theorem encodes_iff {K : ℕ} {S : Type} (a : ℕ) (fn : Bool) {x : List Bool} {W : ℕ}
    (T : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x) :
    Encodes a fn T c σ o d ↔
      (∀ j : Fin 8, d.workTapePos (σ j) = o j) ∧
      (∃ es, KeyTableAt d (σ 0) (o 0) es ∧ TableOf a W T c.mem es) ∧
      (∃ w, WordAt d (σ 1) w ∧ w.length = W + a) ∧
      (∀ r : Fin 8, 2 ≤ r.val → r.val ≤ 4 → ∃ w, WordAt d (σ r) w ∧ w.length = W) ∧
      WordAt d (σ 5) (Nat.bits x.length) ∧
      (∀ r : Fin 8, 6 ≤ r.val → ∀ q : ℤ, d.workTapes (σ r) q = none) ∧
      d.output = if fn then c.out else [] :=
  Iff.rfl

end WordRAM.Sim
```

## ===== TCSlib/Complexity/TuringMachine/Build/WordArith.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Reach
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-width words on tapes: arithmetic rows

A word of `W` bits (`BitVec W`) is held on a work tape as its `W` bits, least significant first,
delimited by blanks at the head's offsets `-1` and `W`. This file states the rows that compute
on such words: addition, subtraction and multiplication modulo `2^W`, the arithmetic shift right,
sign extension, writing the word of an integer constant, and the sign and zero tests. They are the
arithmetic of a word RAM run on a Turing machine (`WordRAM.exists_simulation`).

Every row is a five-tape machine over `Bool`: tapes `0` and `1` hold the operands, tape `2` the
destination, and tapes `3` and `4` are blank scratch tapes, left blank. A row writes only the
destination's word interval, leaves every head where it was, and is stated with
`Turing.ReachesWithin`. A consumer places the five tapes among its own with `Turing.embedEmitTM`
and composes the rows with `Turing.Contract.ofReaches`. The words have one width throughout, so
the length of an operand delimits every scan and `W = 0` (empty words) needs no special case.

No row of the catalog reads two tapes with a carry, so addition, subtraction and the tests are
new rows here (the one-tape `Turing.scanTM` covers only single-word transducers).

## Main definitions

* `Turing.bvBits`: the bits of a word, least significant first.
* `Turing.WordAt`: a word delimited at a head.
* `Turing.wordWrite`: the tapes after writing a word at a head.

## Main results

* `Turing.exists_wordAddTM`, `Turing.exists_wordSubTM`, `Turing.exists_wordMulTM`: addition,
  subtraction and multiplication modulo `2^W`, in `O(W)`, `O(W)` and `O(W²)` steps.
* `Turing.exists_wordHalfTM`: the arithmetic shift right by one place.
* `Turing.exists_wordSignExtendTM`: sign extension from `W` to `W + a` bits.
* `Turing.exists_wordIntTM`: the word of an integer constant, as wide as a guide word plus `a`.
* `Turing.exists_wordSignTM`, `Turing.exists_wordNonzeroTM`: the tests `u < 0` and `u ≠ 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: multitape machines; Exercise 1.9: a RAM simulated by a
  Turing machine, whose arithmetic these rows provide.)
-/

namespace Turing

/-! ## Words on tapes -/

/-- **The bits of a word**, least significant first: `bvBits v = [v₀, v₁, …, v_{W-1}]`. -/
def bvBits {W : ℕ} (v : BitVec W) : List Bool := List.ofFn fun i : Fin W => v.getLsbD i

/-- The bits of a word, as an equation. -/
theorem bvBits_def {W : ℕ} (v : BitVec W) :
    bvBits v = List.ofFn fun i : Fin W => v.getLsbD i := rfl

/-- A word of `W` bits has `W` bits. -/
theorem bvBits_length {W : ℕ} (v : BitVec W) : (bvBits v).length = W := by
  simp [bvBits]

/-- Distinct words have distinct bits.

**Proof sketch.** Equal bit lists give `getLsbD` equal at every `i < W` (`List.ofFn_inj`), and
`BitVec.eq_of_getLsbD_eq` concludes. -/
theorem bvBits_injective {W : ℕ} : Function.Injective (bvBits (W := W)) := by
  sorry

/-- **A word delimited at a head**: tape `r` holds `w` from its head, with blanks at the head's
offsets `-1` and `|w|`. The cells beyond are arbitrary. -/
def WordAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (w : List Bool) :
    Prop :=
  ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p

/-- `WordAt`, as an equivalence with its definition. -/
theorem wordAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) :
    WordAt d r w ↔ ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p :=
  Iff.rfl

/-- **The tapes after writing a word at a head**: on tape `r`, the cells from its head on hold `w`
over `|w|` cells; every other cell, of every tape, is unchanged. -/
def wordWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (q - d.workTapePos j)
    else d.workTapes j q

/-- `wordWrite`, as an equation. -/
theorem wordWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) (j : Fin K) (q : ℤ) :
    wordWrite d r w j q =
      if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (q - d.workTapePos j)
      else d.workTapes j q :=
  rfl

/-- **The common precondition of the word rows**: tapes `3` and `4` are blank everywhere. -/
def ScratchBlank {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) : Prop :=
  ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none

/-- `ScratchBlank`, as an equivalence with its definition. -/
theorem scratchBlank_iff {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) :
    ScratchBlank d ↔ ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none :=
  Iff.rfl

/-! ## Arithmetic modulo `2^W` -/

/-- **Addition modulo `2^W`.** From the entry, with `u` on tape `0`, `v` on tape `1`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u + v` on tape `2` and stops at its
exit within `C·(W + 1)` steps, every head within `C·(W + 1)` cells and back where it started.
[AB09, Exercise 1.9]

**Proof sketch.** One lockstep sweep over the three words from their heads, carrying the carry bit
in the state and writing `uᵢ xor vᵢ xor carry`, ending at the blank after the words; then one
sweep back to the heads. The carry out of the top bit is dropped, which is reduction modulo `2^W`
(`BitVec.add` is `BitVec.ofNat` of the sum; the low `W` bits of a sum are the ripple-carry bits).
-/
theorem exists_wordAddTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u + v)) } := by
  sorry

/-- **Subtraction modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u - v`.
[AB09, Exercise 1.9]

**Proof sketch.** The lockstep sweep with a borrow bit in place of the carry, writing
`uᵢ xor vᵢ xor borrow` (equivalently, `u + ¬v + 1`: start the carry at `1` and complement `v`'s
bits as they are read); then the sweep back. -/
theorem exists_wordSubTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u - v)) } := by
  sorry

/-- **Multiplication modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u * v`, within
`C·(W + 1)²` steps and radius `C·(W + 1)`. [AB09, Exercise 1.9]

**Proof sketch.** Shift and add. Copy `u` to scratch tape `3` and clear the destination to `0`.
For each bit of `v`, from the least significant: if it is `1`, add tape `3` into the destination
(the lockstep adder with the destination as an operand, using scratch tape `4` for the sum and
copying it back); then shift tape `3` up by one place in place, dropping its top bit. The
iteration walks `v`'s head one cell per round and stops at its delimiter, so it needs no counter.
Each round is `O(W)` and there are `W` rounds. Finally clear the scratch tapes and return the
heads. The invariant after `r` rounds: the destination holds `u * (v mod 2^r)` and tape `3` holds
`u <<< r`, both modulo `2^W`. -/
theorem exists_wordMulTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1) ^ 2) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u * v)) } := by
  sorry

/-- **The arithmetic shift right by one place.** From the entry, with `u` on tape `0`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u.sshiftRight 1` (that is,
`⌊u / 2⌋` read signed) on tape `2`, within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1`
untouched. [AB09, Exercise 1.9]

**Proof sketch.** Bit `i` of the result is bit `i + 1` of `u`, and the top bit is `u`'s top bit.
Start `u`'s head one cell to the right and sweep both heads together, writing the bit read and
remembering it in the state; at `u`'s right delimiter write the remembered bit once more. For
`W = 0` both words are empty and nothing is written. Then return the heads. -/
theorem exists_wordHalfTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u.sshiftRight 1)) } := by
  sorry

/-- **Sign extension by `a` places.** From the entry, with `u` on tape `0`, a word of `W + a`
cells on tape `2` and blank scratch tapes, the row writes `u.signExtend (W + a)` on tape `2`,
within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1` untouched. The constant `C` depends on
`a`. [AB09, Exercise 1.9]

**Proof sketch.** Copy `u` into the first `W` cells, remembering its last bit read (`false` if
`W = 0`, where the extension is `0`); then write that bit `a` times, counted in the state; then
return the heads. -/
theorem exists_wordSignExtendTM (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W + a →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (u.signExtend (W + a))) } := by
  sorry

/-- **The word of an integer constant.** For an integer `c` and `a ≥ 0`: from the entry, with a
word of `W + a` cells on tape `2` and blank scratch tapes, the row writes `BitVec.ofInt (W + a) c`
over it, within `C·(W + 1)` steps and radius `C·(W + 1)`, tapes `0` and `1` untouched. The
constant `C` depends on `c` and `a`. With `a = 0` and `c = 1` this writes the word `1`.
[AB09, Exercise 1.9]

**Proof sketch.** Let `b` be the bit length of `|c|` plus one. Bit `i` of `BitVec.ofInt n c` is
`c.testBit i` (two's complement), which for `i ≥ b` is the sign of `c`. Sweep the destination's
old word, writing `c.testBit i` from a table in the state for `i < b` and the sign beyond, and stop
at its right delimiter; then return the head. -/
theorem exists_wordIntTM (c : ℤ) (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 2 w → w.length = W + a → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (BitVec.ofInt (W + a) c)) } := by
  sorry

/-! ## Tests -/

/-- **The sign test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u` is negative read signed (`u.toInt < 0`) and at `no` otherwise, within `C·(W + 1)`
steps and radius `C·(W + 1)`, writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** Sweep `u`, remembering the last bit read (`false` for `W = 0`); at the right
delimiter that bit is the sign (`BitVec.toInt_neg_iff`, `u.msb`); return the head and branch. -/
theorem exists_wordSignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u.toInt < 0 then yes else no) } := by
  sorry

/-- **The zero test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u ≠ 0` and at `no` otherwise, within `C·(W + 1)` steps and radius `C·(W + 1)`,
writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** Sweep `u`, remembering whether a `1` was read; return the head and branch.
`u ≠ 0` exactly when some bit is set (`bvBits_injective` with the zero word). -/
theorem exists_wordNonzeroTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u ≠ 0 then yes else no) } := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/KeyTable.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.WordArith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed tables: lookup and assignment by a key held on another tape

A **keyed table** is a list of entries `(key, value)` of binary words, laid out on one work tape
in the record-table layout of `Build/RecordTable` (`Turing.TableAt`): the header `[true]`, then
for each entry the two fields `true :: key` and `true :: value`, fields separated by one blank,
two blanks before the header and after the last field. The leading `true` of each field keeps
every field nonempty, so the layout is well formed (`Turing.TableWF`) even for empty keys or
values, and a blank pair marks the table's end.

The two rows are the host of a memory: **lookup** copies the value stored under a key, held on
another tape, into a register (the all-`false` word if the key is absent), and **assignment**
overwrites the value stored under a key in place, or appends a new entry. They are the memory of
a word RAM run on a Turing machine (`WordRAM.exists_simulation`), where keys are addresses and
values are words, but they are generic in both.

The record-table rows `Turing.exists_tableFindTM` and `Turing.exists_tableAppendTM` select by a
finite-state predicate and do not read a key from another tape; they are not used here.

## Main definitions

* `Turing.keyFields`, `Turing.keyTableLength`, `Turing.KeyTableAt`: the layout.
* `Turing.keyLookup`, `Turing.keyAssign`: the two operations on lists of entries.
* `Turing.keyTableWrite`: the tapes after laying a keyed table out.

## Main results

* `Turing.exists_keyLookupTM`: lookup, within `O(table + key + value)` steps.
* `Turing.exists_keyAssignTM`: assignment, within the same bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: a RAM's memory kept by a Turing machine as a
  list of address and value pairs, scanned at each access.)
-/

namespace Turing

/-! ## The layout -/

/-- **The fields of a keyed table's entries**: each entry `(k, v)` gives the two fields
`true :: k` and `true :: v`. -/
def keyFields (es : List (List Bool × List Bool)) : List (List (List Bool)) :=
  es.map fun e => [true :: e.1, true :: e.2]

/-- The fields of a keyed table's entries, as an equation. -/
theorem keyFields_def (es : List (List Bool × List Bool)) :
    keyFields es = es.map fun e => [true :: e.1, true :: e.2] := rfl

/-- **The length of a keyed table's layout**: the cells from the header's first to the last
field's last, separators included (the sentinels excluded). -/
def keyTableLength (es : List (List Bool × List Bool)) : ℕ :=
  (joinFields (tableFields [true] (keyFields es))).length

/-- The length of a keyed table's layout, as an equation. -/
theorem keyTableLength_def (es : List (List Bool × List Bool)) :
    keyTableLength es = (joinFields (tableFields [true] (keyFields es))).length := rfl

/-- **A keyed table on a tape**: tape `r` holds the record-table layout of the header `[true]`
and the entries `keyFields es` from the origin `o` (`Turing.TableAt`, with its two blank cells on
either side), and every cell after the layout is blank, so that the table can grow. -/
def KeyTableAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Prop :=
  TableAt d r o [true] (keyFields es) ∧
    ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none

/-- `KeyTableAt`, as an equivalence with its definition. -/
theorem keyTableAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt d r o es ↔ TableAt d r o [true] (keyFields es) ∧
      ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none :=
  Iff.rfl

/-- **The tapes after laying a keyed table out**: on tape `r`, the cells `[o, o + L)` hold the
layout of `es`, `L = keyTableLength es`; every other cell, of every tape, is unchanged. -/
def keyTableWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (q - o)
    else d.workTapes j q

/-- `keyTableWrite`, as an equation. -/
theorem keyTableWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) (j : Fin K) (q : ℤ) :
    keyTableWrite d r o es j q =
      if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
        then fieldsTape (tableFields [true] (keyFields es)) (q - o)
      else d.workTapes j q :=
  rfl

/-! ## The operations -/

/-- **Lookup**: the value of the first entry whose key is `k`, if any. -/
def keyLookup (es : List (List Bool × List Bool)) (k : List Bool) : Option (List Bool) :=
  (es.find? fun e => e.1 = k).map Prod.snd

/-- Lookup, as an equation. -/
theorem keyLookup_def (es : List (List Bool × List Bool)) (k : List Bool) :
    keyLookup es k = (es.find? fun e => e.1 = k).map Prod.snd := rfl

/-- **Assignment**: if some entry has the key `k`, every such entry's value becomes `v`;
otherwise the entry `(k, v)` is appended. -/
def keyAssign (es : List (List Bool × List Bool)) (k v : List Bool) :
    List (List Bool × List Bool) :=
  if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
  else es ++ [(k, v)]

/-- Assignment, as an equation. -/
theorem keyAssign_def (es : List (List Bool × List Bool)) (k v : List Bool) :
    keyAssign es k v =
      if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
      else es ++ [(k, v)] := rfl

/-! ## The rows

Both rows are five-tape machines over `Bool`: tape `0` holds the table, with its head at the
origin; tape `1` the key; tape `2` the value register; tapes `3` and `4` are blank scratch tapes
(`Turing.ScratchBlank`), left blank. Every head ends where it started. -/

/-- **Keyed lookup.** From the entry, with a keyed table `es` at the head of tape `0`, a key `k`
on tape `1` and a register word `w` on tape `2`, every value of the table as long as `w`, and
blank scratch tapes: the row writes over `w` the value stored under `k`, or `|w|` zeros if `k` is
absent, and stops at its exit within `C·(L + |k| + |w| + 1)` steps and radius, where `L` is the
table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** The field payloads follow their markers, so the catalog's word rows, which
need a blank at the word's offset `-1`, apply to a payload only through an adapter: blank the
marker cell (one step), run the row on the payload, now delimited, and write the marker back (one
step). An empty payload is then the empty word between two blanks. For each entry in turn:
compare its key payload with tape `1` in lockstep through the adapter (`Turing.compareTM`'s
method, returning both heads); on a match, copy the value payload to tape `2` through the adapter
(`Turing.copyTM`), return to the origin and exit; otherwise skip the entry's two fields
(`Turing.skipTM`). At the blank pair after the last field, clear tape `2` to
zeros over its own length and return to the origin. Each entry is crossed a constant number of
times. A comparison stops at the first differing cell, so it and the return of tape `1`'s head
cost at most a constant times the entry's key field plus one; summed over the entries this is
`O(L)`, and the final copy and return are `O(L + |k| + |w|)`. -/
theorem exists_keyLookupTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k w : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 w → (∀ e ∈ es, e.2.length = w.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + w.length + 1))
          (C * (keyTableLength es + k.length + w.length + 1))
          { d with state := some exit,
                   workTapes :=
                     wordWrite d 2 ((keyLookup es k).getD (List.replicate w.length false)) } := by
  sorry

/-- **Keyed assignment.** From the entry, with a keyed table `es` at the head of tape `0`, a key
`k` on tape `1` and a value `v` on tape `2`, every value of the table as long as `v`, and blank
scratch tapes: the row lays out `keyAssign es k v` from the origin, overwriting the value under
`k` in place or appending `(k, v)`, and stops at its exit within `C·(L + |k| + |v| + 1)` steps
and radius, where `L` is the old table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** Search as in `Turing.exists_keyLookupTM`, with its marker adapter. On a match,
copy tape `2` over the value payload through the adapter (same length, so the layout is unchanged elsewhere), and continue
the search through the rest of the table, overwriting every further match. If there was no match,
the head reaches the first blank of the pair after the table: write a separator, the field
`true :: k` from tape `1`, a separator and the field `true :: v` from tape `2`; the cells beyond
were blank (`KeyTableAt`), so the new layout's trailing blank pair is there. Return to the
origin. -/
theorem exists_keyAssignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k v : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 v → (∀ e ∈ es, e.2.length = v.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + v.length + 1))
          (C * (keyTableLength es + k.length + v.length + 1))
          { d with state := some exit, workTapes := keyTableWrite d 0 o (keyAssign es k v) } := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/InputBit.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.WordArith
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.InputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading an input bit at a position held in a word

The input of a machine is read in place: its head moves, and nothing is copied to a work tape.
This file states the row that reads the input bit at a position given as a signed word on a work
tape, with the input's length in binary on another: it writes the word `1` if the position lies
on the input and the bit there is `true`, and the word `0` otherwise, off the input and at
negative positions included. Its work-tape space is `O(W + log n)`, not `O(n)`, so a logarithmic
space bound survives it. It is the `rdIn` instruction of a word RAM run on a Turing machine
(`WordRAM.exists_simulation`).

## Main results

* `Turing.exists_inputBitTM`: the row, within `O(W + n)` steps and `O(W + log n)` cells of
  radius.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: the read-only input of a space-bounded machine;
  Exercise 1.9.)
-/

namespace Turing

/-- **Reading an input bit at a word's position.** A five-tape machine over `Bool`. From the entry,
with a word `u` of `W` bits on tape `0`, the input length `Nat.bits |x|` on tape `1`, a register
word of `W` cells on tape `2` and blank scratch tapes (`Turing.ScratchBlank`), the input head
anywhere: the row writes on tape `2` the word `1` if `0 ≤ u.toInt` and the input bit at position
`u.toInt` is `true`, and the word `0` otherwise (positions past the input read `false`), and
stops at its exit within `C·(W + |x| + 1)` steps, every work head within `C·(W + log |x| + 1)`
cells and back where it started. The input head ends somewhere. [AB09, §4.1, Exercise 1.9]

**Proof sketch.** Sign test (`Turing.exists_wordSignTM`): a negative position reads `0`.
Otherwise compare `u`'s value with `|x|` (both little-endian; a lockstep comparison of different
lengths, the longer word's excess bits deciding when nonzero): a position `≥ |x|` reads `0`.
Otherwise copy `u` to a scratch tape, increment it once (the input head's position `p + 1` holds
bit `p`; no overflow, since `u.toInt < |x|` and the sign bit is clear), and seek the input head
there with `Turing.exists_inputSeekTM`, whose work envelope is `O(W)` and time
`O(W + pos + p + 1) = O(W + |x|)`. Read the bit under the input head and write `1` or `0` over
the register (`Turing.exists_wordIntTM`). Clear the scratch tapes and return the heads. -/
theorem exists_inputBitTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (Nat.bits x.length) →
        WordAt d 2 w → w.length = W → ScratchBlank d →
        ∃ ip : Fin (x.length + 2),
          ReachesWithin R d {some exit} (C * (W + x.length + 1))
            (C * (W + (Nat.bits x.length).length + 1))
            { d with state := some exit, inputPos := ip,
                     workTapes := wordWrite d 2 (bvBits
                       (if 0 ≤ u.toInt ∧ x.getD u.toInt.toNat false = true then (1 : BitVec W)
                        else 0)) } := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Reach.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reaching an endpoint within bounds

Many rows of the construction layer are stated existentially: from a configuration satisfying a
precondition, the machine reaches a stated endpoint at some time within a bound, with no exit
earlier and every head within a radius. `Turing.ReachesWithin` names that shape once, and
`Turing.Contract.ofReaches` turns a row in that shape into a `Turing.Contract`, choosing the time,
so that existential rows compose with `Turing.Contract.seq`, `inPhase` and `branch`.

## Main definitions

* `Turing.ReachesWithin`: the endpoint is reached within `B` steps, no state of `X` earlier, every
  head within `E` cells of its start.
* `Turing.Contract.ofReaches`: the contract of a row stated with `ReachesWithin`.

## Main results

* `Turing.reachesWithin_iff`, `Turing.ReachesWithin.mono`.
* `Turing.Contract.ofReaches_time_le`, and the field equations of `Contract.ofReaches`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the framing adapted as `Turing.Contract` (design adaptation; full entry in
  `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **Reaching an endpoint within bounds.** `ReachesWithin M d X B E post`: run from `d`, the
machine `M` is at `post` at some time `t ≤ B`; at every earlier time its state is not in `X`; and
at every time up to `t` each work head is within `E` cells of where it was in `d`. -/
def ReachesWithin {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) : Prop :=
  ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
    (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
    M.runFrom d t = post

/-- `ReachesWithin`, as an equivalence with its definition. -/
theorem reachesWithin_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) :
    ReachesWithin M d X B E post ↔
      ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
        (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
        M.runFrom d t = post :=
  Iff.rfl

/-- Larger bounds: an endpoint reached within `B` steps and radius `E` is reached within any
`B' ≥ B` and `E' ≥ E`. -/
theorem ReachesWithin.mono {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {d : Cfg k Γ S x}
    {X : Set (Option S)} {B E B' E' : ℕ} {post : Cfg k Γ S x}
    (h : ReachesWithin M d X B E post) (hB : B ≤ B') (hE : E ≤ E') :
    ReachesWithin M d X B' E' post := by
  obtain ⟨t, ht, hcut, henv, hrun⟩ := h
  exact ⟨t, ht.trans hB, hcut, fun s hs j => (henv s hs j).trans (by exact_mod_cast hE), hrun⟩

/-- **The contract of a row stated with `ReachesWithin`.** If from the entry, under `pre`, the
machine reaches `post` within `B` steps and radius `E`, with no state of `X` earlier, and the
endpoint's state lies in `X`, then this is the contract with that precondition and endpoint, the
exits `X`, the time chosen from the row (`0` off the precondition), and the head intervals
`[pos - E, pos + E]`.

**Proof sketch.** Under the precondition the time is the chosen witness, so the run, the cut and
the envelope are the row's clauses, the envelope read through `abs_le`; the exit is `hX`. -/
noncomputable def Contract.ofReaches {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) :
    Contract M entry X ι x where
  pre := pre
  time i d := haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0
  post := post
  lo i d j := d.workTapePos j - E i d
  hi i d j := d.workTapePos j + E i d
  run i d hd hp := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
    exact (Classical.choose_spec (h i d hd hp)).2.2.2
  exit_mem i d hd hp := hX i d hd hp
  cut i d hd hp u hu := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    exact (Classical.choose_spec (h i d hd hp)).2.1 u hu
  env i d hd hp u hu j := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    have := (Classical.choose_spec (h i d hd hp)).2.2.1 u hu j
    rw [abs_le] at this
    exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- The contract of a row stated with `ReachesWithin` takes at most the row's bound.

**Proof sketch.** Under the precondition the time is the chosen witness, which is at most `B`. -/
theorem Contract.ofReaches_time_le {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : pre i d) :
    (Contract.ofReaches pre B E post h hX).time i d ≤ B i d := by
  show (haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0) ≤ B i d
  simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
  exact (Classical.choose_spec (h i d hd hp)).1

attribute [simps (config := { isSimp := false }) pre post lo hi] Contract.ofReaches

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the core

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
This module is the core of the layering split (design §16a item 4). It holds the MIG-0a core,
moved here from `Build/Contract.lean` as landed on 2026-10-13 (after the MIG-0a gate closed at
round 2) with no statement changed, and MIG-0b's segment, round and joint-trajectory layers, the
sanity lemmas, state renaming and the macro-step lockstep. It imports only the machine core
(`Simulation`, `StateRenaming`) and `Mathlib.Tactic.Linarith`, so that `Build/Loop` and
`Build/CounterLoop` can import it. The seam, embedding and routine adapters are in
`Build/Contract/Seam`, `Build/Contract/Embed` and `Build/Contract/Catalog`, and the symbol lift in
`Build/Contract/Lift` (the facade `Build/Contract` lists them).

A *contract* packages what the library's framed rows state one by one (design §14 item 0,
§16): started at `entry` in a configuration satisfying the precondition, the machine reaches
the endpoint `post` after **exactly** `time` steps, has **not** reached an exit before, and
keeps every work head inside an interval. "Within `B`" and the space bound are derived. It is
the **first-exit** specialization; the layers below cover what it cannot: *segments*, whose
endpoint need not be a first exit; *rounds*, which return to their anchor or escape; and *joint
trajectories*, relations on the whole head vector.

## Design

* **Exact time and the cut are fields** (§16). The cut includes time `0`, as in about 45 of the
  library's rows. A row that returns to its own anchor, so that its cut starts at time `1` (the
  advancing writer `Turing.writeAdvTM_run_ofCfg`), is a `Turing.ReturnContract`, turned into a
  contract by the release adapter (`Turing.ReturnContract.release` in `Build/Contract/Seam`,
  over `Turing.seamReleaseTM`). The install and emit calls (`Turing.FinTM.exists_installCallTM`,
  `Turing.FinTM.exists_emitCallTM`) quantify separate `entry` and `exit` states that may
  coincide: with arbitrary witnesses, split on `entry = exit` (see `Turing.ReturnContract`).
* **Exits form a set**, so one structure covers single anchors, verdict pairs (`yes`/`no`),
  loop exits (`done`/`escape`) and halting (`none`).
* **The endpoint is a function** of a data index `i : ι` and the start configuration. Data the
  module reads (a stored word, a record's fields) is the index; the precondition says where it
  is stored.
* **Head envelopes are intervals** `[lo, hi]` per tape, functions of the index and the start
  configuration. The radius form is a special case (`Turing.Contract.mem_Icc_of_abs_le`); space
  follows from `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
* **Frames are part of the endpoint** (rows already state them as `{ d with … }`); a derived
  layer names them for composition proofs (user decision, 2026-10-12): `Turing.Cfg.SameOutside`,
  its `.keep` lemmas, and `Turing.Contract.Frames`, adapted from [AFM26]'s framing.
  `Turing.Cfg.SameOutside` is an endpoint relation on work-tape contents only.
* **Segments** (MIG-0b; `Turing.Segment`): fixed-length runs, possibly of length zero, between
  two actual configurations, avoiding a forbidden set strictly before the end, with a relation on
  the whole head vector through the end (`CfgRecord`'s `RecordRun`, `SingleTape`'s `DGSpan`,
  `EmitIterEmbed`'s `SafeRun`, `CounterLoop`'s `counterSpan`). `Turing.SafeSegment` also keeps
  the endpoint off the set (`Primitives`' `splitSafe`).
* **Rounds** (MIG-0b; `Turing.Round`, `Turing.RoundContract`): positive runs from an anchor that
  end at the anchor or in an escape set, live and off both strictly in between (the find round
  of `RecordTable`, the counter loop's body interface).
* **Joint trajectories** (MIG-0b; `Turing.Contract.Traj`): a relation on the head vector at
  every time through the endpoint, derived like `Turing.Contract.Frames`.
* **Universes:** alphabet, states and index in `Type`, the universe of `FinTM`, `phaseHostTM`
  and `counterLoopTMVia` (backlog UNIV-1 folds in here).

## Main definitions

* `Turing.Contract`: the structure; `Turing.Contract.Positive`.
* `Turing.Contract.trans`: first-exit sequencing on one machine, with no dispatch step.
* `Turing.Cfg.SameOutside`, `Turing.Contract.Frames`: the derived frame layer.
* `Turing.ReturnContract`: returning modules.
* `Turing.HeadBox`, `Turing.Segment`, `Turing.SafeSegment`, `Turing.Contract.ofSegment`: the
  segment layer and its bridge to contracts.
* `Turing.Contract.zero`: the zero-time contract of a machine started at its own exit.
* `Turing.roundStop`, `Turing.Round`, `Turing.roundOrbit`, `Turing.RoundContract` (with
  `returning` and `escaping`), `Turing.ReturnContract.toRound`, `Turing.RoundContract.hullLo`
  and `hullHi`: the round layer.
* `Turing.Contract.Traj`: the joint-trajectory layer.
* `Turing.Contract.mapState`: state renaming along an embedding.
* `Turing.Lockstep`, `Turing.Contract.lockstep`: the macro-step lockstep and its transport.

## Main results

* `Turing.Contract.within`, `Turing.Contract.spaceUsedByTape_le`: the derived forms.
* `Turing.Contract.live`: a contract run is live before its endpoint.
* `Turing.Cfg.SameOutside.keep_word`, `Turing.Cfg.SameOutside.keep_blank`: frame preservation.
* `Turing.Segment.trans`, `Turing.Segment.iterate_seq`, `Turing.Segment.live`,
  `Turing.Segment.time_eq`, `Turing.SafeSegment.trans`, `Turing.Contract.segment`: segment
  concatenation (of two, and along a sequence), liveness, uniqueness of first exits, and the
  contract bridge.
* `Turing.Round.iterate_seq`, `Turing.Round.iterate`, `Turing.RoundContract.orbit_round`: round
  iteration along a sequence of starts, and along an orbit.
* `Turing.Contract.Traj.trans`, `Turing.Contract.Frames.trans`: preservation by `trans`.
* `Turing.Contract.time_eq_zero_iff`, `Turing.Contract.trans_positive`: sanity lemmas.
* `Turing.Contract.lockstep_admissible`: the target entry compatible with the encoding.
* `Turing.Contract.trans_pre`, `_time`, `_post`, `_lo`, `_hi` — the specification API
  (user, 2026-10-16): the fields of a sequenced contract as equations, generated by
  `simps` without the `simp` attribute, so that consumers never unfold the definition.
* `Turing.Contract.ofSegment_pre`, `_time`, `_post`, `_lo`, `_hi` — the segment bridge's
  fields, the same way (the specification API's gate, finding 1).
* `Turing.Contract.zero_pre`, `_time`, `_post`, `_lo`, `_hi` — the zero-time contract's
  fields as equations.
* `Turing.RoundContract.returning_*`, `Turing.RoundContract.escaping_*`,
  `Turing.ReturnContract.toRound_*`, `Turing.Contract.mapState_*`, `Turing.Contract.lockstep_*`
  (`pre`, `time`, `post`, `lo`, `hi`) — the remaining constructors' fields, the same way.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math` (https://github.com/anthropics/formal-math),
  project `3sum-apsp`, commit `e1a4e650` (2026-10-05), Apache-2.0, © Anthropic, PBC; examined
  2026-10-12 (design §15, *Prior art examined*). Design adaptation (policy §2): the framing of
  `ThreeSumApsp/Lang/Regions.lean` (`SameOn`, `SameOutside` and the `.keep` lemmas), adapted as
  `Turing.Cfg.SameOutside`, its `.keep` lemmas and `Turing.Contract.Frames`; and the
  specification-only calls of `ThreeSumApsp/Lang/Calls.lean` (`Meets`, over the program logic
  `Ends` of `ThreeSumApsp/Lang/Logic.lean`), adapted as `Turing.Contract`, through which the
  compositions use their operands. These upstream files are vendored, with the local changes
  their headers list, as `TCSlib/Programs/Light/Regions.lean`, `Calls.lean` and `Logic.lean`.
  The treatment of time differs: exact time and a no-earlier-exit cut, not "within `T`" (§16).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16: the alphabet-reduction simulation, the
  model case of `Turing.Lockstep`.)
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **A framed contract** (design §14 item 0, §16). For every data index `i` and every start
configuration `d` at `entry` satisfying `pre i d` (an *admissible* start), the machine reaches
`post i d` after exactly `time i d` steps; `post i d` is at an exit; no exit is reached earlier
(the cut includes time `0`); and through the endpoint every work head `j` stays in
`[lo i d j, hi i d j]`. Nothing is asserted for other starts. This is the first-exit
specialization (see the module docstring for the segment, round and joint-trajectory layers of
MIG-0b).

[AFM26], design adaptation: a specification that a caller uses instead of the run, as with the
specification-only calls (`Meets`) of `Lang/Calls.lean`. Unlike there, the time is exact and
comes with a no-earlier-exit cut, rather than "within `T`" (§16). -/
structure Contract {S : Type} (M : MultiTapeTM k Γ S) (entry : S) (exits : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition on the start configuration, for data `i`. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  run : ∀ i d, d.state = some entry → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits
  cut : ∀ i d, d.state = some entry → pre i d →
    ∀ u < time i d, (M.runFrom d u).state ∉ exits
  env : ∀ i d, d.state = some entry → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace Contract

section Derived

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The derived "within `B`" form, the shape of the library's existential rows. -/
theorem within (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) {B : ℕ} (hB : C.time i d ≤ B) :
    ∃ t ≤ B, (∀ u < t, (M.runFrom d u).state ∉ exits) ∧ M.runFrom d t = C.post i d :=
  ⟨C.time i d, hB, C.cut i d hd hp, C.run i d hd hp⟩

/-- The derived per-tape space bound: the envelope's width. -/
theorem spaceUsedByTape_le (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) (j : Fin k) :
    M.spaceUsedByTape d (C.time i d) j ≤ (C.hi i d j + 1 - C.lo i d j).toNat :=
  M.spaceUsedByTape_le_card_Icc d (C.time i d) j (C.lo i d j) (C.hi i d j)
    fun u hu => C.env i d hd hp u hu j

/-- A positive running time on every admissible start: what a loop round needs. -/
def Positive (C : Contract M entry exits ι x) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → 0 < C.time i d

/-- The radius form of an envelope is the interval form about the start position. -/
theorem mem_Icc_of_abs_le {p q R : ℤ} (h : |p - q| ≤ R) : p ∈ Finset.Icc (q - R) (q + R) := by
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_le.mp h]

end Derived

/-- **First-exit sequencing on one machine**: run `C₁` to its single exit `e₂`, then `C₂` from
there. Times add with no dispatch step; the envelopes take the pointwise hull. `C₂`'s
precondition is needed only at `C₁`'s actual endpoint (`hlink`), for the linked index. `hX` says
that `C₁` does not pass through an exit of `C₂` before its own exit; it cannot be dropped, since
`C₁`'s cut excludes only `e₂`. This is not a general `RecordRun` concatenation: a segment whose
endpoint need not be a first exit belongs to the segment layer (`Turing.Segment.trans`).

**Proof sketch.** Split the time at `C₁`'s time `t₁`. By `C₁`'s run, the run for `t₁ + v` steps
is `C₂`'s run for `v` steps from `C₁`'s endpoint, which is at `e₂` and satisfies `C₂`'s
precondition; this gives the run and the exit. Before `t₁` the cut is `hX`; at a time `t₁ + v`
below the total it is `C₂`'s cut at `v`. Up to `t₁` the heads are in `C₁`'s envelope, and after
it in `C₂`'s; the hull contains both. -/
def trans {S : Type} {M : MultiTapeTM k Γ S} {e₁ e₂ : S} {X : Set (Option S)} {ι κ : Type}
    {x : List Γ} (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d →
      ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X) :
    Contract M e₁ X ι x where
  pre := C₁.pre
  time i d := C₁.time i d + C₂.time (link i) (C₁.post i d)
  post i d := C₂.post (link i) (C₁.post i d)
  lo i d j := min (C₁.lo i d j) (C₂.lo (link i) (C₁.post i d) j)
  hi i d j := max (C₁.hi i d j) (C₂.hi (link i) (C₁.post i d) j)
  run i d hd hp := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    show M.runFrom d (C₁.time i d + C₂.time (link i) (C₁.post i d)) =
      C₂.post (link i) (C₁.post i d)
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact C₂.run _ _ hx (hlink i d hd hp)
  exit_mem i d hd hp :=
    C₂.exit_mem _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp)
  cut i d hd hp u hu := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u < C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u < C₁.time i d
    · exact hX i d hd hp u h
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact C₂.cut _ _ hx (hlink i d hd hp) v (by omega)
  env i d hd hp u hu j := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u ≤ C₁.time i d
    · exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i d hd hp u h j)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)

/-! The specification API (user, 2026-10-16): `Turing.Contract.trans`'s data fields as
equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] trans

/-- **Liveness**: a contract run is live strictly before its endpoint. A halt would persist to
the endpoint, putting `none` among the exits, which the cut excludes.

**Proof sketch.** Halting is absorbing, so a halt before the time would make the endpoint's
state `none`; `exit_mem` then puts `none` among the exits, against the cut at that time. -/
theorem live {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {exits : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry exits ι x) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) {u : ℕ}
    (hu : u < C.time i d) : (M.runFrom d u).state ≠ none := by
  intro h
  have hend : (M.runFrom d (C.time i d)).state ≠ none := by
    intro h'
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h'] at hx
    exact C.cut i d hd hp u hu (h ▸ hx)
  exact MultiTapeTM.runFrom_state_ne_none_of_le M d _ hend u hu.le h

end Contract

/-! ## Frames: the derived layer (user decision, 2026-10-12)

A contract's endpoint already states its frame (`{ d with … }`). The predicates below name the
frame for composition proofs: a *footprint* per tape, `Turing.Cfg.SameOutside`, its `.keep`
lemmas, and `Turing.Contract.Frames`. They are derived properties, not fields. The layer is
[AFM26]'s framing (`SameOn` and the `.keep` lemmas of `Lang/Regions.lean`), adapted from memory
cells to the cells of each work tape (design adaptation). -/

/-- `d'` agrees with `d` outside the footprint: every work-tape cell off `fp j` is unchanged.
This is an **endpoint relation on work-tape contents only**: it constrains neither the control
state, the heads, the input position nor the output, and says nothing about intermediate
times. A consumer that needs a cell kept at every time must keep the corresponding trajectory
fact. The two configurations may have different state types.

[AFM26], design adaptation: `SameOn` of `Lang/Regions.lean` (cells kept off a set, as in its
`SameOutside`), here per work tape. -/
def Cfg.SameOutside {S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) : Prop :=
  ∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q

/-- `Turing.Cfg.SameOutside fp d d'` holds exactly when every cell `q` of every work tape `j`
outside `fp j` holds in `d'` what it holds in `d`:
`∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q` (the definition as a lemma). -/
theorem Cfg.sameOutside_iff {S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) :
    Cfg.SameOutside fp d d' ↔ ∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q :=
  Iff.rfl

/-- Footprints compose by union. -/
theorem Cfg.SameOutside.trans {S S' S'' : Type} {x : List Γ} {fp fp' : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} {d'' : Cfg k Γ S'' x} (h : Cfg.SameOutside fp d d')
    (h' : Cfg.SameOutside fp' d' d'') : Cfg.SameOutside (fun j => fp j ∪ fp' j) d d'' := by
  intro j q hq
  simp only [Set.mem_union, not_or] at hq
  rw [h' j q hq.2, h j q hq.1]

/-- Replacing the control state keeps the frame. -/
theorem Cfg.SameOutside.mapState {S S' S'' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (f : S' → S'') :
    Cfg.SameOutside fp d (d'.mapState f) := fun j q hq => h j q hq

/-- **`.keep`, a stored word**: a delimited word lying outside the footprint survives. If `d`
holds `w` at offset `o` of tape `j`, its two blank delimiters included, and none of those cells
is in the footprint, then `d'` holds `w` there too. [AFM26], design adaptation: the `.keep`
lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_word {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k) (o : ℤ)
    (w : List Γ) (hout : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → o + p ∉ fp j)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d.workTapes j (o + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d'.workTapes j (o + p) = FinTM.bufferTape w p :=
  fun p hp₁ hp₂ => (h j (o + p) (hout p hp₁ hp₂)).trans (hw p hp₁ hp₂)

/-- **`.keep`, a blank tape**: a tape with an empty footprint that was blank stays blank.
[AFM26], design adaptation: the `.keep` lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_blank {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k)
    (hfp : fp j = ∅) (hb : ∀ q, d.workTapes j q = none) : ∀ q, d'.workTapes j q = none :=
  fun q => (h j q (by simp [hfp])).trans (hb q)

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- A contract **frames** the footprint `fp` when every endpoint agrees with its start outside
it: for every index `i` and every admissible start `d`, `Turing.Cfg.SameOutside (fp i d)` holds
between `d` and `C.post i d`. [AFM26], design adaptation: a routine's `SameOn` promise for the
cells it leaves alone (`Lang/Regions.lean`). -/
def Frames (C : Contract M entry exits ι x) (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → Cfg.SameOutside (fp i d) d (C.post i d)

/-- A contract frames `fp` exactly when, for every index `i` and every admissible start `d`,
every cell `q` of every work tape `j` outside `fp i d j` holds at the endpoint what it held at
the start. This is the definition unfolded, as a `@[simp]` lemma, so that `simp` and `rw` see
the footprint. -/
@[simp] theorem frames_iff (C : Contract M entry exits ι x)
    (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) :
    C.Frames fp ↔ ∀ i d, d.state = some entry → C.pre i d →
      ∀ j q, q ∉ fp i d j → (C.post i d).workTapes j q = d.workTapes j q :=
  Iff.rfl

end Contract

/-! ## Returning contracts

Their release adapter is in `Build/Contract/Seam`. -/

/-- **A returning contract**: from every admissible start at `anchor`, the run first comes back
to `anchor` at a positive exact time. The endpoint is at the anchor, no strictly positive
earlier time is at the anchor (the cut starts at time `1`, since time `0` is at the anchor),
and through the endpoint every head stays in its interval. `Turing.ReturnContract.release`
turns it into a `Turing.Contract`.

The advancing writer (`Turing.writeAdvTM_run_ofCfg` in `Build/Scan`, anchor `0`, time
`|w₀| + 1`) genuinely returns to its anchor and has this shape. The install and emit calls
(`Turing.FinTM.exists_installCallTM`, `Turing.FinTM.exists_emitCallTM`, in `Build/Loop`) also
have positive cuts, but quantify separate `entry` and `exit` states that may coincide. With
arbitrary witnesses, split on `entry = exit`: when they are equal, use a `ReturnContract`; when
they differ, use an ordinary `Turing.Contract` with exits `{some exit}`, whose cut at time `0`
follows from `entry ≠ exit` and at positive times is the row's positive cut. Either way the
canonical `Cfg.ofWords` start goes into the precondition, and the time bound is kept. A round
that may instead end at a distinct escape is not a `ReturnContract`: it belongs to MIG-0b's
round layer. -/
structure ReturnContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (ι : Type)
    (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, back at the anchor. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_eq : ∀ i d, d.state = some anchor → pre i d → (post i d).state = some anchor
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ≠ some anchor
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

/-! ## The segment layer (design §16a, MIG-0b item 1)

A *segment* is a run of a fixed length, possibly zero, between two actual configurations (the
configuration seam), that avoids a forbidden set of states before its end, with a relation on the
whole head vector at every time up to and including its end: `CfgRecord`'s `RecordRun` (its
verdict pair forbidden, a radius about a base), `EmitIterEmbed`'s `SafeRun` (one avoided state),
`SingleTape`'s `DGSpan` (nothing forbidden, an interval on one tape) and `CounterLoop`'s
`counterSpan` (both exits forbidden, the counter head's interval and a relation on the body heads,
with a genuine zero-time case in `counter_rounds`). The relation is the **joint-trajectory layer
for general segments**: it constrains the whole head vector, so a shared witness for all heads
(the counter loop's round and offset) survives concatenation. Its endpoint need not be a first
visit of anything: the MIG-0a auditor's idling machine (round 1, counterexample 4) gives a
length-2 segment from `a` to `a`. A segment whose endpoint lies in its forbidden set is a first
exit, and then it is a contract (`Turing.Contract.ofSegment`).

An **endpoint-inclusive** segment (`Turing.SafeSegment`) also keeps its endpoint off the forbidden
set: `Primitives`' `splitSafe` and `Catalog`'s `f2_splitSafe`, whose phase traces avoid the anchor
at every time through the endpoint. Such a segment is never a first exit (MIG-0a gate, round 2):
a positive stationary run away from the anchor is one, but no first-exit contract of that
duration exists. -/

/-- The **interval box** `∏ⱼ [lo j, hi j]`, as a predicate on head vectors: the per-tape
envelope of `Turing.Contract`, seen as one relation on the whole head vector. -/
def HeadBox (lo hi : Fin k → ℤ) (p : Fin k → ℤ) : Prop :=
  ∀ j, p j ∈ Finset.Icc (lo j) (hi j)

/-- A head vector `p` lies in the box `Turing.HeadBox lo hi` exactly when
`p j ∈ [lo j, hi j]` on every tape `j` (the definition as a lemma). -/
theorem headBox_iff (lo hi p : Fin k → ℤ) :
    HeadBox lo hi p ↔ ∀ j, p j ∈ Finset.Icc (lo j) (hi j) :=
  Iff.rfl

/-- **A segment**: the run of `M` from `a` reaches `b` after exactly `t` steps, no state at a
time before `t` lies in the forbidden set `F`, and the head vector satisfies `P` at every time up
to `t`. Nothing is said about the endpoint's state. -/
def Segment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
    ∀ u ≤ t, P (M.runFrom a u).workTapePos

/-- `Turing.Segment M F P a b t` holds exactly when `M.runFrom a t = b`, no state at a time
`u < t` lies in `F`, and the head vector satisfies `P` at every time `u ≤ t` (the definition as
a lemma). -/
theorem segment_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) :
    Segment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos :=
  Iff.rfl

namespace Segment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty segment: zero steps, with the start's head vector satisfying the relation. -/
theorem zero {a : Cfg k Γ S x} (h : P a.workTapePos) : Segment M F P a a 0 :=
  ⟨rfl, fun _ hu => absurd hu (Nat.not_lt_zero _), fun u hu => by
    obtain rfl : u = 0 := Nat.le_zero.mp hu
    exact h⟩

/-- A single step from a start outside the forbidden set. -/
theorem one {a : Cfg k Γ S x} (ha : a.state ∉ F) (h₀ : P a.workTapePos)
    (h₁ : P (M.step a).workTapePos) : Segment M F P a (M.step a) 1 := by
  refine ⟨MultiTapeTM.runFrom_one _ _, fun u hu => ?_, fun u hu => ?_⟩
  · obtain rfl : u = 0 := by omega
    exact ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · exact h₀
    · rw [MultiTapeTM.runFrom_one]
      exact h₁

/-- **Same-machine concatenation** (the `recordRun_trans` pattern): segments sharing the forbidden
set and the relation concatenate, with lengths adding and **no dispatch step**.

**Proof sketch.** Split a time at the first length `t`. Before it, use the first segment; after
it, the run is the second segment's from `b` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : Segment M F P a b t)
    (g : Segment M F P b c v) : Segment M F P a c (t + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h.1, g.1], ?_, ?_⟩
  · intro u hu
    by_cases hut : u < t
    · exact h.2.1 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.1 _ (by omega)
  · intro u hu
    by_cases hut : u ≤ t
    · exact h.2.2 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.2 _ (by omega)

/-- **Segments compose along a sequence**: if, for each `r < n`, the run from `cs r` is a segment
of `τ r` steps to `cs (r + 1)`, all with the forbidden set `F` and the head relation `P`, and `P`
holds at `cs 0`, then the run from `cs 0` is one segment of `∑ r < n, τ r` steps to `cs n`. The
starts `cs r` are arbitrary configurations: unlike `Turing.Round.iterate_seq`, they need not share
a state.

**Proof sketch.** Induction on `n`: the empty sequence is `Turing.Segment.zero`, and each further
segment is appended by `Turing.Segment.trans`. -/
theorem iterate_seq (cs : ℕ → Cfg k Γ S x) (τ : ℕ → ℕ) (h0 : P (cs 0).workTapePos) (n : ℕ)
    (h : ∀ r < n, Segment M F P (cs r) (cs (r + 1)) (τ r)) :
    Segment M F P (cs 0) (cs n) (∑ r ∈ Finset.range n, τ r) := by
  induction n with
  | zero => exact Segment.zero h0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun r hr => h r (by omega)).trans (h n (by omega))

/-- Weakening: a smaller forbidden set and a weaker relation. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : Segment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) : Segment M F' P' a b t :=
  ⟨h.1, fun u hu hm => h.2.1 u hu (hF hm), fun u hu => hP _ (h.2.2 u hu)⟩

/-- Two relations along one segment hold jointly. -/
theorem and {Q : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t)
    (g : Segment M F Q a b t) : Segment M F (fun p => P p ∧ Q p) a b t :=
  ⟨h.1, h.2.1, fun u hu => ⟨h.2.2 u hu, g.2.2 u hu⟩⟩

/-- An initial part of a segment is a segment. -/
theorem take {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P a (M.runFrom a u) u :=
  ⟨rfl, fun v hv => h.2.1 v (by omega), fun v hv => h.2.2 v (by omega)⟩

/-- A final part of a segment is a segment.

**Proof sketch.** Shift every time by `u` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem drop {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P (M.runFrom a u) b (t - u) := by
  refine ⟨?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' hu]
    exact h.1
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.1 _ (by omega)
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.2 _ (by omega)

/-- **First exits are unique**: two segments from one start, each ending in its forbidden set,
have the same length. This is what a proof clock (`RecordTable`'s `rt_findClock`) needs.

**Proof sketch.** If one were shorter, its endpoint, which is in the forbidden set, would be a
state of the longer one before its end. -/
theorem time_eq {a b b' : Cfg k Γ S x} {t t' : ℕ} {P' : (Fin k → ℤ) → Prop}
    (h : Segment M F P a b t) (hb : b.state ∈ F) (h' : Segment M F P' a b' t')
    (hb' : b'.state ∈ F) : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd (h.1 ▸ hb) (h'.2.1 t hlt)
  · exact heq
  · exact absurd (h'.1 ▸ hb') (h.2.1 t' hgt)

/-- Prepending one step from outside the forbidden set (the `SafeRun.cons` pattern). -/
theorem cons {a a₁ b : Cfg k Γ S x} {t : ℕ} (hstep : M.step a = a₁) (ha : a.state ∉ F)
    (h₀ : P a.workTapePos) (h : Segment M F P a₁ b t) : Segment M F P a b (1 + t) := by
  have h₁ : P a₁.workTapePos := by
    have := h.2.2 0 (Nat.zero_le _)
    rwa [MultiTapeTM.runFrom_zero] at this
  have hs : Segment M F P a a₁ 1 := by
    have h1 := one (M := M) ha h₀ (by rw [hstep]; exact h₁)
    rwa [hstep] at h1
  exact hs.trans h

/-- **Liveness**: a segment whose endpoint is live is live throughout, so `none` can be added to
its forbidden set. Halting is absorbing.

**Proof sketch.** A halt before the end would persist to the endpoint
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
theorem live {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t) (hb : b.state ≠ none) :
    Segment M (insert none F) P a b t := by
  refine ⟨h.1, fun u hu hm => ?_, h.2.2⟩
  rcases hm with hm | hm
  · exact MultiTapeTM.runFrom_state_ne_none_of_le M a t (by rw [h.1]; exact hb) u hu.le hm
  · exact h.2.1 u hu hm

end Segment

/-- **An endpoint-inclusive segment**: a segment whose endpoint is also off the forbidden set, so
that no time up to and including the end is in it. This is `splitSafe`'s shape; it is never a
first exit. -/
def SafeSegment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  Segment M F P a b t ∧ b.state ∉ F

/-- An endpoint-inclusive segment avoids the forbidden set at every time through its end.

**Proof sketch.** Times before the end are the segment's cut; the end is the endpoint. -/
theorem safeSegment_iff {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
    {P : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} :
    SafeSegment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u ≤ t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos := by
  constructor
  · rintro ⟨⟨hr, hc, hp⟩, hb⟩
    refine ⟨hr, fun u hu => ?_, hp⟩
    rcases Nat.lt_or_ge u t with h | h
    · exact hc u h
    · obtain rfl : u = t := le_antisymm hu h
      rw [hr]
      exact hb
  · rintro ⟨hr, hc, hp⟩
    refine ⟨⟨hr, fun u hu => hc u hu.le, hp⟩, ?_⟩
    rw [← hr]
    exact hc t le_rfl

namespace SafeSegment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty endpoint-inclusive segment, at a start off the forbidden set. -/
theorem zero {a : Cfg k Γ S x} (ha : a.state ∉ F) (h : P a.workTapePos) :
    SafeSegment M F P a a 0 :=
  ⟨Segment.zero h, ha⟩

/-- Endpoint-inclusive segments concatenate at their configuration seam (`splitSafe_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : SafeSegment M F P a b t)
    (g : SafeSegment M F P b c v) : SafeSegment M F P a c (t + v) :=
  ⟨h.1.trans g.1, g.2⟩

/-- Weakening an endpoint-inclusive segment. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : SafeSegment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) :
    SafeSegment M F' P' a b t :=
  ⟨h.1.mono hF hP, fun hm => h.2 (hF hm)⟩

/-- **Never a first exit**: the endpoint of an endpoint-inclusive segment is off the forbidden
set, so a contract with those exits cannot end there. -/
theorem endpoint_not_mem {a b : Cfg k Γ S x} {t : ℕ} (h : SafeSegment M F P a b t) :
    b.state ∉ F :=
  h.2

end SafeSegment

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **Contract to segment**: every admissible run of a contract is a segment that avoids the
exits, ends at the endpoint, and keeps the heads in the envelope box. -/
theorem segment (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (HeadBox (C.lo i d) (C.hi i d)) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, fun u hu j => C.env i d hd hp u hu j⟩

/-- **Segment to contract** (the bridge when the endpoint is a first exit): a family of segments
that avoid `exits` and end in `exits`, with an interval box, is a contract. A segment avoiding a
larger forbidden set is first weakened by `Turing.Segment.mono`. -/
def ofSegment (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (lo hi : ι → Cfg k Γ S x → Fin k → ℤ)
    (seg : ∀ i d, d.state = some entry → pre i d →
      Segment M exits (HeadBox (lo i d) (hi i d)) d (post i d) (time i d))
    (exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits) :
    Contract M entry exits ι x where
  pre := pre
  time := time
  post := post
  lo := lo
  hi := hi
  run i d hd hp := (seg i d hd hp).1
  exit_mem := exit_mem
  cut i d hd hp := (seg i d hd hp).2.1
  env i d hd hp u hu j := (seg i d hd hp).2.2 u hu j

/-! The specification API (user, 2026-10-16; its gate, finding 1): the segment bridge's data
fields as equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] ofSegment

/-- **The zero-time contract** of a machine started at its own exit `e`: every start is
admissible, the run is empty (`Turing.Segment.zero`), the endpoint is the start and the envelope
is the start's heads. It is the continuation of a branch or a phase that has nothing left to do. -/
def zero (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) : Contract M e {some e} ι x :=
  ofSegment (fun _ _ => True) (fun _ _ => 0) (fun _ d => d) (fun _ d => d.workTapePos)
    (fun _ d => d.workTapePos)
    (fun _ _ _ _ => Segment.zero
      ((headBox_iff _ _ _).mpr fun _ => Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
    (fun _ _ hd _ => by rw [hd]; exact Set.mem_singleton _)

/-! The zero-time contract's data fields as equations, without the `simp` attribute. -/

/-- Every start is admissible for `Turing.Contract.zero`. -/
theorem zero_pre (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).pre i d = True :=
  rfl

/-- `Turing.Contract.zero` takes no step. -/
theorem zero_time (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).time i d = 0 :=
  rfl

/-- `Turing.Contract.zero`'s endpoint is its start. -/
theorem zero_post (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).post i d = d :=
  rfl

/-- `Turing.Contract.zero`'s lower envelope is its start's heads. -/
theorem zero_lo (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).lo i d = d.workTapePos :=
  rfl

/-- `Turing.Contract.zero`'s upper envelope is its start's heads. -/
theorem zero_hi (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).hi i d = d.workTapePos :=
  rfl

/-- **The time-derived envelope of a contract**: every head stays within `time` cells of its
start, whatever the contract's own envelope says. -/
theorem time_envelope (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x) (u : ℕ)
    (hu : u ≤ C.time i d) (j : Fin k) :
    (M.runFrom d u).workTapePos j ∈
      Finset.Icc (d.workTapePos j - C.time i d) (d.workTapePos j + C.time i d) := by
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M d u j
  rw [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ C.time i d := by exact_mod_cast hu
  constructor <;> omega

end Contract

/-! ## The round layer (design §16a, MIG-0b item 2)

A *round* starts at its anchor `a` and ends, after a positive exact time, back at `a` or in an
escape set `E`; at every strictly intermediate time it is live and visits neither `a` nor `E`.
This is the shape of `RecordTable`'s `rt_find_round_entry` and of the counter loop's **body
interface** (the round hypothesis of `counterLoopTMVia_run_done`, `_run_escape`): a
`Turing.Contract` fails its time-zero cut there, and a `Turing.ReturnContract` excludes the escape
(MIG-0a gate, round 1, counterexample 5). The counter loop's **host** runs are not rounds: they,
and the private `counterSpan` that describes them, are segments with a joint relation, with a
genuine zero-time case (MIG-0a gate, round 2). The counter loop over round contracts is in
`Build/CounterLoop`. -/

/-- The states a round's interior avoids: halting, the anchor and the escapes. -/
def roundStop {S : Type} (a : S) (E : Set (Option S)) : Set (Option S) :=
  insert none (insert (some a) E)

/-- Outside the round stop set means live, off the anchor and off the escapes: the form in which
the rows state their round cuts. -/
theorem not_mem_roundStop {S : Type} {a : S} {E : Set (Option S)} {q : Option S} :
    q ∉ roundStop a E ↔ ∃ s, q = some s ∧ s ≠ a ∧ some s ∉ E := by
  constructor
  · intro h
    cases q with
    | none => exact absurd (Set.mem_insert _ _) h
    | some s =>
      refine ⟨s, rfl, fun hs => h ?_, fun hs => h ?_⟩
      · rw [hs]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hs)
  · rintro ⟨s, rfl, hsa, hsE⟩ h
    rcases h with h | h | h
    · exact Option.some_ne_none s h
    · exact hsa (Option.some.inj h)
    · exact hsE h

/-- **A round** of `M` from `c`, with anchor `a` and escape set `E`: `c` is at the anchor, the
exact time `t` is positive, the run reaches `c'` at `t`, `c'` is at the anchor or in `E`, every
strictly intermediate state is live and off the anchor and `E`, and the head vector satisfies
`P` at every time up to `t`. -/
def Round {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) : Prop :=
  c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧ c'.state ∈ insert (some a) E ∧
    (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
    ∀ u ≤ t, P (M.runFrom c u).workTapePos

/-- `Turing.Round M a E P c c' t` holds exactly when `c` is at the anchor `a`, `0 < t`,
`M.runFrom c t = c'`, the state of `c'` is `some a` or in `E`, every state at a time
`0 < u < t` lies outside `Turing.roundStop a E`, and the head vector satisfies `P` at every time
`u ≤ t` (the definition as a lemma). -/
theorem round_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) :
    Round M a E P c c' t ↔ c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧
      c'.state ∈ insert (some a) E ∧
      (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
      ∀ u ≤ t, P (M.runFrom c u).workTapePos :=
  Iff.rfl

namespace Round

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- **A round avoiding its escapes is a segment against them**, whatever its endpoint: at time
`0` it is at the anchor, which is no escape, and later it avoids the stop set. When the endpoint
is an escape, this segment is a first exit. -/
theorem segment {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) (ha : some a ∉ E) :
    Segment M E P c c' t := by
  obtain ⟨hc, -, hrun, -, hcut, henv⟩ := h
  refine ⟨hrun, fun u hu hm => ?_, henv⟩
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rw [MultiTapeTM.runFrom_zero, hc] at hm
    exact ha hm
  · exact hcut u hpos hu (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hm))

/-- The round cut in the rows' form: every intermediate state is `some s` with `s` off the anchor
and the escapes. -/
theorem cut_some {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ some s ∉ E :=
  fun u hu hut => not_mem_roundStop.mp (h.2.2.2.2.1 u hu hut)

/-- **Rounds from the rows' form** (the fit for `rt_find_round_entry` and the counter loop): a
positive-time run from the anchor whose intermediate states are live and off both the anchor `a`
and a single escape `e`, ending at one of them, is a round with escape set `{some e}`.

**Proof sketch.** Rewrite the cut by `Turing.not_mem_roundStop`; the endpoint is in
`{some a, some e}`; the relation is trivial. -/
theorem of_cut {e : S} {c : Cfg k Γ S x} {t : ℕ} (hc : c.state = some a) (ht : 0 < t)
    (hcut : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ s ≠ e)
    (hend : (M.runFrom c t).state = some a ∨ (M.runFrom c t).state = some e) :
    Round M a {some e} (fun _ => True) c (M.runFrom c t) t := by
  refine ⟨hc, ht, rfl, ?_, fun u hu hut => ?_, fun _ _ => trivial⟩
  · rcases hend with h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _ rfl
  · obtain ⟨s, hs, hsa, hse⟩ := hcut u hu hut
    exact not_mem_roundStop.mpr ⟨s, hs, hsa, fun h => hse (Option.some.inj h)⟩

/-- A round's relation can be replaced by the time-derived box about its start. -/
theorem time_box {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    Round M a E (HeadBox (fun j => c.workTapePos j - t) (fun j => c.workTapePos j + t)) c c' t := by
  obtain ⟨hc, ht, hrun, hend, hcut, -⟩ := h
  refine ⟨hc, ht, hrun, hend, hcut, fun u hu j => ?_⟩
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M c u j
  simp only [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ t := by exact_mod_cast hu
  constructor <;> omega

end Round

/-- **The round orbit**: the round-start configurations when each round from `c` lasts `τ c`
steps, stated in the core so that round iteration needs no counter. `CounterLoop`'s
`Turing.counterLoopOrbit` is an abbreviation of it. -/
def roundOrbit {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) : Cfg k Γ S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-- The orbit starts at its start: `roundOrbit M τ c 0 = c`. -/
theorem roundOrbit_zero {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) : roundOrbit M τ c 0 = c :=
  rfl

/-- The next round starts where the current one ends. -/
theorem roundOrbit_succ {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) :
    roundOrbit M τ c (r + 1) = M.runFrom (roundOrbit M τ c r) (τ (roundOrbit M τ c r)) :=
  Function.iterate_succ_apply' _ _ _

/-- **Round iteration along a sequence of starts**: if the anchor is not an escape
(`some a ∉ E`), the head condition `P` holds at `cs 0`, and, for each `r < n`, the run from `cs r`
is a round ending at `cs (r + 1)` after `τ r` steps, then the run from `cs 0` is one segment
against the escapes to `cs n`, of length the sum of the round times. When the last round ends in
an escape, the segment is a first exit (`Turing.Contract.ofSegment`).

**Proof sketch.** Each round is a segment (`Turing.Round.segment`, since the anchor is not an
escape); compose them along the sequence (`Turing.Segment.iterate_seq`). -/
theorem Round.iterate_seq {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S}
    {E : Set (Option S)} {P : (Fin k → ℤ) → Prop} (cs : ℕ → Cfg k Γ S x) (τ : ℕ → ℕ)
    (ha : some a ∉ E) (h0 : P (cs 0).workTapePos) (n : ℕ)
    (hround : ∀ r < n, Round M a E P (cs r) (cs (r + 1)) (τ r)) :
    Segment M E P (cs 0) (cs n) (∑ r ∈ Finset.range n, τ r) :=
  Segment.iterate_seq cs τ h0 n fun r hr => (hround r hr).segment ha

/-- **Round iteration on one machine** (the counter loop's composition, without the counter):
if the anchor is not an escape (`some a ∉ E`), the head condition `P` holds at `c`, and the first
`n` rounds of the orbit are rounds, each lasting `τ` of its start, then the whole orbit prefix is
one segment against the escapes, of length the sum of the round times. When the last round ends
in an escape, the segment is a first exit (`Turing.Contract.ofSegment`).

**Proof sketch.** The orbit `Turing.roundOrbit` as the sequence of starts in
`Turing.Round.iterate_seq`; it starts at `c` (`Turing.roundOrbit_zero`). -/
theorem Round.iterate {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S}
    {E : Set (Option S)} {P : (Fin k → ℤ) → Prop} (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (ha : some a ∉ E) (h0 : P c.workTapePos) (n : ℕ)
    (hround : ∀ r < n, Round M a E P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r))) :
    Segment M E P c (roundOrbit M τ c n) (∑ r ∈ Finset.range n, τ (roundOrbit M τ c r)) := by
  have h := Round.iterate_seq (roundOrbit M τ c) (fun r => τ (roundOrbit M τ c r)) ha
    (by rw [roundOrbit_zero]; exact h0) n hround
  rwa [roundOrbit_zero] at h

/-- **A round contract** (design §16a item 2): from every admissible start at `anchor`, the run
ends after a positive exact time back at the anchor or in the escape set; strictly in between it
is live and avoids both; and every head stays in its interval. A `Turing.ReturnContract` is the
case without escapes (`Turing.ReturnContract.toRound`). -/
structure RoundContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (escape : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, at the anchor or an escape. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some anchor → pre i d →
    (post i d).state ∈ insert (some anchor) escape
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ∉ roundStop anchor escape
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {escape : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every admissible run of a round contract is a round. -/
theorem round (R : RoundContract M anchor escape ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some anchor) (hp : R.pre i d) :
    Round M anchor escape (HeadBox (R.lo i d) (R.hi i d)) d (R.post i d) (R.time i d) :=
  ⟨hd, R.pos i d hd hp, R.run i d hd hp, R.exit_mem i d hd hp, R.cut i d hd hp,
    fun u hu j => R.env i d hd hp u hu j⟩

/-- **The returning case** is a `Turing.ReturnContract`: restrict the precondition to the starts
whose endpoint is back at the anchor. -/
def returning (R : RoundContract M anchor escape ι x) : ReturnContract M anchor ι x where
  pre i d := R.pre i d ∧ (R.post i d).state = some anchor
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  pos i d hd hp := R.pos i d hd hp.1
  run i d hd hp := R.run i d hd hp.1
  exit_eq _ _ _ hp := hp.2
  cut i d hd hp u hu hut h := R.cut i d hd hp.1 u hu hut (by
    rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  env i d hd hp := R.env i d hd hp.1

/-- **The escaping case** is a `Turing.Contract` with the escapes as exits: restrict the
precondition to the starts whose endpoint escapes. The time-zero cut needs the anchor to be no
escape.

**Proof sketch.** At time `0` the state is the anchor, which is no escape; later it avoids the
stop set, which contains the escapes. -/
def escaping (R : RoundContract M anchor escape ι x) (ha : some anchor ∉ escape) :
    Contract M anchor escape ι x where
  pre i d := R.pre i d ∧ (R.post i d).state ∈ escape
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  run i d hd hp := R.run i d hd hp.1
  exit_mem _ _ _ hp := hp.2
  cut i d hd hp := ((R.round i d hd hp.1).segment ha).2.1
  env i d hd hp := R.env i d hd hp.1

/-! The specification API: the two restrictions' data fields as equations, without the `simp`
attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] returning escaping

end RoundContract

/-- **A returning contract is a round contract without escapes.** Its intermediate states are
live, since a halt would persist to the endpoint, which is at the anchor.

**Proof sketch.** Off the anchor is the returning cut. Liveness: halting is absorbing
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), so a halt before the time would make
the endpoint's state `none`, not the anchor. -/
def ReturnContract.toRound {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) : RoundContract M anchor ∅ ι x where
  pre := C.pre
  time := C.time
  post := C.post
  lo := C.lo
  hi := C.hi
  pos := C.pos
  run := C.run
  exit_mem i d hd hp := by
    rw [C.exit_eq i d hd hp]
    exact Set.mem_insert _ _
  cut i d hd hp u hu hut := by
    apply not_mem_roundStop.mpr
    cases hs : (M.runFrom d u).state with
    | none =>
      refine absurd hs (MultiTapeTM.runFrom_state_ne_none_of_le M d _ ?_ u hut.le)
      rw [C.run i d hd hp, C.exit_eq i d hd hp]
      exact Option.some_ne_none _
    | some s =>
      refine ⟨s, rfl, fun h => C.cut i d hd hp u hu hut (by rw [hs, h]), fun h => h⟩
  env := C.env

/-! The specification API: the conversion's data fields as equations, without the `simp`
attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] ReturnContract.toRound

/-! ## Hulls of round boxes along an orbit (MIG-0b)

The envelope of an iterated round contract: the tape-wise hull of the first `n` round boxes and
of the final orbit head. `Build/CounterLoop`'s round-contract compositions use it. -/

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The lower ends of the **hull of an orbit's round boxes**: tape by tape, the least lower end
of the envelopes of the first `n` rounds of the orbit from `c` (each lasting the round
contract's time), and of the head at the `n`-th orbit point. -/
def hullLo (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
    if r < n then R.lo i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- The hull's lower end on tape `j` is the least, over `r ≤ n`, of the `r`-th round's lower end
`R.lo i (orbit r) j` for `r < n` and of the `n`-th orbit point's head, the orbit taken with the
round contract's time (the definition as a lemma). -/
theorem hullLo_eq (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) :
    R.hullLo i c n j = (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
      if r < n then R.lo i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j :=
  rfl

/-- The upper ends of the hull of an orbit's round boxes (see `Turing.RoundContract.hullLo`). -/
def hullHi (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun r =>
    if r < n then R.hi i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- The hull's upper end on tape `j` is the greatest, over `r ≤ n`, of the `r`-th round's upper
end `R.hi i (orbit r) j` for `r < n` and of the `n`-th orbit point's head, the orbit taken with
the round contract's time (the definition as a lemma). -/
theorem hullHi_eq (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) :
    R.hullHi i c n j = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun r =>
      if r < n then R.hi i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j :=
  rfl

/-- Along admissible rounds of the orbit, each returning except possibly the last, every orbit
point before `n` is at the anchor.

**Proof sketch.** Induction: a round from the anchor ends at the round contract's endpoint
(`run`), which is the next orbit point, and that endpoint is at the anchor when the round
returns. -/
theorem orbit_anchor (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, (roundOrbit M (R.time i) c r).state = some a := by
  intro r hr
  induction r with
  | zero => exact hc
  | succ r ih =>
    rw [roundOrbit_succ, R.run i _ (ih (by omega)) (hpre r (by omega))]
    exact hret r hr

/-- **The orbit's rounds** under the hull box: each of the first `n` orbit rounds is a round,
ending at the next orbit point, with its heads in the hull of all the round boxes.

**Proof sketch.** `Turing.RoundContract.round` at each orbit point, which is at the anchor by
`Turing.RoundContract.orbit_anchor`; its endpoint is the next orbit point (`run`), and its own box
lies in the hull (`Finset.inf'_le`, `Finset.le_sup'`). -/
theorem orbit_round (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, Round M a E (HeadBox (R.hullLo i c n) (R.hullHi i c n))
      (roundOrbit M (R.time i) c r) (roundOrbit M (R.time i) c (r + 1))
      (R.time i (roundOrbit M (R.time i) c r)) := by
  intro r hr
  have ha := R.orbit_anchor i c hc n hpre hret r hr
  have hR := R.round i _ ha (hpre r hr)
  have hnext : roundOrbit M (R.time i) c (r + 1) = R.post i (roundOrbit M (R.time i) c r) := by
    rw [roundOrbit_succ, R.run i _ ha (hpre r hr)]
  rw [hnext]
  refine ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2.1, fun u hu j => ?_⟩
  have hb := hR.2.2.2.2.2 u hu j
  have hmem : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.mem_Icc] at hb ⊢
  constructor
  · refine le_trans (Finset.inf'_le (fun r => if r < n then R.lo i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j) hmem) ?_
    simp only [if_pos hr]
    exact hb.1
  · refine le_trans ?_ (Finset.le_sup' (fun r => if r < n then
      R.hi i (roundOrbit M (R.time i) c r) j else (roundOrbit M (R.time i) c r).workTapePos j) hmem)
    simp only [if_pos hr]
    exact hb.2

/-- The start of the orbit lies in the hull box.

**Proof sketch.** With no round, the hull is the start itself; otherwise the start is time `0`
of the first round. -/
theorem orbit_start (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    HeadBox (R.hullLo i c n) (R.hullHi i c n) c.workTapePos := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro j
    simp [hullLo, hullHi, roundOrbit]
  · exact (R.orbit_round i c hc n hpre hret 0 hn).2.2.2.2.2 0 (Nat.zero_le _)

end RoundContract

/-- The host box of a counter loop: the counter interval on the last tape, and a body box on the
others. -/
theorem headBox_lastCases {lo hi : Fin k → ℤ} {clo chi : ℤ} {p : Fin (k + 1) → ℤ}
    (hc : p (Fin.last k) ∈ Finset.Icc clo chi) (hb : HeadBox lo hi fun j => p j.castSucc) :
    HeadBox (Fin.lastCases (motive := fun _ => ℤ) clo lo)
      (Fin.lastCases (motive := fun _ => ℤ) chi hi) p := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [Fin.lastCases_last] using hc
  | cast i => simpa only [Fin.lastCases_castSucc] using hb i

/-! ## The joint-trajectory layer (design §16a, MIG-0b item 3)

Per-tape intervals cannot express a relation between heads, such as "the two heads are equal"
(MIG-0a gate, round 1, counterexample 6), and `CounterLoop`'s `counterSpan` carries exactly such a
relation on the body heads. `Turing.Contract.Traj` names one, as a derived property in the manner
of `Turing.Contract.Frames`: it is not a field, every contract has its envelope box as one
(`Turing.Contract.traj_env`), and the compositions preserve them (`trans` here; `seq`, `inPhase`
and `branch` in `Build/Contract/Seam`; `embed` in `Build/Contract/Embed`). -/

namespace Contract

/-- A contract **has the joint trajectory** `R` when, for every index `i` and every admissible
start `d`, the whole head vector satisfies `R i d` at every time up to the endpoint. -/
def Traj {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry exits ι x)
    (R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → ∀ u ≤ C.time i d, R i d (M.runFrom d u).workTapePos

/-- A contract has the joint trajectory `R` exactly when, for every index `i` and every
admissible start `d` at the entry, the head vector satisfies `R i d` at every time
`u ≤ C.time i d` (the definition as a lemma). -/
theorem traj_iff {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)}
    {ι : Type} {x : List Γ} (C : Contract M entry exits ι x)
    (R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop) :
    C.Traj R ↔ ∀ i d, d.state = some entry → C.pre i d →
      ∀ u ≤ C.time i d, R i d (M.runFrom d u).workTapePos :=
  Iff.rfl

section TrajBasic

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every contract has its envelope box as a joint trajectory. -/
theorem traj_env (C : Contract M entry exits ι x) :
    C.Traj fun i d => HeadBox (C.lo i d) (C.hi i d) :=
  fun i d hd hp u hu j => C.env i d hd hp u hu j

/-- Weakening a joint trajectory. -/
theorem Traj.mono {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (hR : ∀ i d p, R i d p → R' i d p) : C.Traj R' :=
  fun i d hd hp u hu => hR i d _ (h i d hd hp u hu)

/-- Two joint trajectories hold jointly. -/
theorem Traj.and {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (h' : C.Traj R') : C.Traj fun i d p => R i d p ∧ R' i d p :=
  fun i d hd hp u hu => ⟨h i d hd hp u hu, h' i d hd hp u hu⟩

/-- **A joint trajectory is a segment relation**: every admissible run is a segment against the
exits, ending at the endpoint, with the relation along it. -/
theorem Traj.segment {C : Contract M entry exits ι x}
    {R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} (h : C.Traj R) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (R i d) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, h i d hd hp⟩

/-- **`trans` preserves joint trajectories**: up to the first contract's time the first relation
holds, and after it the second, at the linked index and the first endpoint.

**Proof sketch.** Split the time at the first contract's time, as in `Turing.Contract.trans`'s
envelope. -/
theorem Traj.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type} {C₁ : Contract M e₁ {some e₂} ι x}
    {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {R₁ : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.trans C₂ link hlink hX).Traj fun i d p => R₁ i d p ∨ R₂ (link i) (C₁.post i d) p := by
  intro i d hd hp u hu
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
  change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
  by_cases h : u ≤ C₁.time i d
  · exact Or.inl (h₁ i d hd hp u h)
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact Or.inr (h₂ _ _ hx (hlink i d hd hp) v (by omega))

/-- **`trans` preserves frames**: footprints add up (`Turing.Cfg.SameOutside.trans`). -/
theorem Frames.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    {C₁ : Contract M e₁ {some e₂} ι x} {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {fp₁ : ι → Cfg k Γ S x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.trans C₂ link hlink hX).Frames fun i d j => fp₁ i d j ∪ fp₂ (link i) (C₁.post i d) j :=
  fun i d hd hp => (h₁ i d hd hp).trans
    (h₂ _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp))

end TrajBasic

end Contract

/-! ## Sanity lemmas (design §16a, MIG-0b item 7; MIG-0a gate, round 1, counterexample 1)

The positivity of the seam compositions and of the releases is in `Build/Contract/Seam`, and that
of `embed` in `Build/Contract/Embed`. -/

namespace Contract

section Sanity

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **The zero-time characterization**: on an admissible start, a contract's time is `0` exactly
when its entry is among its exits.

**Proof sketch.** If the time is `0`, the endpoint is the start, which is at the entry, and the
endpoint is at an exit. If the entry is an exit and the time were positive, the cut at time `0`
would exclude it. -/
theorem time_eq_zero_iff (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) : C.time i d = 0 ↔ some entry ∈ exits := by
  constructor
  · intro h
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h, MultiTapeTM.runFrom_zero, hd] at hx
    exact hx
  · intro h
    by_contra hne
    exact C.cut i d hd hp 0 (Nat.pos_of_ne_zero hne) (by rw [MultiTapeTM.runFrom_zero, hd]; exact h)

/-- A contract whose entry is no exit is positive. -/
theorem positive_of_not_mem (C : Contract M entry exits ι x) (h : some entry ∉ exits) :
    C.Positive :=
  fun i d hd hp => Nat.pos_of_ne_zero fun h0 => h ((C.time_eq_zero_iff i d hd hp).mp h0)

/-- A positive contract with an admissible start has its entry outside its exits. -/
theorem not_mem_of_positive (C : Contract M entry exits ι x) (h : C.Positive) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) : some entry ∉ exits :=
  fun hm => (Nat.pos_iff_ne_zero.mp (h i d hd hp)) ((C.time_eq_zero_iff i d hd hp).mpr hm)

/-- `trans` of a positive first contract is positive. -/
theorem trans_positive {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X)
    (h : C₁.Positive) : (C₁.trans C₂ link hlink hX).Positive :=
  fun i d hd hp => Nat.lt_of_lt_of_le (h i d hd hp) (Nat.le_add_right _ _)

end Sanity

end Contract

/-! ## Transports (design §16a, MIG-0b item 6; §16, *transports*)

Contract-to-contract theorems along the library's simulations: state renaming along an embedding,
and the macro-step lockstep (`Turing.Lockstep`), the common shape of alphabet reduction
([AB09, Claim 1.5]; `Robustness/AlphabetReduction`, `L = 3(|Γ| + 1) + 2` steps per source step)
and of the robustness layer's lockstep combinators. The alphabet-reduction adapter (the
lockstep instance and its contract theorem) lands with RS-5 in `Robustness/AlphabetReduction`,
where its lockstep is proved; the symbol lift (through `Cfg.decodeSymbols`) is in
`Build/Contract/Lift`. -/

namespace Contract

/-- The renamed prefix of a contract run: up to its time, the host run from a start at the renamed
entry is the source run from the state-replaced start, renamed.

**Proof sketch.** The renamed source start is the host start. The guard holds before the time,
so `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` transports every prefix. -/
private lemma mapState_traj {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)}
    {ι : Type} {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q)
    (i : ι) (d : Cfg k Γ H x) (hd : d.state = some (emb entry))
    (hp : C.pre i (d.mapState fun _ => entry)) :
    ∀ u ≤ C.time i (d.mapState fun _ => entry),
      N.runFrom d u = (M.runFrom (d.mapState fun _ => entry) u).mapState emb := by
  have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
  have hd' : (d.mapState fun _ => entry).mapState emb = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  intro u hu
  have H := MultiTapeTM.runFrom_mapState_of_agreeOn M N emb good hagree _ u
    (fun v hv => hgood i _ hc hp v (by omega))
  rwa [hd'] at H

/-- **State renaming along an embedding** (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`): a
host whose table agrees, on the renamed good states, with the source table renamed, runs every
contract of the source whose runs stay in good states before their time. The host's entry and
exits are the renamed ones; the time and the envelope are the source's, at the state-replaced
start, and the endpoint is the source endpoint, renamed. This is the transport behind the phase
host, the counter loop's body phase and the call controllers.

**Proof sketch.** By the renamed prefix (`mapState_traj`): the run and the exit are the source's,
renamed; a renamed state is a renamed exit only if the source state is an exit, by injectivity;
and the heads are the source's. -/
def mapState {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q) :
    Contract N (emb entry) (Option.map emb '' X) ι x where
  pre i d := C.pre i (d.mapState fun _ => entry)
  time i d := C.time i (d.mapState fun _ => entry)
  post i d := (C.post i (d.mapState fun _ => entry)).mapState emb
  lo i d := C.lo i (d.mapState fun _ => entry)
  hi i d := C.hi i (d.mapState fun _ => entry)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp _ le_rfl, C.run i _ hc hp]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    exact ⟨_, C.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu.le]
    rintro ⟨q, hq, heq⟩
    have hq' : q = (M.runFrom (d.mapState fun _ => entry) u).state :=
      Option.map_injective emb.injective heq
    exact C.cut i _ hc hp u hu (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu]
    exact C.env i _ hc hp u hu j

end Contract

/-- **A macro-step lockstep** (design §16, *lockstep combinators*): every source step from a
configuration off the exits `X` is simulated by exactly `cost c` target steps through the
encoding `enc`; an encoded exit is a target exit in `X'`; and inside a simulated step the target
meets no target exit. Alphabet reduction ([AB09, Claim 1.5]) is the case
`cost = 3(|Γ| + 1) + 2`; a lockstep decoration is the case `cost = 1`. Neither a positive cost
nor an injective encoding is required. -/
structure Lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    (M : MultiTapeTM k Γ S) (N : MultiTapeTM k' Γ' S') (enc : Cfg k Γ S x → Cfg k' Γ' S' x')
    (cost : Cfg k Γ S x → ℕ) (X : Set (Option S)) (X' : Set (Option S')) : Prop where
  step : ∀ c, c.state ∉ X → N.runFrom (enc c) (cost c) = enc (M.step c)
  exit : ∀ c, c.state ∈ X → (enc c).state ∈ X'
  inner : ∀ c, c.state ∉ X → ∀ v < cost c, (N.runFrom (enc c) v).state ∉ X'

namespace Lockstep

variable {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'} {M : MultiTapeTM k Γ S}
  {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'} {cost : Cfg k Γ S x → ℕ}
  {X : Set (Option S)} {X' : Set (Option S')}

/-- **The lockstep over a run**: a source run of `t` steps that avoids `X` before `t` is simulated
by the sum of its step costs.

**Proof sketch.** Induction on `t`, with one `step` per source step
(`Turing.MultiTapeTM.runFrom_add`). -/
theorem runFrom (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    N.runFrom (enc d) (∑ u ∈ Finset.range t, cost (M.runFrom d u)) = enc (M.runFrom d t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, MultiTapeTM.runFrom_add, ih fun u hu => ht u (by omega),
      L.step _ (ht t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- **The lockstep cut**: a simulated run that avoids `X` before `t` avoids `X'` before the sum
of its step costs.

**Proof sketch.** Induction on `t`: a time in the last simulated step is an inner time of that
step, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem cut (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v < ∑ u ∈ Finset.range t, cost (M.runFrom d u), (N.runFrom (enc d) v).state ∉ X' := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hlt : v < ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · exact ih (fun u hu => ht u (by omega)) v hlt
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hlt)
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]
      exact L.inner _ (ht t (by omega)) w (by omega)

/-- **Locating a target time**: every target time up to the simulated length of a source run
lies in one simulated step, at an offset inside it (or is the start of the step after the last).

**Proof sketch.** Induction on `t`: a time beyond the first `t` simulated steps is an offset in
the last one, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem locate (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u), ∃ u ≤ t, ∃ w,
      (w = 0 ∨ ((M.runFrom d u).state ∉ X ∧ w ≤ cost (M.runFrom d u))) ∧
      N.runFrom (enc d) v = N.runFrom (enc (M.runFrom d u)) w := by
  induction t with
  | zero =>
    intro v hv
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hv
    exact ⟨0, le_rfl, 0, Or.inl rfl, by rw [hv]; rfl⟩
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hle : v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · obtain ⟨u, hu, w, hw, he⟩ := ih (fun u hu => ht u (by omega)) v hle
      exact ⟨u, by omega, w, hw, he⟩
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp hle))
      refine ⟨t, by omega, w, Or.inr ⟨ht t (by omega), by omega⟩, ?_⟩
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]

end Lockstep

/-- **Transport along a macro-step lockstep**. A source contract becomes a
target contract whose index also records the source start: an admissible target start is the
encoding of an admissible source start. The time is the sum of the step costs along the source
run, the endpoint is the encoded source endpoint, and the envelope is the hull of per-step boxes
`blo`, `bhi`, which `hbox` asserts for every simulated step and every encoded configuration.

**Proof sketch.** The run is `Turing.Lockstep.runFrom` and the cut `Turing.Lockstep.cut`, fed the
source cut; the exit is `exit` at the source endpoint. For the envelope, a target time lies in
one simulated step, at an offset inside it (`Turing.Lockstep.locate`); `hbox` bounds the heads
there by that step's box, which lies inside the hull over the source run.

The target entry `entry'` is a free parameter: no premise relates it to the encoding. The
admissible target starts are the encodings of admissible source starts that lie at `entry'`.
A sufficient condition for every admissible source start to transport is that the encoding
sends every source configuration at `entry` to one at `entry'`
(`Turing.Contract.lockstep_admissible`; for a state-renaming encoding,
`Turing.Contract.lockstep_admissible_map`); compatibility on the admissible source starts
alone also suffices. Without any compatibility the contract may have no admissible start. -/
def Contract.lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j)) :
    Contract N entry' X' (ι × Cfg k Γ S x) x' where
  pre p d' := d' = enc p.2 ∧ p.2.state = some entry ∧ C.pre p.1 p.2
  time p _ := ∑ u ∈ Finset.range (C.time p.1 p.2), cost (M.runFrom p.2 u)
  post p _ := enc (C.post p.1 p.2)
  lo p _ j := (Finset.range (C.time p.1 p.2 + 1)).inf' Finset.nonempty_range_add_one
    fun u => blo (M.runFrom p.2 u) j
  hi p _ j := (Finset.range (C.time p.1 p.2 + 1)).sup' Finset.nonempty_range_add_one
    fun u => bhi (M.runFrom p.2 u) j
  run p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    rw [L.runFrom p.2 _ (C.cut p.1 p.2 hs hc), C.run p.1 p.2 hs hc]
  exit_mem p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.exit _ (C.exit_mem p.1 p.2 hs hc)
  cut p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.cut p.2 _ (C.cut p.1 p.2 hs hc)
  env p d' _ hp v hv j := by
    obtain ⟨rfl, hs, hc⟩ := hp
    obtain ⟨u, hu, w, hw, he⟩ := L.locate p.2 _ (C.cut p.1 p.2 hs hc) v hv
    have hb := hbox (M.runFrom p.2 u) w hw j
    rw [he]
    have hmem : u ∈ Finset.range (C.time p.1 p.2 + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.mem_Icc] at hb ⊢
    exact ⟨(Finset.inf'_le (fun u => blo (M.runFrom p.2 u) j) hmem).trans hb.1,
      hb.2.trans (Finset.le_sup' (fun u => bhi (M.runFrom p.2 u) j) hmem)⟩

/-! The specification API: the state renaming's and the lockstep transport's data fields as
equations, without the `simp` attribute. (`Turing.Contract.mapState`'s line sits here, not after
its definition, so that the copy-text screen does not attach it to that body.) -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  Contract.mapState Contract.lockstep

/-- **Admissible starts of a lockstep transport** (the entry-compatibility condition, MIG-0b
gate, round 1, minor 3). If the encoding sends every source configuration at `entry` to a target
configuration at `entry'`, then every admissible source start `c` gives an admissible target start
`enc c`, at the index `(i, c)`. The condition is sufficient, not necessary: the transported
contract's admissible starts are the encodings of admissible source starts that lie at
`entry'`, so compatibility on the admissible source starts alone also suffices (the proof uses
`hentry` only at `c`; MIG-0b gate, round 2, minor 3). Without any compatibility the contract
may have no admissible start: with an identity encoding and `entry' ≠ entry` it has none. -/
theorem Contract.lockstep_admissible {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (hentry : ∀ c : Cfg k Γ S x, c.state = some entry → (enc c).state = some entry')
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some entry' ∧ (C.lockstep L entry' blo bhi hbox).pre (i, c) (enc c) :=
  ⟨hentry c hc, rfl, hc, hp⟩

/-- **Admissible starts for a state-renaming encoding**: when the encoding renames states by `ρ`
(as alphabet reduction's does), the renamed entry `ρ entry` is compatible, so every admissible
source start `c` gives the admissible target start `enc c`. -/
theorem Contract.lockstep_admissible_map {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (ρ : S → S')
    (hρ : ∀ c, (enc c).state = c.state.map ρ)
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some (ρ entry) ∧
      (C.lockstep L (ρ entry) blo bhi hbox).pre (i, c) (enc c) :=
  C.lockstep_admissible L (ρ entry) blo bhi hbox
    (fun c hc => by rw [hρ, hc]; rfl) i c hc hp

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: seams, the phase host and the release adapter

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`). The
MIG-0a compositions over `Build/Seam` (`seq`, `inPhase`, `branch` and `ReturnContract.release`)
moved here from `Build/Contract.lean` as landed on 2026-10-13, with no statement changed; with
MIG-0b's round release, the joint trajectories and frames of these compositions, and their
positivity.

**Routing.** `Turing.Contract.seq` is the single-live-exit seam, `Turing.Contract.branch` the
binary case, and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live
exits, several of which may share one continuation. A first phase that halts cannot resume
through a seam, which dispatches only at a live anchor.

## Main definitions

* `Turing.Contract.seq`: sequencing through the R2 seam `Turing.seamCompTM`, after a first
  phase with a single live exit.
* `Turing.Contract.inPhase`: a phase run inside the phase host `Turing.phaseHostTM`, with an
  arbitrary set of live exits, each redirected; `Turing.Cfg.bindState`, its redirect.
* `Turing.Contract.branch`: the two-way seam `Turing.seamCompTM₂`, after a first phase with two
  live exits.
* `Turing.ReturnContract.release`, `Turing.RoundContract.release`: returning modules and rounds
  through the release adapter `Turing.seamReleaseTM`.

## Main results

* `Turing.Contract.Traj.seq`, `Turing.Contract.Traj.inPhase`, `Turing.Contract.Traj.branch`,
  `Turing.Contract.Frames.seq`: preservation of joint trajectories and frames.
* `Turing.Contract.seq_positive`, `Turing.Contract.inPhase_positive`,
  `Turing.Contract.branch_positive`, `Turing.ReturnContract.release_positive`,
  `Turing.RoundContract.release_positive`: positivity.
* `Turing.Contract.seq_pre`, `Turing.Contract.inPhase_time`, `Turing.Contract.branch_post`
  and the rest — the specification API (user, 2026-10-16): the composites' data fields as
  equations, without the `simp` attribute.
* `Turing.ReturnContract.release_pre`, `_time`, `_post`, `_lo`, `_hi` and
  `Turing.RoundContract.release_pre` … `_hi` — the release adapters' data fields as equations,
  the same way (the specification API's gate, finding 1).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

namespace Contract

section Compose

private lemma mapState_state {S S' : Type} {x : List Γ} (f : S → S') (c : Cfg k Γ S x) :
    (c.mapState f).state = c.state.map f := rfl

/-- The composed start is the left-mapped first-phase start. -/
private lemma mapState_const_inl {S₁ S₂ : Type} {x : List Γ} {e : S₁}
    {d : Cfg k Γ (S₁ ⊕ S₂) x} (hd : d.state = some (Sum.inl e)) :
    (d.mapState fun _ => e).mapState Sum.inl = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The seam trajectory of a contract run: the left segment up to the first exit (live
throughout), and the right segment after the dispatch, at every offset. The composite starts
at `Sum.inl entry₁`; the first phase runs from that start with its state replaced by `entry₁`.

**Proof sketch.** Re-tagging the replaced start by `Sum.inl` gives back the composite start.
`C₁`'s cut is the strict exit cut of `Turing.seamCompTM_runFrom_left`, which gives the left
segment up to `t₁`. It is live: a halt before `t₁` would persist to the endpoint, which is at
`exit₁`. The right segment is `Turing.seamCompTM_run_ofCfg` with second-phase time `v` and that
run's endpoint taken to be itself. The replaced endpoint is at `entry₂` by construction. -/
private lemma seq_traj {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} (entry₂ : S₂) {ι : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (i : ι) (d : Cfg k Γ (S₁ ⊕ S₂) x)
    (hd : d.state = some (Sum.inl entry₁)) (hp : C₁.pre i (d.mapState fun _ => entry₁)) :
    (∀ u ≤ C₁.time i (d.mapState fun _ => entry₁),
      (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d u =
          (M₁.runFrom (d.mapState fun _ => entry₁) u).mapState Sum.inl ∧
        (M₁.runFrom (d.mapState fun _ => entry₁) u).state ≠ none) ∧
    (∀ v, (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d
        (C₁.time i (d.mapState fun _ => entry₁) + 1 + v) =
      (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
        v).mapState Sum.inr) ∧
    ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂).state =
      some entry₂ := by
  have hd' := mapState_const_inl (S₂ := S₂) hd
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have h1 := C₁.run i _ hd₁ hp
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
  have hcut : ∀ t < C₁.time i (d.mapState fun _ => entry₁),
      (M₁.runFrom (d.mapState fun _ => entry₁) t).state ≠ some exit₁ :=
    fun t ht => C₁.cut i _ hd₁ hp t ht
  refine ⟨fun u hu => ⟨?_, ?_⟩, fun v => ?_, by rw [mapState_state, hx]; rfl⟩
  · have hl := seamCompTM_runFrom_left M₁ exit₁ M₂ entry₂ hcut u hu
    rwa [hd'] at hl
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₁ _ _ ?_ u hu
    rw [h1, hx]
    exact Option.some_ne_none _
  · have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ h1 hx hcut (T₂ := v) rfl
    rwa [hd'] at hr

/-- **Sequencing through the R2 seam** (`Turing.seamCompTM_run_ofCfg`,
`Turing.seamCompTM_firstReturn_ofCfg`): run `C₁` to its single live exit `exit₁`, take one
stationary dispatch step, and run `C₂`, so the time is `t₁ + 1 + t₂`. The second phase starts
from the first's endpoint with its state replaced by `entry₂`; the endpoint and the exits are
right-tagged, and the envelopes take the hull.

This is the **single-live-exit seam**. Two live exits go through `Turing.Contract.branch`, and
an arbitrary set of live exits through the phase host (`Turing.Contract.inPhase`). A first phase
that halts cannot resume through a seam, which dispatches only at a live anchor.

**Proof sketch.** By the seam trajectory (`seq_traj`): up to `t₁` the composite is the
left-tagged first phase, live throughout, and at `t₁ + 1 + v` it is the right-tagged second
phase at `v`, from its entry. The run is `Turing.seamCompTM_run_ofCfg` with `C₂`'s run, and the
exit is `C₂`'s, right-tagged. For the cut, a time up to `t₁` carries a live left-tagged state,
which is no right-tagged exit; a later time is `t₁ + 1 + v` with `v < t₂`, and injectivity of the
right tag reduces it to `C₂`'s cut at `v`. The envelope is `C₁`'s up to `t₁` and `C₂`'s after
the dispatch (offset `0` is the dispatch step), inside the hull. -/
def seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)} {ι κ : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM M₁ exit₁ M₂ entry₂) (Sum.inl entry₁) (Option.map Sum.inr '' X₂) ι x where
  pre i d := C₁.pre i (d.mapState fun _ => entry₁)
  time i d := C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
  post i d :=
    (C₂.post (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)).mapState
      Sum.inr
  lo i d j := min (C₁.lo i (d.mapState fun _ => entry₁) j)
    (C₂.lo (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  hi i d j := max (C₁.hi i (d.mapState fun _ => entry₁) j)
    (C₂.hi (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hd' := mapState_const_inl (S₂ := S₂) hd
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ (C₁.run i _ hd₁ hp) hx
      (fun t ht => C₁.cut i _ hd₁ hp t ht) (C₂.run _ _ hd₂ (hlink i _ hd₁ hp))
    rw [hd'] at hr
    exact hr
  exit_mem i d hd hp := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    exact ⟨_, C₂.exit_mem _ _ hd₂ (hlink i _ hd₁ hp), rfl⟩
  cut i d hd hp u hu := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u < C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    rintro ⟨q, hq, heq⟩
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · obtain ⟨hrun, hlive⟩ := hL u hle
      rw [hrun] at heq
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rw [mapState_state, hs] at heq
      cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v] at heq
      have hq' : q = (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState
          fun _ => entry₂) v).state := Option.map_injective Sum.inr_injective heq
      exact C₂.cut _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · rw [(hL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i _ hd₁ hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)

/-- Re-type a configuration's control state through a partial map: the phase host's redirect.
A halted configuration stays halted; every other field is kept. -/
def _root_.Turing.Cfg.bindState {S S' : Type} {x : List Γ} (d : Cfg k Γ S x) (f : S → Option S') :
    Cfg k Γ S' x :=
  ⟨d.state.bind f, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-! The redirect's fields as equations, generated without the `simp` attribute (`policy.md` §1):
the state is `d.state.bind f`, and the input position, tapes, heads and output are `d`'s. -/
attribute [simps (config := { isSimp := false })] Turing.Cfg.bindState

/-- The phase-host trajectory of a contract run: the tagged prefix through the phase's exit,
the redirected endpoint one dispatch step later, and the live exit state.

**Proof sketch.** The endpoint's state lies in `X`, which excludes `none`, so it is a live exit
`s'`, which `red p` redirects (`hsome`). Before the endpoint the cut keeps every state out of
`X`, so `hred` says that none of them is redirected. `Turing.phaseHostTM_run` then gives the
prefix tagged with `p` up to the time and, one dispatch step later, the endpoint with its state
replaced by the target of `s'`, which is the endpoint's state bound through `red p`. The
other-phase clause of `hsome` is not used here. -/
private lemma inPhase_traj {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p)
    (i : ι) (d : Cfg k Γ (Σ i, Ph i) x) (hd : d.state = some ⟨p, s₀⟩)
    (hp : C.pre i (d.mapState fun _ => s₀)) :
    (∀ u ≤ C.time i (d.mapState fun _ => s₀),
      (phaseHostTM Mf q0 red).runFrom d u =
        ((Mf p).runFrom (d.mapState fun _ => s₀) u).mapState (Sigma.mk p)) ∧
    (phaseHostTM Mf q0 red).runFrom d (C.time i (d.mapState fun _ => s₀) + 1) =
      (C.post i (d.mapState fun _ => s₀)).bindState (red p) ∧
    ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' ∧ some s' ∈ X := by
  have hd' : (d.mapState fun _ => s₀).mapState (Sigma.mk p) = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  have hx := C.exit_mem i _ hc hp
  obtain ⟨s', hs'⟩ : ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' := by
    cases h : (C.post i (d.mapState fun _ => s₀)).state with
    | none => rw [h] at hx; exact absurd hx hnone
    | some s' => exact ⟨s', rfl⟩
  have hs'X : some s' ∈ X := by rw [← hs']; exact hx
  obtain ⟨q', hq', -⟩ := hsome s' hs'X
  have H := phaseHostTM_run Mf q0 red p (d.mapState fun _ => s₀) _ _ (C.run i _ hc hp) s' hs'
    q' hq' (fun u hu s hs => hred s (fun hm => C.cut i _ hc hp u hu (by rw [hs]; exact hm)))
  rw [hd'] at H
  refine ⟨H.1, ?_, s', hs', hs'X⟩
  rw [H.2]
  refine Cfg.ext ?_ rfl rfl rfl rfl
  show Option.map (fun _ => q') (C.post i (d.mapState fun _ => s₀)).state =
    (C.post i (d.mapState fun _ => s₀)).state.bind (red p)
  rw [hs']
  simp [hq']

/-- **A phase inside the phase host** (`Turing.phaseHostTM_run`). Phase `p` runs under its own
contract, whose exits are live (`hnone`) and are exactly the states of phase `p` that the host
redirects (`hred`, `hsome`), each to a state of another phase. The host's exits are the
redirect targets, the time gains one dispatch step, and the envelopes are the phase's. The
phase host thus handles an **arbitrary set of live exits**, each sent to its own target, and
several may share one continuation; `Turing.Contract.seq` and `Turing.Contract.branch` are the
one- and two-exit seams.

The other-phase condition `q.1 ≠ p` is **sufficient, not necessary**. What the cut needs is that
the run avoids every redirect target up to its endpoint; up to there the host run is tagged with
phase `p`, so it never meets a state of another phase. A same-phase target that the run avoids
up to its endpoint would also do, while a redirect back to the entry fails at time `0`; a
generalization could ask for that avoidance instead.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`): up to the phase's time the
host is the phase run tagged with `p`, and one dispatch step later it is the phase's endpoint
with its state bound through `red p`. This gives the run, and the exit is the target of the
phase's live exit. For the cut, a time up to the phase's time carries a state tagged with `p`,
or `none`; a target equal to it would lie in phase `p`, against `q.1 ≠ p`. The envelope is the
phase's up to its time; at the dispatch step the heads are those of the phase's endpoint. -/
def inPhase {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p} {X : Set (Option (Ph p))}
    {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x) (hnone : none ∉ X)
    (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    Contract (phaseHostTM Mf q0 red) ⟨p, s₀⟩ {q | ∃ s, some s ∈ X ∧ q = red p s} ι x where
  pre i d := C.pre i (d.mapState fun _ => s₀)
  time i d := C.time i (d.mapState fun _ => s₀) + 1
  post i d := (C.post i (d.mapState fun _ => s₀)).bindState (red p)
  lo i d := C.lo i (d.mapState fun _ => s₀)
  hi i d := C.hi i (d.mapState fun _ => s₀)
  run i d hd hp := (inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp).2.1
  exit_mem i d hd hp := by
    obtain ⟨-, -, s', hs', hs'X⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    refine ⟨s', hs'X, ?_⟩
    show (C.post i (d.mapState fun _ => s₀)).state.bind (red p) = red p s'
    rw [hs']
    rfl
  cut i d hd hp u hu := by
    change u < C.time i (d.mapState fun _ => s₀) + 1 at hu
    obtain ⟨hL, -, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rw [hL u (by omega)]
    rintro ⟨s, hsX, heq⟩
    obtain ⟨q, hq, hqp⟩ := hsome s hsX
    rw [hq, mapState_state] at heq
    obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp heq
    exact hqp (by rw [← ha])
  env i d hd hp u hu j := by
    change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
    have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h | h
    · rw [hL u (by omega)]
      exact C.env i _ hc hp u (by omega) j
    · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
      rw [hE]
      have h' := C.env i _ hc hp _ le_rfl j
      rw [C.run i _ hc hp] at h'
      exact h'

end Compose

/-! ## The two-way branch -/

/-- The two-way composed start is the doubly left-mapped first-phase start. -/
private lemma mapState_const_inl_inl {S₀ S₁ S₂ : Type} {x : List Γ} {e : S₀}
    {d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x} (hd : d.state = some (Sum.inl (Sum.inl e))) :
    ((d.mapState fun _ => e).mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState
      (Sum.inl : S₀ ⊕ S₁ → (S₀ ⊕ S₁) ⊕ S₂) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The two-way seam trajectory of a contract run: the doubly left-mapped first phase up to
its exit (live throughout), then, per exit, the matching continuation at every offset.

**Proof sketch.** The two-way seam nests two seams: the inner one dispatches `e₁` to the first
continuation, and the outer one dispatches the inner machine's `Sum.inl e₂` to the second.
`C₀`'s cut excludes both exits before its time. By the inner seam's left segment
(`Turing.seamCompTM_runFrom_left`), the inner machine therefore avoids `Sum.inl e₂` before that
time, so the outer seam's left segment, rewritten by the inner one, is the doubly tagged first
phase up to its time. It is live, since a halt would persist to the endpoint, which is at an
exit. The two continuations are the two halves of `Turing.seamCompTM₂_run_ofCfg`. -/
private lemma branch_traj {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} (M₁ : MultiTapeTM k Γ S₁) (M₂ : MultiTapeTM k Γ S₂)
    {entry₀ e₁ e₂ : S₀} (entry₁ : S₁) (entry₂ : S₂) {ι : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (i : ι)
    (d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x) (hd : d.state = some (Sum.inl (Sum.inl entry₀)))
    (hp : C₀.pre i (d.mapState fun _ => entry₀)) :
    (∀ u ≤ C₀.time i (d.mapState fun _ => entry₀),
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d u =
          ((M₀.runFrom (d.mapState fun _ => entry₀) u).mapState Sum.inl).mapState Sum.inl ∧
        (M₀.runFrom (d.mapState fun _ => entry₀) u).state ≠ none) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        ((M₁.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
          v).mapState Sum.inr).mapState Sum.inl) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        (M₂.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
          v).mapState Sum.inr) := by
  have hd' := mapState_const_inl_inl (S₁ := S₁) (S₂ := S₂) hd
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  have h0 := C₀.run i _ hc hp
  have hx := C₀.exit_mem i _ hc hp
  have hcut₁ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₁ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert _ _)
  have hcut₂ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₂ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  have hcutO : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      ((seamCompTM M₀ e₁ M₁ entry₁).runFrom ((d.mapState fun _ => entry₀).mapState Sum.inl)
        t).state ≠ some (Sum.inl e₂) := by
    intro t ht h
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ t ht.le] at h
    exact hcut₂ t ht (by simpa [Cfg.mapState] using h)
  have H := seamCompTM₂_run_ofCfg M₀ e₁ e₂ he M₁ entry₁ M₂ entry₂ h0
    (fun t ht => ⟨hcut₁ t ht, hcut₂ t ht⟩)
  rw [hd'] at H
  refine ⟨fun u hu => ⟨?_, ?_⟩, H.1, H.2⟩
  · have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO u hu
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ u hu, hd'] at h
    exact h
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₀ _ _ ?_ u hu
    rw [h0]
    intro h'
    rw [h'] at hx
    simp at hx

/-- **The two-way branch** (`Turing.seamCompTM₂_run_ofCfg`): the first phase ends at one of two
distinct live exits, and the seam dispatches, in one step, to the matching continuation, which
starts from the first phase's endpoint with its state replaced by its entry. Each
continuation's precondition is needed only when its exit is the one reached. The time, the
endpoint and the continuation part of the envelope hull are the selected continuation's.

This is the **binary case** of the routing: `Turing.Contract.seq` is the single-live-exit seam,
and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live exits. Halted
endpoints of the two continuations share the untagged `none`, so a consumer that must recover
the branch from the final state needs live tagged exits or an explicit verdict.

**Proof sketch.** By the two-way trajectory (`branch_traj`), and by cases on the exit reached
(`e₁`, or else `e₂` by `exit_mem`). Up to the first phase's time the composite is the doubly
left-tagged first phase, live throughout, so it meets no exit of either continuation. At time
`t₀ + 1 + v` it is the selected continuation's run at `v`, tagged, which gives the run, the exit
and the envelope. For the cut at `v` below the continuation's time, a tagged exit of the
selected continuation is excluded by that continuation's cut, through injectivity of the tags;
an exit of the other continuation carries the other tag or is `none`, and the state is live by
`Turing.Contract.live`. -/
def branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁] {M₀ : MultiTapeTM k Γ S₀}
    {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂} {entry₀ e₁ e₂ : S₀} {entry₁ : S₁}
    {entry₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ}
    (he : e₁ ≠ e₂) (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x)
    (C₁ : Contract M₁ entry₁ X₁ κ₁ x) (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁)
    (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂) (Sum.inl (Sum.inl entry₀))
      ((Option.map (Sum.inl ∘ Sum.inr) '' X₁) ∪ (Option.map Sum.inr '' X₂)) ι x where
  pre i d := C₀.pre i (d.mapState fun _ => entry₀)
  time i d :=
    C₀.time i (d.mapState fun _ => entry₀) + 1 +
      if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
        C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
      else C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
  post i d :=
    if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      ((C₁.post (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)).mapState
        Sum.inr).mapState Sum.inl
    else
      (C₂.post (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)).mapState
        Sum.inr
  lo i d j := min (C₀.lo i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.lo (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.lo (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  hi i d j := max (C₀.hi i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.hi (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.hi (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨-, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h, if_pos h, H₁ h, C₁.run _ _ hd₁ (h₁ i _ hc hp h)]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h, if_neg h, H₂ h', C₂.run _ _ hd₂ (h₂ i _ hc hp h')]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h]
      refine Or.inl ⟨_, C₁.exit_mem _ _ hd₁ (h₁ i _ hc hp h), ?_⟩
      rw [mapState_state, mapState_state, Option.map_map]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h]
      exact Or.inr ⟨_, C₂.exit_mem _ _ hd₂ (h₂ i _ hc hp h'), rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · obtain ⟨hrun, hlive⟩ := HL u hle
      rw [hrun]
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rintro (⟨q, -, heq⟩ | ⟨q, -, heq⟩) <;>
        rw [mapState_state, mapState_state, hs] at heq <;> cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        have hv : v < C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₁) := by omega
        have hcut := C₁.cut _ _ hd₁ (h₁ i _ hc hp h) v hv
        have hlive := live C₁ _ _ hd₁ (h₁ i _ hc hp h) hv
        rw [H₁ h v]
        rintro (⟨q, hq, heq⟩ | ⟨q, -, heq⟩)
        · rw [mapState_state, mapState_state, Option.map_map] at heq
          exact hcut (Option.map_injective (Sum.inl_injective.comp Sum.inr_injective) heq ▸ hq)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, mapState_state, hs] at heq
          cases q <;> simp at heq
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        have hv : v < C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₂) := by omega
        have hcut := C₂.cut _ _ hd₂ (h₂ i _ hc hp h') v hv
        have hlive := live C₂ _ _ hd₂ (h₂ i _ hc hp h') hv
        rw [H₂ h' v]
        rintro (⟨q, -, heq⟩ | ⟨q, hq, heq⟩)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, hs] at heq
          cases q <;> simp at heq
        · rw [mapState_state] at heq
          exact hcut (Option.map_injective Sum.inr_injective heq ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · rw [(HL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₀.env i _ hc hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        rw [if_pos h, if_pos h, H₁ h v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        rw [if_neg h, if_neg h, H₂ h' v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₂.env _ _ hd₂ (h₂ i _ hc hp h') v (by omega) j)

/-! ### The specification API (user, 2026-10-16)

The data fields of the seam, phase and branch composites as equations, generated by `simps`
without the `simp` attribute, so that consumers never unfold the definitions. -/

attribute [simps (config := { isSimp := false }) pre time post lo hi] seq inPhase branch

end Contract

/-! ## The release adapter -/

/-- The release start is the anchor-mapped start, re-tagged fresh. -/
private lemma release_start {S : Type} {anchor : S} {x : List Γ} {d : Cfg k Γ (Unit ⊕ S) x}
    (hd : d.state = some (Sum.inl ())) :
    (d.mapState fun _ => anchor).mapState (fun _ => (Sum.inl () : Unit ⊕ S)) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- **The release adapter** (`Turing.seamReleaseTM_firstReturn`): a fresh start state executes the
anchor's first step, so the returning run becomes an ordinary contract whose cut includes time
`0`, at the same time and with no dispatch step. Its single exit is the right-tagged anchor, and
the envelopes are unchanged.

**Proof sketch.** The release start is the anchor-mapped start re-tagged fresh
(`release_start`). Fed the returning contract's positivity, run, return and positive cut,
`Turing.seamReleaseTM_firstReturn` gives the run to the right-tagged endpoint at the same time,
and the cut against the right-tagged anchor at every earlier time, time `0` included since the
fresh state is left-tagged. The exit is the endpoint's state, the anchor, right-tagged. For the
envelope, the head vector at time `0` is the start's; at a positive time the release run is
the source run, right-tagged (`Turing.seamReleaseTM_runFrom_pos`), so its heads are the
source's, inside the source envelope. -/
def ReturnContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ()) {some (Sum.inr anchor)} ι x where
  pre i d := C.pre i (d.mapState fun _ => anchor)
  time i d := C.time i (d.mapState fun _ => anchor)
  post i d := (C.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := C.lo i (d.mapState fun _ => anchor)
  hi i d := C.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.1
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    show Option.map Sum.inr (C.post i (d.mapState fun _ => anchor)).state ∈ _
    rw [C.exit_eq i _ hc hp]
    rfl
  cut i d hd hp u hu hmem := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.2 u hu (Set.mem_singleton_iff.mp hmem)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := C.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact C.env i _ hc hp u hu j

/-- **The round release** (design §16a item 2, with item 5's export): a fresh start state
executes the anchor's first step, so a round becomes an ordinary contract whose exits are the
right-tagged images of the anchor and of the escape set, at the same time and with the same
envelope. The escape set is arbitrary: it may contain `none` (a round that halts still ends
halted, since the tag keeps `none`), several states, or the anchor itself. **Only for a single
live escape distinct from the anchor**, `escape = {some e}` with `e ≠ anchor`, are the exits two
distinct live states, `some (Sum.inr anchor)` and `some (Sum.inr e)`, the shape of
`Turing.Contract.branch`'s first phase. Routing through the phase host
(`Turing.Contract.inPhase`) needs in general that `none` is not an exit and the redirect
conditions.

**Proof sketch.** At every positive time the release run is the round run, right-tagged
(`Turing.seamReleaseTM_runFrom_pos`), and the release start re-tags the anchor-mapped start. The
run and the exit are the round's, tagged. The cut at time `0` holds since the fresh state is
left-tagged; at a positive time a tagged exit would be an anchor or escape state of the round
before its end, which its cut excludes. The heads are the round's at every time. -/
def RoundContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ())
      (Option.map Sum.inr '' insert (some anchor) escape) ι x where
  pre i d := R.pre i (d.mapState fun _ => anchor)
  time i d := R.time i (d.mapState fun _ => anchor)
  post i d := (R.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := R.lo i (d.mapState fun _ => anchor)
  hi i d := R.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_runFrom_pos M anchor _ hc _ (R.pos i _ hc hp)
    rw [release_start hd, R.run i _ hc hp] at H
    exact H
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    exact ⟨_, R.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rintro ⟨q, hq, heq⟩
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · rw [MultiTapeTM.runFrom_zero, hd] at heq
      cases q <;> simp at heq
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H] at heq
      have hq' : q = (M.runFrom (d.mapState fun _ => anchor) u).state :=
        Option.map_injective Sum.inr_injective heq
      exact R.cut i _ hc hp u hpos hu (hq' ▸ Set.mem_insert_of_mem _ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := R.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact R.env i _ hc hp u hu j

/-! The specification API (user, 2026-10-16; its gate, finding 1): the two release adapters'
data fields as equations, generated by `simps` without the `simp` attribute, so that consumers
never unfold the definitions. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  ReturnContract.release RoundContract.release

/-! ## Joint trajectories, frames and positivity of the seam compositions (MIG-0b) -/

namespace Contract

/-- **`seq` preserves joint trajectories**: the first relation through the first phase, and the
second from the dispatch on (the dispatch step is stationary, so it is the second phase's time
`0`).

**Proof sketch.** By the seam trajectory (`seq_traj`), split at the first phase's time, as in
`Turing.Contract.seq`'s envelope. -/
theorem Traj.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {R₁ : ι → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.seq C₂ link hlink).Traj fun i d p => R₁ i (d.mapState fun _ => entry₁) p ∨
      R₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) p := by
  intro i d hd hp u hu
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
  change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
  by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
  · rw [(hL u hle).1]
    exact Or.inl (h₁ i _ hd₁ hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
      ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
    rw [hR v]
    exact Or.inr (h₂ _ _ hd₂ (hlink i _ hd₁ hp) v (by omega))

/-- **`seq` preserves frames**: the first footprint at the first-phase start and the second at
the second-phase start. Frames ignore control states, so the seam's tags do not matter.

**Proof sketch.** The first phase frames the start against its endpoint, and the second its
start, the state-replaced first endpoint, against the second endpoint; compose
(`Turing.Cfg.SameOutside.trans`) and re-tag (`Turing.Cfg.SameOutside.mapState`). -/
theorem Frames.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {fp₁ : ι → Cfg k Γ S₁ x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S₂ x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.seq C₂ link hlink).Frames fun i d j => fp₁ i (d.mapState fun _ => entry₁) j ∪
      fp₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j := by
  intro i d hd hp
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
  have f₁ : Cfg.SameOutside (fp₁ i (d.mapState fun _ => entry₁)) d
      (C₁.post i (d.mapState fun _ => entry₁)) := h₁ i _ hd₁ hp
  have f₂ := h₂ _ _ hd₂ (hlink i _ hd₁ hp)
  exact (f₁.trans fun j q hq => f₂ j q hq).mapState Sum.inr

/-- **`inPhase` preserves joint trajectories**: the phase's relation, at the state-replaced start.
The dispatch step is stationary.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`), as in
`Turing.Contract.inPhase`'s envelope: up to the phase's time the host heads are the phase's, and
at the dispatch they are the phase endpoint's. -/
theorem Traj.inPhase {I : Type} {Ph : I → Type} {Mf : (i : I) → MultiTapeTM k Γ (Ph i)}
    {q0 : Σ i, Ph i} {red : (i : I) → Ph i → Option (Σ i, Ph i)} {p : I} {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} {C : Contract (Mf p) s₀ X ι x}
    {hnone : none ∉ X} {hred : ∀ s, some s ∉ X → red p s = none}
    {hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p}
    {R : ι → Cfg k Γ (Ph p) x → (Fin k → ℤ) → Prop} (h : C.Traj R) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Traj
      fun i d => R i (d.mapState fun _ => s₀) := by
  intro i d hd hp u hu
  change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
  rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h' | h'
  · rw [hL u (by omega)]
    exact h i _ hc hp u (by omega)
  · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
    rw [hE]
    have h'' := h i _ hc hp _ le_rfl
    rw [C.run i _ hc hp] at h''
    exact h''

/-- **`branch` preserves joint trajectories**: the first phase's relation up to its time, then
the relation of the continuation that its exit selects.

**Proof sketch.** By the two-way trajectory (`branch_traj`) and by cases on the exit reached, as
in `Turing.Contract.branch`'s envelope. -/
theorem Traj.branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} {he : e₁ ≠ e₂}
    {C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x} {C₁ : Contract M₁ entry₁ X₁ κ₁ x}
    {C₂ : Contract M₂ entry₂ X₂ κ₂ x} {l₁ : ι → κ₁} {l₂ : ι → κ₂}
    {h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁)}
    {h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)}
    {R₀ : ι → Cfg k Γ S₀ x → (Fin k → ℤ) → Prop} {R₁ : κ₁ → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop}
    {R₂ : κ₂ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (t₀ : C₀.Traj R₀) (t₁ : C₁.Traj R₁) (t₂ : C₂.Traj R₂) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Traj fun i d p =>
      R₀ i (d.mapState fun _ => entry₀) p ∨
        (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
          R₁ (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) p
        else
          R₂ (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) p) := by
  intro i d hd hp u hu
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
  by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
  · rw [(HL u hle).1]
    exact Or.inl (t₀ i _ hc hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
      ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
    right
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_pos h] at hu
      rw [if_pos h, H₁ h v]
      exact t₁ _ _ hd₁ (h₁ i _ hc hp h) v (by omega)
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_neg h] at hu
      rw [if_neg h, H₂ h' v]
      exact t₂ _ _ hd₂ (h₂ i _ hc hp h') v (by omega)

/-- `seq` is positive: it takes a dispatch step. -/
theorem seq_positive {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} (C₁ : Contract M₁ entry₁ {some exit₁} ι x)
    (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    (C₁.seq C₂ link hlink).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

/-- `inPhase` is positive: it takes a dispatch step. -/
theorem inPhase_positive {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Positive :=
  fun _ _ _ _ => Nat.succ_pos _

/-- `branch` is positive: it takes a dispatch step. -/
theorem branch_positive {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (C₁ : Contract M₁ entry₁ X₁ κ₁ x)
    (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁) (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

end Contract

/-- The release of a returning contract is positive, since a return takes positive time. -/
theorem ReturnContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {ι : Type} {x : List Γ} (C : ReturnContract M anchor ι x) : C.release.Positive :=
  fun i d hd hp => C.pos i _ (by simp [Cfg.mapState, hd]) hp

/-- The release of a round contract is positive, since a round takes positive time. -/
theorem RoundContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    R.release.Positive :=
  fun i d hd hp => R.pos i _ (by simp [Cfg.mapState, hd]) hp

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: transport along the R1 embedding

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
MIG-0a's `Turing.Contract.embed`, moved here from `Build/Contract.lean` as landed on 2026-10-13
with no statement changed, with MIG-0b's joint trajectory and positivity of the transport.

## Main definitions

* `Turing.Contract.embed`: transport along the R1 embedding `Turing.embedEmitTM`, for
  output-normalized preconditions.

## Main results

* `Turing.Contract.Traj.embed`, `Turing.Contract.embed_positive`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

namespace Contract

/-- **Transport along the R1 embedding** (`Turing.embedEmitTM_runFrom`): the source contract
holds on the selected tapes; unselected tapes and heads are framed, and output is appended.
The precondition and the time are the source contract's at the selection `d.select σ`, and so
is the envelope of a selected head; an unselected head has the one-point envelope at its start.
The endpoint embeds the source endpoint into `d`'s tapes, heads and output.

The selection empties the source output, so `embed` transports **output-normalized**
preconditions only: a source precondition that inspects the output is tested on `[]` and is not
preserved (one asking for output `[true]` becomes false for every host). The intended
clean-call and tape-word instances fit; output-sensitive contracts would need a transport with
an explicit decomposition of the host output.

**Proof sketch.** By `Turing.embedEmitCfg_select`, `d` is the embedding of its own selection, so
`Turing.embedEmitTM_runFrom` makes the host run, at every time, the embedding of the source run
from the selection. The run is the embedded source run, and the exit and the cut are the
source's, since the selection and the embedding keep the state. For the envelope, a selected
head is the source head (`Turing.embedEmitCfg_selected_pos`), with the source bounds; an
unselected head stays at its start by the frame lemma `Turing.embedEmitTM_frame`, inside its
one-point interval. -/
noncomputable def embed {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S}
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry X ι x) :
    Contract (embedEmitTM σ M) entry X ι x where
  pre i d := C.pre i (d.select σ)
  time i d := C.time i (d.select σ)
  post i d := embedEmitCfg σ d.workTapes d.workTapePos d.output (C.post i (d.select σ))
  lo i d := Function.extend σ (C.lo i (d.select σ)) d.workTapePos
  hi i d := Function.extend σ (C.hi i (d.select σ)) d.workTapePos
  run i d hd hp := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ)
      (C.time i (d.select σ))
    rw [embedEmitCfg_select σ d] at hr
    rw [hr, C.run i _ hd hp]
  exit_mem i d hd hp := C.exit_mem i _ hd hp
  cut i d hd hp u hu := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    rw [hr]
    exact C.cut i _ hd hp u hu
  env i d hd hp u hu j := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    show ((embedEmitTM σ M).runFrom d u).workTapePos j ∈
      Finset.Icc (Function.extend σ (C.lo i (d.select σ)) d.workTapePos j)
        (Function.extend σ (C.hi i (d.select σ)) d.workTapePos j)
    rw [hr]
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨a, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, σ.injective.extend_apply, σ.injective.extend_apply]
      exact C.env i _ hd hp u hu a
    · have hf := (embedEmitTM_frame σ M d.workTapes d.workTapePos d.output (d.select σ) u).1 j hj
      rw [embedEmitTM_runFrom] at hf
      have hne : ¬∃ a, σ a = j := fun ⟨a, ha⟩ => hj ⟨a, ha⟩
      rw [hf.2, Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- **`embed` preserves joint trajectories**: the source relation holds of the selected heads,
at the selection, and every unselected head stays at its start.

**Proof sketch.** As in `Turing.Contract.embed`'s envelope: the host run is the embedded source
run (`Turing.embedEmitTM_runFrom` with `Turing.embedEmitCfg_select`), whose selected heads are
the source's (`Turing.embedEmitCfg_selected_pos`) and whose unselected heads are the frame
(`Turing.embedEmitCfg_unselected`). -/
theorem Traj.embed {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} {C : Contract M entry X ι x}
    {R : ι → Cfg m Γ S x → (Fin m → ℤ) → Prop} (h : C.Traj R) :
    (Contract.embed σ C).Traj fun i d p => R i (d.select σ) (fun a => p (σ a)) ∧
      ∀ j, j ∉ Set.range σ → p j = d.workTapePos j := by
  intro i d hd hp u hu
  have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
  rw [embedEmitCfg_select σ d] at hr
  rw [hr]
  refine ⟨?_, fun j hj => (embedEmitCfg_unselected σ _ _ _ _ j hj).2⟩
  have hs : (fun a => (embedEmitCfg σ d.workTapes d.workTapePos d.output
      (M.runFrom (d.select σ) u)).workTapePos (σ a)) = (M.runFrom (d.select σ) u).workTapePos :=
    funext fun a => embedEmitCfg_selected_pos σ _ _ _ _ a
  rw [hs]
  exact h i _ hd hp u hu

/-- `embed` keeps positivity: the time is the source's. -/
theorem embed_positive {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S}
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry X ι x)
    (h : C.Positive) : (Contract.embed σ C).Positive :=
  fun i _ hd hp => h i _ hd hp

end Contract

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Convention

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: proved.** The transformers and configuration transports below
are real definitions, and every contract is proved: the §12 fill epochs
(gates closed 2026-10-09) and the later additive exports, the last of them
the guarded state transport (retrofit RB5, 2026-10-10).

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.Cfg.select` — the selected bank of a host configuration, with empty output
  (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

* `Turing.embedEmitCfg_unselected`, `Turing.embedEmitCfg_select` — the frame export and
  the selection identity (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedEmitCfg_eq`, `Turing.embedEmitCfg_mapState_eq`,
  `Turing.embedEmitCfg_ofWords_eq` — the R1 reconstruction lemma and its corollaries
  (MIG-0b; the wave-1 fill gate's major F1). `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`
  moved to `StateRenaming` at MIG-0b.
* `Turing.embedEmitTM_tr` — the forwarding transformer's transition at the action level:
  the source action on each selected tape, `(none, 0)` on every other tape, and the input
  move, output and successor state unchanged (12.2c item 6's export).
* `Turing.embedSilentCfg_cap` — the silent transport's capture tape and head, off the
  selection (the C1-A assembly gate's export, 2026-10-14).
* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.
* `Turing.embedSilentCfg_unselected`, `Turing.embedSilentCfg_state`, `_inputPos`, `_output`,
  `Turing.embedEmitCfg_state`, `_inputPos`, `_output` — the transports' remaining fields, the
  specification API (user, 2026-10-16).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {Symbol : Type*} {x : List Symbol}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Symbol S) : Action k Symbol S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding transformer's transition** (12.2c item 6's prerequisite export;
user, 2026-10-10, from the RB5 review). One host transition of `embedEmitTM ι M` is the
source transition, read through `ι` and transported along it. Each selected host tape
`ι i` performs the source's tape-`i` action. Every unselected tape is stationary and
unwritten, `(none, 0)`. The input move, the output and the successor state are the
source's. Consumers cite this rather than unfolding the private slot search. [Bon26]

**Proof sketch.** `embedEmitTM` is `embedActionCore ι none` of the source action. The
selected and unselected tapes are the slot inverse's two equations, `embedSlot ι (ι i) =
some i` and `embedSlot ι j = none` off `Set.range ι`. The other three fields are copied
verbatim. -/
theorem embedEmitTM_tr (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) (q : S)
    (inp : Option Symbol) (w : Fin k → Option Symbol) :
    ((embedEmitTM ι M).tr q inp w).inputTape = (M.tr q inp fun i => w (ι i)).inputTape ∧
      (∀ i, ((embedEmitTM ι M).tr q inp w).workTapes (ι i) =
        (M.tr q inp fun i => w (ι i)).workTapes i) ∧
      (∀ j, j ∉ Set.range ι → ((embedEmitTM ι M).tr q inp w).workTapes j = (none, 0)) ∧
      ((embedEmitTM ι M).tr q inp w).output = (M.tr q inp fun i => w (ι i)).output ∧
      ((embedEmitTM ι M).tr q inp w).state = (M.tr q inp fun i => w (ι i)).state := by
  refine ⟨rfl, fun i => ?_, fun j hj => ?_, rfl, rfl⟩
  · simp [embedEmitTM, embedActionCore, embedSlot_selected]
  · simp [embedEmitTM, embedActionCore, embedSlot_unselected ι j hj]

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted symbol at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes**
(design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes**
(design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Symbol S) : Action k Symbol (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Symbol S x) : Cfg k Symbol (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Symbol S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (E : Cfg m Symbol S x → Cfg k Symbol S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Symbol S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor**
(round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor**
(round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports; `Turing.embedSilentCfg_cap`, after
them, exports the silent transport's capture field (the C1-A assembly gate, finding M1). They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- **The silent transport's capture tape.** If the capture tape `cap` lies outside the selection
`ι`, the transported configuration `Turing.embedSilentCfg ι cap tapes heads pre out₀ c` holds the
recorded word `pre ++ c.output` on `cap`, and that tape's head sits just after it, at
`|pre ++ c.output|`, for every frame, prefix, physical output and source configuration. It is the
capture-field companion of the selected-tape exports, so that consumers need not unfold the
transport's private slot search (the C1-A assembly gate, finding M1). (Technical glue.)

**Proof sketch.** Off the selection the slot search finds no source tape
(`embedSlot_unselected`), so both fields are the capture branch of the transport's
definition. -/
theorem embedSilentCfg_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes cap =
        FinTM.bufferTape (pre ++ c.output) ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos cap =
        ((pre ++ c.output).length : ℤ) := by
  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]

/-- **The silent transport's frame** (the specification API, user 2026-10-16): a host tape
outside the selection `ι`, other than the capture tape, holds the ambient frame `tapes j` with
its head at `heads j`. The frame companion of `Turing.embedSilentCfg_cap`.

**Proof sketch.** Off the selection the slot search finds no source tape
(`embedSlot_unselected`), and `j ≠ cap` selects the frame branch. -/
theorem embedSilentCfg_unselected (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (j : Fin k) (hj : j ∉ Set.range ι)
    (hcap : j ≠ cap) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes j = tapes j ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos j = heads j := by
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hcap]

/-! The specification API (user, 2026-10-16): the two transports' state, input position and
output as equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) state inputPos output] embedSilentCfg embedEmitCfg


end Turing

namespace Turing

variable {k : ℕ} {Γ : Type*}

/-! ## Reconstruction of embedded configurations (MIG-0b)

The frame export missing beside `Turing.embedEmitCfg_selected_tape` and `_pos`, the selection of
a host configuration, and the **R1 reconstruction lemma** (the wave-1 fill gate's major F1,
acknowledged by the user; backlog F6-1(i), F7-1(b)), with its relabelling and word-layout
corollaries. The first three moved here from `Build/Contract.lean` at MIG-0b's layering split.
All are stated over any universes, like the rest of `Build/Embed`: MIG-0a stated its three over
`Type`, which are instances (the generalization changes nothing else in their statements), so
that the lemma can replace every member of the family at its own signature (`RecordTable`'s
`rt_embed_matches` is stated over `Type*`). -/

/-- The forwarding embedding keeps an unselected tape and head as its frame: the export missing
from `Build/Embed.lean` beside `Turing.embedEmitCfg_selected_tape` and `_pos`. It moved to
`Build/Embed` from `Build/Contract.lean` at MIG-0b's layering split.

**Proof sketch.** At time `0`, `Turing.embedEmitTM_frame` for a one-state machine says exactly
this; the transport's tape fields do not depend on the state type. -/
theorem embedEmitCfg_unselected {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (j : Fin k) (hj : j ∉ Set.range σ) :
    (embedEmitCfg σ tapes heads pre c).workTapes j = tapes j ∧
      (embedEmitCfg σ tapes heads pre c).workTapePos j = heads j := by
  let M0 : MultiTapeTM m Γ Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let c0 : Cfg m Γ Unit x := ⟨none, c.inputPos, c.workTapes, c.workTapePos, c.output⟩
  have h := (embedEmitTM_frame σ M0 tapes heads pre c0 0).1 j hj
  simp only [MultiTapeTM.runFrom_zero] at h
  exact h

/-- The source configuration seen through an R1 selection: selected tapes and heads, the same
state and input position, and an **empty output**. The selection empties the source output, so
a source precondition is always tested on the output `[]`: `Turing.Contract.embed` transports
output-normalized preconditions only. -/
def Cfg.select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) : Cfg m Γ S x :=
  ⟨d.state, d.inputPos, fun i => d.workTapes (σ i), fun i => d.workTapePos (σ i), []⟩

/-- **The R1 reconstruction lemma** (MIG-0b; backlog F6-1(i), F7-1(b)): an embedded
configuration is determined by its selected bank and its ambient frame. If `d` has the state,
input position and selected tapes and heads of `c`, its output is `pre` followed by `c`'s, and
off the selection it holds the frame `tapes`, `heads`, then `d` is the forwarding embedding of `c`
into that frame. At their migrations it replaces `OracleSim.oracleBankCfg_eq`,
`CodeSimulator.canonEmbedEq`, `Primitives.emitterP2_frame` and the local `hframe` of
`Loop.emCall_exit_fixed` (the MIG-0b fit tests derive each in one term).

**Proof sketch.** Compare field by field. A selected tape or head is the source's
(`Turing.embedEmitCfg_selected_tape`, `_pos`), which is `d`'s by hypothesis; an unselected one is
the frame (`Turing.embedEmitCfg_unselected`), which is `d`'s by hypothesis. The state, the input
position and the output are the hypotheses. -/
theorem embedEmitCfg_eq {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (d : Cfg k Γ S x) (hs : c.state = d.state) (hin : c.inputPos = d.inputPos)
    (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    embedEmitCfg σ tapes heads pre c = d := by
  have fields (j : Fin k) :
      (embedEmitCfg σ tapes heads pre c).workTapes j = d.workTapes j ∧
        (embedEmitCfg σ tapes heads pre c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
      exact selected i
    · obtain ⟨ht, hp⟩ := embedEmitCfg_unselected σ tapes heads pre c j hj
      exact ⟨ht.trans (outside j hj).1, hp.trans (outside j hj).2⟩
  exact Cfg.ext hs hin (funext fun j => (fields j).1) (funext fun j => (fields j).2) hout

/-- **R1 reconstruction with state relabelling**: as `Turing.embedEmitCfg_eq`, for a host whose
control is the source's relabelled by `f` (the phase-host and call-controller tags). This is the
shape of `Primitives.emitterP2_frame` and of `Loop.emCall_exit_fixed`'s `hframe`.

**Proof sketch.** Relabelling the embedded configuration is embedding the relabelled source, by
definition; apply `Turing.embedEmitCfg_eq` to it. -/
theorem embedEmitCfg_mapState_eq {m : ℕ} {S H : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (f : S → H) (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ)
    (c : Cfg m Γ S x) (d : Cfg k Γ H x) (hs : c.state.map f = d.state)
    (hin : c.inputPos = d.inputPos) (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    (embedEmitCfg σ tapes heads pre c).mapState f = d :=
  embedEmitCfg_eq σ tapes heads pre (c.mapState f) d hs hin hout selected outside

/-- **R1 reconstruction, word layout**: embedding a word seam into a word frame gives the word
seam of the combined layout, when the target's selected words are the source's and its other words
the frame's. This is the shape of `CodeSimulator.canonEmbedWords` and `CertShell.cert_embed_words`
(`Build/Embed` imports `Build/Convention`, where `Turing.Cfg.ofWords` lives, for it).

**Proof sketch.** `Turing.embedEmitCfg_eq`: the selected tapes are the source buffers, the other
tapes the frame buffers, and every head is at the origin. -/
theorem embedEmitCfg_ofWords_eq {m : ℕ} {S : Type*} {x : List Bool} (σ : Fin m ↪ Fin k) (q : S)
    (v : Fin m → List Bool) (frame target : Fin k → List Bool)
    (selected : ∀ i, target (σ i) = v i)
    (outside : ∀ j, j ∉ Set.range σ → frame j = target j) :
    embedEmitCfg σ (fun j => FinTM.bufferTape (frame j)) (fun _ => 0) []
        (Cfg.ofWords (input := x) q v) = Cfg.ofWords q target :=
  embedEmitCfg_eq σ _ _ [] _ _ rfl rfl rfl
    (fun i => ⟨congrArg FinTM.bufferTape (selected i).symm, rfl⟩)
    (fun j hj => ⟨congrArg FinTM.bufferTape (outside j hj), rfl⟩)

/-- Every host configuration is the forwarding embedding of its selection, framed by itself:
embedding the selection of `d` into `d`'s own tapes, heads and output gives back `d`.

**Proof sketch.** The R1 reconstruction lemma (`Turing.embedEmitCfg_eq`) at `d`'s own tapes,
heads and output: the selection keeps the state, the input position and the selected tapes and
heads, its empty output follows `d`'s, and off the selection the frame is `d`'s own. -/
theorem embedEmitCfg_select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d :=
  embedEmitCfg_eq σ _ _ _ _ d rfl rfl (List.append_nil _) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩)

end Turing
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

## ===== TCSlib/Programs/WordRAM/Steps.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Machine/Steps.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/WordRAM/Steps.lean`, with imports remapped;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header;
* added four TCSlib readers, so that other files can read `step`, `effect` and `Steps` without
  unfolding them (policy rule 10; Seyoon, 2026-11-17): `step_def`, `effect_def`,
  `Steps.zero_iff` and `Steps.succ_iff`. Each restates its definition and is proved by `rfl`.
The remaining content is unchanged.
-/
import TCSlib.Programs.WordRAM.Basic
import TCSlib.Programs.Util.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace WordRAM

open WordRAM (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/

/-- The integer v is the signed value of a W-bit word. -/
def InRange (W : ℕ) (v : ℤ) : Prop := -(2 : ℤ) ^ W ≤ 2 * v ∧ 2 * v < (2 : ℤ) ^ W

/-- The word of an integer. -/
abbrev wd (W : ℕ) (v : ℤ) : BitVec W := BitVec.ofInt W v

/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : InRange W v) : (wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : wd W w.toInt = w := BitVec.ofInt_toInt

private theorem wd_add (a b : ℤ) : wd W a + wd W b = wd W (a + b) := (BitVec.ofInt_add a b).symm

private theorem wd_mul (a b : ℤ) : wd W a * wd W b = wd W (a * b) := (BitVec.ofInt_mul a b).symm

private theorem wd_sub (a b : ℤ) : wd W a - wd W b = wd W (a - b) := by
  rw [sub_eq_add_neg a b, wd, wd, wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

private theorem wd_one : (1 : BitVec W) = wd W 1 := BitVec.eq_of_toNat_eq rfl

/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros. -/
theorem loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by
  simp [loadWords, show ¬ ((a : ℤ) < 0) by omega]

/-- The negative cells of the initial memory hold zeros. -/
theorem loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0) :
    loadWords W ws a = wd W 0 := by
  simp [loadWords, ha]

/-! ## Configurations and single steps -/

/-- A configuration of the machine: the position of the next instruction and the memory. -/
structure Cfg (W : ℕ) where
  pc : ℕ
  mem : ℤ → BitVec W

/-- One step: the next configuration, or the verdict. -/
def step (P : List Instr) (c : Cfg W) : Cfg W ⊕ Bool :=
  let m := c.mem
  let write (i : ℤ) (v : BitVec W) : Cfg W ⊕ Bool :=
    .inl ⟨c.pc + 1, fun x => if x = i then v else m x⟩
  match P.getD c.pc .reject with
  | .one i => write i 1
  | .add i j k => write i (m j + m k)
  | .sub i j k => write i (m j - m k)
  | .mul i j k => write i (m j * m k)
  | .load i j => write i (m (m j).toInt)
  | .store i j => write (m i).toInt (m j)
  | .bltz i l => .inl ⟨if (m i).toInt < 0 then l else c.pc + 1, m⟩
  | .accept => .inr true
  | .reject => .inr false

/-- (TCSlib reader.) **One step, as an equation**: `step P c` reads the instruction at `c.pc`
(`reject` past the end of `P`). The six memory instructions write one cell and advance, `bltz`
jumps to `l` on a negative cell and otherwise advances, and `accept` and `reject` give the
verdicts. -/
theorem step_def (P : List Instr) (c : Cfg W) :
    step P c =
      match P.getD c.pc .reject with
      | .one i => .inl ⟨c.pc + 1, fun x => if x = i then 1 else c.mem x⟩
      | .add i j k => .inl ⟨c.pc + 1, fun x => if x = i then c.mem j + c.mem k else c.mem x⟩
      | .sub i j k => .inl ⟨c.pc + 1, fun x => if x = i then c.mem j - c.mem k else c.mem x⟩
      | .mul i j k => .inl ⟨c.pc + 1, fun x => if x = i then c.mem j * c.mem k else c.mem x⟩
      | .load i j => .inl ⟨c.pc + 1, fun x => if x = i then c.mem (c.mem j).toInt else c.mem x⟩
      | .store i j =>
        .inl ⟨c.pc + 1, fun x => if x = (c.mem i).toInt then c.mem j else c.mem x⟩
      | .bltz i l => .inl ⟨if (c.mem i).toInt < 0 then l else c.pc + 1, c.mem⟩
      | .accept => .inr true
      | .reject => .inr false := rfl

/-! ## Runs -/

/-- n steps of the machine, none of which gives a verdict, lead from c to c'. -/
def Steps (P : List Instr) : ℕ → Cfg W → Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, step P c = .inl c₁ ∧ Steps P n c₁ c'

theorem Steps.refl (c : Cfg W) : Steps P 0 c c := rfl

/-- (TCSlib reader.) A run of no steps leads from `c` exactly to itself. -/
theorem Steps.zero_iff {c c' : Cfg W} : Steps P 0 c c' ↔ c = c' := Iff.rfl

/-- (TCSlib reader.) A run of `n + 1` steps is a first step to some `c₁`, giving no verdict,
followed by a run of `n` steps from `c₁`. -/
theorem Steps.succ_iff {n : ℕ} {c c' : Cfg W} :
    Steps P (n + 1) c c' ↔ ∃ c₁, step P c = .inl c₁ ∧ Steps P n c₁ c' := Iff.rfl

private theorem Steps.one {c c' : Cfg W} (h : step P c = .inl c') : Steps P 1 c c' := ⟨c', h, rfl⟩

/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : Cfg W} (h₁ : Steps P n c c₁) (h₂ : Steps P k c₁ c₂) :
    Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {n p p' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := hp ▸ h

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n n' : ℕ} {c c' : Cfg W} (h : Steps P n c c') (hn : n = n') :
    Steps P n' c c' := hn ▸ h

/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

private theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]

/-- A run that reaches a verdict. -/
theorem exec_of_steps {n : ℕ} {c c' : Cfg W} {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    rw [exec_succ_of_step hs]
    exact ih hr

/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/

/-- The program P has the instructions of the list l from position pos on. -/
def CodeAt (P : List Instr) (pos : ℕ) (l : List Instr) : Prop := l <+: P.drop pos

/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List Instr) : CodeAt l 0 l := List.prefix_refl l

/-- The first part of a piece of code. -/
theorem CodeAt.left {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l :=
  CodeAt.right (l₁ := [i]) h

/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos {pos pos' : ℕ} {l : List Instr} (h : CodeAt P pos l) (hp : pos = pos') :
    CodeAt P pos' l := hp ▸ h

/-! ## Straight-line code -/

/-- The instructions that only change the memory and go on to the next position. -/
def Straight : Instr → Prop
  | .one _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .load _ _ | .store _ _ => True
  | _ => False

/-- What an instruction that only changes the memory does to it. -/
def effect (i : Instr) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  match i with
  | .one i => Function.update m i (wd W 1)
  | .add i j k => Function.update m i (m j + m k)
  | .sub i j k => Function.update m i (m j - m k)
  | .mul i j k => Function.update m i (m j * m k)
  | .load i j => Function.update m i (m (m j).toInt)
  | .store i j => Function.update m (m i).toInt (m j)
  | _ => m

/-- (TCSlib reader.) **The memory effect, as an equation**: each of the six memory instructions
updates one cell, and `bltz`, `accept` and `reject` leave the memory unchanged. -/
theorem effect_def (i : Instr) (m : ℤ → BitVec W) :
    effect i m =
      match i with
      | .one i => Function.update m i (wd W 1)
      | .add i j k => Function.update m i (m j + m k)
      | .sub i j k => Function.update m i (m j - m k)
      | .mul i j k => Function.update m i (m j * m k)
      | .load i j => Function.update m i (m (m j).toInt)
      | .store i j => Function.update m (m i).toInt (m j)
      | _ => m := rfl

/-- What a list of instructions that only change the memory does to it. -/
def effects (l : List Instr) (m : ℤ → BitVec W) : ℤ → BitVec W := l.foldl (fun m i => effect i m) m

@[simp] theorem effects_nil (m : ℤ → BitVec W) : effects [] m = m := rfl

@[simp] theorem effects_cons (i : Instr) (l : List Instr) (m : ℤ → BitVec W) :
    effects (i :: l) m = effects l (effect i m) := rfl

theorem effects_append (l₁ l₂ : List Instr) (m : ℤ → BitVec W) :
    effects (l₁ ++ l₂) m = effects l₂ (effects l₁ m) := by
  simp [effects, List.foldl_append]

private theorem step_straight {c : Cfg W} {i : Instr} (h : P.getD c.pc .reject = i)
    (hi : Straight i) : step P c = .inl ⟨c.pc + 1, effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [Straight] at hi <;> simp only [step, h, effect, write, wd_one]

/-- One instruction that only changes the memory. -/
private theorem steps_instr {rest : List Instr} {pos : ℕ} {i : Instr}
    (hcode : CodeAt P pos (i :: rest)) (hi : Straight i) (m : ℤ → BitVec W) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, effect i m⟩ :=
  Steps.one (step_straight hcode.head hi)

/-- A list of instructions that only change the memory. -/
theorem steps_straight (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : CodeAt P pc l)
    (hl : ∀ i ∈ l, Straight i) : Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, step_straight hcode.head hi,
      (ih (pc + 1) (effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

/-- The only constant. -/
theorem effect_one (i : ℤ) : effect (.one i) m = Function.update m i (wd W 1) := rfl

/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.add i j k) m = Function.update m i (wd W (a + b)) := by
  rw [effect, hj, hk, wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by
  rw [effect, hj, hk, wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by
  rw [effect, hj, hk, wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by
  rw [effect, hj, toInt_wd ha]

/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by
  rw [effect, hi, toInt_wd ha]

theorem steps_add {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.add i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a + b))⟩ :=
  effect_add i hj hk ▸ steps_instr hcode trivial m

theorem steps_sub {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.sub i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a - b))⟩ :=
  effect_sub i hj hk ▸ steps_instr hcode trivial m

theorem steps_load {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.load i j :: rest))
    (hj : m j = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  effect_load i hj ha ▸ steps_instr hcode trivial m

theorem steps_store {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.store i j :: rest))
    (hi : m i = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  effect_store j hi ha ▸ steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {rest : List Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine Steps.one ?_
  simp only [step, hcode.head, hc, toInt_wd hv]

/-- A run that ends with a branch on the sign of v, where v is negative if and only if p fails. -/
theorem Steps.branch {n l pos pos' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by
  subst hpos
  by_cases hp : p
  · exact ⟨fun _ => by rwa [if_neg (hv.1 hp)] at h, fun h' => absurd hp h'⟩
  · exact ⟨fun h' => absurd h' hp, fun _ => by rwa [if_pos (not_not.1 (mt hv.2 hp))] at h⟩

theorem step_accept {c : Cfg W} (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by
  simp only [step, h]

theorem step_reject {c : Cfg W} (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by
  simp only [step, h]

/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

/-- The memory m' differs from m only in cells of the set s. -/
def AgreeOutside (s : Set ℤ) (m m' : ℤ → BitVec W) : Prop := Set.EqOn m' m sᶜ

theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside t m₂ m₃) :
    AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)

/-- The instruction writes no cell outside s, whatever the memory holds. -/
def WritesIn (s : Set ℤ) : Instr → Prop
  | .one i | .add i _ _ | .sub i _ _ | .mul i _ _ | .load i _ => i ∈ s
  | .store _ _ => False
  | _ => True

theorem WritesIn.mono {i : Instr} (h : WritesIn s i) (hst : s ⊆ t) : WritesIn t i := by
  cases i <;> first | exact hst h | exact h

private theorem agreeOutside_effect {i : Instr} (h : WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effect i m) := by
  cases i <;>
    first | exact (AgreeOutside.refl s m).update h _ | exact AgreeOutside.refl s m | exact h.elim

/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by
  induction l generalizing m with
  | nil => exact AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (agreeOutside_effect hi m).trans (ih hl _)

end framing

end WordRAM
end
```

## ===== TCSlib/Programs/WordRAM/Basic.lean =====

```
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `EndStatement.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/WordRAM/Basic.lean`, with imports remapped;
* kept only the word RAM (`Instr`, `exec`, `loadWords`); dropped the paper's problems and claims, and rewrote the module docstring accordingly;
* namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` to `Light`, with module names and paths in comments updated;
* added the repository-standard `set_option` header.
The remaining content is unchanged.
-/


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word RAM

The word RAM of [AFM26] (file `EndStatement.lean` there): `Instr`, the nine instructions of a program;
`exec`, a run of a program within a step budget; and `loadWords`, the initial memory. Imports
nothing, proves nothing.

## References

* [AFM26] anthropics/formal-math, `3sum-apsp`, commit e1a4e650, Apache-2.0.
-/

section

namespace WordRAM

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell `i`. The only constant is 1. -/
inductive Instr where
  | one (i : Int)             -- [i] := 1
  | add (i j k : Int)         -- [i] := [j] + [k]
  | sub (i j k : Int)         -- [i] := [j] - [k]
  | mul (i j k : Int)         -- [i] := [j] * [k]
  | load (i j : Int)          -- [i] := [[j]]
  | store (i j : Int)         -- [[i]] := [j]
  | bltz (i : Int) (l : Nat)  -- if [i] < 0, go to position l
  | accept
  | reject

/-- The verdict and the final memory, if `P`, run from position `pc` on memory `m`, halts within `t` steps, the halting
step counted; past its end `P` rejects. Addresses are read signed; `bltz` jumps on a negative word; `write` runs on. -/
def exec {W : Nat} (P : List Instr) : (t pc : Nat) → (m : Int → BitVec W) → Option (Bool × (Int → BitVec W))
  | 0, _, _ => none
  | t + 1, pc, m =>
    let write (i : Int) (v : BitVec W) := exec P t (pc + 1) fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => write i (m (m j).toInt)
    | .store i j => write (m i).toInt (m j)
    | .bltz i l => exec P t (if (m i).toInt < 0 then l else pc + 1) m
    | .accept => some (true, m)
    | .reject => some (false, m)

/-- The memory at the start: `ws` in cells 0, 1, 2, …, and 0 in every other cell. -/
def loadWords (W : Nat) (ws : List Int) : Int → BitVec W :=
  fun a => if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0)

end WordRAM
end
```

## ===== TCSlib/Complexity/TuringMachine/Nondeterministic.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic Multi-Tape Turing Machines

[AB09, §2.1.2]: a nondeterministic Turing machine (NDTM) is a standard TM with **two**
transition functions `δ₀` and `δ₁`; at every step the machine chooses which of the two to
apply. A finite run is therefore governed by a *choice word* — one bit per step — and the
run function is indexed by it. This module defines the raw machine, its choice-word
semantics in the style of the deterministic `Turing.MultiTapeTM.runFrom`, the all-branch
halting predicate that time bounds quantify over, the bundled finite layer `FinNDTM`, and
the embedding of deterministic machines. Acceptance and the class `NTIME` live one layer
up, in `TCSlib.Complexity.ClassNP.NTIME`, because they fix the binary alphabet. The last
section is the run-level layer of the nondeterministic contract variant (C1): runs along
state embeddings, the slice lemma, state relabelling and input locality.

## Design and deviations from [AB09]

* **Two total transition functions, `Bool`-indexed**: the single field
  `tr : Bool → …` carries [AB09]'s `δ₀` as `tr false` and `δ₁` as `tr true`. Both
  functions are total, so no configuration is ever *stuck* — every choice word of every
  length drives a complete run. (This is the load-bearing difference from a
  relational model such as cslib's `MultiTapeNTM`, surveyed and deliberately not
  ported — see the plan's decision log: with binary choice the accepting choice word
  *is* the polynomial-length certificate of [AB09, Theorem 2.6], while arbitrary
  branching relations have no canonical certificate encoding.)
* **Choice words are finite lists** (`List Bool`), consumed left to right, one bit per
  step: `runWith w cfg` is the configuration after `|w|` steps under the choices `w`.
  The alternative — infinite choice streams `ℕ → Bool` with a separate step count — is
  equivalent for every notion built here (only the first `t` bits of a stream are ever
  consulted); the list form makes the choice word a finite string that can be a
  certificate. **Design question (c) for the phase-2 audit.**
* **No `q_accept` state.** [AB09] equips NDTMs with a distinguished accepting state;
  our machines signal through their output tape, exactly as the deterministic
  development does (`Turing.FinTM.DecidesInTime` reads acceptance off the output
  `[true]`/`[false]`). Acceptance-by-output is defined in
  `TCSlib.Complexity.ClassNP.NTIME` and is **design question (a) for the phase-2
  audit**.
* **Halting is absorbing under every choice**: stepping a halted configuration is the
  identity regardless of the choice bit, mirroring the deterministic `step`. Extending
  a choice word beyond the halting time therefore never changes the reached
  configuration — the lemma `runWith_of_halt` below. This is what the exact-length
  quantifiers lean on, *directionally*: accepting witnesses pad to any larger exact
  length, and all-branch halting at a larger budget follows by splitting at the old
  one (`HaltsWithin.mono`). It does **not** make every bounded-length rewriting valid —
  "every word of length at most `t` is halted" already fails at the empty word — and
  the correct bounded readings are recorded in `TCSlib.Complexity.ClassNP.NTIME`
  (round-1 audit, finding 2).
* The model reuses the vendored configuration layer (`Turing.Cfg`, `Turing.Action`)
  unchanged: an NDTM step applies an `Action` exactly as a deterministic step does; only
  the *selection* of the action is new.

## Main definitions

* `Turing.NDTM` — the binary-choice nondeterministic machine. [AB09, §2.1.2]
* `Turing.NDTM.stepWith`, `Turing.NDTM.runWith` — one step under a choice bit; the run
  under a choice word. [AB09, §2.1.2]
* `Turing.NDTM.HaltsWithin` — every choice word of length `t` halts the machine on the
  given input; the totality condition of [AB09]'s "runs in `T(n)` time".
* `Turing.NDTM.fixChoice` — the deterministic slice at a fixed choice bit, with
  `Turing.NDTM.stepWith_eq_fixChoice_step` (added 2026-10-10).
* `Turing.FinNDTM` — the bundled finite layer, mirroring `Turing.FinTM`.
* `Turing.MultiTapeTM.toNDTM`, `Turing.FinTM.toFinNDTM` — a deterministic machine as an
  NDTM whose two transition functions coincide.
* `Turing.NDTM.relabelState` — state relabelling of an NDTM along an equivalence, mirroring
  `Turing.MultiTapeTM.relabelState` (C1).

## Main results

* `Turing.NDTM.runWith_eq_fixChoice_runFrom` — a branch that meets no real choice is the run of
  the deterministic slice (stage 2's slice lemma; statement gated 2026-10-14; proved, by the
  agreement transfer at the identity embedding, C1).
* `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt` — the choice-word run
  algebra (proved; pure unfoldings, the nondeterministic counterparts of the vendored
  `runFrom` lemmas).
* `Turing.NDTM.HaltsWithin.mono` — all-branch halting is monotone in the time bound.
* `Turing.NDTM.exists_first_halt` — a halted branch halts first at a least prefix of its choice
  word, live before it and already in its final configuration there.
* `Turing.NDTM.not_haltsWithin_zero` — no machine halts within `0` steps along every branch: the
  initial configuration is live (the counterpart of `Turing.FinTM.not_computesInTime_zero`).
* `Turing.MultiTapeTM.toNDTM_runWith` — the embedded deterministic machine ignores its
  choices: every choice word of length `t` reproduces `runFrom` at time `t`.
* `Turing.NDTM.runWith_mapState_of_agreeOn`, `Turing.NDTM.runWith_mapState_of_agreeOn_det` —
  the agreement transfer: a host whose transition functions agree with a nondeterministic or a
  deterministic source along a state embedding, at the states visited, runs as the source
  renamed (with the one-step form `Turing.NDTM.stepWith_mapState_of_agreeOn`; proved, C1).
* `Turing.NDTM.relabelState_runWith` — relabelled branches are the renamed branches (proved).
* `Turing.NDTM.runWith_initCfg_take` — input locality: a branch of at most `m` steps reads only
  the first `m` input symbols (proved, C1).
* The ND inventory API (C1's pre-ship inventory, 2026-10-17): the live step
  `Turing.NDTM.stepWith_of_some`; `Turing.NDTM.initCfg_eq` and `Turing.NDTM.haltsWithin_iff`;
  the fields of the slice `Turing.NDTM.fixChoice_q₀`, `_tr`, of the embedding
  `Turing.MultiTapeTM.toNDTM_q₀`, `_tr` and `Turing.FinTM.toFinNDTM_k`, `_State`, `_tm`, and of
  the relabelling `Turing.NDTM.relabelState_q₀`, `_tr`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.4; §2.1.2, pp. 41-42.)
* cslib (https://github.com/leanprover/cslib), `MultiTape/Nondeterministic.lean` at
  commit a3747758: a relational nondeterministic model (related work, not ported — see
  `AroraBarakChapter2Plan.md`, decision log).
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A binary-choice nondeterministic multi-tape Turing machine [AB09, §2.1.2]: a
machine with **two** total transition functions, carried as the `Bool`-indexed field
`tr` — `tr false` is [AB09]'s `δ₀` and `tr true` is `δ₁`. Tapes, actions, and
configurations are exactly those of the deterministic `Turing.MultiTapeTM`; as there,
`Symbol` and `State` need not be finite at this layer (the bundled finite layer is
`Turing.FinNDTM` below). -/
structure NDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- the two transition functions, indexed by the nondeterministic choice: `tr false`
  is `δ₀`, `tr true` is `δ₁`; each maps the state, input symbol, and work-head symbols
  to an action, exactly as the deterministic transition function does -/
  tr (choice : Bool) (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace NDTM

variable {input : List Symbol} {tm : NDTM k Symbol State}

/-- One step under the choice bit `b`: apply the action selected by transition function
`tr b`, or stay put when already halted. Halting is absorbing under **every** choice —
the halted branch does not consult `b` — mirroring `Turing.MultiTapeTM.step`. -/
def stepWith (b : Bool) (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration corresponding to an input string — identical to the
deterministic initialization (blank work tapes, input head on the first symbol). -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- **The initial configuration is `Cfg.init` at the start state** (the ND inventory API,
2026-10-17), the counterpart of `Turing.MultiTapeTM.initCfg_eq`:
`tm.initCfg input = Cfg.init tm.q₀ input`. -/
theorem initCfg_eq (input : List Symbol) : tm.initCfg input = Cfg.init tm.q₀ input :=
  rfl

/-- The configuration reached from `cfg` by running under the choice word `w`, one
choice bit per step, consumed left to right: `|w|` steps in total. This is the
nondeterministic counterpart of `Turing.MultiTapeTM.runFrom`; a "branch" of the
computation tree of [AB09, §2.1.2] is the run under one choice word. -/
def runWith : List Bool → Cfg k Symbol State input → Cfg k Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => runWith w (tm.stepWith b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil {cfg : Cfg k Symbol State input} : tm.runWith [] cfg = cfg := rfl

/-- Consuming one choice bit is one step: the run under `b :: w` is the run under `w`
from the configuration one `stepWith b` ahead. -/
lemma runWith_cons {b : Bool} {w : List Bool} {cfg : Cfg k Symbol State input} :
    tm.runWith (b :: w) cfg = tm.runWith w (tm.stepWith b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the counterpart of `Turing.MultiTapeTM.runFrom_add`. -/
lemma runWith_append (w w' : List Bool) (cfg : Cfg k Symbol State input) :
    tm.runWith (w ++ w') cfg = tm.runWith w' (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- The deterministic slice of a nondeterministic machine at a fixed choice bit: the
multi-tape machine that always uses the transition function `tm.tr b`. [AB09, §2.1.2: an
NDTM has two transition functions, and a choice bit selects one] (Shared by the
configuration-graph layer; added 2026-10-10.) -/
def fixChoice (tm : NDTM k Symbol State) (b : Bool) : MultiTapeTM k Symbol State :=
  ⟨tm.q₀, tm.tr b⟩

/-! The slice's fields as equations (the ND inventory API, 2026-10-17), generated by `simps` without
the `simp` attribute: `(tm.fixChoice b).q₀ = tm.q₀` and `(tm.fixChoice b).tr = tm.tr b`. -/
attribute [simps (config := { isSimp := false }) q₀ tr] fixChoice

/-- One nondeterministic step under the choice bit `b` is one step of the slice at `b`.

**Proof sketch.** Both steps fix a halted configuration, and otherwise apply the action
that `tm.tr b` reads from the same configuration (`cases` on the state). -/
theorem stepWith_eq_fixChoice_step (tm : NDTM k Symbol State) (b : Bool)
    (cfg : Cfg k Symbol State input) : tm.stepWith b cfg = (tm.fixChoice b).step cfg := by
  cases h : cfg.state <;> simp only [NDTM.stepWith, MultiTapeTM.step, fixChoice, h]

/-- Stepping a halted configuration is the identity, under either choice. -/
@[simp]
lemma stepWith_of_halt {b : Bool} {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.stepWith b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- **A live step applies the chosen action** (the ND inventory API, 2026-10-17), the counterpart of
`Turing.MultiTapeTM.step_of_some`: at a live state `q` one step under the choice bit `b` applies the
action of `tm.tr b` for the scanned symbols, `cfg.state = some q →`
`tm.stepWith b cfg = (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg`. -/
theorem stepWith_of_some {b : Bool} {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    tm.stepWith b cfg = (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under **every** choice word — the
counterpart of `Turing.MultiTapeTM.runFrom_of_halt`. Extending a choice word beyond the
halting time therefore never changes the reached configuration. -/
@[simp]
lemma runWith_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none)
    {w : List Bool} : tm.runWith w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt h]; exact ih

/-- The machine halts on `input` within `t` steps **along every branch**: after any `t`
nondeterministic choices the configuration is halted. This is the totality condition in
[AB09]'s "runs in `T(n)` time" (§2.1.2: *every* sequence of choices reaches the halting
state within the bound), rendered over choice words of length exactly `t`; by
`Turing.NDTM.runWith_of_halt` the exact-length quantifier already covers all longer
words, and `Turing.NDTM.HaltsWithin.mono` makes this precise. -/
def HaltsWithin (tm : NDTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none

/-- **All-branch halting, unfolded** (the ND inventory API, 2026-10-17): `tm.HaltsWithin input t`
holds iff every choice word `w` of length `t` leaves the run from `tm.initCfg input` halted,
`∀ w, w.length = t → (tm.runWith w (tm.initCfg input)).state = none`. -/
theorem haltsWithin_iff {tm : NDTM k Symbol State} {input : List Symbol} {t : ℕ} :
    tm.HaltsWithin input t ↔
      ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none :=
  Iff.rfl

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Given `w` with `|w| = t' ≥ t`, split `w = w.take t ++ w.drop t`
(`List.take_append_drop`) with `|w.take t| = t` (`List.length_take`, since `t ≤ t'`).
By the hypothesis the run under `w.take t` is halted; `Turing.NDTM.runWith_append`
factors the run under `w` through it, and `Turing.NDTM.runWith_of_halt` absorbs the
remaining choices, so the state at `w` equals the halted state at `w.take t`. -/
theorem HaltsWithin.mono {tm : NDTM k Symbol State} {input : List Symbol} {t t' : ℕ}
    (h : tm.HaltsWithin input t) (hle : t ≤ t') : tm.HaltsWithin input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (tm := tm) (w.take t) (w.drop t) (tm.initCfg input)
  rw [List.take_append_drop, runWith_of_halt _ hhalt] at hrun
  rw [hrun]
  exact hhalt

/-- **No branch halts in zero steps**: on every input, a machine
does not halt within `0` steps along every branch, `¬ tm.HaltsWithin input 0`, because the empty
choice word leaves the run at the initial configuration, whose state `some tm.q₀` is live. In
particular an all-branch time budget of `0` (e.g. from a vanishing time bound) is never met. This
is the nondeterministic counterpart of `Turing.FinTM.not_computesInTime_zero`.

**Proof sketch.** Apply all-branch halting at budget `0` to the empty choice word: the run under
it is the initial configuration (`Turing.NDTM.runWith_nil`), which is `Cfg.init` at the start
state (`Turing.NDTM.initCfg_eq`) and so has state `some tm.q₀` (`Turing.Cfg.init_state`), not
`none`. -/
theorem not_haltsWithin_zero (tm : NDTM k Symbol State) (input : List Symbol) :
    ¬ tm.HaltsWithin input 0 := by
  intro h
  have h0 := haltsWithin_iff.mp h [] rfl
  rw [runWith_nil, initCfg_eq, Cfg.init_state] at h0
  exact Option.some_ne_none _ h0

/-- **First halt along a choice word**: if the run from `cfg` along the choice word `w` has
halted, there is a least prefix length `u ≤ |w|` at which it has halted: the run along
`w.take u` is halted, the run along every shorter prefix is live, and the run along `w` is the
run along `w.take u`, halting being absorbing under every choice [AB09, §2.1.2]. The
nondeterministic counterpart of `Turing.MultiTapeTM.exists_first_halt`.

**Proof sketch.** Take `u` least with a halted run along `w.take u` (`Nat.find`; `u = |w|`
qualifies, `List.take_length`). Minimality gives liveness below `u`. Splitting
`w = w.take u ++ w.drop u`, `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`
identify the run along `w` with the run along `w.take u`. -/
theorem exists_first_halt (tm : NDTM k Symbol State) (cfg : Cfg k Symbol State input)
    {w : List Bool} (h : (tm.runWith w cfg).state = none) :
    ∃ u ≤ w.length, (tm.runWith (w.take u) cfg).state = none ∧
      (∀ v < u, (tm.runWith (w.take v) cfg).state ≠ none) ∧
      tm.runWith w cfg = tm.runWith (w.take u) cfg := by
  classical
  have hex : ∃ u, (tm.runWith (w.take u) cfg).state = none :=
    ⟨w.length, by rw [List.take_length]; exact h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by rw [List.take_length]; exact h),
    Nat.find_spec hex, fun v hv => Nat.find_min hex hv, ?_⟩
  conv_lhs => rw [← List.take_append_drop (Nat.find hex) w]
  rw [runWith_append, runWith_of_halt _ (Nat.find_spec hex)]

end NDTM

/-- A nondeterministic machine bundled with a finite state type, mirroring
`Turing.FinTM`: the instances are data (`Fintype`/`DecidableEq`, not `Finite`) for the
same reason as there — a machine that is to be encoded as a string must enumerate its
transition tables. All headline nondeterministic-complexity definitions
(`Turing.FinNDTM.DecidesInTime`, `Complexity.NTIME`) are stated over this layer. -/
structure FinNDTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic machine -/
  tm : NDTM k Symbol State

attribute [instance] FinNDTM.fintypeState FinNDTM.decEqState

/-- A deterministic machine as a nondeterministic one whose two transition functions
coincide: both choices apply the deterministic transition. This is the embedding behind
`DTIME ⊆ NTIME` ([AB09, §2.1.2]: a TM is an NDTM that ignores its choices). -/
def MultiTapeTM.toNDTM (tm : MultiTapeTM k Symbol State) : NDTM k Symbol State :=
  ⟨tm.q₀, fun _ => tm.tr⟩

/-! The embedding's fields as equations (the ND inventory API, 2026-10-17), by `simps` without the
`simp` attribute: `tm.toNDTM.q₀ = tm.q₀` and `tm.toNDTM.tr b = tm.tr` for either choice. -/
attribute [simps (config := { isSimp := false }) q₀ tr] MultiTapeTM.toNDTM

/-- The embedded deterministic machine starts where the original does. -/
@[simp]
lemma MultiTapeTM.toNDTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNDTM.initCfg input = tm.initCfg input := rfl

/-- The embedded deterministic machine ignores its choices: running `toNDTM` under any
choice word `w` is running the original machine for `|w|` steps.

**Proof sketch.** Induction on `w` generalizing the configuration. For one step,
`Turing.NDTM.stepWith` on `toNDTM` and `Turing.MultiTapeTM.step` are the same match on
the state — halted branches are both the identity, and on a live state both apply the
action `tm.tr q …` since `toNDTM.tr b = tm.tr` for either `b`. The cons case is then
`Turing.NDTM.runWith_cons` against `Turing.MultiTapeTM.runFrom_succ_eq_step` (the step
count on the right is `|w| + 1`, `List.length_cons`). -/
theorem MultiTapeTM.toNDTM_runWith (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.runWith w cfg = tm.runFrom cfg w.length := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    rw [NDTM.runWith_cons, List.length_cons, runFrom_succ_eq_step]
    exact ih (tm.step cfg)

/-- A bundled deterministic machine as a bundled nondeterministic one — the `FinTM`
layer of `Turing.MultiTapeTM.toNDTM`, with the same tapes and state type. -/
def FinTM.toFinNDTM {Symbol : Type} (M : FinTM Symbol) : FinNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toNDTM⟩

/-! The bundled embedding's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: `M.toFinNDTM.k = M.k`, `M.toFinNDTM.State = M.State` and
`M.toFinNDTM.tm = M.tm.toNDTM`. -/
attribute [simps (config := { isSimp := false }) k State tm] FinTM.toFinNDTM

end Turing

/-! ## Branches along state embeddings, deterministic slices, relabelling, input locality

The run-level layer of the nondeterministic contract variant (design §15d and §16; the C1 design
note §3.1). A deterministic host whose correctness is a per-step lockstep lifts to NDTMs slice by
slice: `Turing.NDTM.runWith_mapState_of_agreeOn` transfers a run along a state embedding when the
host's two transition functions agree with the source's on the states visited, and its
deterministic-source form `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries every
deterministic phase contract to every branch. `Turing.NDTM.runWith_eq_fixChoice_runFrom` is the
slice lemma that stage 2's nondeterministic form needs (statement gated by the stage-2 pack,
`audits/stage2-statements-pack.md`; proof here). `Turing.NDTM.relabelState` mirrors
`Turing.MultiTapeTM.relabelState`. `Turing.NDTM.runWith_initCfg_take` is input locality: a
branch of at most `m` steps reads only the first `m` input symbols. -/

namespace Turing.NDTM

section Transfer

variable {k : ℕ} {Γ S H : Type*}

/-- **One step transfers along a state embedding.** Suppose that at every good state both
transition functions of `host` are the transition functions of `src` with successors renamed
along `emb`. Then from a configuration that is halted or at a good state, one step of `host`
under either choice bit is the renamed step of `src` under that bit. (Technical glue, no
textbook counterpart: the one-step identity behind `Turing.NDTM.runWith_mapState_of_agreeOn`.)

**Proof sketch.** A halted configuration is fixed by both steps. At a good state both steps read
the same symbols, the agreement selects the renamed action, and renaming commutes with applying
an action (`Turing.Cfg.mapState_apply`). -/
theorem stepWith_mapState_of_agreeOn {x : List Γ}
    (src : NDTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr b q inp work).mapState emb)
    (c : Cfg k Γ S x) (hc : ∀ q, c.state = some q → good q) (b : Bool) :
    host.stepWith b (c.mapState emb) = (src.stepWith b c).mapState emb := by
  cases hs : c.state with
  | none =>
    have h1 : (c.mapState emb).state = none := by simp [Cfg.mapState, hs]
    rw [stepWith_of_halt h1, stepWith_of_halt hs]
  | some q =>
    have h1 : (c.mapState emb).state = some (emb q) := by simp [Cfg.mapState, hs]
    unfold stepWith
    rw [h1, hs]
    simp only
    rw [hagree b q (hc q hs)]
    exact Cfg.mapState_apply emb _ c

/-- **The nondeterministic agreement transfer** (the run-level nondeterministic contract
variant of design §15d and §16). Suppose that both transition functions of `host` agree, along
the state embedding `emb`, with the corresponding transition functions of `src` at every good
state, and that the run of `src` under the choice word `w` is at a good state whenever it is
live before its end. Then `host` under `w` runs exactly as `src` under `w`, renamed. The
endpoint is unrestricted, and `w = []` is the trivial case. [AB09, §2.1.2: a branch is the run
along one choice word]

**Proof sketch.** Induct on `w`. The guard at time `0` licenses the one-step identity
(`Turing.NDTM.stepWith_mapState_of_agreeOn`), and the shifted guard feeds the induction
hypothesis. -/
theorem runWith_mapState_of_agreeOn {x : List Γ}
    (src : NDTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr b q inp work).mapState emb)
    (c : Cfg k Γ S x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, (src.runWith (w.take u) c).state = some q → good q) :
    host.runWith w (c.mapState emb) = (src.runWith w c).mapState emb := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih =>
    have h0 : ∀ q, c.state = some q → good q := fun q hq =>
      hguard 0 (by simp) q (by simpa using hq)
    rw [runWith_cons, runWith_cons,
      stepWith_mapState_of_agreeOn src host emb good hagree c h0 b]
    apply ih
    intro u hu q hq
    exact hguard (u + 1) (by simp; omega) q
      (by simpa [List.take_succ_cons, runWith_cons] using hq)

/-- **The transfer from a deterministic source.** Suppose that both transition functions of
`host` reproduce, renamed along `emb`, the transition function of the deterministic machine
`src` at every good state, and that the run of `src` from `c` is at a good state whenever it
is live before time `|w|`. Then every branch of `host` of length `|w|` from the renamed `c` is
the renamed run of `src` for `|w|` steps. So a deterministic phase contract of `src` (a MIG-0a
`Turing.Contract`, say) holds for `host` under every choice word of its length. It is the
nondeterministic mirror of `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`. [AB09, §2.1.2]

**Proof sketch.** Apply `Turing.NDTM.runWith_mapState_of_agreeOn` to `src.toNDTM`, whose
branches are `src`'s run (`Turing.MultiTapeTM.toNDTM_runWith`), on both sides. -/
theorem runWith_mapState_of_agreeOn_det {x : List Γ}
    (src : MultiTapeTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr q inp work).mapState emb)
    (c : Cfg k Γ S x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, (src.runFrom c u).state = some q → good q) :
    host.runWith w (c.mapState emb) = (src.runFrom c w.length).mapState emb := by
  have h := runWith_mapState_of_agreeOn src.toNDTM host emb good
    (fun b q hq inp work => hagree b q hq inp work) c w (by
      intro u hu q hq
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hq
      exact hguard u hu q hq)
  rw [h, MultiTapeTM.toNDTM_runWith]

end Transfer

section Slice

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- **A branch that meets no real choice is a deterministic run.** If, at each of the first
`|w|` configurations of the run of the slice `tm.fixChoice b` from `cfg`, the machine is halted
or in a state at which its two transition functions agree, then the run of `tm` under the choice
word `w` is that deterministic run: `tm.runWith w cfg = (tm.fixChoice b).runFrom cfg |w|`.
[AB09, §2.1.2]

**Statement gated by the stage-2 pack** (`audits/stage2-statements-pack.md`, `NDSlice` Part A,
verbatim); **proof here**, by C1's argument (design §15d: one copy lands, in this file).

**Proof sketch.** This is `Turing.NDTM.runWith_mapState_of_agreeOn_det` with the slice as the
deterministic source, `tm` as the host, the identity embedding, and "the two transition
functions coincide" as the good states: at such a state either transition function of `tm` is
the slice's. Renaming along the identity is the identity. -/
theorem runWith_eq_fixChoice_runFrom (tm : NDTM k Symbol State) (b : Bool) (w : List Bool)
    (cfg : Cfg k Symbol State input)
    (hagree : ∀ j < w.length, ∀ q : State, ((tm.fixChoice b).runFrom cfg j).state = some q →
      tm.tr false q = tm.tr true q) :
    tm.runWith w cfg = (tm.fixChoice b).runFrom cfg w.length := by
  have e₁ : ∀ a : Action k Symbol State, a.mapState (Function.Embedding.refl State) = a := by
    intro a
    cases a with
    | mk i wt o st => cases st <;> rfl
  have e₂ : ∀ d : Cfg k Symbol State input,
      d.mapState (Function.Embedding.refl State) = d := by
    intro d
    cases d with
    | mk st ip wt wp o => cases st <;> rfl
  have h := runWith_mapState_of_agreeOn_det (tm.fixChoice b) tm (Function.Embedding.refl State)
    (fun q => tm.tr false q = tm.tr true q)
    (fun b' q hq inp work => by
      rw [e₁]
      cases b' <;> cases b <;> simp [fixChoice, hq]) cfg w hagree
  simpa only [e₂] using h

end Slice

section Relabel

variable {k : ℕ} {Γ S S' : Type*}

/-- **State relabelling of an NDTM** along an equivalence `e`: the initial state is mapped
forward, and both transition functions read the table through `e.symm` and rename successors
by `e`. It mirrors `Turing.MultiTapeTM.relabelState` and packages the linear normal form into
the `Fin`-state `Turing.CodeNDTM`. (Technical glue; [AB09, §1.4]'s finite state sets.) -/
def relabelState (tm : NDTM k Γ S) (e : S ≃ S') : NDTM k Γ S' where
  q₀ := e tm.q₀
  tr := fun b q inp w => (tm.tr b (e.symm q) inp w).mapState e

/-! The relabelling's fields as equations (the ND inventory API, 2026-10-17), by `simps` without the
`simp` attribute: `(tm.relabelState e).q₀ = e tm.q₀` and
`(tm.relabelState e).tr b q inp w = (tm.tr b (e.symm q) inp w).mapState e`. -/
attribute [simps (config := { isSimp := false }) q₀ tr] relabelState

/-- **Relabelled branches are the renamed branches**, under every choice word and from every
configuration: `(tm.relabelState e).runWith w (c.mapState e) = (tm.runWith w c).mapState e`.

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn` with every state good: the relabelled
table at `e q` is the original table at `q`, renamed. -/
theorem relabelState_runWith {x : List Γ} (tm : NDTM k Γ S) (e : S ≃ S')
    (c : Cfg k Γ S x) (w : List Bool) :
    (tm.relabelState e).runWith w (c.mapState e) = (tm.runWith w c).mapState e := by
  exact runWith_mapState_of_agreeOn tm (tm.relabelState e) e.toEmbedding (fun _ => True)
    (fun b q _ inp work => by simp [relabelState]) c w (fun _ _ _ _ => trivial)

end Relabel

section Locality

variable {k : ℕ} {Γ S : Type*}

/-- At an input position at most `m`, the input reads of `x` and of `x.take m` coincide.

**Proof sketch.** Three cases of the position `v`: at `0` both read the left blank; at
`|x| + 1` the input is shorter than `m`, so `x.take m` has the same length and both read the
right blank; otherwise both read the symbol at index `v - 1 < min m |x|`. -/
private lemma inputSymbol_take_eq {x : List Γ} {m : ℕ} (c : Cfg k Γ S x)
    (c' : Cfg k Γ S (x.take m)) (hp : c'.inputPos.val = c.inputPos.val)
    (hm : c.inputPos.val ≤ m) : c'.inputSymbol = c.inputSymbol := by
  have hlen : (x.take m).length = min m x.length := List.length_take
  have hlt := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have hz : c.inputPos = 0 := Fin.ext (by simp [h0])
    have hz' : c'.inputPos = 0 := Fin.ext (by simp [hp, h0])
    simp [Cfg.inputSymbol, hz, hz']
  · by_cases hr : c.inputPos.val = x.length + 1
    · have hz : c.inputPos ≠ 0 := fun h => h0 (by simp [h])
      have hz' : c'.inputPos ≠ 0 := fun h => h0 (by rw [← hp, h]; simp)
      have hr' : c'.inputPos.val = (x.take m).length + 1 := by omega
      simp only [Cfg.inputSymbol, dif_neg hz, dif_neg hz', dif_pos hr, dif_pos hr']
    · have hin := inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) (by omega)
      have hin' := inputSymbolInner (cfg := c') (c.inputPos.val - 1) (by omega)
        (by omega)
      rw [hin, hin', List.getElem_take]

/-- An input move lands at the proposed position, clamped to the right end. -/
private lemma moveInputPos_val {N : ℕ} (q : Fin (N + 2)) (s : SignType) :
    (moveInputPos q s).val = min (((q.val : ℤ) + (s.cast : ℤ)).toNat) (N + 1) := by
  unfold moveInputPos
  dsimp only
  split_ifs with h
  · exact (Nat.min_eq_left (by omega)).symm
  · exact (Nat.min_eq_right (by omega)).symm

/-- An input move from the same position, below the shorter input's right end or on inputs of
the same length, lands at the same position, at most one cell further right.

**Proof sketch.** Both moves clamp the same proposed position to their right ends, which agree
or are not reached; the proposed position is at most one cell right of the start. -/
private lemma moveInputPos_val_take {n n' : ℕ} (pos : Fin (n + 2)) (pos' : Fin (n' + 2))
    (hp : pos'.val = pos.val) (hn : n' ≤ n) (hle : pos.val ≤ n' ∨ n' = n) (s : SignType) :
    (moveInputPos pos' s).val = (moveInputPos pos s).val ∧
      (moveInputPos pos s).val ≤ pos.val + 1 := by
  have hs1 : (s.cast : ℤ) ≤ 1 := by cases s <;> simp
  have hs2 : -1 ≤ (s.cast : ℤ) := by cases s <;> simp
  rw [moveInputPos_val, moveInputPos_val, hp]
  have hpv : ((pos.val : ℤ) + (s.cast : ℤ)).toNat ≤ pos.val + 1 := by omega
  have hlt := pos.isLt
  generalize ((pos.val : ℤ) + (s.cast : ℤ)).toNat = p at hpv ⊢
  omega

/-- One step from agreeing configurations on `x` and on `x.take m`, with the input head at most
at `m`, gives agreeing configurations, and moves the input head at most one cell right.

**Proof sketch.** Halted configurations are fixed. At a live state both configurations read
the same input symbol (by the read lemma) and the same work symbols, so the same action applies;
its fields agree, the input move by the move lemma. -/
private lemma stepWith_take_agree (tm : NDTM k Γ S) {x : List Γ} {m : ℕ} (b : Bool)
    (c : Cfg k Γ S x) (c' : Cfg k Γ S (x.take m))
    (hs : c'.state = c.state) (hp : c'.inputPos.val = c.inputPos.val)
    (hw : c'.workTapes = c.workTapes) (hq : c'.workTapePos = c.workTapePos)
    (ho : c'.output = c.output) (hm : c.inputPos.val ≤ m) :
    (tm.stepWith b c').state = (tm.stepWith b c).state ∧
      (tm.stepWith b c').inputPos.val = (tm.stepWith b c).inputPos.val ∧
      (tm.stepWith b c').workTapes = (tm.stepWith b c).workTapes ∧
      (tm.stepWith b c').workTapePos = (tm.stepWith b c).workTapePos ∧
      (tm.stepWith b c').output = (tm.stepWith b c).output ∧
      (tm.stepWith b c).inputPos.val ≤ c.inputPos.val + 1 := by
  have hsym := inputSymbol_take_eq c c' hp hm
  have hws : c'.workTapeSymbols = c.workTapeSymbols := by
    funext i
    simp only [Cfg.workTapeSymbols, hw, hq]
  have hmv := moveInputPos_val_take c.inputPos c'.inputPos hp (by simp)
    (by rw [List.length_take]; omega)
  cases hst : c.state with
  | none =>
    have hst' : c'.state = none := by rw [hs, hst]
    rw [stepWith_of_halt hst, stepWith_of_halt hst']
    exact ⟨hs, hp, hw, hq, ho, by omega⟩
  | some q =>
    have hst' : c'.state = some q := by rw [hs, hst]
    have e₁ : tm.stepWith b c = (tm.tr b q c.inputSymbol c.workTapeSymbols).apply c := by
      unfold stepWith
      rw [hst]
    have e₂ : tm.stepWith b c' = (tm.tr b q c.inputSymbol c.workTapeSymbols).apply c' := by
      unfold stepWith
      rw [hst', hsym, hws]
    rw [e₁, e₂]
    refine ⟨rfl, (hmv _).1, ?_, ?_, ?_, (hmv _).2⟩
    · funext i
      simp only [Action.apply, hw, hq]
    · funext i
      simp only [Action.apply, hq]
    · simp only [Action.apply, ho]

/-- Agreement of branches on `x` and on `x.take m` propagates along a choice word while the
input head cannot pass position `m`.

**Proof sketch.** Induct on the word with the one-step lemma; the head budget
`position + remaining length ≤ m + 1` is preserved because each step moves the head at most one
cell. -/
private lemma runWith_take_agree (tm : NDTM k Γ S) {x : List Γ} {m : ℕ} :
    ∀ (w : List Bool) (c : Cfg k Γ S x) (c' : Cfg k Γ S (x.take m)),
      c'.state = c.state → c'.inputPos.val = c.inputPos.val → c'.workTapes = c.workTapes →
      c'.workTapePos = c.workTapePos → c'.output = c.output →
      c.inputPos.val + w.length ≤ m + 1 →
      (tm.runWith w c').state = (tm.runWith w c).state ∧
        (tm.runWith w c').inputPos.val = (tm.runWith w c).inputPos.val ∧
        (tm.runWith w c').workTapes = (tm.runWith w c).workTapes ∧
        (tm.runWith w c').workTapePos = (tm.runWith w c).workTapePos ∧
        (tm.runWith w c').output = (tm.runWith w c).output
  | [], _, _, hs, hp, hw, hq, ho, _ => ⟨hs, hp, hw, hq, ho⟩
  | b :: w, c, c', hs, hp, hw, hq, ho, hlen => by
    simp only [List.length_cons] at hlen
    obtain ⟨hs₁, hp₁, hw₁, hq₁, ho₁, hb⟩ :=
      stepWith_take_agree tm b c c' hs hp hw hq ho (by omega)
    simp only [runWith_cons]
    exact runWith_take_agree tm w _ _ hs₁ hp₁ hw₁ hq₁ ho₁ (by omega)

/-- **Input locality.** A branch of at most `m` steps from the initial configuration reads only
the first `m` input symbols: run on the truncated input `x.take m` under the same choice word,
it has the same state, work tapes, work-head positions and output, and its input head is at the
same position. The universal NDTM therefore needs only the window `x.take t` of its input to
simulate `t` steps, which keeps `|x|` out of its time bound (user decision 5 of 2026-10-13).
[AB09, §1.2: the input head moves at most one cell per step]

**Proof sketch.** The input head starts at position `1` and moves at most one cell per step, so
before each of the first `m` steps it is at a position at most `m`. There both inputs read the
same symbol: a blank at `0`, and otherwise the symbol at that index, or the right blank when `x`
is shorter than `m`. Equal reads select the same action, and the input move lands at the same
position, because the shorter input's right end is not reached. Induct on the word. -/
theorem runWith_initCfg_take (tm : NDTM k Γ S) (x : List Γ) (m : ℕ) (w : List Bool)
    (hw : w.length ≤ m) :
    let c := tm.runWith w (tm.initCfg x)
    let c' := tm.runWith w (tm.initCfg (x.take m))
    c'.state = c.state ∧ c'.inputPos.val = c.inputPos.val ∧ c'.workTapes = c.workTapes ∧
      c'.workTapePos = c.workTapePos ∧ c'.output = c.output := by
  have h := runWith_take_agree tm (x := x) (m := m) w (tm.initCfg x) (tm.initCfg (x.take m))
    rfl (by simp) rfl rfl rfl (by simp; omega)
  exact h

end Locality

end Turing.NDTM
```

## ===== TCSlib/Complexity/RAMSimulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.RAMSimulation.Classes

/-!
# Word-RAM programs on Turing machines

Stage 2 of the programming layer (`machine-library-design.md` §15d, backlog PROG-4): one Turing
machine that simulates a program of the extended word RAM (`WordRAM.XInstr`,
`TCSlib/Programs/WordRAM/Extended.lean`), in deterministic and nondeterministic forms, and the
complexity classes that follow from a program's time, cells and word size. The statements passed
their gate on 2026-10-14 (`audits/stage2-statements-findings.md`); their proofs are pending.

## Contents

- `RAMSimulation.WordSize`: the word-size hypothesis `WordRAM.WordSizeComputable` and its two
  bridges (`c · logSpace`, and `c · S` from a space-constructible `S`)
- `RAMSimulation.Sim.Encoding`, `RAMSimulation.Sim.Startup`, `RAMSimulation.Sim.Phases`: the
  simulation's internal interfaces (namespace `WordRAM.Sim`): how eight tapes encode a
  configuration, the start-up, and one phase per instruction
- `RAMSimulation.Simulation`: stage 2, `WordRAM.exists_simulation` and
  `WordRAM.exists_ndSimulation`, with their time and space bounds
- `RAMSimulation.Classes`: the nine corollaries (DTIME, P, SPACE, L, log-space transducers,
  Savitch's `SPACE(S·S)` shape, NSPACE and NL)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Exercise 1.9; §4.1.)
* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the word RAM
  and the language whose programs stage 2 runs (see `TCSlib/Programs` and the repository NOTICE).
-/
```
