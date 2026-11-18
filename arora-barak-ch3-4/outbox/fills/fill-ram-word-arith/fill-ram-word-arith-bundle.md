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

## ===== campaign/items/ram-tm/briefs/fill-ram-word-arith.md =====

# RAM fill (Codex), tier 2 job A: word arithmetic (`Build/WordArith`, 9 admissions)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-word-arith`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/TuringMachine/Build/WordArith.lean` states the arithmetic of a word RAM run on
a Turing machine. A word of `W` bits is held least significant first and delimited by blanks
(`Turing.WordAt`). Every row is a five-tape machine over `Bool`: operands on tapes `0` and `1`, the
destination on `2`, blank scratch on `3` and `4` (`Turing.ScratchBlank`). It writes only the
destination's word interval (`Turing.wordWrite`), returns every head, and is stated with
`Turing.ReachesWithin`. The definitions and their readers are proved; **this job proves the nine
admissions.** Jobs B, C and D cite these statements.

## Targets (in file order)

1. `bvBits_injective`
2. `exists_wordAddTM`: `u + v`, `O(W)` steps and radius
3. `exists_wordSubTM`: `u - v`
4. `exists_wordMulTM`: `u * v`, `O(W²)` steps, `O(W)` radius
5. `exists_wordHalfTM`: `u.sshiftRight 1`
6. `exists_wordSignExtendTM a`: `u.signExtend (W + a)`
7. `exists_wordIntTM c a`: `BitVec.ofInt (W + a) c` over a word of `W + a` cells
8. `exists_wordSignTM`: exits `yes`/`no` on `u.toInt < 0`
9. `exists_wordNonzeroTM`: exits `yes`/`no` on `u ≠ 0`

Each has a proof sketch. Gate 162's auditor checked them all achievable, `W = 0` included
(findings G162-06, G162-09 to G162-16).

## Route

- **The lockstep machine, once.** No catalog row reads two tapes with a carry. Write one private
  machine: a finite-state transducer that sweeps the heads of tapes `0`, `1` and `2` together,
  reading a cell of each, writing tape `2` and carrying a state, until the operand's delimiter;
  then sweeps back. Prove its run once, for an arbitrary transducer. Then add, sub and the
  in-place adder that the multiplier uses are instances.
- **The frame (G162-11).** State the lockstep machine's run lemma with an **arbitrary frame**: any
  cells outside the swept intervals, and the scratch tapes, may hold anything and are unchanged.
  The exported add row's `ScratchBlank` precondition does not cover the multiplier, whose scratch
  tapes are occupied mid-run.
- **The multiplier:**
  - copy `u` to scratch tape `3` (`Turing.copyTM`) and set the destination to `0`;
  - for each bit of `v`, least significant first: if it is `1`, add tape `3` into the destination
    (the in-place adder, with scratch tape `4` for the sum, copied back); then shift tape `3` up
    one place, dropping the top bit;
  - walk `v`'s head one cell per round, so the loop needs no counter and stops at `v`'s
    delimiter;
  - clear the scratch tapes and return the heads.

  Invariant after `r` rounds: the destination holds `u * (v mod 2^r)` and tape `3` holds
  `u <<< r`, both modulo `2^W`. Compose the rounds by a phase loop, or by `Contract.trans` and
  induction on `r`.
- **Sign and zero tests (G162-15, G162-16):** instances of `Turing.scanTM` (`Build/Catalog`,
  `Turing.scanTM_run_ofCfg`): forward with a flag (last bit read, or "a `1` was read"), symbols
  unchanged, then branch. They need no new machine.
- **Half, sign extension, constants:** one-word sweeps with finite state. `exists_wordIntTM`'s
  table of `c`'s low bits is finite: the bits from `c`'s bit length upward are all `c`'s sign.
- **BitVec facts:** the ripple-carry bits of `BitVec.add` (`BitVec.getLsbD_add` and the carry
  lemmas in core), `BitVec.toInt_neg_iff` or `msb`, `BitVec.getLsbD_sshiftRight`,
  `BitVec.getLsbD_signExtend`, `BitVec.getLsbD_ofInt`. Search core and Mathlib before proving one.

## Owned file

`TCSlib/Complexity/TuringMachine/Build/WordArith.lean`. Statements byte-identical. Private
helpers in sections before their first use. You may add imports of existing
`TCSlib/Complexity/TuringMachine/Build/*` modules and of Mathlib, each listed in `REPORT.md`
with its reason.

## Admitted dependencies allowed

None: this job's proofs reach no admission.

## Downstream check

Elaborate every module that imports `WordArith` at the base: `Build/KeyTable`, `Build/InputBit`,
`RAMSimulation/Sim/*`, `RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facades
`TuringMachine.lean` and `RAMSimulation.lean`.

## Frontier

The order above is the order of difficulty, mul last. Deliver checkpoints as you go.

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

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the routine instance

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
R3 clear as a contract, with its frame (MIG-0a, moved here from `Build/Contract.lean` as landed on
2026-10-13 with no statement changed) and its joint trajectory (MIG-0b). MIG-11's instances of the
framed rows join it.

## Main definitions

* `Turing.clearTM_contract`: R3 clear as a contract.
* `Turing.framedContract`: the contract of any framed one-exit row; `Turing.sweepContract` is
  its two-pass instance.
* `Turing.walkTM_contract`, `Turing.skipTM_contract`, `Turing.skipBackTM_contract`,
  `Turing.seekEndTM_contract`, `Turing.seekStartTM_contract`, `Turing.scanTM_contract`: the
  lockstep walk, the seek family and the scan as contracts (§13d G4), with the seek family's
  endpoint `Turing.seekPost`.
* `Turing.copyTM_contract`, `Turing.compareTM_contract`: R3 copy and the framed compare as
  contracts (MIG-11a, user 2026-10-16), with `Turing.copyTM_contract_frames`. The counter rows'
  contracts are in `Build/Contract/Counter`.

## Main results

* `Turing.clearTM_contract_frames`, `Turing.clearTM_contract_traj`.
* `Turing.framedContract_pre` … `_hi`, `Turing.seekPost_workTapePos`, `Turing.sweepPost_workTapes`,
  and `Turing.<row>_contract_pre`, `_time`, `_post`, `_lo`, `_hi` for every row contract — the
  specification API (user, 2026-10-16): fields as equations, without the `simp` attribute.
* `Turing.sweepMapWrite_apply`, `Turing.copyMapTM_contract_post_workTapes`,
  `Turing.transferMapTM_contract_post_workTapes` — the values the mapped sweeps write, and their
  endpoints' cells (the specification API's gate, finding 2).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the framing adapted as `Turing.Contract.Frames` (design adaptation; full entry in
  `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-! ### One constructor for the framed one-exit rows (§13d G4's hosts survey; user 2026-10-15)

Every framed catalog row with one live exit states its run in one shape: from the entry under
its precondition, the run reaches the endpoint at exactly the row's time, never the exit
earlier, every touched head within its interval and every other head fixed.
`Turing.framedContract` turns that statement into a contract once. `Turing.sweepContract` is
its two-pass instance, and the seek family and the lockstep walk get theirs below, so that the
G4 rows can be composed by `Turing.Contract.seq`, `inPhase` and `branch`. -/

/-- **The contract of a framed one-exit row.** Given a machine `M`, its entry and its exit
`done`, a precondition, an exact time, an endpoint at `done`, the predicate `touched` of the
tapes whose heads may move with their intervals `[lo, hi]`, and the row's framed theorem in the
catalog's shape (from the entry under the precondition: the run reaches the endpoint at exactly
the time, never `done` earlier, each touched head within its interval and every other head
fixed), this is the contract with those fields, the exits `{some done}`, and the untouched heads'
envelopes their one-point intervals. [AFM26], design adaptation (full entry in
`Build/Contract/Basic`).

**Proof sketch.** Each field is the matching clause of `hrun`; the exit is `hpost`; a fixed head
lies in its one-point interval. -/
def framedContract {S ι : Type} (M : MultiTapeTM k Γ S) (entry done : S) (x : List Γ)
    (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (touched : Fin k → Prop) [DecidablePred touched]
    (lo hi : ι → Cfg k Γ S x → Fin k → ℤ) (hpost : ∀ i d, (post i d).state = some done)
    (hrun : ∀ i d, d.state = some entry → pre i d →
      M.runFrom d (time i d) = post i d ∧
      (∀ t < time i d, (M.runFrom d t).state ≠ some done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ time i d →
        if touched j then (M.runFrom d t).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)
        else (M.runFrom d t).workTapePos j = d.workTapePos j)) :
    Contract M entry {some done} ι x where
  pre := pre
  time := time
  post := post
  lo i d j := if touched j then lo i d j else d.workTapePos j
  hi i d j := if touched j then hi i d j else d.workTapePos j
  run i d hd hp := (hrun i d hd hp).1
  exit_mem i d _ _ := by
    show (post i d).state ∈ ({some done} : Set (Option S))
    rw [hpost]
    exact Set.mem_singleton _
  cut i d hd hp u hu h := (hrun i d hd hp).2.1 u hu (Set.mem_singleton_iff.mp h)
  env i d hd hp u hu j := by
    have h := (hrun i d hd hp).2.2 j u hu
    by_cases hj : touched j
    · simpa only [hj, if_true] using h
    · simp only [hj, if_false] at h ⊢
      rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-! ### One constructor for the framed sweep rows (§13d G2, shared with R3 clear)

Every two-pass sweep row of the §12.6 shape (`Turing.clearTM_run_ofCfg`, the mapped copy and the
mapped transfer) gives a contract in the same way: the index is the word read from one tape, the
time `2|w| + 2`, the exit `done`, the touched heads within one cell of the word interval and the
others fixed. `Turing.sweepContract` builds it once from the row's framed theorem, and
`Turing.sweepPost` is the endpoint shape they share (an interval of one tape overwritten); the
instances supply only the machine, the read tape, the touched tapes and the written values.
(Landing: this block is inserted before `Turing.clearTM_contract`, which is then defined through
it.) -/

/-- **The endpoint of a sweep row**: `d` at the exit `done`, with the word interval
`[pos, pos + |w|)` of tape `a` (from its head) overwritten cell by cell, cell `q` by `v w d j q`,
and every other cell, all work heads, the input position and the output unchanged. -/
def sweepPost {S : Type} {x : List Γ} (done : S) (a : Fin k)
    (v : List Γ → Cfg k Γ S x → Fin k → ℤ → Option Γ) (w : List Γ) (d : Cfg k Γ S x) :
    Cfg k Γ S x :=
  { d with
    state := some done
    workTapes := fun j q =>
      if j = a ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then v w d j q
      else d.workTapes j q }

/-- **The contract of a framed two-pass sweep row** (§12.6 shape; design §13d, G2). Given a
machine `M`, its entry and exit `done`, the tape `src` it reads, the predicate `touched` of the
tapes whose heads move, an endpoint `post` at `done`, and the row's framed theorem `hrun` (from
the entry, with a word `w` delimited at the head of `src`: the run reaches `post w d` at exactly
`2|w| + 2`, no `done` earlier, touched heads within `[pos - 1, pos + |w|]`, the others fixed), this
is the contract with index `w`, that precondition, time `2|w| + 2`, endpoint `post`, exits
`{some done}`, and those envelopes. [AFM26], design adaptation (full entry in
`Build/Contract/Basic`): a specification used in place of the run.

**Proof sketch.** `Turing.framedContract` at the two-pass shape: time `2|w| + 2`, the touched
heads within one cell of the word interval. -/
def sweepContract {S : Type} (M : MultiTapeTM k Γ S) (entry done : S) (src : Fin k)
    (touched : Fin k → Prop) [DecidablePred touched] (x : List Γ)
    (post : List Γ → Cfg k Γ S x → Cfg k Γ S x) (hpost : ∀ w d, (post w d).state = some done)
    (hrun : ∀ (w : List Γ) (d : Cfg k Γ S x), d.state = some entry →
      (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) →
      M.runFrom d (2 * w.length + 2) = post w d ∧
      (∀ t < 2 * w.length + 2, (M.runFrom d t).state ≠ some done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if touched j then
          (M.runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else (M.runFrom d t).workTapePos j = d.workTapePos j)) :
    Contract M entry {some done} (List Γ) x :=
  framedContract M entry done x
    (fun w d => ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p)
    (fun w _ => 2 * w.length + 2) post touched
    (fun _ d j => d.workTapePos j - 1) (fun w d j => d.workTapePos j + w.length) hpost hrun

/-- **The joint trajectory of every framed sweep contract**: every untouched head stays at its
start, a relation on the whole head vector.

**Proof sketch.** An untouched head's envelope is the one-point interval at its start. -/
theorem sweepContract_traj {S : Type} (M : MultiTapeTM k Γ S) (entry done : S) (src : Fin k)
    (touched : Fin k → Prop) [DecidablePred touched] (x : List Γ)
    (post : List Γ → Cfg k Γ S x → Cfg k Γ S x) (hpost : ∀ w d, (post w d).state = some done)
    (hrun : ∀ (w : List Γ) (d : Cfg k Γ S x), d.state = some entry →
      (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) →
      M.runFrom d (2 * w.length + 2) = post w d ∧
      (∀ t < 2 * w.length + 2, (M.runFrom d t).state ≠ some done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if touched j then
          (M.runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else (M.runFrom d t).workTapePos j = d.workTapePos j)) :
    (sweepContract M entry done src touched x post hpost hrun).Traj
      fun _ d p => ∀ j, ¬ touched j → p j = d.workTapePos j := by
  intro w d hd hp u hu j hj
  have h := (sweepContract M entry done src touched x post hpost hrun).env w d hd hp u hu j
  have hlo : (sweepContract M entry done src touched x post hpost hrun).lo w d j =
      d.workTapePos j := if_neg hj
  have hhi : (sweepContract M entry done src touched x post hpost hrun).hi w d j =
      d.workTapePos j := if_neg hj
  rw [hlo, hhi, Finset.mem_Icc] at h
  exact le_antisymm h.2 h.1

/-- **A cell outside an overwritten interval keeps its value**: the frame of every sweep row,
whose endpoint overwrites `[lo, lo + n)` on tape `a` (with any values) and keeps every other
cell. If `q` lies outside that footprint, the endpoint's cell is the start's. -/
theorem sweep_ite_keep {α : Type} {j a : Fin k} {lo : ℤ} {n : ℕ} {q : ℤ} (v f : α)
    (hq : q ∉ (if j = a then Set.Ico lo (lo + n) else ∅)) :
    (if j = a ∧ lo ≤ q ∧ q < lo + n then v else f) = f := by
  rw [if_neg]
  rintro ⟨rfl, h₁, h₂⟩
  rw [if_pos rfl] at hq
  exact hq ⟨h₁, h₂⟩

/-- **R3 clear as a contract** (the fit test, from `Turing.clearTM_run_ofCfg`): the index is the
stored word `w`. Started in the sweep phase with `w`, delimited, at the head of tape `i`, the
routine reaches `done` in exactly `2|w| + 2` steps, and not earlier, with the cells
`[pos, pos + |w|)` of tape `i` blank and every other field unchanged; through the endpoint the
head of tape `i` stays in `[pos - 1, pos + |w|]` and every other head is fixed.

**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.clearTM_run_ofCfg`. -/
def clearTM_contract (i : Fin k) (x : List Γ) :
    Contract (clearTM k i) SweepPhase.sweep {some SweepPhase.done} (List Γ) x :=
  sweepContract _ _ _ i (fun j => j = i) x (sweepPost .done i fun _ _ _ _ => none) (fun _ _ => rfl)
    (clearTM_run_ofCfg i)

/-- R3 clear frames the cleared word's cells on its tape, and nothing else: its footprint is
`[pos, pos + |w|)` on tape `i` and empty on every other tape.

**Proof sketch.** `Turing.sweep_ite_keep` at tape `i`. -/
theorem clearTM_contract_frames (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).Frames fun w d j =>
      if j = i then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ :=
  fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq

/-- **A joint trajectory of R3 clear** (an instance): every head other than the cleared tape's
stays at its start, a relation on the whole head vector. -/
theorem clearTM_contract_traj (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).Traj fun _ d p => ∀ j, j ≠ i → p j = d.workTapePos j :=
  sweepContract_traj _ _ _ _ _ _ _ _ _

end Turing

namespace Turing

variable {k : ℕ} {Γ : Type}

/-! ### §13d G2: the mapped sweeps as contracts

The two G2 rows of `Build/Catalog` stated as `Turing.Contract`s from the start (design §16b,
item 5), through the shared constructor `Turing.sweepContract` and endpoint `Turing.sweepPost`. -/

/-- The values a mapped sweep writes into its destination interval: at cell `q`, the merge of the
cell's original content with the extract of the source word's symbol at offset `q - pos`. -/
def sweepMapWrite {S : Type} {x : List Γ} {Δ : Type} (extract : Γ → Δ) (merge : Option Γ → Δ → Γ)
    (w : List Γ) (d : Cfg k Γ S x) (j : Fin k) (q : ℤ) : Option Γ :=
  (FinTM.bufferTape w (q - d.workTapePos j)).map fun γ => merge (d.workTapes j q) (extract γ)

/-- **The values a mapped sweep writes** (the specification API, user 2026-10-16; its gate,
finding 2): at cell `q` of tape `j`, whose head is at `pos`, the merge of the cell's original
content with the extract of the source word's symbol at offset `q - pos`, and blank where the
buffered word has no symbol. -/
theorem sweepMapWrite_apply {S : Type} {x : List Γ} {Δ : Type} (extract : Γ → Δ)
    (merge : Option Γ → Δ → Γ) (w : List Γ) (d : Cfg k Γ S x) (j : Fin k) (q : ℤ) :
    sweepMapWrite extract merge w d j q =
      (FinTM.bufferTape w (q - d.workTapePos j)).map
        fun γ => merge (d.workTapes j q) (extract γ) :=
  rfl

/-- **The mapped copy as a contract** (design §13d, G2): the index is the source word `w`.
Started in the sweep phase with `w`, delimited, at the head of tape `src`, the mapped copy
reaches `done` in exactly `2|w| + 2` steps, and not earlier, with the destination interval
`[pos, pos + |w|)` holding `merge c (extract γ)` cell by cell (`c` the original destination
cell, `γ` the source cell) and every other field unchanged; through the endpoint the heads of
`src` and `dst` stay within one cell of their intervals and every other head is fixed.

**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.copyMapTM_run_ofCfg`. -/
def copyMapTM_contract {Δ : Type} (src dst : Fin k) (hne : src ≠ dst) (extract : Γ → Δ)
    (merge : Option Γ → Δ → Γ) (x : List Γ) :
    Contract (copyMapTM k src dst extract merge) SweepPhase.sweep {some SweepPhase.done}
      (List Γ) x :=
  sweepContract _ _ _ src (fun j => j = src ∨ j = dst) x
    (sweepPost .done dst (sweepMapWrite extract merge)) (fun _ _ => rfl)
    (copyMapTM_run_ofCfg src dst hne extract merge)

/-- **The mapped transfer as a contract** (design §13d, G2): as `Turing.copyMapTM_contract`,
with the source interval holding the residues `rest γ` at the endpoint.

**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.transferMapTM_run_ofCfg`. -/
def transferMapTM_contract {Δ : Type} (src dst : Fin k) (hne : src ≠ dst) (extract : Γ → Δ)
    (merge : Option Γ → Δ → Γ) (rest : Γ → Option Γ) (x : List Γ) :
    Contract (transferMapTM k src dst extract merge rest) SweepPhase.sweep
      {some SweepPhase.done} (List Γ) x :=
  sweepContract _ _ _ src (fun j => j = src ∨ j = dst) x
    (fun w d => sweepPost .done src (fun w d j q => (FinTM.bufferTape w (q - d.workTapePos j)).bind
      rest) w (sweepPost .done dst (sweepMapWrite extract merge) w d)) (fun _ _ => rfl)
    (transferMapTM_run_ofCfg src dst hne extract merge rest)

/-- **R3 copy as a contract** (MIG-11a, user 2026-10-16): the index is the source word `w`.
Started in the sweep phase with `w` delimited at the head of tape `src`, the copy reaches `done`
at exactly `2|w| + 2`, and not earlier, with the destination interval `[pos, pos + |w|)` of tape
`dst` (from its head `pos`) holding `w` cell by cell and every other cell unchanged; the heads of
`src` and `dst` stay within one cell of their intervals and every other head is fixed.

**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.copyTM_run_ofCfg`. -/
def copyTM_contract (src dst : Fin k) (hne : src ≠ dst) (x : List Γ) :
    Contract (copyTM k src dst) SweepPhase.sweep {some SweepPhase.done} (List Γ) x :=
  sweepContract _ _ _ src (fun j => j = src ∨ j = dst) x
    (sweepPost .done dst fun w d j q => FinTM.bufferTape w (q - d.workTapePos j)) (fun _ _ => rfl)
    (copyTM_run_ofCfg src dst hne)

/-- R3 copy frames exactly the destination interval: its footprint is `[pos, pos + |w|)` on tape
`dst` and empty elsewhere (MIG-11a, user 2026-10-16).

**Proof sketch.** `Turing.sweep_ite_keep` at `dst`. -/
theorem copyTM_contract_frames (src dst : Fin k) (hne : src ≠ dst) (x : List Γ) :
    (copyTM_contract src dst hne x).Frames fun w d j =>
      if j = dst then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ :=
  fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq

/-- The mapped copy frames exactly the destination interval: its footprint is
`[pos, pos + |w|)` on tape `dst` and empty elsewhere.

**Proof sketch.** `Turing.sweep_ite_keep` at `dst`. -/
theorem copyMapTM_contract_frames {Δ : Type} (src dst : Fin k) (hne : src ≠ dst)
    (extract : Γ → Δ) (merge : Option Γ → Δ → Γ) (x : List Γ) :
    (copyMapTM_contract src dst hne extract merge x).Frames fun w d j =>
      if j = dst then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ :=
  fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq

/-- The mapped transfer frames exactly its two word intervals, on `src` and on `dst`: its
footprint is `[pos, pos + |w|)` on each and empty elsewhere.

**Proof sketch.** `Turing.sweep_ite_keep` at `src`, then at `dst`. -/
theorem transferMapTM_contract_frames {Δ : Type} (src dst : Fin k) (hne : src ≠ dst)
    (extract : Γ → Δ) (merge : Option Γ → Δ → Γ) (rest : Γ → Option Γ) (x : List Γ) :
    (transferMapTM_contract src dst hne extract merge rest x).Frames fun w d j =>
      if j = src ∨ j = dst then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length)
      else ∅ := by
  intro w d _ _ j q hq
  have hs : q ∉ (if j = src then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length)
      else ∅) := by
    by_cases h : j = src <;> simp_all
  have hd : q ∉ (if j = dst then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length)
      else ∅) := by
    by_cases h : j = dst <;> simp_all
  exact (sweep_ite_keep _ _ hs).trans (sweep_ite_keep _ _ hd)

/-- **A joint trajectory of the mapped copy**: every head other than the two touched ones stays
at its start.

**Proof sketch.** `Turing.sweepContract_traj`. -/
theorem copyMapTM_contract_traj {Δ : Type} (src dst : Fin k) (hne : src ≠ dst)
    (extract : Γ → Δ) (merge : Option Γ → Δ → Γ) (x : List Γ) :
    (copyMapTM_contract src dst hne extract merge x).Traj
      fun _ d p => ∀ j, j ≠ src → j ≠ dst → p j = d.workTapePos j :=
  fun w d hd hp u hu j h₁ h₂ =>
    sweepContract_traj _ _ _ _ _ _ _ _ _ w d hd hp u hu j (by tauto)

/-- **The lockstep walk as a contract** (design §13d, G4): index the ruler `w` read along `dir`
from `src`'s head; time `|w| + 1`; endpoint every moved head `|w| + 1` cells along `dir`; each
moved head between its start and its end. From `Turing.walkTM_run_ofCfg`.

**Proof sketch.** `Turing.framedContract`. The walk's framed theorem gives each moved head's
exact position `pos + dir · t`, which for `t ≤ |w| + 1` lies between `pos` and
`pos + dir · (|w| + 1)`, by cases on the sign of `dir`. -/
def walkTM_contract (src : Fin k) (moved : Fin k → Prop) [DecidablePred moved]
    (hsrc : moved src) (dir : SignType) (x : List Γ) :
    Contract (walkTM k src moved dir) SeekPhase.run {some SeekPhase.done} (List Γ) x :=
  framedContract (walkTM k src moved dir) .run .done x
    (fun w d => ∀ p : ℕ, p ≤ w.length →
      d.workTapes src (d.workTapePos src + (dir : ℤ) * p) = FinTM.bufferTape w p)
    (fun w _ => w.length + 1)
    (fun w d => { d with
      state := some .done
      workTapePos := fun j =>
        d.workTapePos j + if moved j then (dir : ℤ) * ((w.length + 1 : ℕ) : ℤ) else 0 })
    moved
    (fun w d j => d.workTapePos j + min 0 ((dir : ℤ) * ((w.length + 1 : ℕ) : ℤ)))
    (fun w d j => d.workTapePos j + max 0 ((dir : ℤ) * ((w.length + 1 : ℕ) : ℤ)))
    (fun _ _ => rfl)
    (fun w d hd hp => by
      obtain ⟨h1, h2, h3⟩ := walkTM_run_ofCfg src moved hsrc dir w d hd hp
      refine ⟨h1, h2, fun j t ht => ?_⟩
      dsimp only at ht ⊢
      rw [h3 j t ht]
      by_cases hj : moved j
      · simp only [hj, if_true, Finset.mem_Icc]
        rcases dir with _ | _ | _ <;> simp <;> omega
      · simp [hj])

/-- **The endpoint of a seek-family row**: `d` at the exit `done`, with the head of tape `i` at
`p` and everything else unchanged. -/
def seekPost {S : Type} {x : List Γ} (done : S) (i : Fin k) (p : ℤ) (d : Cfg k Γ S x) :
    Cfg k Γ S x :=
  { d with state := some done, workTapePos := Function.update d.workTapePos i p }

/-- **R8.3 skip as a contract**: index the word `w` from the head of tape `i`; time `|w| + 1`;
endpoint the head one past `w`'s right delimiter. `Turing.skipTM_run_ofCfg`. -/
def skipTM_contract (i : Fin k) (x : List Γ) :
    Contract (skipTM k i) SeekPhase.run {some SeekPhase.done} (List Γ) x :=
  framedContract (skipTM k i) .run .done x
    (fun w d => ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p)
    (fun w _ => w.length + 1)
    (fun w d => seekPost .done i (d.workTapePos i + w.length + 1) d)
    (· = i) (fun _ d j => d.workTapePos j) (fun w d j => d.workTapePos j + w.length + 1)
    (fun _ _ => rfl) (fun w d hd hp => skipTM_run_ofCfg i w d hd hp)

/-- **R8.3 skip back as a contract**: index the delimited word `u` ending one blank before the
head of tape `i`; time `|u| + 3`; endpoint the head at `u`'s first cell.
`Turing.skipBackTM_run_ofCfg`. -/
def skipBackTM_contract (i : Fin k) (x : List Γ) :
    Contract (skipBackTM k i) SeekPhase.run {some SeekPhase.done} (List Γ) x :=
  framedContract (skipBackTM k i) .run .done x
    (fun u d => ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes i (d.workTapePos i - u.length - 1 + p) = FinTM.bufferTape u p)
    (fun u _ => u.length + 3)
    (fun u d => seekPost .done i (d.workTapePos i - u.length - 1) d)
    (· = i) (fun u d j => d.workTapePos j - u.length - 2) (fun _ d j => d.workTapePos j)
    (fun _ _ => rfl) (fun u d hd hp => skipBackTM_run_ofCfg i u d hd hp)

/-- **R8.3 seek to the end as a contract**: index a nonempty list `ws` of nonempty fields laid
out from the head of tape `i` (`Turing.fieldsTape`); time `fieldOffset ws |ws| + 1`; endpoint the
head at the layout's end. `Turing.seekEndTM_run_ofCfg`. -/
def seekEndTM_contract (i : Fin k) (x : List Γ) :
    Contract (seekEndTM k i) SeekPhase.run {some SeekPhase.done} (List (List Γ)) x :=
  framedContract (seekEndTM k i) .run .done x
    (fun ws d => ws ≠ [] ∧ (∀ u ∈ ws, u ≠ []) ∧
      ∀ p : ℤ, 0 ≤ p → p ≤ (fieldOffset ws ws.length : ℤ) →
        d.workTapes i (d.workTapePos i + p) = fieldsTape ws p)
    (fun ws _ => fieldOffset ws ws.length + 1)
    (fun ws d => seekPost .done i (d.workTapePos i + fieldOffset ws ws.length) d)
    (· = i) (fun _ d j => d.workTapePos j)
    (fun ws d j => d.workTapePos j + fieldOffset ws ws.length)
    (fun _ _ => rfl) (fun ws d hd hp => seekEndTM_run_ofCfg i ws hp.1 hp.2.1 d hd hp.2.2)

/-- **R8.3 seek to the start as a contract**: index the fields `ws` ending at the head of tape
`i`, its current cell nonblank; time `fieldOffset ws |ws| + 4`; endpoint the head at the layout's
first cell. `Turing.seekStartTM_run_ofCfg`. -/
def seekStartTM_contract (i : Fin k) (x : List Γ) :
    Contract (seekStartTM k i) SeekPhase.run {some SeekPhase.done} (List (List Γ)) x :=
  framedContract (seekStartTM k i) .run .done x
    (fun ws d => (∀ u ∈ ws, u ≠ []) ∧ d.workTapes i (d.workTapePos i) ≠ none ∧
      ∀ p : ℤ, -2 ≤ p → p < (fieldOffset ws ws.length : ℤ) →
        d.workTapes i (d.workTapePos i - fieldOffset ws ws.length + p) = fieldsTape ws p)
    (fun ws _ => fieldOffset ws ws.length + 4)
    (fun ws d => seekPost .done i (d.workTapePos i - fieldOffset ws ws.length) d)
    (· = i) (fun ws d j => d.workTapePos j - fieldOffset ws ws.length - 2)
    (fun _ d j => d.workTapePos j)
    (fun _ _ => rfl) (fun ws d hd hp => seekStartTM_run_ofCfg i ws hp.1 d hd hp.2.1 hp.2.2)

/-- **R8.2 the scan as a contract**: index the word `w` delimited at the head of tape `i`; time
`2|w| + 2`; endpoint the word's interval rewritten to the scan's output, at the exit carrying the
final accumulator; exits every `done a`; the head within one cell of the interval, the others
fixed. `Turing.scanTM_run_ofCfg`. The exit set is not a singleton, so this is built directly.

**Proof sketch.** Each field is the matching clause of the scan's framed theorem; the exit lies in
the range by construction; a fixed head lies in its one-point interval. -/
def scanTM_contract {A : Type} (i : Fin k) (δf δb : A → Γ → A × Γ) (a₀ : A) (x : List Γ) :
    Contract (scanTM k i δf δb a₀) (ScanPhase.fwd a₀) (Set.range fun a => some (ScanPhase.done a))
      (List Γ) x where
  pre w d := ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p
  time w _ := 2 * w.length + 2
  post w d := { d with
    state := some (.done (scanResult δf δb a₀ w).1)
    workTapes := fun j q =>
      if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape (scanResult δf δb a₀ w).2 (q - d.workTapePos j)
      else d.workTapes j q }
  lo w d j := if j = i then d.workTapePos j - 1 else d.workTapePos j
  hi w d j := if j = i then d.workTapePos j + w.length else d.workTapePos j
  run w d hd hp := (scanTM_run_ofCfg i δf δb a₀ w d hd hp).1
  exit_mem w d _ _ := ⟨_, rfl⟩
  cut w d hd hp u hu h := by
    obtain ⟨a, ha⟩ := h
    exact (scanTM_run_ofCfg i δf δb a₀ w d hd hp).2.1 u hu a ha.symm
  env w d hd hp u hu j := by
    have h := (scanTM_run_ofCfg i δf δb a₀ w d hd hp).2.2 j u hu
    split_ifs at h ⊢ with hj
    · exact h
    · rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- **The framed compare as a contract** (MIG-11a, user 2026-10-16): the index is the pair of
words `(u, v)`, delimited at the heads of tapes `fst` and `snd`. From the working phase the
compare reaches the verdict `done (decide (u = v))` at exactly `2 · compareStop u v + 2`, with no
verdict earlier and nothing written; the two heads stay within `[pos - 1, pos + compareStop u v]`
and every other head is fixed. The exits are both verdicts, so the exit is not a singleton and
the contract is built directly.

**Proof sketch.** Each field is the matching clause of `Turing.compareTM_run_stop_ofCfg`; the
exit lies in the range at the verdict; a fixed head lies in its one-point interval. -/
def compareTM_contract [DecidableEq Γ] (fst snd : Fin k) (hne : fst ≠ snd) (x : List Γ) :
    Contract (compareTM k fst snd) FlagPhase.run (Set.range fun b => some (FlagPhase.done b))
      (List Γ × List Γ) x where
  pre p d := (∀ q : ℤ, -1 ≤ q → q ≤ (p.1.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + q) = FinTM.bufferTape p.1 q) ∧
    ∀ q : ℤ, -1 ≤ q → q ≤ (p.2.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + q) = FinTM.bufferTape p.2 q
  time p _ := 2 * compareStop p.1 p.2 + 2
  post p d := { d with state := some (FlagPhase.done (decide (p.1 = p.2))) }
  lo p d j := if j = fst ∨ j = snd then d.workTapePos j - 1 else d.workTapePos j
  hi p d j := if j = fst ∨ j = snd then d.workTapePos j + (compareStop p.1 p.2 : ℤ)
    else d.workTapePos j
  run p d hd hp := (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).1
  exit_mem _ _ _ _ := ⟨_, rfl⟩
  cut p d hd hp u hu h := by
    obtain ⟨b, hb⟩ := h
    exact (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).2.1 u hu b hb.symm
  env p d hd hp u hu j := by
    have h := (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).2.2 j u hu
    split_ifs at h ⊢ with hj
    · exact h
    · rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-! ### The specification API (user, 2026-10-16)

The data fields of every contract in this file, and the fields of the two endpoint shapes,
as equations: generated by `simps` without the `simp` attribute, so that consumers read a
contract's precondition, time, endpoint and envelope without unfolding its definition. The row
contracts are built through `Turing.framedContract`, so their lemmas use `simps!`. -/

attribute [simps (config := { isSimp := false }) pre time post lo hi] framedContract
attribute [simps (config := { isSimp := false })] seekPost sweepPost
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  sweepContract clearTM_contract
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  copyMapTM_contract transferMapTM_contract
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  walkTM_contract skipTM_contract skipBackTM_contract
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  seekEndTM_contract seekStartTM_contract scanTM_contract
attribute [simps! (config := { isSimp := false }) pre time post lo hi] copyTM_contract
attribute [simps (config := { isSimp := false }) pre time post lo hi] compareTM_contract

/-- **The mapped copy's cells at its endpoint** (the specification API's gate, finding 2): on
tape `dst`, inside the word interval `[pos, pos + |w|)` from its head `pos`, cell `q` holds
`merge c (extract γ)` for its original content `c` and the source symbol `γ` at offset
`q - pos`; every other cell of every tape is unchanged.

**Proof sketch.** The endpoint equation, `Turing.sweepPost_workTapes` and
`Turing.sweepMapWrite_apply`. -/
theorem copyMapTM_contract_post_workTapes {Δ : Type} (src dst : Fin k) (hne : src ≠ dst)
    (extract : Γ → Δ) (merge : Option Γ → Δ → Γ) (x w : List Γ)
    (d : Cfg k Γ SweepPhase x) (j : Fin k) (q : ℤ) :
    ((copyMapTM_contract src dst hne extract merge x).post w d).workTapes j q =
      if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
        (FinTM.bufferTape w (q - d.workTapePos j)).map
          fun γ => merge (d.workTapes j q) (extract γ)
      else d.workTapes j q := by
  rw [copyMapTM_contract_post, sweepPost_workTapes, sweepMapWrite_apply]

/-- **The mapped transfer's cells at its endpoint** (the specification API's gate, finding 2):
on tape `src`, inside the word interval from its head `pos`, cell `q` holds the residue
`rest γ` of the source symbol `γ` at offset `q - pos`; on tape `dst`, inside its word interval,
the merge as for the mapped copy; every other cell is unchanged.

**Proof sketch.** The endpoint equation and `Turing.sweepPost_workTapes` twice, with
`Turing.sweepPost_workTapePos` for the inner endpoint's heads and
`Turing.sweepMapWrite_apply`. -/
theorem transferMapTM_contract_post_workTapes {Δ : Type} (src dst : Fin k) (hne : src ≠ dst)
    (extract : Γ → Δ) (merge : Option Γ → Δ → Γ) (rest : Γ → Option Γ) (x w : List Γ)
    (d : Cfg k Γ SweepPhase x) (j : Fin k) (q : ℤ) :
    ((transferMapTM_contract src dst hne extract merge rest x).post w d).workTapes j q =
      if j = src ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
        (FinTM.bufferTape w (q - d.workTapePos j)).bind rest
      else if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
        (FinTM.bufferTape w (q - d.workTapePos j)).map
          fun γ => merge (d.workTapes j q) (extract γ)
      else d.workTapes j q := by
  simp only [transferMapTM_contract_post, sweepPost_workTapes, sweepPost_workTapePos,
    sweepMapWrite_apply]

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Catalog.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: catalog promotions and space annotations (R3)

This module collects tape routines with exact time **and** space costs,
plus space annotations for the functional catalog and control surface.
Named function witnesses and their intrinsic specifications live in their
construction modules, including `Build/Primitives.lean`; the corresponding
existential time-and-space rows are packaged here.

**Status: proved.** The five routine machines and their two phase
alphabets are real definitions (TM1-style labelled control, the catalog's
house idiom), and every contract is proved: the §12 fill epochs F1/F2
(gates closed 2026-10-09) and the §12.6 framed contracts (fill gate closed
2026-10-10). Part 3 below is also proved: its §12.8 machines are real
definitions, and its contracts share the public catalog trace and action-step lemmas.

## Part 1 — new promotions (seam routines)

Configuration-level routines at the `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`, entering at their
start anchor with heads at the origin and exiting at a **live** anchor
(first-return cut included in each contract), so they compose under
`Turing.seamCompTM`. These are D6-style promotions of the audited 4A
privates — the A3 chain proved `3|w| + 3` copy and `2|w| + 2` clear,
matching the external prior art's catalog to within one step
(independent convergence, 2026-10-06 survey; [Bon26], the
transfer/clear/copy routine catalog):

* `Turing.transferTM` — move a word from tape `src` to tape `dst`
  (source erased), within `3|w| + 3`.
* `Turing.copyTM` — copy a word from tape `src` to tape `dst` (source
  kept), within `3|w| + 3`.
* `Turing.clearTM` — blank the word on one tape, within `2|w| + 2`.
* `Turing.compareTM` — word equality of two tapes, verdict in the exit
  anchor, tapes restored, within `2·min(|u|,|v|) + 2`.
* `Turing.incrementTM` — in-place little-endian fixed-width increment
  (`Turing.incFixed`), success/overflow in the exit anchor, within
  `2|w| + 2`; on overflow the word wraps to all-`false`.

Each routine carries per-tape space statements
(`Turing.MultiTapeTM.spaceUsedByTape`): the touched tapes visit at most
the word interval plus the two boundary blanks, and every other tape
stays at its origin singleton.

## Part 2 — space retro-annotation

Per frozen decision 12.3, the existing catalog rows (P1–P15 as realized)
and the control combinators W1–W3 and L receive `spaceUsed` theorems: each
annotation restates the audited row's existential contract joined with a
space clause. Each is a short corollary of its named witness's own specs in
the witness's home (`Turing.FinTM.idTM_computes`, `Turing.FinTM.lengthBitsTM_spaceUsed`,
`Turing.FinTM.polyUnaryTM_spaceUsed`, `Turing.FinTM.timedCondTM_spaceUsed`,
`Turing.FinTM.loopHostTM_spaceUsed_le_budget`, `Turing.FinTM.pairMapSndTM_spaceUsed`, …),
or of the space-from-time bound `Turing.FinTM.ComputesInTime.spaceUsed_le`; for witnesses with
no work tapes the space is zero. The emitter combinators (E1/E2/E3′/E4′ —
`exists_emitLoopTM`, `emit_run`/`exists_emitCallTM`, the stream rows
P16–P18, `splitSolveWith`) stay lazy until a space consumer appears.

## Part 3 — the §12.8 rows (proved)

The alphabet-generic rows of the rich-alphabet design
(`machine-library-design.md` §12.8a): the framed compare (R8.1), the seek
family over blank-separated fields (R8.3) with its field-layout vocabulary, the
lockstep walk `Turing.walkTM` (R8.3b, §13d G4's ruler; `Turing.skipTM` is its one-tape
instance), and the two-pass transducer scan `Turing.scanTM` (R8.2). The scan is the G2
core of the §13d revision: fold, in-place map, head-mark shifts and carry
odometers are its instances, as pure identities of `Turing.scanResult`, so
one framed contract and one trace serve them all.

## Main definitions

* `Turing.SweepPhase`, `Turing.FlagPhase` — the two phase alphabets.
* `Turing.catalogTrace` — the two-pass sweep trace, with its run lemma
  `Turing.catalog_trace_run`: the one trace every two-pass row cites
  (public since the §12.8 fill). With it, the write-step lemma
  `Turing.catalog_write_take` and the one-step lemmas of the two Part 3 actions,
  `Turing.step_of_tapeAction_move`, `Turing.step_of_tapeAction_write` and
  `Turing.step_of_inputMoveAction`; the field-layout facts `Turing.joinFields_cons_cons`,
  `Turing.fieldsTape_cons_shift`, `Turing.fieldOffset_succ`, `Turing.fieldOffset_cons_succ`,
  `Turing.length_joinFields_add_one` and `Turing.fieldOffset_add_length_le`.
* `Turing.wordPatch` — a tape with a word written over an interval, with its equation
  `Turing.wordPatch_apply`, its cells `Turing.wordPatch_of_mem` and `Turing.wordPatch_of_not_mem`
  (the specification API, user 2026-10-16), `Turing.wordPatch_append` (adjacent patches join),
  `Turing.wordPatch_self`, `Turing.wordPatch_twice` and `Turing.wordPatch_frame` (same-width patches),
  and `Turing.wordPatch_replicate` (a constant word).
* `Turing.transferTM`, `Turing.copyTM`, `Turing.clearTM`,
  `Turing.compareTM`, `Turing.incrementTM`.
* Part 3: `Turing.tapeAction`, `Turing.inputMoveAction` (one-tape
  actions); `Turing.joinFields`, `Turing.fieldsTape`, `Turing.fieldOffset`
  (the field layout); `Turing.SeekPhase`, `Turing.skipTM`,
  `Turing.skipBackTM`, `Turing.seekEndTM`, `Turing.seekStartTM`;
  `Turing.mealyRun`, `Turing.scanResult`, `Turing.ScanPhase`,
  `Turing.scanTM`, and the instance steps `Turing.scanKeep`,
  `Turing.scanFold`, `Turing.scanMap`, `Turing.scanShift`,
  `Turing.scanCarry`.
* `Turing.compareStop` — the compare's stop, the length of the two words' common prefix
  (MIG-11a, user 2026-10-16), with `Turing.compareStop_eq`, `Turing.compareStop_cons_cons`,
  `Turing.compareStop_spec`, `Turing.compareStop_unique` and `Turing.compareStop_le`; the framed
  compare at that exact time, `Turing.compareTM_run_stop_ofCfg`, of which
  `Turing.compareTM_run_ofCfg` is now a corollary.

## Main results

The five routines' framed run contracts from arbitrary configurations
(`*_run_ofCfg`, design §12.6) and their per-tape space contracts
(`*_spaceUsedByTape`); at a canonical seam the copy and transfer endpoints are canonical
seams again (`Turing.Cfg.ofWords_copy_endpoint`, `Turing.Cfg.ofWords_transfer_endpoint`), so
a consumer reads a seam-to-seam run from the framed form; the catalog space rows
`Turing.FinTM.computesFunInTime_*_spaceUsed` (P1–P15 as realized,
including the threaded-map row with its payload space hypothesis); and
the control-layer rows `Turing.capture_visitedByTapeHead` (W1),
`Turing.FinTM.redirectTM_spaceUsedByTape` (W2, imported from `Build/Wrappers`),
`Turing.FinTM.computesFunInTime_cond_spaceUsed` (W3), and
`Turing.FinTM.exists_loopTM_spaceUsed` (L).

Part 3 (proved): `Turing.fieldsTape_field`;
`Turing.compareTM_run_ofCfg`; `Turing.skipTM_run_ofCfg`,
`Turing.skipBackTM_run_ofCfg`, `Turing.seekEndTM_run_ofCfg`,
`Turing.seekStartTM_run_ofCfg`; `Turing.scanTM_run_ofCfg`; and the instance
identities `Turing.scanResult_fold`, `Turing.scanResult_map`,
`Turing.scanResult_shiftRight`, `Turing.scanResult_shiftLeft`,
`Turing.scanResult_carry`, and the identity scan `Turing.scanResult_keep_keep` (the
brief-inventory API, round 3).

* `Turing.Cfg.ofWords_copy_endpoint`, `Turing.Cfg.ofWords_transfer_endpoint`:
  the framed copy and transfer endpoints started at a canonical seam `Cfg.ofWords q w`
  with an empty destination are canonical seams again.
* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — the head-interval bound the
  Z4 space annotation consumes — moved on to `Finite` at MIG-0b's layering split
  (2026-10-13; it was here from `Build/Zone.lean` for B4, 2026-10-12).
* `Turing.FinTM.rewind_scan_heads`, `Turing.FinTM.rewind_heads` — the rewind head
  bounds — moved on to `TuringMachine/Simulation` at MIG-1 stage S (2026-10-14).
* `Turing.joinFields_nil`, `Turing.joinFields_singleton`, `Turing.fieldsTape_of_nonneg`,
  `Turing.fieldsTape_of_neg`, `Turing.fieldsTape_of_length_le`, `Turing.fieldsTape_nil`,
  `Turing.fieldOffset_zero` — the field layout's base and boundary facts, the specification
  API (user, 2026-10-16).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: the routines are the
  folklore tape subroutines of the textbook's simulation arguments;
  Definition 4.1: the visited-cells space measure the annotations use.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the transfer/clear/copy/compare routine catalog
  and its exact-cost discipline.
-/

namespace Turing

/-- Phase alphabet of the sweep-shaped routines (`Turing.transferTM`,
`Turing.copyTM`, `Turing.clearTM`): a forward pass over the stored word,
a return pass to the origin, and the live exit anchor. -/
inductive SweepPhase where
  /-- the forward pass over the stored word -/
  | sweep
  /-- the return pass back to the origin -/
  | rewind
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- Phase alphabet of the verdict-bearing routines (`Turing.compareTM`,
`Turing.incrementTM`): a forward working pass, a return pass carrying the
verdict, and a pair of live exit anchors indexed by the verdict. -/
inductive FlagPhase where
  /-- the forward working pass -/
  | run
  /-- the return pass, carrying the verdict -/
  | rewind (flag : Bool)
  /-- the live exit anchors, one per verdict -/
  | done (flag : Bool)
deriving DecidableEq, Fintype

variable {k : ℕ} {x : List Bool}

/-! ### §13d G2 — mapped sweeps, the cross-tape rows beside the scan

The one-tape core of G2 is the scan `Turing.scanTM` above (decision Q7, 2026-10-11). The two
rows below move **one component** of each cell across tapes, which whole-symbol copying cannot
do: they read each source cell through `extract : Symbol → Δ` and write
`merge (destination cell) (extract source cell)` into the destination, where the destination
cell may be blank (`merge : Option Symbol → Δ → Symbol`). **The tables are written once**: the
plain rows `Turing.transferTM` and `Turing.copyTM` are *defined* as these rows at the identity
map (`extract := id`, `merge := fun _ s => s`, and for the transfer the blank residue), so they
are definitional instances (`Turing.copyMapTM_plain`, `Turing.transferMapTM_plain`, by `rfl`).
The mapped framed rows share the two-pass sweep trace `Turing.catalog_trace_run` that every
sweep row cites (one trace per routine family, as §12.6 established), through one trace lemma:
the copy is the transfer with the identity residue `some`, whose return pass writes back what it
reads (`Turing.copyMapTM_run_ofCfg`). (Landing: this
block is inserted before `Turing.transferTM`; in the gate unit it follows the plain rows.) -/

/-- **§13d G2, the mapped copy** (design §13d, G2; [Bon26], the copy row's shape). Copy the word
stored on tape `src` onto tape `dst` through a map. For distinct tapes (`src ≠ dst`, the
hypothesis of the framed theorem) the forward pass reads each source cell `γ` and the
destination cell `c` under the destination head (`c` may be blank), writes
`merge c (extract γ)` there, and moves both heads right; the source's right blank turns both
heads; the return pass, guided by the intact source, brings both back; the left blank steps them
right into the live `done` anchor. The source is then never written. `Turing.copyTM` is this row
at `extract := id` and `merge := fun _ s => s`. -/
def copyMapTM {Symbol : Type*} {Δ : Type*} (k : ℕ) (src dst : Fin k) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) : MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some (merge (w dst) (extract b))), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **§13d G2, the mapped transfer** (design §13d, G2; [Bon26], the transfer row's shape). As
`Turing.copyMapTM` (again for `src ≠ dst`), except that the return pass also rewrites each source
cell `γ` to its residue `rest γ` (`none` blanks it). With a residue that keeps a cell's other
components (the per-track case), the source word stays a delimited word. `Turing.transferTM` is
this row at `extract := id`, `merge := fun _ s => s` and `rest := fun _ => none`. -/
def transferMapTM {Symbol : Type*} {Δ : Type*} (k : ℕ) (src dst : Fin k) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) (rest : Symbol → Option Symbol) :
    MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some (merge (w dst) (extract b))), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = src then (some (rest b), SignType.neg)
            else if j = dst then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, transfer** (design §12; [Bon26]). Move the word stored on tape
`src` to tape `dst`: a forward pass copies cell by cell (both heads in
lockstep), the turn at the source's right blank starts the return pass,
which erases the source on the way back, and the overshoot to the left
blank steps right into the live `done` anchor with both heads at the
origin. Its table is the mapped transfer's
(`Turing.transferMapTM`, §13d G2) at the identity map with the blank residue. -/
def transferTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : MultiTapeTM k Symbol SweepPhase :=
  transferMapTM k src dst id (fun _ s => s) (fun _ => none)

/-- **R3, copy** (design §12; [Bon26]; the A3 chain's `3|w| + 3` row).
Copy the word stored on tape `src` onto tape `dst`, keeping the source:
the same two-pass sweep as `Turing.transferTM` without the erasure on the
return pass. Its table is the mapped copy's (`Turing.copyMapTM`, §13d G2) at the identity
map. -/
def copyTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : MultiTapeTM k Symbol SweepPhase :=
  copyMapTM k src dst id (fun _ s => s)

/-- **R3, clear** (design §12; [Bon26]; P12's engine, the A3 chain's
`2|w| + 2` row, and the frozen §3 scratch discipline's supporting
primitive). Blank the word on tape `i`: a forward pass to the right blank,
then a return pass erasing each cell, with the left-blank overshoot
stepping right into the live `done` anchor at the origin. -/
def clearTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
    | .rewind =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (some none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, compare** (design §12; [Bon26]; the 4A chain's `clCmp*` shape).
Test the words on tapes `fst` and `snd` for equality, read-only: a
lockstep forward scan compares cell by cell — the first mismatch (a
differing pair, or one word ending early) selects the `false` verdict, a
simultaneous double blank selects `true` — then a return pass guided by
`fst`'s intact content carries the verdict to the live `done` anchor with
both heads at the origin and both words untouched. -/
def compareTM {Symbol : Type*} [DecidableEq Symbol] (k : ℕ) (fst snd : Fin k) : MultiTapeTM k Symbol FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w fst, w snd with
      | some a, some b =>
        if a = b then
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
              else (none, 0), none, some .run⟩
        else
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
              else (none, 0), none, some (.rewind false)⟩
      | none, none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | _, _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind false)⟩
    | .rewind v =>
      match w fst with
      | some _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
            else (none, 0), none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- **R3, increment** (design §12; [Bon26]; the enumerator's
`enumCarryTM` discipline in place, cf. the string-function row
`Turing.FinTM.computesFunInTime_incFixed`). In-place little-endian
fixed-width binary increment on tape `i`: the carry pass flips `true`
cells to `false` moving right; the first `false` flips to `true` and
selects the success verdict; running off the width (all `true`) selects
the overflow verdict, leaving the wrapped all-`false` word — the
enumerator's counter convention. The return pass carries the verdict to
the live `done` anchor at the origin. -/
def incrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some true =>
        ⟨0, fun j => if j = i then (some (some false), SignType.pos)
            else (none, 0), none, some .run⟩
      | some false =>
        ⟨0, fun j => if j = i then (some (some true), SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind false)⟩
    | .rewind v =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- Configuration at a scan position, with explicit words and head positions. -/
private def catalogCfg {S : Type*} (q : S) (w : Fin k → List Bool)
    (heads : Fin k → ℤ) : Cfg k Bool S x :=
  { Cfg.ofWords q w with workTapePos := heads }

/-- **The two-pass sweep trace** (design §12.6; public since the §12.8 fill, so
that every sweep row cites one trace). The chronological trace of a forward pass of
`L` steps, a turn, a return of `L` steps, and an entry: the configuration at time `t`
is the forward family `F t` up to `L`, the return family `R` counted down from `L` to
`0` up to `2L + 1`, and the exit configuration `D` afterwards. -/
def catalogTrace {Symbol : Type*} {x : List Symbol} {S : Type*} (F R : ℕ → Cfg k Symbol S x)
    (D : Cfg k Symbol S x) (L t : ℕ) : Cfg k Symbol S x :=
  if t ≤ L then F t else if t ≤ 2 * L + 1 then R (2 * L + 1 - t) else D

/-- **Local transition equations determine the sweep trace** (design §12.6; public
since the §12.8 fill). If one step takes each forward configuration to the next for
`L` steps, turns the last into the return family's start, takes each return
configuration to the previous one, enters `D` from the return's end, and leaves `D`
fixed, then the run from `F 0` is `Turing.catalogTrace F R D L` at every time,
including all stationary steps after the exit. Every two-pass row (the R3 sweeps, the
framed compare, the scan, the writers and the native-input sweeps) is an instance.

**Proof sketch.** Induct on elapsed time; split at the forward endpoint, return
endpoint, and stationary tail. -/
theorem catalog_trace_run {Symbol : Type*} {x : List Symbol} {S : Type*} (M : MultiTapeTM k Symbol S)
    (F R : ℕ → Cfg k Symbol S x) (D : Cfg k Symbol S x) (L : ℕ)
    (hF : ∀ r < L, M.step (F r) = F (r + 1))
    (hturn : M.step (F L) = R L)
    (hR : ∀ r < L, M.step (R (r + 1)) = R r)
    (hentry : M.step (R 0) = D) (hD : M.step D = D) (t : ℕ) :
    M.runFrom (F 0) t = catalogTrace F R D L t := by
  induction t with
  | zero => simp [catalogTrace]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    by_cases h₁ : t < L
    · simpa [catalogTrace, show t ≤ L by omega, show t + 1 ≤ L by omega]
        using hF t h₁
    · by_cases h₂ : t = L
      · subst t
        simpa [catalogTrace, show ¬L + 1 ≤ L by omega,
          show L + 1 ≤ 2 * L + 1 by omega, show 2 * L + 1 - (L + 1) = L by omega]
          using hturn
      · by_cases h₃ : t < 2 * L + 1
        · have he : 2 * L + 1 - t = (2 * L - t) + 1 := by omega
          simpa [catalogTrace, show ¬t ≤ L by omega, show ¬t + 1 ≤ L by omega,
            show t ≤ 2 * L + 1 by omega, show t + 1 ≤ 2 * L + 1 by omega,
            he, show 2 * L + 1 - (t + 1) = 2 * L - t by omega]
            using hR (2 * L - t) (by omega)
        · by_cases h₄ : t = 2 * L + 1
          · subst t
            simpa [catalogTrace, show ¬2 * L + 1 ≤ L by omega,
              show ¬2 * L + 1 + 1 ≤ L by omega] using hentry
          · simpa [catalogTrace, show ¬t ≤ L by omega,
              show ¬t + 1 ≤ L by omega, show ¬t ≤ 2 * L + 1 by omega,
              show ¬t + 1 ≤ 2 * L + 1 by omega] using hD

/-- A head confined to the inclusive interval from minus one to `L` visits
at most `L+2` cells. -/
private lemma catalog_space_bound {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (L t : ℕ) (i : Fin k)
    (h : ∀ u, -1 ≤ (M.runFrom c u).workTapePos i ∧
      (M.runFrom c u).workTapePos i ≤ (L : ℤ)) :
    M.spaceUsedByTape c t i ≤ L + 2 := by
  have hb := M.spaceUsedByTape_le_card_Icc c t i (-1) L fun u _ => Finset.mem_Icc.mpr (h u)
  have he : ((L : ℤ) + 1 - -1).toNat = L + 2 := by omega
  exact he ▸ hb

/-- A head stationary at zero has exactly its origin singleton as visited set. -/
private lemma catalog_space_one {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k)
    (h : ∀ u, (M.runFrom c u).workTapePos i = 0) :
    M.spaceUsedByTape c t i = 1 := by
  simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead, h]
  rw [Finset.image_const Finset.nonempty_range_add_one]
  rfl

/-- **A tape with a word patched in**: the cells `cp, …, cp + |u| - 1` hold `u`, every other
cell is `ct`'s. -/
def wordPatch {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) : ℤ → Option Γ :=
  fun q => if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q

/-- **The patch's cells** (its published equation, for consumers in other files): a cell inside
`[cp, cp + |u|)` reads `u`'s letter at its offset, and every other cell reads `ct`. -/
theorem wordPatch_apply {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) (q : ℤ) :
    wordPatch ct cp u q =
      if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q :=
  rfl

/-- A cell inside the patched interval holds the word's letter at its offset:
`wordPatch ct cp u q = FinTM.bufferTape u (q - cp)` when `cp ≤ q < cp + u.length`
(the specification API, user 2026-10-16). -/
theorem wordPatch_of_mem {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) {q : ℤ}
    (h₁ : cp ≤ q) (h₂ : q < cp + (u.length : ℤ)) :
    wordPatch ct cp u q = FinTM.bufferTape u (q - cp) := by
  simp [wordPatch, h₁, h₂]

/-- A cell outside the patched interval is the original tape's: `wordPatch ct cp u q = ct q`
(the specification API, user 2026-10-16). -/
theorem wordPatch_of_not_mem {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) {q : ℤ}
    (h : ¬(cp ≤ q ∧ q < cp + (u.length : ℤ))) : wordPatch ct cp u q = ct q := by
  simp only [wordPatch, if_neg h]

/-- **Adjacent patches join**: patching `u` at `cp` and then `v` at `cp + |u|`, right after it,
is patching `u ++ v` at `cp`.

**Proof sketch.** Split on the cell. Inside `u`'s interval both sides read `u`'s letter, since
`u ++ v` begins with `u`; inside `v`'s interval both read `v`'s letter at the offset past `u`;
outside both intervals both read the original tape. -/
theorem wordPatch_append {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ) :
    wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v) := by
  funext q
  have hlen : ((u ++ v).length : ℤ) = u.length + v.length := by simp
  by_cases h₁ : cp ≤ q ∧ q < cp + (u.length : ℤ)
  · have hn : 0 ≤ q - cp := by omega
    rw [wordPatch_of_not_mem _ _ _ (by omega), wordPatch_of_mem _ _ _ h₁.1 h₁.2,
      wordPatch_of_mem _ _ _ h₁.1 (by omega), ← Int.toNat_of_nonneg hn, FinTM.bufferTape_nat,
      FinTM.bufferTape_nat, List.getElem?_append_left (by omega)]
  · by_cases h₂ : cp + (u.length : ℤ) ≤ q ∧ q < cp + u.length + (v.length : ℤ)
    · have hn : 0 ≤ q - (cp + u.length) := by omega
      have hm : 0 ≤ q - cp := by omega
      rw [wordPatch_of_mem _ _ _ h₂.1 h₂.2, wordPatch_of_mem _ _ _ (by omega) (by omega),
        ← Int.toNat_of_nonneg hn, ← Int.toNat_of_nonneg hm, FinTM.bufferTape_nat,
        FinTM.bufferTape_nat, List.getElem?_append_right (by omega)]
      congr 1
      omega
    · rw [wordPatch_of_not_mem _ _ _ h₂, wordPatch_of_not_mem _ _ _ h₁,
        wordPatch_of_not_mem _ _ _ (by omega)]

/-- **Patching in the word a tape already holds changes nothing**: if
`ct` holds `u` delimited at `cp`, then `wordPatch ct cp u = ct`.

**Proof sketch.** Inside the interval the hypothesis says `ct` already reads `u`; outside it the
patch is `ct`. -/
theorem wordPatch_self {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) → ct (cp + p) = FinTM.bufferTape u p) :
    wordPatch ct cp u = ct := by
  funext q
  simp only [wordPatch_apply]
  split_ifs with inside
  · have h := hu (q - cp) (by omega) (by omega)
    rw [add_sub_cancel] at h
    exact h.symm
  · rfl

/-- **Patching one interval twice keeps the last patch**, for two words
of the same width.

**Proof sketch.** Pointwise: inside the interval both sides read the second word; outside it
neither patch is visible. -/
theorem wordPatch_twice {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (huv : v.length = u.length) :
    wordPatch (wordPatch ct cp u) cp v = wordPatch ct cp v := by
  funext q
  simp only [wordPatch_apply]
  rw [huv]
  by_cases hq : cp ≤ q ∧ q < cp + (u.length : ℤ) <;> simp [hq]

/-- **A same-width patch keeps the word delimited**: if `ct` holds
`u` delimited at `cp`, then patching `v` of the same width over it holds `v` delimited at
`cp`.

**Proof sketch.** Inside the interval the patch reads `v`. The two delimiters, at `cp - 1` and
`cp + |v|`, lie outside it, where `ct` is blank by the hypothesis on `u`. -/
theorem wordPatch_frame {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (huv : v.length = u.length)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) → ct (cp + p) = FinTM.bufferTape u p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      wordPatch ct cp v (cp + p) = FinTM.bufferTape v p := by
  intro p lo hi
  simp only [wordPatch_apply]
  by_cases inside : cp ≤ cp + p ∧ cp + p < cp + (v.length : ℤ)
  · rw [if_pos inside, add_sub_cancel_left]
  · rw [if_neg inside]
    rcases (by omega : p = -1 ∨ p = (v.length : ℤ)) with rfl | rfl
    · rw [hu (-1) le_rfl (by omega), FinTM.bufferTape_left, FinTM.bufferTape_left]
    · rw [hu _ (by omega) (by omega)]
      simp [huv]

/-- **Patching a constant word**: patching `n` copies of `a` at `cp` writes `a` on
`[cp, cp + n)` and keeps every other cell.

**Proof sketch.** Inside the interval the constant word's buffer reads `a` at every offset;
outside it the patch is the original tape. -/
theorem wordPatch_replicate {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (n : ℕ) (a : Γ) :
    wordPatch ct cp (List.replicate n a) =
      fun q => if cp ≤ q ∧ q < cp + (n : ℤ) then some a else ct q := by
  funext q
  simp only [wordPatch_apply, List.length_replicate]
  split_ifs with h
  · rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
  · rfl

/-- **Extending a written prefix writes exactly its next cell** (design §12.6; public
since the §12.8 fill, so that every writing sweep cites it). Writing `w[r]` at `a + r` on
a tape that holds `w`'s first `r` cells from `a` (and arbitrary cells elsewhere) gives the
tape that holds its first `r + 1` cells. The cells outside the written interval keep their
original values.

**Proof sketch.** Split off the new endpoint; away from it, the two integer interval
tests agree. The untouched suffix keeps its original arbitrary values. -/
theorem catalog_write_take {Symbol : Type*} (f : ℤ → Option Symbol) (a : ℤ)
    (w : List Symbol) (r : ℕ) (hr : r < w.length) :
    Function.update
      (fun q => if a ≤ q ∧ q < a + (r : ℤ) then FinTM.bufferTape w (q - a) else f q)
      (a + (r : ℤ)) (some w[r]) =
      (fun q => if a ≤ q ∧ q < a + ((r + 1 : ℕ) : ℤ)
        then FinTM.bufferTape w (q - a) else f q) := by
  funext q
  by_cases hq : q = a + (r : ℤ)
  · subst q
    simp [List.getElem?_eq_getElem hr]
  · rw [Function.update_of_ne hq]
    split_ifs <;> simp_all <;> omega

/-- Clear's forward phase preserves the entire arbitrary frame and translates
only the selected head. -/
private def catalogClearF {Symbol : Type*} {x : List Symbol} (i : Fin k) (d : Cfg k Symbol SweepPhase x) (r : ℕ) :
    Cfg k Symbol SweepPhase x :=
  { d with state := some .sweep
           workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) else 0 }

/-- Clear's return index counts the remaining unerased cells. The erased
suffix is bounded above by the original word's right delimiter. -/
private def catalogClearR {Symbol : Type*} {x : List Symbol} (i : Fin k) (d : Cfg k Symbol SweepPhase x) (n r : ℕ) :
    Cfg k Symbol SweepPhase x :=
  { d with state := some .rewind
           workTapes := fun j q =>
             if j = i ∧ d.workTapePos j + (r : ℤ) ≤ q ∧ q < d.workTapePos j + (n : ℤ)
               then none else d.workTapes j q
           workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) - 1 else 0 }

/-- Clear's exact framed invariant. **Proof sketch.** The forward pass reads
the original interval. The right blank turns without writing. Each return
step erases just the last remaining cell, and the left blank restores the head.
All cells outside the interval and all other configuration fields are retained. -/
private lemma catalog_clear_trace {Symbol : Type*} {x : List Symbol} (i : Fin k) (w : List Symbol)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some .sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) (t : ℕ) :
    (clearTM k i).runFrom d t =
      catalogTrace (catalogClearF i d) (catalogClearR i d w.length)
        { d with state := some .done
                 workTapes := fun j q =>
                   if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
                     then none else d.workTapes j q } w.length t := by
  have h0 : catalogClearF i d 0 = d := by
    apply Cfg.ext <;> simp [catalogClearF, hstate]
  conv_lhs => rw [← h0]
  -- Keep the original frame fixed while inducting on elapsed time.
  apply catalog_trace_run
  · intro r hr
    have hs : (catalogClearF i d r).workTapeSymbols i = some w[r] := by
      simp [catalogClearF, Cfg.workTapeSymbols_eq, hw r (by omega) (by omega),
        List.getElem?_eq_getElem hr]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogClearF]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · have hs : (catalogClearF i d w.length).workTapeSymbols i = none := by
      simp [catalogClearF, Cfg.workTapeSymbols_eq, hw w.length (by omega) (by omega)]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogClearF, catalogClearR]
    · funext j q
      split_ifs <;> simp_all <;> omega
    · funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · intro r hr
    have hs : (catalogClearR i d w.length (r + 1)).workTapeSymbols i = some w[r] := by
      simp [catalogClearR, Cfg.workTapeSymbols_eq,
        hw r (by omega) (by omega), List.getElem?_eq_getElem hr]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogClearR]
    · funext j
      by_cases hj : j = i
      · subst j
        simp only [ite_true, true_and, Prod.fst]
        funext q
        simp only [Function.update_apply]
        split_ifs <;> simp_all <;> omega
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · have hs : (catalogClearR i d w.length 0).workTapeSymbols i = none := by
      simpa [catalogClearR, Cfg.workTapeSymbols_eq] using hw (-1) (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogClearR]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · rw [MultiTapeTM.step_of_some (by rfl)]
    apply Cfg.ext
    · simp [-Action.apply, Action.apply_state, clearTM]
    · simp [-Action.apply, Action.apply_inputPos, clearTM]
    · funext j
      simp [-Action.apply, Action.apply_workTapes, Cfg.workTapeSymbols_eq, clearTM]
    · funext j
      simp [-Action.apply, Action.apply_workTapePos, clearTM]
    · simp [-Action.apply, Action.apply_output, clearTM]

/-- The framed forward phase of the mapped copy and transfer: after `r` forward steps the
destination interval `[pos, pos + r)` holds the row's written values `v q`, every other cell is
the start's, and both selected heads have moved `r` cells. For the mapped rows `v q` is `merge`
of the cell's original content and the extracted source symbol (the trace lemmas below). -/
private def catalogSweepF {Symbol : Type*} {x : List Symbol} (src dst : Fin k)
    (v : ℤ → Option Symbol) (d : Cfg k Symbol SweepPhase x) (r : ℕ) :
    Cfg k Symbol SweepPhase x :=
  { d with state := some .sweep
           workTapes := fun j q =>
             if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (r : ℤ) then v q
             else d.workTapes j q
           workTapePos := fun j =>
             d.workTapePos j + if j = src ∨ j = dst then (r : ℤ) else 0 }

/-- The return phase over the complete written destination interval of length `L`, without
further writes; the heads are `r - 1` cells along. -/
private def catalogSweepR {Symbol : Type*} {x : List Symbol} (src dst : Fin k)
    (v : ℤ → Option Symbol) (d : Cfg k Symbol SweepPhase x) (L r : ℕ) :
    Cfg k Symbol SweepPhase x :=
  { catalogSweepF src dst v d L with
      state := some .rewind
      workTapePos := fun j =>
        d.workTapePos j + if j = src ∨ j = dst then (r : ℤ) - 1 else 0 }

/-- The transfer's return phase: as `catalogSweepR`, with the already-crossed source suffix
`[pos + r, pos + L)` rewritten to the residue values `u q`. -/
private def catalogSweepResidueR {Symbol : Type*} {x : List Symbol} (src dst : Fin k)
    (v u : ℤ → Option Symbol) (d : Cfg k Symbol SweepPhase x) (L r : ℕ) :
    Cfg k Symbol SweepPhase x :=
  { catalogSweepR src dst v d L r with
      workTapes := fun j q =>
        if j = src ∧ d.workTapePos j + (r : ℤ) ≤ q ∧ q < d.workTapePos j + (L : ℤ) then u q
        else (catalogSweepR src dst v d L r).workTapes j q }

/-- **The trajectory clauses of a framed two-pass row, from its trace.** If the forward family is
in the `sweep` phase with the touched heads `r` cells along, the return family is in the `rewind`
phase with them `r - 1` cells along, and the exit configuration is in `done` with the start's
heads, then the run is not at `done` before `2L + 2`, and up to then every touched head stays
within one cell of its interval `[pos, pos + L)` while every other head is fixed.

**Proof sketch.** Rewrite the run by the trace and split at the forward endpoint, the return
endpoint and the exit: the state is `sweep`, `rewind` or (only from `2L + 2` on) `done`, and the
head offset is `t`, `2L + 1 - t - 1` or `0`. -/
private lemma catalog_trace_clauses {Symbol : Type*} {x : List Symbol}
    (M : MultiTapeTM k Symbol SweepPhase) (d : Cfg k Symbol SweepPhase x)
    (touched : Fin k → Prop) [DecidablePred touched] (F R : ℕ → Cfg k Symbol SweepPhase x)
    (D : Cfg k Symbol SweepPhase x) (L : ℕ)
    (htrace : ∀ t, M.runFrom d t = catalogTrace F R D L t)
    (hF : ∀ r, (F r).state = some .sweep ∧
      ∀ j, (F r).workTapePos j = d.workTapePos j + if touched j then (r : ℤ) else 0)
    (hR : ∀ r, (R r).state = some .rewind ∧
      ∀ j, (R r).workTapePos j = d.workTapePos j + if touched j then (r : ℤ) - 1 else 0)
    (hD : D.state = some .done ∧ D.workTapePos = d.workTapePos) :
    (∀ t < 2 * L + 2, (M.runFrom d t).state ≠ some .done) ∧
    (∀ (j : Fin k) (t : ℕ), t ≤ 2 * L + 2 →
      if touched j then
        (M.runFrom d t).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (L : ℤ))
      else (M.runFrom d t).workTapePos j = d.workTapePos j) := by
  constructor
  · intro t ht
    rw [htrace]
    unfold catalogTrace
    split_ifs with h1 h2
    · rw [(hF t).1]; simp
    · rw [(hR _).1]; simp
    · omega
  · intro j t ht
    rw [htrace]
    unfold catalogTrace
    by_cases hj : touched j
    · rw [if_pos hj, Finset.mem_Icc]
      split_ifs with h1 h2
      · rw [(hF t).2 j, if_pos hj]; omega
      · rw [(hR _).2 j, if_pos hj]; omega
      · rw [hD.2]; omega
    · rw [if_neg hj]
      split_ifs with h1 h2
      · rw [(hF t).2 j, if_neg hj]; simp
      · rw [(hR _).2 j, if_neg hj]; simp
      · rw [hD.2]

/-- **The mapped copy is the mapped transfer with the identity residue.** With `rest := some`
the transfer's return pass writes back, at each source cell it leaves, the symbol it has just read
there, which changes nothing; every other transition of the two tables is the same. So the two
machines take the same step from every configuration.

**Proof sketch.** Read the step equations, then split on the phase and the scanned cell. Only the
`rewind` phase over a nonblank source cell differs, where the transfer's write is
`Function.update` of the tape at the head with the cell's own content. -/
private lemma copyMapTM_step_eq {Symbol : Type*} {Δ : Type*} {x : List Symbol} (src dst : Fin k)
    (extract : Symbol → Δ) (merge : Option Symbol → Δ → Symbol)
    (c : Cfg k Symbol SweepPhase x) :
    (copyMapTM k src dst extract merge).step c =
      (transferMapTM k src dst extract merge some).step c := by
  cases hq : c.state with
  | none => simp only [MultiTapeTM.step_of_halt hq]
  | some q =>
    simp only [MultiTapeTM.step_of_some hq]
    cases q with
    | sweep => rfl
    | done => rfl
    | rewind =>
      cases hb : c.workTapeSymbols src with
      | none => simp only [copyMapTM, transferMapTM, hb]
      | some b =>
        have hc : c.workTapes src (c.workTapePos src) = some b :=
          (Cfg.workTapeSymbols_eq c src).symm.trans hb
        simp only [copyMapTM, transferMapTM, hb]
        apply Cfg.ext <;> simp only [Action.apply.eq_1]
        · funext j
          by_cases hs : j = src
          · subst hs
            simp only [true_or, if_true]
            rw [← hc, Function.update_eq_self]
          · by_cases hd : j = dst
            · subst hd; simp [hs]
            · simp [hs, hd]
        · funext j
          by_cases hs : j = src
          · simp [hs]
          · by_cases hd : j = dst
            · subst hd; simp [hs]
            · simp [hs, hd]

/-- The runs of the mapped copy are those of the mapped transfer with the identity residue
(`copyMapTM_step_eq`, iterated). -/
private lemma copyMapTM_runFrom_eq {Symbol : Type*} {Δ : Type*} {x : List Symbol}
    (src dst : Fin k) (extract : Symbol → Δ) (merge : Option Symbol → Δ → Symbol)
    (d : Cfg k Symbol SweepPhase x) (t : ℕ) :
    (copyMapTM k src dst extract merge).runFrom d t =
      (transferMapTM k src dst extract merge some).runFrom d t := by
  unfold MultiTapeTM.runFrom
  rw [show (copyMapTM k src dst extract merge).step (input := x) =
      (transferMapTM k src dst extract merge some).step from
    funext (copyMapTM_step_eq src dst extract merge)]

/-- **The mapped transfer's exact framed phase invariant.** The run from a sweep-phase start whose
source tape carries `w` delimited at its head is, at every time, the two-pass trace whose forward
phase writes `merge c (extract w[s])` at destination offset `s` (`c` the cell's original content)
and whose return rewrites each source cell to its residue `rest w[s]` as the head leaves it, with
the exit at `2|w| + 2`. At the identity map with the blank residue it is the plain transfer's
trace; with the identity residue `some` it is the mapped copy's (`copyMapTM_runFrom_eq`).

**Proof sketch.** `Turing.catalog_trace_run` with `catalogSweepF` and `catalogSweepResidueR`, in
the plain transfer's shape: the forward phase is the mapped copy's (the two tables agree on the
`sweep` phase); on return each source write extends the rewritten suffix by one cell and leaves
the next read unchanged, since the cell read is still original (the forward pass never writes the
source, and the return pass writes a cell only as it leaves it); the two delimiter cells are never
written, so the final entry restores both original head positions. -/
private lemma catalog_transferMap_trace {Symbol : Type*} {Δ : Type*} {x : List Symbol}
    (src dst : Fin k) (hne : src ≠ dst) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) (rest : Symbol → Option Symbol) (w : List Symbol)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some .sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) (t : ℕ) :
    (transferMapTM k src dst extract merge rest).runFrom d t =
      catalogTrace
        (catalogSweepF src dst (fun q => (FinTM.bufferTape w (q - d.workTapePos dst)).map
          fun γ => merge (d.workTapes dst q) (extract γ)) d)
        (catalogSweepResidueR src dst (fun q => (FinTM.bufferTape w (q - d.workTapePos dst)).map
          fun γ => merge (d.workTapes dst q) (extract γ))
          (fun q => (FinTM.bufferTape w (q - d.workTapePos src)).bind rest) d w.length)
        { d with state := some .done
                 workTapes := (catalogSweepResidueR src dst
                   (fun q => (FinTM.bufferTape w (q - d.workTapePos dst)).map
                     fun γ => merge (d.workTapes dst q) (extract γ))
                   (fun q => (FinTM.bufferTape w (q - d.workTapePos src)).bind rest)
                   d w.length 0).workTapes }
        w.length t := by
  have h0 : catalogSweepF src dst
      (fun q => (FinTM.bufferTape w (q - d.workTapePos dst)).map
        fun γ => merge (d.workTapes dst q) (extract γ)) d 0 = d := by
    apply Cfg.ext <;> simp [catalogSweepF, hstate]
    funext j q
    split_ifs <;> simp_all <;> omega
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (catalogSweepF src dst
        (fun q => (FinTM.bufferTape w (q - d.workTapePos dst)).map
          fun γ => merge (d.workTapes dst q) (extract γ)) d r).workTapeSymbols src = some w[r] := by
      simp [catalogSweepF, Cfg.workTapeSymbols_eq, hne,
        hw r (by omega) (by omega), List.getElem?_eq_getElem hr]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [transferMapTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogSweepF]
    · funext j
      by_cases hj : j = dst
      · subst j
        simp only [if_true, true_and, or_true]
        funext q
        rw [Function.update_apply]
        by_cases hq : q = d.workTapePos dst + r
        · subst hq
          simp [Cfg.workTapeSymbols_eq, FinTM.bufferTape_eq, List.getElem?_eq_getElem hr]
        · rw [if_neg hq]
          split_ifs <;> simp_all <;> omega
      · by_cases hs' : j = src <;> simp [hj, hs', hne]
    · funext j
      by_cases hd : j = dst <;> by_cases hs : j = src <;>
        simp [hd, hs, hne, SignType.cast] <;> omega
  · have hs : ∀ v : ℤ → Option Symbol,
        (catalogSweepF src dst v d w.length).workTapeSymbols src = none := by
      intro v
      simp [catalogSweepF, Cfg.workTapeSymbols_eq, hne, hw w.length (by omega) (by omega)]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [transferMapTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogSweepF, catalogSweepR,
      catalogSweepResidueR]
    · funext j
      by_cases hj : j = src <;> by_cases hd : j = dst <;> simp [hj, hd, hne, Ne.symm hne]
      all_goals
        funext q
        split_ifs <;> simp_all <;> omega
    · funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · intro r hr
    have hs : ∀ v u : ℤ → Option Symbol,
        (catalogSweepResidueR src dst v u d w.length (r + 1)).workTapeSymbols src =
          some w[r] := by
      intro v u
      simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, Cfg.workTapeSymbols_eq, hne,
        hw r (by omega) (by omega), List.getElem?_eq_getElem hr]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [transferMapTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogSweepResidueR,
      catalogSweepR, catalogSweepF]
    · funext j
      by_cases hj : j = src
      · subst j
        simp only [ite_true, true_and]
        funext q
        simp only [Function.update_apply]
        split_ifs <;>
          simp_all [FinTM.bufferTape_eq] <;> omega
      · by_cases hd : j = dst <;> simp [hj, hd, hne, Ne.symm hne]
    · funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · have hs : ∀ v u : ℤ → Option Symbol,
        (catalogSweepResidueR src dst v u d w.length 0).workTapeSymbols src = none := by
      intro v u
      simpa [catalogSweepResidueR, catalogSweepR, catalogSweepF, Cfg.workTapeSymbols_eq, hne] using
        hw (-1) (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [transferMapTM, hs]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogSweepResidueR,
      catalogSweepR, catalogSweepF]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · rw [MultiTapeTM.step_of_some (by rfl)]
    apply Cfg.ext <;> simp [transferMapTM, -Action.apply, Action.apply.eq_1]

/-- The first unequal or terminating cells occur after a common nonblank
prefix, and equality at those terminating cells is precisely word equality.
**Proof sketch.** Remove equal leading symbols recursively; unequal symbols or either
empty list stop immediately. This also covers aliased physical tape indices. -/
private lemma catalog_compare_stop {Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol) :
    ∃ d ≤ min u.length v.length,
      (∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      (¬∃ b, u[d]? = some b ∧ v[d]? = some b) ∧
      (u[d]? = v[d]? ↔ u = v) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v =>
      by_cases hab : a = b
      · subst b
        obtain ⟨d, hd, hp, hs, he⟩ := ih v
        refine ⟨d + 1, by simpa using hd, ?_, ?_, ?_⟩
        · intro r hr
          cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using hp r (by omega)
        · simpa using hs
        · simpa using he
      · refine ⟨0, by simp, by simp, ?_, ?_⟩
        · simpa [eq_comm] using hab
        · simp [hab]

/-- Comparison's forward configuration preserves the arbitrary frame and advances
selected physical heads once each, including when the two indices coincide. -/
private def catalogCompareF {Symbol : Type*} {x : List Symbol} (fst snd : Fin k)
    (d : Cfg k Symbol FlagPhase x) (r : ℕ) : Cfg k Symbol FlagPhase x :=
  { d with
    state := some .run
    workTapePos := fun j => d.workTapePos j + if j = fst ∨ j = snd then (r : ℤ) else 0 }

/-- Comparison's return configuration carries the verdict and preserves the entire frame. -/
private def catalogCompareR {Symbol : Type*} {x : List Symbol} (fst snd : Fin k)
    (d : Cfg k Symbol FlagPhase x) (v : Bool) (r : ℕ) : Cfg k Symbol FlagPhase x :=
  { d with
    state := some (.rewind v)
    workTapePos := fun j => d.workTapePos j + if j = fst ∨ j = snd then (r : ℤ) - 1 else 0 }

/-- **The compare's stop** (MIG-11a, user 2026-10-16): the number of leading positions at which `u`
and `v` hold the same symbol, before the first position where they differ or either word ends,
`compareStop u v = |takeWhile (fun p => p.1 = p.2) (zip u v)|`. The framed compare
(`Turing.compareTM_run_stop_ofCfg`) reads exactly this many cells forward. -/
def compareStop {Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol) : ℕ :=
  ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length

/-- The compare's stop as an equation:
`compareStop u v = ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length` (MIG-11a, user
2026-10-16). -/
theorem compareStop_eq {Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol) :
    compareStop u v = ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length :=
  rfl

/-- The stop on two nonempty words: one more than the tails' stop when the heads agree, `0`
otherwise, `compareStop (a :: u) (b :: v) = if a = b then compareStop u v + 1 else 0` (MIG-11a, user
2026-10-16). -/
theorem compareStop_cons_cons {Symbol : Type*} [DecidableEq Symbol] (a b : Symbol)
    (u v : List Symbol) :
    compareStop (a :: u) (b :: v) = if a = b then compareStop u v + 1 else 0 := by
  unfold compareStop
  by_cases h : a = b <;> simp [List.zip_cons_cons, h]

/-- **The stop's characterization** (MIG-11a, user 2026-10-16): below `compareStop u v` both words
hold the same symbol, and at it they do not (they differ, or one has ended).

**Proof sketch.** Induction on `u`: an empty word stops at `0`; two heads that agree add one to the
tails' stop, and two that differ stop at `0`. -/
theorem compareStop_spec {Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol) :
    (∀ r < compareStop u v, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      ¬∃ b, u[compareStop u v]? = some b ∧ v[compareStop u v]? = some b := by
  induction u generalizing v with
  | nil => simp [compareStop]
  | cons a u ih =>
    cases v with
    | nil => simp [compareStop]
    | cons b v =>
      rw [compareStop_cons_cons]
      by_cases hab : a = b
      · subst hab
        obtain ⟨h1, h2⟩ := ih v
        simp only [if_true]
        refine ⟨fun r hr => ?_, ?_⟩
        · cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using h1 r (by omega)
        · simpa using h2
      · simp only [hab, if_false]
        refine ⟨fun r hr => absurd hr (Nat.not_lt_zero _), ?_⟩
        rintro ⟨c, hc1, hc2⟩
        simp at hc1 hc2
        exact hab (hc1.trans hc2.symm)

/-- **The stop is the unique such position** (MIG-11a, user 2026-10-16): a position below which both
words hold the same symbol and at which they do not is `compareStop u v`.

**Proof sketch.** By `Turing.compareStop_spec`, a smaller position contradicts its own second
clause, and a larger one the stop's. -/
theorem compareStop_unique {Symbol : Type*} [DecidableEq Symbol] {u v : List Symbol} {d : ℕ}
    (h1 : ∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b)
    (h2 : ¬∃ b, u[d]? = some b ∧ v[d]? = some b) : d = compareStop u v := by
  obtain ⟨c1, c2⟩ := compareStop_spec u v
  rcases Nat.lt_trichotomy d (compareStop u v) with h | h | h
  · exact absurd (c1 d h) h2
  · exact h
  · exact absurd (h1 _ h) c2

/-- The stop is at most either word's length: `compareStop u v ≤ min |u| |v|` (MIG-11a, user
2026-10-16). -/
theorem compareStop_le {Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol) :
    compareStop u v ≤ min u.length v.length := by
  unfold compareStop
  exact (List.takeWhile_sublist _).length_le.trans (by simp)

/-- Comparison's exact framed invariant at a first differing or blank position.
**Proof sketch.** The delimited common prefix supplies both passes' reads. The stopping
condition determines the turn and verdict, and both heads return to their entry positions. -/
private lemma catalog_compare_trace {Symbol : Type*} [DecidableEq Symbol] {x : List Symbol}
    (fst snd : Fin k) (u v : List Symbol) (d : Cfg k Symbol FlagPhase x)
    (hstate : d.state = some .run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + p) = FinTM.bufferTape u p)
    (hv : ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + p) = FinTM.bufferTape v p)
    (δ : ℕ) (hδ : δ ≤ min u.length v.length)
    (hp : ∀ r < δ, ∃ b, u[r]? = some b ∧ v[r]? = some b)
    (hs : ¬∃ b, u[δ]? = some b ∧ v[δ]? = some b)
    (he : (u[δ]? = v[δ]?) ↔ u = v) (t : ℕ) :
    (compareTM k fst snd).runFrom d t =
      catalogTrace (catalogCompareF fst snd d)
        (catalogCompareR fst snd d (decide (u = v)))
        { d with state := some (.done (decide (u = v))) } δ t := by
  have h0 : catalogCompareF fst snd d 0 = d := by
    apply Cfg.ext <;> simp [catalogCompareF, hstate]
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    obtain ⟨b, hf, hg⟩ := hp r hr
    have hsf : (catalogCompareF fst snd d r).workTapeSymbols fst = some b := by
      simpa [catalogCompareF, Cfg.workTapeSymbols_eq, hf] using hu r (by omega) (by omega)
    have hsg : (catalogCompareF fst snd d r).workTapeSymbols snd = some b := by
      simpa [catalogCompareF, Cfg.workTapeSymbols_eq, hg] using hv r (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [compareTM, hsf, hsg, ↓reduceIte]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogCompareF]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast] <;> omega
  · have hreadf : (catalogCompareF fst snd d δ).workTapeSymbols fst = u[δ]? := by
      simpa [catalogCompareF, Cfg.workTapeSymbols_eq] using hu δ (by omega) (by omega)
    have hreadg : (catalogCompareF fst snd d δ).workTapeSymbols snd = v[δ]? := by
      simpa [catalogCompareF, Cfg.workTapeSymbols_eq] using hv δ (by omega) (by omega)
    have ht : (compareTM k fst snd).tr .run
        (catalogCompareF fst snd d δ).inputSymbol
        (catalogCompareF fst snd d δ).workTapeSymbols =
        ⟨0, (fun j => if j = fst ∨ j = snd then (none, SignType.neg) else (none, 0)),
          none, some (.rewind (decide (u = v)))⟩ := by
      simp only [compareTM, hreadf, hreadg]
      cases hf : u[δ]? with
      | none =>
        cases hg : v[δ]? with
        | none =>
          have heq : u = v := he.mp (by rw [hf, hg])
          simp [heq]
        | some b =>
          have hneq : u ≠ v := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hneq]
      | some a =>
        cases hg : v[δ]? with
        | none =>
          have hneq : u ≠ v := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hneq]
        | some b =>
          have hab : a ≠ b := by
            intro h
            subst b
            exact hs ⟨a, hf, hg⟩
          have hneq : u ≠ v := by
            intro h
            have h' := he.mpr h
            exact hab (by simpa only [hf, hg, Option.some.injEq] using h')
          simp [hab, hneq]
    rw [MultiTapeTM.step_of_some (by rfl)]
    rw [ht]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogCompareF, catalogCompareR]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · intro r hr
    obtain ⟨b, hf, _⟩ := hp r hr
    have hread : (catalogCompareR fst snd d (decide (u = v)) (r + 1)).workTapeSymbols fst =
        some b := by
      simpa [catalogCompareR, Cfg.workTapeSymbols_eq, hf,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using hu r (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [compareTM, hread]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogCompareR]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hread : (catalogCompareR fst snd d (decide (u = v)) 0).workTapeSymbols fst =
        none := by
      simpa [catalogCompareR, Cfg.workTapeSymbols_eq] using hu (-1) (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [compareTM, hread]
    apply Cfg.ext <;> simp [-Action.apply, Action.apply.eq_1, catalogCompareR]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · rw [MultiTapeTM.step_of_some (by rfl)]
    apply Cfg.ext <;> simp [compareTM, -Action.apply, Action.apply.eq_1]

/-- A word consists of its leading true bits followed by either a first false
bit and its tail, or no remaining bits. -/
private lemma catalog_increment_split (w : List Bool) :
    ∃ p : ℕ, ∃ tail : Option (List Bool),
      w = List.replicate p true ++ tail.elim [] (false :: ·) := by
  induction w with
  | nil => exact ⟨0, none, rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact ⟨0, some w, rfl⟩
    | true =>
      obtain ⟨p, tail, hw⟩ := ih
      exact ⟨p + 1, tail, by simp [List.replicate_succ, hw]⟩

/-- Fixed-width increment flips the leading true prefix and the first false;
an absent first false gives overflow.
Now derived from `Turing.incFixed_replicate_true_append` (CH34-D4). -/
private lemma catalog_increment_value (p : ℕ) (tail : Option (List Bool)) :
    incFixed (List.replicate p true ++ tail.elim [] (false :: ·)) =
      tail.map (fun v => List.replicate p false ++ true :: v) := by
  rw [incFixed_replicate_true_append]
  cases tail <;> rfl

/-- Changing the cell immediately after a framed prefix changes just that cell.
**Proof sketch.** At the write coordinate use indexing at the prefix length.
Elsewhere the frame tests agree; inside the window, prefix and suffix lookups
agree away from the changed cell. -/
private lemma catalog_write_middle {Symbol : Type*} (f : ℤ → Option Symbol) (z : ℤ)
    (pre rest : List Symbol) (a b : Symbol) :
    Function.update (wordPatch f z (pre ++ a :: rest)) (z + (pre.length : ℤ)) (some b) =
      wordPatch f z (pre ++ b :: rest) := by
  funext q
  by_cases hq : q = z + (pre.length : ℤ)
  · subst q
    simp [wordPatch]
  · rw [Function.update_of_ne hq]
    unfold wordPatch
    simp only [List.length_append, List.length_cons]
    split_ifs with h
    · have h0 : 0 ≤ q - z := by omega
      simp only [FinTM.bufferTape_eq, if_pos h0, List.getElem?_append]
      by_cases hlt : (q - z).toNat < pre.length
      · simp [hlt]
      · have he : (q - z).toNat - pre.length = ((q - z).toNat - pre.length - 1) + 1 := by
          omega
        simp only [if_neg hlt]
        rw [he]
        rfl
    · rfl

/-- Increment's framed carry configuration: the first `r` bits have been
reset and the remaining word and arbitrary exterior frame are intact. -/
private def catalogIncF (i : Fin k) (d : Cfg k Bool FlagPhase x) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  { d with state := some .run
           workTapes := fun j => if j = i then
             wordPatch (d.workTapes j) (d.workTapePos j)
               (List.replicate r false ++ List.replicate (p - r) true ++ tail.elim [] (false :: ·))
             else d.workTapes j
           workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) else 0 }

/-- Increment's framed return holds the updated or wrapped word and carries
the verdict; its head is one cell before the return index. -/
private def catalogIncR (i : Fin k) (d : Cfg k Bool FlagPhase x) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  { d with state := some (.rewind tail.isSome)
           workTapes := fun j => if j = i then
             wordPatch (d.workTapes j) (d.workTapePos j)
               (List.replicate p false ++ tail.elim [] (true :: ·))
             else d.workTapes j
           workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) - 1 else 0 }

/-- Increment's exact framed phase invariant. **Proof sketch.** Each carry
step resets one true bit. The first false is changed on the left turn, so the
cell beyond it is never visited. Overflow turns at the right blank without a
write. Both branches return over the reset prefix to the unchanged left blank,
then enter the live exit after exactly `2p+2` steps, preserving the outer frame. -/
private lemma catalog_increment_trace (i : Fin k) (w : List Bool)
    (d : Cfg k Bool FlagPhase x) (hstate : d.state = some .run)
    (hw : ∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + q) = FinTM.bufferTape w q)
    (p : ℕ) (tail : Option (List Bool))
    (hsplit : w = List.replicate p true ++ tail.elim [] (false :: ·)) (t : ℕ) :
    (incrementTM k i).runFrom d t =
      catalogTrace (catalogIncF i d p tail) (catalogIncR i d p tail)
        { d with state := some (.done tail.isSome)
                 workTapes := (catalogIncR i d p tail 0).workTapes } p t := by
  have h0 : catalogIncF i d p tail 0 = d := by
    apply Cfg.ext <;> simp [catalogIncF, hstate, ← hsplit]
    funext j
    by_cases hj : j = i
    · subst j
      funext q
      simp only [ite_true, wordPatch]
      split_ifs with h
      · simpa using (hw (q - d.workTapePos i) (by omega) (by omega)).symm
      · rfl
    · simp [hj]
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hpr : p - r = (p - (r + 1)) + 1 := by omega
    have hs : (catalogIncF i d p tail r).workTapeSymbols i = some true := by
      simp [catalogIncF, wordPatch, Cfg.workTapeSymbols_eq, hpr,
        List.replicate_succ, List.append_assoc]
      omega
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [incrementTM, hs]
    apply Cfg.ext
    · rw [Action.apply_state]; simp [catalogIncF]
    · rw [Action.apply_inputPos, moveInputPos_zero]; simp [catalogIncF]
    · funext j
      rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      by_cases hj : j = i
      · subst j
        have hh := catalog_write_middle (d.workTapes i) (d.workTapePos i)
          (List.replicate r false)
          (List.replicate (p - (r + 1)) true ++ tail.elim [] (false :: ·)) true false
        simp only [ite_true, Option.getD_some, catalogIncF]
        rw [hpr, List.replicate_succ]
        simpa only [List.length_replicate, List.replicate_succ',
          List.append_assoc, List.singleton_append] using hh
      · simp [hj, catalogIncF]
    · funext j
      rw [Action.apply_workTapePos]
      by_cases hj : j = i <;> simp [hj, catalogIncF, SignType.pos_eq_one, SignType.neg_eq_neg_one,
          SignType.coe_one, SignType.coe_neg_one,
        SignType.coe_zero] <;> omega
    · rw [Action.apply_output]; simp [catalogIncF]
  · cases tail with
    | none =>
      have hs : (catalogIncF i d p none p).workTapeSymbols i = none := by
        have hh := hw p (by omega) (by simp [hsplit])
        simpa [catalogIncF, wordPatch, Cfg.workTapeSymbols_eq, hsplit] using hh
      rw [MultiTapeTM.step_of_some (by rfl)]
      simp only [incrementTM, hs]
      apply Cfg.ext
      · rw [Action.apply_state]; simp [catalogIncR]
      · rw [Action.apply_inputPos, moveInputPos_zero]; simp [catalogIncF, catalogIncR]
      · funext j q
        rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
        by_cases hj : j = i
        · subst hj; simp [catalogIncF, catalogIncR, Function.update_apply]
          rintro rfl; rfl
        · simp [hj, catalogIncF, catalogIncR, Function.update_apply]
          rintro rfl; rfl
      · funext j
        rw [Action.apply_workTapePos]
        by_cases hj : j = i <;> simp [hj, catalogIncF, catalogIncR, SignType.pos_eq_one,
            SignType.neg_eq_neg_one, SignType.coe_one, SignType.coe_neg_one,
        SignType.coe_zero] <;> omega
      · rw [Action.apply_output]; simp [catalogIncF, catalogIncR]
    | some v =>
      have hs : (catalogIncF i d p (some v) p).workTapeSymbols i = some false := by
        simp [catalogIncF, wordPatch, Cfg.workTapeSymbols_eq]
      rw [MultiTapeTM.step_of_some (by rfl)]
      simp only [incrementTM, hs]
      apply Cfg.ext
      · rw [Action.apply_state]; simp [catalogIncR]
      · rw [Action.apply_inputPos, moveInputPos_zero]; simp [catalogIncF, catalogIncR]
      · funext j
        rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
        by_cases hj : j = i
        · subst j
          simp only [ite_true, Option.getD_some, catalogIncF, catalogIncR]
          simpa using catalog_write_middle (d.workTapes i) (d.workTapePos i)
            (List.replicate p false) v false true
        · simp [hj, catalogIncF, catalogIncR, Function.update_apply]
      · funext j
        rw [Action.apply_workTapePos]
        by_cases hj : j = i <;> simp [hj, catalogIncF, catalogIncR, SignType.pos_eq_one,
            SignType.neg_eq_neg_one, SignType.coe_one, SignType.coe_neg_one,
        SignType.coe_zero] <;> omega
      · rw [Action.apply_output]; simp [catalogIncF, catalogIncR]
  · intro r hr
    have hs : (catalogIncR i d p tail (r + 1)).workTapeSymbols i = some false := by
      have hb : (r : ℤ) < p + (tail.elim [] (true :: ·)).length := by omega
      simp [catalogIncR, wordPatch, Cfg.workTapeSymbols_eq, List.getElem?_append, hr, hb]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [incrementTM, hs]
    apply Cfg.ext
    · rw [Action.apply_state]; simp [catalogIncR]
    · rw [Action.apply_inputPos, moveInputPos_zero]; simp [catalogIncR]
    · funext j q
      rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      by_cases hj : j = i
      · subst hj; simp [catalogIncR, Function.update_apply]
        rintro rfl; first | rfl | (congr 1; omega)
      · simp [hj, catalogIncR, Function.update_apply]
        rintro rfl; rfl
    · funext j
      rw [Action.apply_workTapePos]
      by_cases hj : j = i <;> simp [hj, catalogIncR, SignType.pos_eq_one, SignType.neg_eq_neg_one,
          SignType.coe_one, SignType.coe_neg_one,
        SignType.coe_zero] <;> omega
    · rw [Action.apply_output]; simp [catalogIncR]
  · have hs : (catalogIncR i d p tail 0).workTapeSymbols i = none := by
      simpa [catalogIncR, wordPatch, Cfg.workTapeSymbols_eq] using
        hw (-1) (by omega) (by omega)
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [incrementTM, hs]
    apply Cfg.ext
    · rw [Action.apply_state]
    · rw [Action.apply_inputPos, moveInputPos_zero]; simp [catalogIncR]
    · funext j q
      rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      by_cases hj : j = i
      · subst hj; simp [catalogIncR, Function.update_apply]
        rintro rfl; first | rfl | (congr 1; omega)
      · simp [hj, catalogIncR, Function.update_apply]
        rintro rfl; rfl
    · funext j
      rw [Action.apply_workTapePos]
      by_cases hj : j = i <;> simp [hj, catalogIncR, SignType.pos_eq_one, SignType.neg_eq_neg_one,
          SignType.coe_one, SignType.coe_neg_one,
        SignType.coe_zero] <;> omega
    · rw [Action.apply_output]; simp [catalogIncR]
  · rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [incrementTM]
    apply Cfg.ext
    · rw [Action.apply_state]
    · rw [Action.apply_inputPos, moveInputPos_zero]
    · funext j; rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]; simp
    · funext j; rw [Action.apply_workTapePos]; simp
    · rw [Action.apply_output]; simp

/-! ### Framed contracts (design §12.6)

The R3 rows above start from `Cfg.ofWords`: every head at the origin and every
tape a globally buffered word. The routines themselves are local, since each
step reads only the scanned cells of the touched tapes. The contracts below
state them for an **arbitrary** configuration whose touched tapes carry a
*delimited* word at the current head: the word's cells, plus a blank at
relative positions `-1` and `|w|`. Every other cell, every other tape, the
native input position and the output are arbitrary and are preserved. This is
the form a consumer needs when the routine runs at displaced heads inside a
larger tape (the zone carrier, `Build/Zone.lean`; escalation of ZF-A2,
`audits/zone-agent-reports/f1-A2-REPORT.md`).

Times are exact. For increment the time is carry-sensitive, so a counter's
total cost can be summed geometrically.
-/

/-- The plain copy is the mapped copy at the identity map: `Turing.copyTM` is
`Turing.copyMapTM` with `extract := id` and `merge := fun _ s => s`, definitionally (at landing,
by `Turing.copyTM`'s definition). -/
theorem copyMapTM_plain {Symbol : Type*} (k : ℕ) (src dst : Fin k) :
    copyMapTM k src dst (id : Symbol → Symbol) (fun _ s => s) = copyTM k src dst :=
  rfl

/-- The plain transfer is the mapped transfer at the identity map with the blank residue,
definitionally (at landing, by `Turing.transferTM`'s definition). -/
theorem transferMapTM_plain {Symbol : Type*} (k : ℕ) (src dst : Fin k) :
    transferMapTM k src dst (id : Symbol → Symbol) (fun _ s => s) (fun _ => none) =
      transferTM k src dst :=
  rfl

/-- **§13d G2, the mapped transfer, framed** (design §13d, G2, in the §12.6 shape). As
`Turing.copyMapTM_run_ofCfg`, except that in addition the source interval `[pos, pos + |w|)`
holds, at offset `r`, the residue `rest w[r]` at the exit. At the identity map with the blank
residue this is `Turing.transferTM_run_ofCfg`.

**Proof sketch.** The shared mapped trace `catalog_transferMap_trace`, by
`Turing.catalog_trace_run` over the value-parametric sweep families: the forward pass writes at
offset `r` the `merge` of the original destination cell and the extracted source cell, updating
the written prefix inline; on the way back each source cell is read while still original (the
forward pass never writes the source, and the return pass writes a cell only as it leaves it),
rewritten to its residue, and left; the left delimiter, never written, supplies the entry step.
The no-earlier-exit and head clauses are `catalog_trace_clauses`. -/
theorem transferMapTM_run_ofCfg {Symbol : Type*} {Δ : Type*} {k : ℕ} {x : List Symbol}
    (src dst : Fin k) (hne : src ≠ dst) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) (rest : Symbol → Option Symbol) (w : List Symbol)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (transferMapTM k src dst extract merge rest).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = src ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then (FinTM.bufferTape w (q - d.workTapePos j)).bind rest
            else if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then (FinTM.bufferTape w (q - d.workTapePos j)).map
                fun γ => merge (d.workTapes j q) (extract γ)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((transferMapTM k src dst extract merge rest).runFrom d t).state ≠
          some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((transferMapTM k src dst extract merge rest).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((transferMapTM k src dst extract merge rest).runFrom d t).workTapePos j =
          d.workTapePos j) := by
  have htr := catalog_transferMap_trace src dst hne extract merge rest w d hstate hw
  refine ⟨?_, catalog_trace_clauses _ d (fun j => j = src ∨ j = dst) _ _ _ w.length htr
    (fun _ => ⟨rfl, fun _ => rfl⟩) (fun _ => ⟨rfl, fun _ => rfl⟩) ⟨rfl, rfl⟩⟩
  rw [htr]
  simp only [catalogTrace, show ¬2 * w.length + 2 ≤ w.length by omega,
    show ¬2 * w.length + 2 ≤ 2 * w.length + 1 by omega, if_false]
  congr 1
  funext j q
  by_cases hs : j = src
  · subst hs; simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hne]
  · by_cases hd : j = dst
    · subst hd; simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hs]
    · simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hs, hd]

/-- **§13d G2, the mapped copy, framed** (design §13d, G2, in the §12.6 shape). From any
configuration in the sweep phase whose source tape carries the word `w` delimited by blanks at
relative positions `-1` and `|w|`, the mapped copy reaches `done` at exactly `2|w| + 2` and not
earlier. At that point the destination interval `[pos, pos + |w|)` holds, at offset `r`,
`merge c (extract w[r])`, where `c` is that destination cell's **original** content (possibly
blank); every other cell, the head positions, the native input position and the output are
unchanged. Up to the exit both touched heads stay within one cell of their word interval and
every other head is fixed. At the identity map this is `Turing.copyTM_run_ofCfg`.

**Proof sketch.** The mapped copy is the mapped transfer with the identity residue `some`: that
transfer's return pass writes back exactly what it reads (`copyMapTM_step_eq`), so the two runs
agree (`copyMapTM_runFrom_eq`), and this is `Turing.transferMapTM_run_ofCfg` at `rest := some`,
with `o.bind some = o` restoring the source interval. That row's shared trace writes, at offset
`r`, the `merge` of the original destination cell: the forward pass reads it before writing it
and never revisits it. The routine never branches on the destination, which is why its old
contents are arbitrary. -/
theorem copyMapTM_run_ofCfg {Symbol : Type*} {Δ : Type*} {k : ℕ} {x : List Symbol}
    (src dst : Fin k) (hne : src ≠ dst) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) (w : List Symbol) (d : Cfg k Symbol SweepPhase x)
    (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (copyMapTM k src dst extract merge).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then (FinTM.bufferTape w (q - d.workTapePos j)).map
                fun γ => merge (d.workTapes j q) (extract γ)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((copyMapTM k src dst extract merge).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((copyMapTM k src dst extract merge).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((copyMapTM k src dst extract merge).runFrom d t).workTapePos j =
          d.workTapePos j) := by
  obtain ⟨h1, h2, h3⟩ := transferMapTM_run_ofCfg src dst hne extract merge some w d hstate hw
  simp only [← copyMapTM_runFrom_eq] at h1 h2 h3
  refine ⟨h1.trans ?_, h2, h3⟩
  congr 1
  funext j q
  by_cases hs : j = src
  · subst hs
    simp only [hne, false_and, if_false]
    split_ifs with hq
    · rw [show ∀ o : Option Symbol, o.bind some = o from fun o => by cases o <;> rfl,
        ← hw (q - d.workTapePos j) (by omega) (by omega)]
      congr 1
      omega
    · rfl
  · simp [hs]

/-- **Transfer, framed** (design §12.6). From any
configuration in the sweep phase whose source tape carries the word `w`
delimited by blanks at relative positions `-1` and `|w|`, the transfer
reaches the `done` anchor at exactly `2|w| + 2` and not earlier. At that
point:

- the source interval `[pos, pos + |w|)` is blank;
- the destination interval holds `w`;
- every other cell, the head positions, the native input position and the
  output are unchanged.

The destination's old contents are arbitrary, because the routine never
branches on them. Up to the exit, both touched heads stay within one cell of
their word interval, and every other head is fixed. At a canonical seam
`Cfg.ofWords` with an empty destination, the endpoint is again a canonical seam
(`Turing.Cfg.ofWords_transfer_endpoint`).

**Proof sketch.** Generalize the canonical forward/rewind trace over the
fixed outer frame and the two start coordinates. The forward pass takes `|w|`
steps copying source to destination in lockstep without touching the source.
The source's right delimiter turns both heads in one step. The rewind takes
`|w|` steps erasing exactly the source interior. The left delimiter supplies
the final entry step. Formally the row is `Turing.transferMapTM_run_ofCfg` at the identity
map with the blank residue (§13d G2: one trace family serves both). -/
theorem transferTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (src dst : Fin k)
    (hne : src ≠ dst) (w : List Symbol) (d : Cfg k Symbol SweepPhase x)
    (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (transferTM k src dst).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = src ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then none
            else if j = dst ∧ d.workTapePos j ≤ q ∧
                q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((transferTM k src dst).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((transferTM k src dst).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((transferTM k src dst).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨h1, h2, h3⟩ :=
    transferMapTM_run_ofCfg src dst hne id (fun _ s => s) (fun _ => none) w d hstate hw
  refine ⟨h1.trans ?_, h2, h3⟩
  apply Cfg.ext <;> simp

/-- Clipping a canonical word to its occupied interval leaves its tape unchanged. -/
private theorem catalog_buffer_clip (w : List Bool) (p : ℤ) :
    (if 0 ≤ p ∧ p < (w.length : ℤ) then FinTM.bufferTape w p else none) =
      FinTM.bufferTape w p := by
  by_cases h : 0 ≤ p ∧ p < (w.length : ℤ)
  · rw [if_pos h]
  · rw [if_neg h]
    symm
    rw [FinTM.bufferTape_eq]
    split_ifs with h0
    · apply List.getElem?_eq_none_iff.mpr
      omega
    · rfl

/-- A canonical seam with a new state and pointwise canonical work tapes is the
canonical seam for those words. The input head, work heads and output keep their
canonical values.

**Proof sketch.** Apply configuration extensionality once. The tape hypothesis
identifies the work tapes; the published seam field equations identify the other
four fields. -/
private theorem catalog_ofWords_with_tapes {k : ℕ} {S : Type*} {x : List Bool}
    (q q' : S) (w w' : Fin k → List Bool)
    (tapes : Fin k → ℤ → Option Bool)
    (htapes : ∀ j p, tapes j p = FinTM.bufferTape (w' j) p) :
    ({ Cfg.ofWords (input := x) q w with
        state := some q'
        workTapes := tapes } : Cfg k Bool S x) = Cfg.ofWords q' w' := by
  apply Cfg.ext
  · simp only [Cfg.ofWords_state]
  · simp only [Cfg.ofWords_inputPos]
  · funext j p
    rw [Cfg.ofWords_workTapes]
    exact htapes j p
  · funext j
    simp only [Cfg.ofWords_workTapePos]
  · simp only [Cfg.ofWords_output]

/-- **The transfer endpoint from a canonical seam**. If `src ≠ dst` and the destination word of the
seam `Cfg.ofWords q w` is empty, then the framed transfer endpoint of `Turing.transferTM_run_ofCfg`
started there (state `q'`, the source interval blanked, the destination interval overwritten with
`w src`, everything else unchanged) is the seam
`Cfg.ofWords q' (Function.update (Function.update w src []) dst (w src))`.

**Proof sketch.** A `Cfg.ext` computation: as the copy endpoint, with the source interval `[0, |w src|)` blanked, which together with the blanks of
`bufferTape (w src)` outside it is `bufferTape []`. -/
theorem Cfg.ofWords_transfer_endpoint {k : ℕ} {S : Type*} {x : List Bool} (q q' : S)
    (w : Fin k → List Bool) (src dst : Fin k) (hne : src ≠ dst) (hdst : w dst = []) :
    ({ (Cfg.ofWords (input := x) q w) with
        state := some q'
        workTapes := fun j p =>
          if j = src ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then none
          else if j = dst ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then FinTM.bufferTape (w src) (p - (Cfg.ofWords (input := x) q w).workTapePos j)
          else (Cfg.ofWords (input := x) q w).workTapes j p } : Cfg k Bool S x) =
      Cfg.ofWords q' (Function.update (Function.update w src []) dst (w src)) := by
  apply catalog_ofWords_with_tapes
  intro j p
  simp only [Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos, zero_add, sub_zero]
  by_cases hs : j = src
  · subst j
    simp only [Function.update_of_ne hne, Function.update_self,
      FinTM.bufferTape_nil, hne, false_and, ite_false, true_and]
    split_ifs with hp
    · rfl
    · have hc := catalog_buffer_clip (w src) p
      rw [if_neg hp] at hc
      exact hc.symm
  · by_cases hd : j = dst
    · subst j
      simp only [Function.update_self, hdst, FinTM.bufferTape_nil,
        hs, false_and, ite_false, true_and]
      exact catalog_buffer_clip (w src) p
    · simp only [hs, hd, false_and, ite_false, Function.update_of_ne hd,
        Function.update_of_ne hs]


/-- **Copy, framed** (design §12.6). As
`Turing.transferTM_run_ofCfg`, except that the source is left intact: at
exactly `2|w| + 2` the destination interval holds `w` and every other cell is
unchanged. At a canonical seam with an empty destination the endpoint is again a
canonical seam (`Turing.Cfg.ofWords_copy_endpoint`).

**Proof sketch.** The transfer's trace without the erasure. The rewind is
guided by the intact source word, whose left delimiter at `-1` is the first
blank met moving left. Formally the row is `Turing.copyMapTM_run_ofCfg` at the identity map
(§13d G2: one trace family serves both). -/
theorem copyTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (src dst : Fin k)
    (hne : src ≠ dst) (w : List Symbol) (d : Cfg k Symbol SweepPhase x)
    (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (copyTM k src dst).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape w (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((copyTM k src dst).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = src ∨ j = dst then
          ((copyTM k src dst).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((copyTM k src dst).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨h1, h2, h3⟩ := copyMapTM_run_ofCfg src dst hne id (fun _ s => s) w d hstate hw
  refine ⟨h1.trans ?_, h2, h3⟩
  apply Cfg.ext <;> simp

/-- **The copy endpoint from a canonical seam**. If the destination word of the seam
`Cfg.ofWords q w` is empty, then the framed copy endpoint of `Turing.copyTM_run_ofCfg` started there
(state `q'`, the destination interval overwritten with `w src`, every other cell, head and the
output unchanged) is the seam `Cfg.ofWords q' (Function.update w dst (w src))`.

**Proof sketch.** A `Cfg.ext` computation: at the origin
heads of `Cfg.ofWords` the destination interval is `[0, |w src|)`, which `bufferTape (w src)` fills
exactly, and outside it the blank destination word agrees with `bufferTape (w src)`'s blanks; every
other tape is untouched. -/
theorem Cfg.ofWords_copy_endpoint {k : ℕ} {S : Type*} {x : List Bool} (q q' : S)
    (w : Fin k → List Bool) (src dst : Fin k) (hdst : w dst = []) :
    ({ (Cfg.ofWords (input := x) q w) with
        state := some q'
        workTapes := fun j p =>
          if j = dst ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then FinTM.bufferTape (w src) (p - (Cfg.ofWords (input := x) q w).workTapePos j)
          else (Cfg.ofWords (input := x) q w).workTapes j p } : Cfg k Bool S x) =
      Cfg.ofWords q' (Function.update w dst (w src)) := by
  apply catalog_ofWords_with_tapes
  intro j p
  simp only [Cfg.ofWords_workTapes, Cfg.ofWords_workTapePos, zero_add, sub_zero]
  by_cases hj : j = dst
  · subst j
    simp only [Function.update_self, hdst, FinTM.bufferTape_nil, true_and]
    exact catalog_buffer_clip (w src) p
  · simp only [hj, false_and, ite_false, Function.update_of_ne hj]


/-- **Clear, framed** (design §12.6). From any
configuration in the sweep phase whose tape `i` carries the delimited word
`w`, the routine reaches `done` at exactly `2|w| + 2` and not earlier, with
the word interval blank and every other cell, head, the input position and the
output unchanged. Up to the exit the head stays within one cell of the
interval.

**Proof sketch.** The forward pass walks right over the intact word in `|w|`
steps, the right delimiter turns the head in one step, the rewind erases the
interior in `|w|` steps, and the left delimiter supplies the entry step. The
no-earlier-exit and head clauses are the shared `catalog_trace_clauses`. -/
theorem clearTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k) (w : List Symbol)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some SweepPhase.sweep)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (clearTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some SweepPhase.done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then none
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2,
        ((clearTM k i).runFrom d t).state ≠ some SweepPhase.done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((clearTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((clearTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  constructor
  · rw [catalog_clear_trace i w d hstate hw]
    simp [catalogTrace, catalogClearF, catalogClearR, show ¬2 * w.length + 2 ≤ w.length by omega]
  · exact catalog_trace_clauses (clearTM k i) d (· = i) _ _ _ w.length
      (catalog_clear_trace i w d hstate hw) (fun _ => ⟨rfl, fun _ => rfl⟩)
      (fun _ => ⟨rfl, fun _ => rfl⟩) ⟨rfl, rfl⟩

/-- A carry sweep has one framed endpoint, first-return cut and head interval for
both a successful increment and overflow, parametrized by the suffix after the carry.

**Proof sketch.** Read the existing carry trace at the final time and at each earlier
time. Its forward and rewind phases avoid both result anchors, and their head offsets
stay between minus one and the carry length. The optional suffix determines the verdict
and final word; replacing its leading bit preserves the delimited word length. -/
private theorem catalog_increment_framed {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p)
    (p : ℕ) (tail : Option (List Bool))
    (hsplit : w = List.replicate p true ++ tail.elim [] (false :: ·)) :
    (incrementTM k i).runFrom d (2 * p + 2) =
        { d with
          state := some (FlagPhase.done tail.isSome)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate p false ++ tail.elim [] (true :: ·))
                (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * p + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * p + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (p : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hlen : (List.replicate p false ++ tail.elim [] (true :: ·)).length = w.length := by
    rw [hsplit]
    cases tail <;> simp
  constructor
  · rw [catalog_increment_trace i w d hstate hw p tail hsplit]
    simp only [catalogTrace, show ¬2 * p + 2 ≤ p by omega,
      show ¬2 * p + 2 ≤ 2 * p + 1 by omega, ite_false]
    apply Cfg.ext <;> simp [catalogIncR]
    funext j q
    by_cases hj : j = i <;> simp [hj, wordPatch, hlen]
  · constructor
    · intro t ht b
      rw [catalog_increment_trace i w d hstate hw p tail hsplit]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR] <;> omega
    · intro j t ht
      rw [catalog_increment_trace i w d hstate hw p tail hsplit]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, Finset.mem_Icc] <;> omega


/-- **Increment, framed success with exact carry cost** (design §12.6).
Let the delimited word `w` on tape `i` have a successor at its
width, `incFixed w = some v`, and let `p = (w.takeWhile id).length` be its
number of leading `true` cells. Then the routine reaches the success anchor
at exactly `2p + 2` and not earlier, with the word interval holding `v` and
everything else unchanged. Up to the exit the head stays within
`[pos - 1, pos + p]`; `2|w| + 2` is a slack form of this bound.

**Proof sketch.** The carry pass takes `p` steps flipping the `true` prefix,
then one step writes the first `false` as `true` and turns left. The return
takes `p` steps and the left delimiter supplies the entry step, so the total
is `2p + 2`. Cells beyond `p` are never visited. -/
theorem incrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : incFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * (w.takeWhile id).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile id).length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile id).length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile id).length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨p, tail, hsplit⟩ := catalog_increment_split w
  rw [hsplit, catalog_increment_value] at hv
  cases tail with
  | none => simp at hv
  | some tail =>
    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
    have hp : (w.takeWhile id).length = p := by
      simp [hsplit]
    rw [hp]
    simpa only [Option.isSome_some, Option.elim_some, hv'] using
      catalog_increment_framed i w d hstate hw p (some tail) hsplit


/-- **Increment, framed overflow** (design §12.6). If the
delimited word `w` on tape `i` has no successor at its width
(`incFixed w = none`, that is, it is all `true`), the routine reaches the
overflow anchor at exactly `2|w| + 2` and not earlier. The word interval then
holds `|w|` copies of `false`, the enumerator's wrap convention, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`.

**Proof sketch.** The carry pass takes `|w|` steps flipping every cell, the
right delimiter turns the head with the overflow verdict, the return takes
`|w|` steps, and the left delimiter supplies the entry step. -/
theorem incrementTM_run_overflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : incFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length false) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨p, tail, hsplit⟩ := catalog_increment_split w
  rw [hsplit, catalog_increment_value] at hv
  cases tail with
  | some tail => simp at hv
  | none =>
    have hp : w.length = p := by simp [hsplit]
    rw [hp]
    simpa only [hp, Option.isSome_none, Option.elim_none, List.append_nil] using
      catalog_increment_framed i w d hstate hw p none hsplit


/-- **Transfer, per-tape space** (design §12 R3).
The two touched tapes visit at most the word interval plus the two
boundary blanks — `|w src| + 2` cells, from the `-1` overshoot to the
right blank at `|w src|` — and every other tape never leaves its origin.

**Proof sketch.** Head-movement count of the phases: both touched heads
walk `0 → |w src| → -1 → 0` in unit steps, so their trajectories lie in
`[-1, |w src|]` (`Finset.Icc`, cardinality `|w src| + 2`); all other
action components are `(none, 0)`, so those trajectories are constant and
the visited set is the origin singleton. -/
theorem transferTM_spaceUsedByTape (k : ℕ) (src dst : Fin k)
    (hne : src ≠ dst) (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (transferTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (transferTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [← transferMapTM_plain, catalog_transferMap_trace src dst hne id (fun _ s => s)
      (fun _ => none) (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;>
      simp only [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [← transferMapTM_plain, catalog_transferMap_trace src dst hne id (fun _ s => s)
    (fun _ => none) (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;>
    simp [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords, hs, hd]

/-- **Copy, per-tape space** (design §12 R3). As the
transfer routine: the two touched tapes visit at most `|w src| + 2` cells
(the word interval plus both boundary blanks), every other tape exactly
its origin singleton.

**Proof sketch.** Identical head-movement count to
`transferTM_spaceUsedByTape`: both touched heads walk
`0 → |w src| → -1 → 0`; all other tapes receive `(none, 0)` throughout. -/
theorem copyTM_spaceUsedByTape (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (copyTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (copyTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [← copyMapTM_plain, copyMapTM_runFrom_eq, catalog_transferMap_trace src dst hne id
      (fun _ s => s) some (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;>
      simp only [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [← copyMapTM_plain, copyMapTM_runFrom_eq, catalog_transferMap_trace src dst hne id
    (fun _ s => s) some (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;>
    simp [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords, hs, hd]

/-- **Clear, per-tape space** (design §12 R3). Tape
`i` visits at most `|w i| + 2` cells (the word interval plus both
boundary blanks); every other tape exactly its origin singleton.

**Proof sketch.** The single touched head walks `0 → |w i| → -1 → 0` in
unit steps, so its trajectory lies in `[-1, |w i|]`; every other tape's
action is `(none, 0)` in every phase. -/
theorem clearTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (clearTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  constructor
  · apply catalog_space_bound
    intro u
    rw [catalog_clear_trace i (w i) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords] <;> omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_clear_trace i (w i) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords, hj]

/-- **Compare, per-tape space** (design §12 R3). The
two compared tapes visit at most `min(|w fst|, |w snd|) + 2` cells (the
scanned interval plus both boundary cells); every other tape exactly its
origin singleton.

**Proof sketch.** Exact position counting, uniformly over mismatches,
equal words, and unequal lengths (round-1 finding 6 — the earlier
`[-1, min + 1]` interval argument did not cover equal inputs): with `d`
the first differing position or the first position where a word ends
(`d ≤ min`), the scan turns at `d`, the return pass overshoots to `-1`,
and both touched trajectories are exactly the integers of `[-1, d]` —
`d + 2 ≤ min + 2` visited cells in every case, aliased indices included;
untouched tapes receive `(none, 0)` throughout. -/
theorem compareTM_spaceUsedByTape (k : ℕ) (fst snd : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t fst
      ≤ min (w fst).length (w snd).length + 2 ∧
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t snd
      ≤ min (w fst).length (w snd).length + 2 ∧
    ∀ j : Fin k, j ≠ fst → j ≠ snd →
      (compareTM k fst snd).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨δ, hδ, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  have trace := catalog_compare_trace fst snd (w fst) (w snd)
    (Cfg.ofWords (input := x) .run w) rfl
    (by intro p _ _; simp [Cfg.ofWords]) (by intro p _ _; simp [Cfg.ofWords])
    δ hδ hp hs he
  have hb (j : Fin k) : (compareTM k fst snd).spaceUsedByTape
      (Cfg.ofWords (input := x) .run w) t j ≤ δ + 2 := by
    apply catalog_space_bound
    intro u
    rw [trace]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCompareF, catalogCompareR, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨(hb fst).trans (by omega), (hb snd).trans (by omega), ?_⟩
  intro j hf hg
  apply catalog_space_one
  intro u
  rw [trace]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCompareF, catalogCompareR, Cfg.ofWords, hf, hg]

/-- **Increment, per-tape space** (design §12 R3).
Tape `i` visits at most `|w i| + 2` cells; every other tape exactly its
origin singleton.

**Proof sketch.** The carry head walks right to at most the right blank
at `|w i|`, back to the `-1` overshoot, and home: trajectory inside
`[-1, |w i|]`; other tapes receive `(none, 0)` in every phase. -/
theorem incrementTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (incrementTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  have hp : p ≤ (w i).length := by simp [hw]
  constructor
  · have hb : (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) .run w) t i ≤ p + 2 := by
      apply catalog_space_bound
      intro u
      rw [catalog_increment_trace i (w i) (Cfg.ofWords .run w) rfl
        (by intro q _ _; simp [Cfg.ofWords]) p tail hw]
      simp only [catalogTrace]
      split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords] <;> omega
    omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_increment_trace i (w i) (Cfg.ofWords .run w) rfl
        (by intro q _ _; simp [Cfg.ofWords]) p tail hw]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords, hj]

/-- **W1 space row** (design §12 R3, decision 12.3).
Under the hypotheses of `Turing.capture_run`, the host's source-bank
tapes visit exactly the source's cells — per-tape, on the nose — and the
capture tape's space usage is bounded by the output recorded in the
window plus one.

**Proof sketch.** `Turing.capture_run` makes the host trajectory on tape
`i.castSucc` pointwise equal to the source's on tape `i`, so the visited
images and their cardinalities agree. The capture head sits at
`|pre ++ output-so-far|`, which is nondecreasing (one cell per recorded
emission, `Turing.MultiTapeTM.output_prefix`), so its visited set is an
integer interval of length the output growth plus one. -/
theorem capture_visitedByTapeHead {k : ℕ} {S H : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    (∀ i : Fin k,
      host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.visitedByTapeHead c₀ t i ∧
      host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.spaceUsedByTape c₀ t i) ∧
    host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t (Fin.last k)
      ≤ (tm.runFrom c₀ t).output.length - c₀.output.length + 1 := by
  have hr (u : ℕ) (hu : u ≤ t) :=
    capture_run tm host emb ret hagree pre out₀ c₀ u
      (fun v hv => hlive v (by omega))
  constructor
  · intro i
    have he : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc =
        tm.visitedByTapeHead c₀ t i := by
      unfold MultiTapeTM.visitedByTapeHead
      apply Finset.image_congr
      intro u hu
      dsimp only
      rw [hr u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
      simp [captureCfg, i.isLt]
    exact ⟨he, congrArg Finset.card he⟩
  · have hmono {u v : ℕ} (huv : u ≤ v) :
        (tm.runFrom c₀ u).output.length ≤ (tm.runFrom c₀ v).output.length :=
      (tm.output_prefix c₀ huv).length_le
    have hbound : c₀.output.length ≤ (tm.runFrom c₀ t).output.length :=
      hmono (Nat.zero_le t)
    have hsub : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t (Fin.last k) ⊆
        Finset.Icc ((pre.length + c₀.output.length : ℕ) : ℤ)
          ((pre.length + (tm.runFrom c₀ t).output.length : ℕ) : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hut : u ≤ t := by have := Finset.mem_range.mp hu; omega
      rw [hr u hut]
      simp only [captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        List.length_append, Finset.mem_Icc]
      have hlo := hmono (Nat.zero_le u)
      have hhi := hmono hut
      simp only [MultiTapeTM.runFrom_zero] at hlo
      constructor <;> omega
    exact (Finset.card_le_card hsub).trans (by
      rw [Int.card_Icc]
      omega)

end Turing

namespace Turing.FinTM

/-- **P1 space row** (design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_id`). The copy machine runs in
constant work-tape space: one witness does the whole job on its input and
output heads alone.

**Proof sketch.** The existing witness `idTM` has no work tapes, so every
`spaceUsed` value is `0`; re-exhibit it and join the audited time
contract with the constant bound. -/
theorem computesFunInTime_id_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime id (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨idTM, 1, (computesFunInTime_iff _ _ _).mpr fun x =>
    (idTM_computes x).mono (le_of_eq (one_mul _).symm), fun x t => by
    rw [idTM_spaceUsed x t]; omega⟩

/-- **P2 space row** (design §12 R3; annotates
`Turing.FinTM.computesFunInTime_const`). The fixed-word emission chain
runs in constant work-tape space.

**Proof sketch.** The existing witness `constTM w` is a zero-work-tape
emission chain, so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_const_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun _ => w) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨constTM w, w.length + 1, (computesFunInTime_iff _ _ _).mpr fun x =>
    (constTM_computes w x).mono (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)), fun x t => by
    rw [constTM_spaceUsed w x t]; omega⟩

/-- **P3 space row** (design §12 R3; annotates
`Turing.FinTM.computesFunInTime_prepend`). Prepending a fixed word runs
in constant work-tape space: an emission chain followed by the input
copy scan never moves a work head.

**Proof sketch.** The witness `prependTM` (time `prependTM_computes`) has no work-tape
movement (head-movement count zero on every phase), so each visited set
is the origin singleton and the total is the tape count, a machine
constant absorbed into `c`. -/
theorem computesFunInTime_prepend_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨prependTM w, w.length + 1, (computesFunInTime_iff _ _ _).mpr fun x =>
    ((computesFunInTime_iff _ _ _).mp (prependTM_computes w) x).mono (by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega), fun x t => by
    rw [prependTM_spaceUsed w x t]; omega⟩

/-- **P4 space row** (design §12 R3; annotates
`Turing.FinTM.computesFunInTime_lengthBits`). The binary length counter
runs in logarithmic work-tape space: the counter word has `Nat.size n`
bits and the scan never leaves its interval (the sharp clause the
chapter-4 campaign consumes).

**Proof sketch.** The witness drives an in-place binary counter on one
work tape (the `Turing.incFixed` carry discipline): its head stays within
the counter interval `[-1, Nat.size n + 1]`, whose visit count the carry
head-movement bounds; constants absorb the boundary cells. -/
theorem computesFunInTime_lengthBits_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (Nat.size x.length + 1) :=
  ⟨lengthBitsTM, 5, lengthBitsTM_computes, lengthBitsTM_spaceUsed⟩

/-- **P5 space row, unary clause** (design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyUnary`). The unary
polynomial generator runs in linear work-tape space: each of its `e`
nested loop tapes holds a unary counter of side `n + 1`.

**Proof sketch.** Head-movement count per loop tape: installed by one
input scan and bounded by the box side `n + 1`, revisited in place
across iterations — per-tape visited sets lie in `[-1, n + 1]`, and the
tape count depends only on `e`, absorbed into `c`. -/
theorem computesFunInTime_polyUnary_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) :=
  ⟨polyUnaryTM C e, C + 10 * e + 4, (computesFunInTime_iff _ _ _).mpr fun x =>
    ((computesFunInTime_iff _ _ _).mp (polyUnaryTM_computes C e) x).mono (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ e))),
    fun x t => (polyUnaryTM_spaceUsed C e x t).trans (Nat.mul_le_mul_right _ (by omega))⟩

/-- The binary polynomial value can be computed with polynomial time and work space
bounded by a constant multiple of its unary intermediate value plus one.

**Proof sketch.** If the coefficient is zero, reuse the constant-output row and
weaken its linear time bound to the required polynomial bound. For a positive
coefficient, use the existing binary evaluator's time contract and the general
space-from-time estimate. The polynomial power is at most its positive coefficient
multiple, so the fixed tape count and time coefficients are absorbed into a single
constant independent of the input. -/
theorem computesFunInTime_polyBits_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (C * (x.length + 1) ^ e + 1) := by
  by_cases hC : C = 0
  · subst C
    obtain ⟨M, c, htime, hspace⟩ := computesFunInTime_const_spaceUsed []
    refine ⟨M, c, ?_, ?_⟩
    · have ht := (computesFunInTime_iff _ _ _).mp htime
      apply (computesFunInTime_iff _ _ _).mpr
      intro x
      simpa only [Nat.zero_mul, Nat.zero_bits] using
        (ht x).mono (Nat.mul_le_mul_left c
          (Nat.le_self_pow (Nat.succ_ne_zero e) (x.length + 1)))
    · intro x t
      simpa only [Nat.zero_mul, Nat.zero_add, Nat.mul_one] using hspace x t
  · have hT := (computesFunInTime_iff _ _ _).mp (polyBitsTM_computes C e)
    refine ⟨polyBitsTM C e,
      (polyBitsTM C e).k * (7 * C + 5 * e + 11 + 1) + (7 * C + 5 * e + 11),
      (computesFunInTime_iff _ _ _).mpr fun x => (hT x).mono
        (Nat.mul_le_mul (Nat.le_add_left _ _)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ e))), fun x t => ?_⟩
    refine (ComputesInTime.spaceUsed_le (hT x) t).trans ?_
    dsimp only
    have hP : (x.length + 1) ^ e ≤ C * (x.length + 1) ^ e :=
      Nat.le_mul_of_pos_left _ (by omega)
    generalize (x.length + 1) ^ e = P at hP ⊢
    have h1 := Nat.mul_le_mul_left (7 * C + 5 * e + 11) hP
    have hb : (7 * C + 5 * e + 11) * P + 1 ≤
        (7 * C + 5 * e + 11 + 1) * (C * P + 1) := by
      have h2 : (7 * C + 5 * e + 11 + 1) * (C * P + 1) =
          (7 * C + 5 * e + 11) * (C * P) + (7 * C + 5 * e + 11) + C * P + 1 := by ring
      omega
    calc (polyBitsTM C e).k * ((7 * C + 5 * e + 11) * P + 1)
        ≤ (polyBitsTM C e).k * ((7 * C + 5 * e + 11 + 1) * (C * P + 1)) :=
          Nat.mul_le_mul_left _ hb
      _ = (polyBitsTM C e).k * (7 * C + 5 * e + 11 + 1) * (C * P + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)


/-- **P6 space row, fixed-first-component encoder**
(design §12 R3; annotates `Turing.FinTM.computesFunInTime_pairEncodeFixed`).
Pairing with a fixed first component runs in constant work-tape space: it
is the prepend row at the doubled fixed word.

**Proof sketch.** Same witness route as
`computesFunInTime_prepend_spaceUsed` at the word
`(α doubled) ++ [false, true]`: no work-head movement at all. -/
theorem computesFunInTime_pairEncodeFixed_spaceUsed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  simpa only [pairEncode_eq] using
    computesFunInTime_prepend_spaceUsed ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- Every buffered pair-extraction choice has a linear work-space bound obtained
from its linear time contract, with its fixed tape count absorbed in the constant.

**Proof sketch.** The general space-from-time estimate bounds visited cells by the
number of tapes times one more than the runtime. The extraction time is at most
five times the positive input length bound. Six times one more than the fixed tape
count therefore bounds both time and space with the same existential constant. -/
private theorem pairExtract_space_row (a b : Bool) (f : List Bool → List Bool)
    (h : (pairExtractTM a b).ComputesFunInTime f (fun n => 5 * (n + 1))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime f (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  have hT := (computesFunInTime_iff _ _ _).mp h
  refine ⟨pairExtractTM a b, 6 * ((pairExtractTM a b).k + 1),
    (computesFunInTime_iff _ _ _).mpr (fun x => (hT x).mono
      (Nat.mul_le_mul_right _ (by omega))), fun x t => ?_⟩
  refine (ComputesInTime.spaceUsed_le (hT x) t).trans ?_
  calc (pairExtractTM a b).k * (5 * (x.length + 1) + 1)
      ≤ (pairExtractTM a b).k * (6 * (x.length + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 6 * (pairExtractTM a b).k * (x.length + 1) := by ring
    _ ≤ 6 * ((pairExtractTM a b).k + 1) * (x.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)

/-- **P6 space row, first extraction** (design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairFst`). The
first-component extractor runs in linear work-tape space: the aligned
scan buffers the undoubled prefix before any emission.

**Proof sketch.** Apply the common extraction-row bound to the published first
projection time contract. The general space-from-time estimate is linear, and the
fixed tape count is absorbed into the existential constant. -/
theorem computesFunInTime_pairFst_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  exact pairExtract_space_row true false _ pairExtractTM_fst


/-- **P6 space row, second extraction** (design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairSnd`). The
second-component extractor runs in linear work-tape space (it shares the
buffered parser with the first extractor).

**Proof sketch.** Apply the common extraction-row bound to the published second
projection time contract, absorbing the fixed tape count into the same constant
used for time and space. -/
theorem computesFunInTime_pairSnd_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  exact pairExtract_space_row false true _ pairExtractTM_snd


/-- **P6 space row, validity test** (design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairValid`). The grammar
validity test runs in constant work-tape space: alignment is finite
control, nothing is buffered.

**Proof sketch.** The existing witness `pairValidTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairValid_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨pairValidTM, 1, (computesFunInTime_iff _ _ _).mpr fun x => by
    simpa using pairValidTM_computes x, fun x t => by
    rw [pairValidTM_spaceUsed x t]; omega⟩

/-- **P13 space row, pair to concatenation** (design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairConcat`). The
concatenation extractor runs in linear work-tape space.

**Proof sketch.** Apply the common extraction-row bound to the published
concatenation time contract. Its fixed tape count and linear runtime give the
required linear space estimate with a common existential constant. -/
theorem computesFunInTime_pairConcat_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  exact pairExtract_space_row true true _ pairExtractTM_concat


/-- **P14 space row, pair duplication** (design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairDup`). The duplication
encoder runs in constant work-tape space: both passes re-read the input
tape, nothing is buffered.

**Proof sketch.** Retain the witness `Turing.pairDiagTM` and the time coefficient from
`Turing.pairDiagTM_computes`. The published `Turing.pairDiagTM_spaceUsed` gives zero space
directly, so the existing constant-space witness bounds it. -/
theorem computesFunInTime_pairDup_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨pairDiagTM, 6, (computesFunInTime_iff _ _ _).mpr fun x =>
    (pairDiagTM_computes x).mono (by omega), fun x t => by
    rw [pairDiagTM_spaceUsed]; omega⟩

/-- **P8 space row, threaded length check** (design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairLenCheck`). The
threaded length checker's space is dominated by the unary polynomial
bank `C·(|a|+1)^e` it counts down against, plus the linear parse
buffers.

**Proof sketch.** Head-movement count per stage: the extractor buffers at
most `n` cells, the unary generator's bank holds `C·(|a|+1)^e ≤
C·(n+1)^e` cells, and the countdown walks that bank in place; boundary
cells and the stage count go into `c`. -/
theorem computesFunInTime_pairLenCheck_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ c * ((x.length + 1) ^ e + x.length + 1) := by
  have hT := (computesFunInTime_iff _ _ _).mp (pairLenCheckTM_computes C e)
  refine ⟨pairLenCheckTM C e,
    2 * (C + 5 * e + 17) + (pairLenCheckTM C e).k * (C + 5 * e + 17 + 1),
    (computesFunInTime_iff _ _ _).mpr fun x => ?_, fun x t => ?_⟩
  · have h1 : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ e)
    have h2 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := Nat.le_self_pow (Nat.succ_ne_zero e) _
    refine (hT x).mono ?_
    calc (C + 5 * e + 17) * ((x.length + 1) ^ e + x.length + 1)
        ≤ (C + 5 * e + 17) * (2 * (x.length + 1) ^ (e + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (C + 5 * e + 17) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · refine (ComputesInTime.spaceUsed_le (hT x) t).trans ?_
    dsimp only
    have hQ : 1 ≤ (x.length + 1) ^ e + x.length + 1 := by omega
    generalize (x.length + 1) ^ e + x.length + 1 = Q at hQ ⊢
    calc (pairLenCheckTM C e).k * ((C + 5 * e + 17) * Q + 1)
        ≤ (pairLenCheckTM C e).k * ((C + 5 * e + 17 + 1) * Q) :=
          Nat.mul_le_mul_left _ (by
            have : (C + 5 * e + 17 + 1) * Q = (C + 5 * e + 17) * Q + Q := by ring
            omega)
      _ = (pairLenCheckTM C e).k * (C + 5 * e + 17 + 1) * Q := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **P9 space row, marker stripping** (design §12
R3; annotates `Turing.FinTM.computesFunInTime_stripLast`). The marker
stripper runs in linear work-tape space: the raw buffer and the guard
banks are each linear, and the quadratic **time** contract is deliberate
slack over the construction's actual linear-derived bound (round-1
finding/note 8 — the attached witness proves a linear intermediate
before weakening; no replay story is needed).

**Proof sketch.** The witness's guard/extraction banks and the raw-strip
buffer are each at most linear (`O(n + 1)` cells); the timed conditional
keeps them disjoint; every head stays inside linear intervals, and the
retained `(n+1)²` time clause is slack, not a resource actually spent on
space. -/
theorem computesFunInTime_stripLast_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        (fun n => c * (n + 1) ^ 2) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  have hT := (computesFunInTime_iff _ _ _).mp stripLastTM_computes
  refine ⟨stripLastTM, 150 + stripLastTM.k * 151, (computesFunInTime_iff _ _ _).mpr fun x => ?_,
    fun x t => ?_⟩
  · refine (hT x).mono ?_
    calc 150 * (x.length + 1) ≤ 150 * (x.length + 1) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · refine (ComputesInTime.spaceUsed_le (hT x) t).trans ?_
    calc stripLastTM.k * (150 * (x.length + 1) + 1) ≤ stripLastTM.k * (151 * (x.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = stripLastTM.k * 151 * (x.length + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **P11 space row, fixed-width increment** (design
§12 R3; annotates `Turing.FinTM.computesFunInTime_incFixed`; the
string-function counterpart of `Turing.incrementTM`). The incrementer
runs in constant work-tape space: it validates and emits from two native
input scans with the carry resident in control.

**Proof sketch.** Retain the existing witness `Turing.FinTM.incFixedTM` and its time coefficient.
The published `Turing.FinTM.incFixedTM_spaceUsed` gives zero space directly, so the existing
constant-space witness bounds it. -/
theorem computesFunInTime_incFixed_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c :=
  ⟨incFixedTM, 3, (computesFunInTime_iff _ _ _).mpr incFixedTM_computes, fun x t => by
    rw [incFixedTM_spaceUsed]; omega⟩

/-- **Threaded-map space row** (design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairMapSnd`, the round-2
catalog addition). Given a payload machine with its own space bound
`Sg` (monotone, since the payload runs on the second component, which is
no longer than the whole input), the threaded-map controller's space is
the payload's plus linear administration. **The witness is a new
forwarding controller, not the received captured-payload machine**
(round-1 finding 4, the witness-honesty refutation: `pairMapTM`'s
capture tape visits `|g b| + 1` cells — the unary-square payload defeats
any linear administrative claim about it; output length is not bounded
by the payload's work space).

**Proof sketch.** The commissioned controller: validate and buffer the
input pair (`O(n + 1)` cells), emit the encoded first component, then
simulate `Mg` on the buffered second component **forwarding its output**
(the E2/`embedEmitTM` discipline — emissions go to the physical output,
never to a work bank), leaving the payload's work-head trajectories
unchanged — coefficient `1` on `Sg` — plus the linear buffer and
administration; the `Monotone Sg` hypothesis transports the payload
bound from `|b|` to `n`. Named construction obligations for the brief:
the validating buffer stage, the forwarding payload stage, and their
seam. -/
theorem computesFunInTime_pairMapSnd_spaceUsed {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ} (Sg : ℕ → ℕ)
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg)
    (hgs : ∀ (y : List Bool) (t : ℕ),
      Mg.tm.spaceUsed (Mg.tm.initCfg y) t ≤ Sg y.length)
    (hSg : Monotone Sg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        (fun n => c * (n + 1 + Tg n)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ Sg x.length + c * (x.length + 1) :=
  ⟨pairMapSndTM Mg, 22, pairMapSndTM_computes hg hTg, pairMapSndTM_spaceUsed Sg hgs hSg⟩

/-- **P15 space row, split search** (design §12 R3;
annotates `Turing.FinTM.computesFunInTime_splitSolve`). The padding
split search runs in space one polynomial degree below its time: per
candidate it rebuilds unary banks of size at most `C·(n+1)^e` in place,
and candidates reuse the same banks.

**Proof sketch.** Head-movement count of the loop body's phases: the
candidate banks and the generator's output bank are rebuilt in place
every round (the round seam restores heads to the origin), so the
per-tape visited sets are intervals of length at most the largest bank,
`C·(n+1)^e` cells plus linear administration; the round count multiplies
time, not space. -/
theorem computesFunInTime_splitSolve_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  refine ⟨splitSolveTM C e,
    (20 + 23 * (splitSolveTM C e).k) * ((C + 1 + 5 * e) * 2 ^ e + 46),
    (computesFunInTime_iff _ _ _).mpr fun x =>
      ((computesFunInTime_iff _ _ _).mp (splitSolveTM_computes C e) x).mono
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))),
    fun x t => (splitSolveTM_spaceUsed C e x t).trans ?_⟩
  rw [Nat.add_mul (20 : ℕ) (23 * (splitSolveTM C e).k), Nat.mul_assoc 23]
  exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **W3 space row** (design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_cond`). Given space bounds for
the decider and both branches, the conditional controller's space is the
decider's plus the selected branch's **max** — the unselected branch's
bank is idle (origin singletons) — plus a machine constant for the
capture tape and the idle banks' origin cells.

**Proof sketch.** The controller's tape banks are disjoint: the decider
bank is only touched in the capture phase (bounded by `sD` through the
W1 lockstep), the selected branch bank only after dispatch (bounded by
its own hypothesis on the same input `x` — no monotonicity needed), the
unselected bank and the capture tape contribute one cell per tape plus
the singleton verdict; sum the three groups. -/
theorem computesFunInTime_cond_spaceUsed {D M₁ M₂ : FinTM Bool}
    {p : List Bool → Bool} {f₁ f₂ : List Bool → List Bool}
    {T₀ T₁ T₂ : ℕ → ℕ} (sD s₁ s₂ : ℕ → ℕ)
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂)
    (hsD : ∀ (x : List Bool) (t : ℕ),
      D.tm.spaceUsed (D.tm.initCfg x) t ≤ sD x.length)
    (hs₁ : ∀ (x : List Bool) (t : ℕ),
      M₁.tm.spaceUsed (M₁.tm.initCfg x) t ≤ s₁ x.length)
    (hs₂ : ∀ (x : List Bool) (t : ℕ),
      M₂.tm.spaceUsed (M₂.tm.initCfg x) t ≤ s₂ x.length) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ sD x.length + max (s₁ x.length) (s₂ x.length) + c := by
  refine ⟨timedCondTM D M₁ M₂, 7 + M₁.k + M₂.k, (computesFunInTime_iff _ _ _).mpr fun x => ?_,
    fun x t => ?_⟩
  · exact ((computesFunInTime_iff _ _ _).mp (timedCondTM_computes hD h₁ h₂) x).mono
      (Nat.mul_le_mul_right _ (by omega))
  · have h := timedCondTM_spaceUsed D M₁ M₂ x (p x) (T₀ x.length) t
      ((computesFunInTime_iff _ _ _).mp hD x)
    rw [branchTM_spaceUsed] at h
    have hd := hsD x (T₀ x.length)
    have h1 := hs₁ x t
    have h2 := hs₂ x t
    have hm1 := Nat.le_max_left (s₁ x.length) (s₂ x.length)
    have hm2 := Nat.le_max_right (s₁ x.length) (s₂ x.length)
    split at h <;> omega

/-- **L space row** (design §12 R3, decision 12.3;
annotates `Turing.FinTM.exists_loopTM`; the `exists_loopCfgTM` and
`exists_loopFindTM` siblings inherit the same host at fill time). Same
hypotheses as the decision loop, plus space bounds for the fuel machine
and for the body — from its initial configuration and from every
admissible seam, within the round budget. Conclusion: the loop host also
runs within a constant multiple of `S n + T n + 1` work-tape cells. The
key point is that space does **not** scale with the round count `R`:
rounds restart from seams with heads at the origin, so their footprints
overlap instead of accumulating.

**Proof sketch.** Per tape, each round's visited set is an interval
containing the seam origin (heads move by unit steps from the origin) of
cardinality at most `S n`, so the union over all rounds lies in
`[-(S n), S n]` — at most `2·S n + 1` cells, not `R·S n`. The counter
tape holds the fuel word, of length at most `T n`
(`Turing.MultiTapeTM.output_length_le` on the fuel machine), walked in
place by the debits; the capture tape records one verdict per round and
is rewound with the round, staying within a constant; the fuel machine's
own banks are bounded by `hFspace`. Sum the groups and absorb tape
counts into `c`.  **Scope note (round-1 note R10)**: this row annotates the
decision-loop export (`Turing.exists_loopTM`) only; the configuration- and
result-bearing siblings (`exists_loopCfgTM`, `exists_loopFindTM`) carry no
exported space clause here — same-witness conjunctions for them are a
recorded future addition, commissioned when a consumer needs them, not an
implied theorem. -/
theorem exists_loopTM_spaceUsed (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s)))
    (hFspace : ∀ (x : List Bool) (t : ℕ),
      F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (hstartSpace : ∀ (x : List Bool) (t : ℕ), t ≤ T x.length →
      body.tm.spaceUsed (body.tm.initCfg x) t ≤ S x.length)
    (hroundSpace : ∀ (x s : List Bool), Inv x s →
      ∀ t ≤ T x.length,
        body.tm.spaceUsed
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t
            ≤ S x.length) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        E.tm.spaceUsed (E.tm.initCfg x) t
          ≤ c * (S x.length + T x.length + 1) := by
  refine ⟨loopHostTM body F anchor false, 10 + 23 * (loopHostTM body F anchor false).k,
    (computesFunInTime_iff _ _ _).mpr fun x =>
      ((computesFunInTime_iff _ _ _).mp (loopHostTM_decides body F anchor Inv stepF acceptF s0 R T
        hF hInv0 hInvStep hstart hround) x).mono
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))), fun x t => ?_⟩
  refine (loopHostTM_spaceUsed_le_budget body F anchor Inv stepF acceptF (fun _ _ => [true])
    false s0 R T hF hInv0 hInvStep hstart hround x t).trans ?_
  rw [Nat.add_mul 10]
  exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_left _ _)

end Turing.FinTM

/-! ## Part 3 — the §12.8 rows (proved)

The alphabet-generic rows of design §12.8a: the one-tape actions their
tables are written with, the field layout, the framed compare (R8.1), the
seek family (R8.3) and the two-pass scan (R8.2, the G2 core). The machines are
real definitions and every contract below is proved. Each follows the §12.6 framed form: exact time, finish configuration, no earlier
exit, and the trajectory of every head. -/

namespace Turing

/-! ### One-tape actions -/

/-- **An action on one work tape** (design §12.8a): move the input head by
`inp`, write `wr` on tape `i` and move its head by `m`, leave every other work
tape untouched, emit nothing, and continue in `q`. The transition tables of the
§12.8 single-sweep rows are built from it and `Turing.inputMoveAction`. -/
def tapeAction {k : ℕ} {Symbol State : Type*} (i : Fin k) (inp : SignType)
    (wr : Option (Option Symbol)) (m : SignType) (q : State) : Action k Symbol State :=
  ⟨inp, fun j => if j = i then (wr, m) else (none, 0), none, some q⟩

/-- **An action on the input head only** (design §12.8a): move the input head
by `inp`, touch no work tape, emit nothing, and continue in `q`. At `inp = 0`
it is the stationary action of a live anchor. -/
def inputMoveAction {k : ℕ} {Symbol State : Type*} (inp : SignType) (q : State) :
    Action k Symbol State :=
  ⟨inp, fun _ => (none, 0), none, some q⟩

/-- An input-only action has the requested input movement and live successor,
with no work-tape writes or head movement and no output symbol. -/
theorem inputMoveAction_eq {k : ℕ} {Symbol State : Type*} (inp : SignType) (q : State) :
    inputMoveAction (k := k) (Symbol := Symbol) inp q =
      (⟨inp, fun _ => (none, 0), none, some q⟩ : Action k Symbol State) := by
  rfl

/-- **One step of a non-writing one-tape action** (design §12.8a). If the machine's table
gives `Turing.tapeAction i inp none m q'` at the current state and reads, one step moves
the input head by `inp` and head `i` by `m`, enters `q'`, and changes nothing else.

**Proof sketch.** Use the live-step equation and the published action-field
equations. Only head `i` moves among the work heads, and every tape cell is
preserved. -/
theorem step_of_tapeAction_move {Symbol State : Type*} {k : ℕ} {x : List Symbol}
    (M : MultiTapeTM k Symbol State) (c : Cfg k Symbol State x) {q q' : State} (i : Fin k)
    (inp m : SignType) (hq : c.state = some q)
    (htr : M.tr q c.inputSymbol c.workTapeSymbols = tapeAction i inp none m q') :
    M.step c =
      { c with
        state := some q'
        inputPos := moveInputPos c.inputPos inp
        workTapePos := Function.update c.workTapePos i (c.workTapePos i + m) } := by
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · simp only [Action.apply_state, tapeAction]
  · simp only [Action.apply_inputPos, tapeAction]
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    by_cases hj : j = i
    · subst j
      simp only [tapeAction, ↓reduceIte, Option.getD_none, Function.update_eq_self]
    · simp only [tapeAction, hj, ↓reduceIte, Option.getD_none, Function.update_eq_self]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [Action.apply_workTapePos, tapeAction, ↓reduceIte, Function.update_self]
    · simp only [Action.apply_workTapePos, tapeAction, hj, ↓reduceIte, SignType.coe_zero,
        add_zero, Function.update_of_ne hj]
  · simp only [Action.apply_output, tapeAction, Option.toList_none, List.append_nil]

/-- **One step of a writing one-tape action** (design §12.8a). If the machine's table
gives `Turing.tapeAction i inp (some s) m q'` at the current state and reads, one step
rewrites the scanned cell of tape `i` to `s`, moves the input head by `inp` and head `i`
by `m`, enters `q'`, and changes nothing else.

**Proof sketch.** As for `Turing.step_of_tapeAction_move`, with the written cell. -/
theorem step_of_tapeAction_write {Symbol State : Type*} {k : ℕ} {x : List Symbol}
    (M : MultiTapeTM k Symbol State) (c : Cfg k Symbol State x) {q q' : State} (i : Fin k)
    (inp : SignType) (s : Option Symbol) (m : SignType) (hq : c.state = some q)
    (htr : M.tr q c.inputSymbol c.workTapeSymbols = tapeAction i inp (some s) m q') :
    M.step c =
      { c with
        state := some q'
        inputPos := moveInputPos c.inputPos inp
        workTapes := Function.update c.workTapes i
          (Function.update (c.workTapes i) (c.workTapePos i) s)
        workTapePos := Function.update c.workTapePos i (c.workTapePos i + m) } := by
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · simp only [Action.apply_state, tapeAction]
  · simp only [Action.apply_inputPos, tapeAction]
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    by_cases hj : j = i
    · subst j
      simp only [tapeAction, ↓reduceIte, Option.getD_some, Function.update_self]
    · simp only [tapeAction, hj, ↓reduceIte, Option.getD_none, Function.update_eq_self,
        Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [Action.apply_workTapePos, tapeAction, ↓reduceIte, Function.update_self]
    · simp only [Action.apply_workTapePos, tapeAction, hj, ↓reduceIte, SignType.coe_zero,
        add_zero, Function.update_of_ne hj]
  · simp only [Action.apply_output, tapeAction, Option.toList_none, List.append_nil]

/-- **One step of an input-only action** (design §12.8a). If the machine's table gives
`Turing.inputMoveAction inp q'` at the current state and reads, one step moves the input
head by `inp`, enters `q'`, and changes nothing else. At `inp = 0` (with
`moveInputPos_zero`) this is every live anchor's stationarity.

**Proof sketch.** With no work tapes, compare the state, input and output fields.
Otherwise use the non-writing one-tape step with zero work-head movement;
its head update is the identity. -/
theorem step_of_inputMoveAction {Symbol State : Type*} {k : ℕ} {x : List Symbol}
    (M : MultiTapeTM k Symbol State) (c : Cfg k Symbol State x) {q q' : State}
    (inp : SignType) (hq : c.state = some q)
    (htr : M.tr q c.inputSymbol c.workTapeSymbols = inputMoveAction inp q') :
    M.step c = { c with state := some q', inputPos := moveInputPos c.inputPos inp } := by
  cases k with
  | zero =>
    rw [MultiTapeTM.step_of_some hq, htr]
    apply Cfg.ext_zero_tapes
    · simp only [Action.apply_state, inputMoveAction_eq]
    · simp only [Action.apply_inputPos, inputMoveAction_eq]
    · simp only [Action.apply_output, inputMoveAction_eq, Option.toList_none, List.append_nil]
  | succ k =>
    have ha : inputMoveAction (k := k + 1) (Symbol := Symbol) inp q' =
        tapeAction (0 : Fin (k + 1)) inp none 0 q' := by
      simp only [inputMoveAction_eq, tapeAction, ite_self]
    rw [step_of_tapeAction_move M c (0 : Fin (k + 1)) inp 0 hq (htr.trans ha)]
    simp only [SignType.coe_zero, add_zero, Function.update_eq_self]

/-! ### The field layout -/

/-- **The field layout** (design §12.8a). A list of fields laid out as cells,
consecutive fields separated by one blank cell. A table of records is the same
layout over all its fields, so two consecutive blanks mark its end as long as
no field is empty. -/
def joinFields {Γ : Type*} (fs : List (List Γ)) : List (Option Γ) :=
  List.intercalate [none] (fs.map (List.map some))

/-- **The tape of a field list** (design §12.8a): `Turing.joinFields fs` laid
out from cell `0`, blank at every negative cell and beyond its end. -/
def fieldsTape {Γ : Type*} (fs : List (List Γ)) (z : ℤ) : Option Γ :=
  if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none

/-- **Field offsets** (design §12.8a): the cell at which field `j` of the
layout starts, the total length of the earlier fields with one separator each.
For a nonempty `fs`, at `j = fs.length` it is the span of the whole layout plus
one cell, `(joinFields fs).length + 1`, which is where a further field would
start. The empty layout has offset `0` there, not `1`. -/
def fieldOffset {Γ : Type*} (fs : List (List Γ)) (j : ℕ) : ℕ :=
  ((fs.take j).map (·.length + 1)).sum

/-! #### The layout's base and boundary facts (the specification API, user 2026-10-16)

Consumers read the layout through these equations, not by unfolding its definitions. -/

/-- **The empty layout** (the specification API): no cells. -/
theorem joinFields_nil {Γ : Type*} : joinFields ([] : List (List Γ)) = [] := by
  simp [joinFields, List.intercalate]

/-- **A one-field layout** (the specification API): the field's cells. -/
theorem joinFields_singleton {Γ : Type*} (u : List Γ) : joinFields [u] = u.map some := by
  simp [joinFields, List.intercalate]

/-- **The layout tape inside its range** (the specification API): from cell `0` on, the
layout's cells, blank past its end. -/
theorem fieldsTape_of_nonneg {Γ : Type*} (fs : List (List Γ)) {z : ℤ} (hz : 0 ≤ z) :
    fieldsTape fs z = ((joinFields fs)[z.toNat]?).join := by
  simp [fieldsTape, hz]

/-- **The layout tape left of the origin** (the specification API): blank at every negative
cell. -/
theorem fieldsTape_of_neg {Γ : Type*} (fs : List (List Γ)) {z : ℤ} (hz : z < 0) :
    fieldsTape fs z = none := by
  simp [fieldsTape, not_le.mpr hz]

/-- **The layout tape past its end** (the specification API): blank from cell
`|joinFields fs|` on.

**Proof sketch.** The cell is nonnegative, and its index is past the list. -/
theorem fieldsTape_of_length_le {Γ : Type*} (fs : List (List Γ)) {z : ℤ}
    (hz : ((joinFields fs).length : ℤ) ≤ z) : fieldsTape fs z = none := by
  have h0 : 0 ≤ z := le_trans (Int.natCast_nonneg _) hz
  rw [fieldsTape_of_nonneg fs h0, List.getElem?_eq_none (by omega)]
  rfl

/-- **The empty layout's tape** (the specification API): blank everywhere. -/
theorem fieldsTape_nil {Γ : Type*} (z : ℤ) : fieldsTape ([] : List (List Γ)) z = none := by
  simp [fieldsTape, joinFields_nil]

/-- **The first field's offset** (the specification API): field `0` starts at cell `0`. -/
theorem fieldOffset_zero {Γ : Type*} (fs : List (List Γ)) : fieldOffset fs 0 = 0 := by
  simp [fieldOffset]

/-- **The field layout, one field at a time** (§12.8 fill): two or more fields are the first
field, a separator, and the layout of the rest. -/
theorem joinFields_cons_cons {Γ : Type*} (u v : List Γ) (fs : List (List Γ)) :
    joinFields (u :: v :: fs) = u.map some ++ none :: joinFields (v :: fs) := by
  simp [joinFields, List.intercalate, List.intersperse_cons₂]

/-- **The layout tape past the first field** (§12.8 fill): beyond the first field and its
separator, the tape of `u :: v :: fs` is the tape of `v :: fs`, from relative position `-1`
(the separator itself) on.

**Proof sketch.** `Turing.joinFields_cons_cons`, then `List.getElem?_append_right` at the
shifted index. -/
theorem fieldsTape_cons_shift {Γ : Type*} (u v : List Γ) (fs : List (List Γ)) (z : ℤ)
    (hz : -1 ≤ z) :
    fieldsTape (u :: v :: fs) ((u.length : ℤ) + 1 + z) = fieldsTape (v :: fs) z := by
  unfold fieldsTape
  rw [joinFields_cons_cons, if_pos (by omega)]
  by_cases h0 : 0 ≤ z
  · rw [if_pos h0]
    have he : ((u.length : ℤ) + 1 + z).toNat = u.length + (z.toNat + 1) := by omega
    rw [he, List.getElem?_append_right (by simp)]
    simp
  · rw [if_neg h0]
    have he : ((u.length : ℤ) + 1 + z).toNat = u.length + 0 := by omega
    rw [he, List.getElem?_append_right (by simp)]
    simp

/-- **The next field's offset** (§12.8 fill): field `j + 1` starts one separator after
field `j` ends. -/
theorem fieldOffset_succ {Γ : Type*} (fs : List (List Γ)) (j : ℕ) (hj : j < fs.length) :
    fieldOffset fs (j + 1) = fieldOffset fs j + (fs[j].length + 1) := by
  unfold fieldOffset
  rw [List.take_succ, List.map_append, List.sum_append]
  simp [List.getElem?_eq_getElem hj]

/-- **Offsets past a first field** (§12.8 fill). -/
theorem fieldOffset_cons_succ {Γ : Type*} (u : List Γ) (fs : List (List Γ)) (j : ℕ) :
    fieldOffset (u :: fs) (j + 1) = u.length + 1 + fieldOffset fs j := by
  simp [fieldOffset, List.take_succ_cons]

/-- **The end offset** (§12.8 fill): for a nonempty layout, the offset past the last field
is the layout's length plus one, where a further field would start.

**Proof sketch.** Induct on the fields with `Turing.joinFields_cons_cons` and
`Turing.fieldOffset_cons_succ`. -/
theorem length_joinFields_add_one {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
    (joinFields fs).length + 1 = fieldOffset fs fs.length := by
  induction fs with
  | nil => exact absurd rfl hfs
  | cons u fs ih =>
    cases fs with
    | nil => simp [joinFields, fieldOffset, List.intercalate]
    | cons v fs =>
      have h := ih (List.cons_ne_nil v fs)
      have e1 : (u :: v :: fs).length = (v :: fs).length + 1 := rfl
      rw [joinFields_cons_cons, e1, fieldOffset_cons_succ, ← h]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega

/-- **Every field lies inside the layout** (§12.8 fill): field `j` ends by the layout's end.

**Proof sketch.** Offsets increase with `j` (`Turing.fieldOffset_succ`), and the offset past
the last field is the layout's length plus one (`Turing.length_joinFields_add_one`). -/
theorem fieldOffset_add_length_le {Γ : Type*} (fs : List (List Γ)) (j : ℕ)
    (hj : j < fs.length) : fieldOffset fs j + fs[j].length ≤ (joinFields fs).length := by
  have hne : fs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hend := length_joinFields_add_one fs hne
  have hmono : ∀ i, j + 1 ≤ i → i ≤ fs.length → fieldOffset fs (j + 1) ≤ fieldOffset fs i := by
    intro i h1 h2
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.lt_or_ge (j + 1) (i + 1) with h | h
      · have := ih (by omega) (by omega)
        rw [fieldOffset_succ fs i (by omega)]; omega
      · have : j + 1 = i + 1 := by omega
        rw [this]
  have h1 := hmono fs.length (by omega) le_rfl
  rw [fieldOffset_succ fs j hj] at h1
  omega

/-- **Each field is a framed word** (design §12.8a). In the tape of a field
list, field `j` read from its offset is the delimited word of §12.6: its cells
at relative positions `0, …, |fs[j]| - 1`, and blanks at `-1` and `|fs[j]|`.
So every framed catalog row applies to a field in place.

**Proof sketch.** Induct on `j`. The intercalated list is field `0`, then for
a nonempty tail one separator and the joined tail, so the cells at offset `0`
are field `0` followed by a blank. For `j + 1`, shift by the length of field
`0` plus one and use the induction hypothesis on the tail; the cell before the
offset is the separator, or the negative cell `-1` when `j = 0`. -/
theorem fieldsTape_field {Γ : Type*} (fs : List (List Γ)) (j : ℕ) (hj : j < fs.length) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (fs[j].length : ℤ) →
      fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p := by
  induction j generalizing fs with
  | zero =>
    cases fs with
    | nil => simp at hj
    | cons u fs =>
      intro p hp hlen
      simp only [List.getElem_cons_zero, fieldOffset, List.take_zero, List.map_nil,
        List.sum_nil, Nat.cast_zero, zero_add] at *
      by_cases h0 : 0 ≤ p
      · cases fs with
        | nil =>
          simp [fieldsTape, joinFields, List.intercalate, FinTM.bufferTape, h0]
          cases u[p.toNat]? <;> rfl
        | cons v fs =>
          unfold fieldsTape FinTM.bufferTape
          rw [if_pos h0, if_pos h0, joinFields_cons_cons]
          by_cases hin : p.toNat < u.length
          · rw [List.getElem?_append_left (by simpa using hin)]
            rw [List.getElem?_map]
            cases u[p.toNat]? <;> rfl
          · have he : p.toNat = u.length := by omega
            rw [he, List.getElem?_append_right (by simp)]
            simp
      · simp [fieldsTape, FinTM.bufferTape, h0]
  | succ j ih =>
    cases fs with
    | nil => simp at hj
    | cons u fs =>
      cases fs with
      | nil => simp at hj
      | cons v fs =>
        intro p hp hlen
        simp only [List.getElem_cons_succ] at hlen ⊢
        rw [fieldOffset_cons_succ]
        have hz : -1 ≤ (fieldOffset (v :: fs) j : ℤ) + p := by omega
        rw [show ((u.length + 1 + fieldOffset (v :: fs) j : ℕ) : ℤ) + p =
          (u.length : ℤ) + 1 + ((fieldOffset (v :: fs) j : ℤ) + p) by omega,
          fieldsTape_cons_shift u v fs _ hz]
        exact ih (v :: fs) (by simpa using hj) p hp hlen

/-! ### R8.1 — the framed compare -/

/-- **R8.1, compare, framed, at its exact time** (MIG-11a, user 2026-10-16): as
`Turing.compareTM_run_ofCfg`, with the stop named. From the working phase, with `u` and `v`
delimited at the heads of `fst` and `snd`, the compare reaches `done (decide (u = v))` at exactly
`2 · compareStop u v + 2`, with no verdict earlier and nothing written; the two heads stay within
`[pos - 1, pos + compareStop u v]` and every other head is fixed.

**Proof sketch.** The shared framed trace at the stop of `catalog_compare_stop`, which is
`Turing.compareStop u v` by `Turing.compareStop_unique`. -/
theorem compareTM_run_stop_ofCfg {Symbol : Type*} [DecidableEq Symbol] {k : ℕ}
    {x : List Symbol} (fst snd : Fin k) (hne : fst ≠ snd) (u v : List Symbol)
    (d : Cfg k Symbol FlagPhase x) (hstate : d.state = some FlagPhase.run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + p) = FinTM.bufferTape u p)
    (hv : ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + p) = FinTM.bufferTape v p) :
    (compareTM k fst snd).runFrom d (2 * compareStop u v + 2) =
        { d with state := some (FlagPhase.done (decide (u = v))) } ∧
      (∀ t < 2 * compareStop u v + 2, ∀ b,
        ((compareTM k fst snd).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * compareStop u v + 2 →
        if j = fst ∨ j = snd then
          ((compareTM k fst snd).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (compareStop u v : ℤ))
        else ((compareTM k fst snd).runFrom d t).workTapePos j = d.workTapePos j) := by
  -- D2: the shared framed trace also covers aliased tape indices.
  have _ := hne
  obtain ⟨δ, hδ, hp, hs, he⟩ := catalog_compare_stop u v
  rw [← compareStop_unique hp hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [catalog_compare_trace fst snd u v d hstate hu hv δ hδ hp hs he]
    simp [catalogTrace, show ¬2 * δ + 2 ≤ δ by omega]
  · intro t ht b
    rw [catalog_compare_trace fst snd u v d hstate hu hv δ hδ hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCompareF, catalogCompareR]
    omega
  · intro j t ht
    rw [catalog_compare_trace fst snd u v d hstate hu hv δ hδ hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, Finset.mem_Icc] <;> omega

/-- **R8.1, compare, framed** (design §12.8a; the generic form of the
canonical compare row). From any configuration in the working phase whose
tapes `fst` and `snd` carry delimited words `u` and `v` at their heads, the
compare reaches the verdict anchor `done (decide (u = v))` at exactly
`2δ + 2` for some `δ ≤ min |u| |v|`, the length of the common prefix it
reads, and no verdict anchor earlier. Nothing is written: the finish is the
start configuration with only the control state replaced. Up to the exit the
two heads stay within `[pos - 1, pos + δ]`, and every other head is fixed.
The outer cells, the other tapes, the input position and the output are
arbitrary. It re-derives from the same framed trace as `Turing.compareTM_run_stop_ofCfg`.

**Proof sketch.** Generalize `catalog_compare_trace` over the fixed outer
frame and the two start coordinates. Let `δ` be the first index at which the
words differ or one of them ends, and `δ = |u| = |v|` when `u = v`. The
forward pass takes `δ` matching steps and one turning step, which selects the
verdict. The return pass is guided by `fst`'s intact cells, `δ` of them,
and the left delimiter of `u` supplies the final entry step, so the total is
`2δ + 2`. -/
theorem compareTM_run_ofCfg {Symbol : Type*} [DecidableEq Symbol] {k : ℕ} {x : List Symbol}
    (fst snd : Fin k) (hne : fst ≠ snd) (u v : List Symbol) (d : Cfg k Symbol FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + p) = FinTM.bufferTape u p)
    (hv : ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + p) = FinTM.bufferTape v p) :
    ∃ δ ≤ min u.length v.length,
      (compareTM k fst snd).runFrom d (2 * δ + 2) =
          { d with state := some (FlagPhase.done (decide (u = v))) } ∧
        (∀ t < 2 * δ + 2, ∀ b,
          ((compareTM k fst snd).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
        (∀ (j : Fin k) (t : ℕ), t ≤ 2 * δ + 2 →
          if j = fst ∨ j = snd then
            ((compareTM k fst snd).runFrom d t).workTapePos j ∈
              Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (δ : ℤ))
          else ((compareTM k fst snd).runFrom d t).workTapePos j = d.workTapePos j) := by
  exact ⟨compareStop u v, compareStop_le u v,
    compareTM_run_stop_ofCfg fst snd hne u v d hstate hu hv⟩

/-! ### R8.3 — the seek family -/

/-- **Phase alphabet of the seek family** (design §12.8a, R8.3):
`Turing.skipTM`, `Turing.skipBackTM`, `Turing.seekEndTM` and
`Turing.seekStartTM`. Each machine documents which phases it uses. -/
inductive SeekPhase where
  /-- the main pass -/
  | run
  /-- a blank has just been crossed -/
  | gap
  /-- the backward or returning pass -/
  | back
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- A one-pass routine is the public two-pass trace with a stationary return family.
Proof sketch: specialize the trace, then read its forward segment and fixed tail. -/
private theorem catalog_pass_contract {k : ℕ} {Symbol : Type*} {x : List Symbol} {S : Type*}
    (M : MultiTapeTM k Symbol S) (F : ℕ → Cfg k Symbol S x) (D : Cfg k Symbol S x) (L : ℕ)
    (hF : ∀ r < L, M.step (F r) = F (r + 1)) (hexit : M.step (F L) = D) (hD : M.step D = D)
    (P Q : Cfg k Symbol S x → Prop) (hP : ∀ r ≤ L, P (F r)) (hQ : ∀ r ≤ L, Q (F r))
    (hQD : Q D) :
    M.runFrom (F 0) (L + 1) = D ∧ (∀ t < L + 1, P (M.runFrom (F 0) t)) ∧
      ∀ t ≤ L + 1, Q (M.runFrom (F 0) t) := by
  have h : ∀ t, M.runFrom (F 0) t = if t ≤ L then F t else D := fun t => by
    simpa [catalogTrace] using
      catalog_trace_run M F (fun _ => D) D L hF hexit (fun _ _ => hD) hD hD t
  refine ⟨by rw [h]; simp, fun t ht => ?_, fun t ht => ?_⟩
  · rw [h, if_pos (by omega)]
    exact hP t (by omega)
  · rw [h]
    split_ifs with h1
    · exact hQ t h1
    · exact hQD

/-- A read-only seek's frame with one relative head displacement and one control state. -/
private def catalogSeekCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (d : Cfg k Symbol SeekPhase x) (q : SeekPhase) (z : ℤ) : Cfg k Symbol SeekPhase x :=
  { d with
    state := some q
    workTapePos := Function.update d.workTapePos i (d.workTapePos i + z) }

/-- The public movement step, specialized to the shared seek frame. -/
private theorem catalog_seek_step {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (M : MultiTapeTM k Symbol SeekPhase) (i : Fin k) (d : Cfg k Symbol SeekPhase x)
    (q q' : SeekPhase) (z : ℤ) (m : SignType)
    (htr : M.tr q (catalogSeekCfg i d q z).inputSymbol
      (catalogSeekCfg i d q z).workTapeSymbols = tapeAction i 0 none m q') :
    M.step (catalogSeekCfg i d q z) = catalogSeekCfg i d q' (z + m) := by
  rw [step_of_tapeAction_move M _ i 0 m rfl htr]
  apply Cfg.ext <;> simp [catalogSeekCfg, Function.update_idem, add_assoc]

/-- **R8.3, skip** (design §12.8a). Move the head of tape `i` right over the
word under it and one cell past its right delimiter, writing nothing. In the
field layout this moves from the first cell of a field to the first cell of
the next. Phases `run` and `done`; the others are stationary and unused. -/
def skipTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SeekPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some _ => tapeAction i 0 none .pos .run
      | none => tapeAction i 0 none .pos .done
    | q => inputMoveAction 0 q

/-! #### R8.3b — the lockstep walk (design §13d, G4's ruler; user 2026-10-15)

The G4 zone rows (`Build/ZoneRebalance`) move the zoned head by a measured distance and leave it
there: to cross home to the mirror zone, to stand on a slot at an offset inside a zone, and to
start a write-back at an offset. The measure is a word on the scratch tape, the ruler. No other
row does this: the mapped copy and transfer move their heads in lockstep but return them, and the
seek family moves one head (the G4 hosts survey, `audits/evidence/s13d/g4-hosts/`). The walk
moves a set of heads together over the word under one of them and one cell past its delimiter,
in either direction, writing nothing. `Turing.skipTM` is its one-tape rightward instance: the
two tables coincide (`Turing.skipTM_eq_walkTM`). -/

/-- **R8.3b, the lockstep walk** (design §13d, G4). While tape `src` reads a nonblank cell, move
every head in `moved` one cell in direction `dir`; at the first blank move them once more and stop
in `done`. Nothing is written and the input head stays. Phases `run` and `done`; the others are
stationary and unused. -/
def walkTM {Symbol : Type*} (k : ℕ) (src : Fin k) (moved : Fin k → Prop) [DecidablePred moved]
    (dir : SignType) : MultiTapeTM k Symbol SeekPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w src with
      | some _ => ⟨0, fun j => if moved j then (none, dir) else (none, 0), none, some .run⟩
      | none => ⟨0, fun j => if moved j then (none, dir) else (none, 0), none, some .done⟩
    | q => inputMoveAction 0 q

/-- **The skip is the one-tape rightward walk**: `Turing.skipTM`'s table is the walk's with
`moved := (· = i)` and `dir := .pos`. -/
theorem skipTM_eq_walkTM {Symbol : Type*} (k : ℕ) (i : Fin k) :
    (skipTM k i : MultiTapeTM k Symbol SeekPhase) = walkTM k i (· = i) .pos :=
  rfl

/-- **R8.3b, the lockstep walk, framed** (design §13d, G4). Let `src` be among the moved tapes,
and let tape `src` hold the word `w` read along `dir` from its head: the cell `p` steps along holds
`w`'s letter `p` for `p < |w|`, and the cell `|w|` steps along is blank. Then the walk reaches
`done` at exactly `|w| + 1` and not earlier, with every moved head `|w| + 1` cells along `dir` and
nothing else changed. The cells under the other moved heads are never read, so they are
arbitrary: the walk carries those heads by the ruler `w`. At every time `t` up to the exit each
moved head is exactly `t` cells along, and every other head is fixed. At `dir = 0` the hypothesis
forces `w = []`. At `moved := (· = i)` and `dir := .pos` this is `Turing.skipTM_run_ofCfg`.

**Proof sketch.** The forward configurations are `d` in `run` with every moved head `r` cells
along, for `r ≤ |w|`: one step per nonblank cell of `w`, and at the blank one more step into
`done`, which is stationary. `Turing.catalog_trace_run` with the stationary return family
`fun _ => D` gives the run, and the three clauses are read off it. -/
theorem walkTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (src : Fin k)
    (moved : Fin k → Prop) [DecidablePred moved] (hsrc : moved src) (dir : SignType)
    (w : List Symbol) (d : Cfg k Symbol SeekPhase x) (hstate : d.state = some .run)
    (hw : ∀ p : ℕ, p ≤ w.length →
      d.workTapes src (d.workTapePos src + (dir : ℤ) * p) = FinTM.bufferTape w p) :
    (walkTM k src moved dir).runFrom d (w.length + 1) =
        { d with
          state := some .done
          workTapePos := fun j =>
            d.workTapePos j + if moved j then (dir : ℤ) * ((w.length + 1 : ℕ) : ℤ) else 0 } ∧
      (∀ t < w.length + 1, ((walkTM k src moved dir).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ w.length + 1 →
        ((walkTM k src moved dir).runFrom d t).workTapePos j =
          d.workTapePos j + if moved j then (dir : ℤ) * (t : ℤ) else 0) := by
  let M := walkTM (Symbol := Symbol) k src moved dir
  let F := fun r : ℕ => ({ d with
    workTapePos := fun j => d.workTapePos j + if moved j then (dir : ℤ) * (r : ℤ) else 0 } :
      Cfg k Symbol SeekPhase x)
  let D : Cfg k Symbol SeekPhase x := { d with
    state := some .done
    workTapePos := fun j =>
      d.workTapePos j + if moved j then (dir : ℤ) * ((w.length + 1 : ℕ) : ℤ) else 0 }
  have h0 : F 0 = d := by
    apply Cfg.ext <;> simp [F]
  -- one step of a `run` configuration whose table entry moves the moved heads into `q`
  have hstep (r : ℕ) (q : SeekPhase)
      (htr : M.tr .run (F r).inputSymbol (F r).workTapeSymbols =
        ⟨0, fun j => if moved j then (none, dir) else (none, 0), none, some q⟩) :
      M.step (F r) = { F (r + 1) with state := some q } := by
    have hst : (F r).state = some .run := hstate
    rw [MultiTapeTM.step_of_some hst, htr]
    apply Cfg.ext
    · simp only [Action.apply_state]
    · simp only [Action.apply_inputPos, F, moveInputPos_zero]
    · funext j
      rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      by_cases hj : moved j
      · simp only [F, hj, if_true, Option.getD_none, Function.update_eq_self]
      · simp only [F, hj, if_false, Option.getD_none, Function.update_eq_self]
    · funext j
      by_cases hj : moved j
      · simp only [Action.apply_workTapePos, F, hj, if_true]
        push_cast
        ring
      · simp only [Action.apply_workTapePos, F, hj, if_false, SignType.coe_zero, add_zero]
    · simp only [Action.apply_output, F, Option.toList_none, List.append_nil]
  have hsym (r : ℕ) : (F r).workTapeSymbols src = d.workTapes src
      (d.workTapePos src + (dir : ℤ) * (r : ℤ)) := by
    simp [F, Cfg.workTapeSymbols_eq, hsrc]
  have hF (r : ℕ) (hr : r < w.length) : M.step (F r) = F (r + 1) := by
    have hs : (F r).workTapeSymbols src = some w[r] := by
      rw [hsym, hw r (by omega)]
      simp [FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
    rw [hstep r .run (by simp only [M, walkTM, hs])]
    apply Cfg.ext <;> simp [F, hstate]
  have hexit : M.step (F w.length) = D := by
    have hs : (F w.length).workTapeSymbols src = none := by
      rw [hsym, hw w.length le_rfl]
      simp [FinTM.bufferTape_nat]
    exact (hstep w.length .done (by simp only [M, walkTM, hs])).trans rfl
  have hD : M.step D = D := by
    rw [step_of_inputMoveAction M D 0 rfl rfl, moveInputPos_zero]
  have h (t : ℕ) : M.runFrom d t = if t ≤ w.length then F t else D := by
    rw [← h0]
    simpa [catalogTrace] using
      catalog_trace_run M F (fun _ => D) D w.length hF hexit (fun _ _ => hD) hD hD t
  refine ⟨?_, fun t ht => ?_, fun j t ht => ?_⟩
  · rw [h, if_neg (by omega)]
  · rw [h, if_pos (by omega)]
    simp [F, hstate]
  · rw [h]
    by_cases ht' : t ≤ w.length
    · simp only [if_pos ht', F]
    · have : t = w.length + 1 := by omega
      subst this
      simp only [if_neg ht', D]

/-- **R8.3, skip, framed** (design §12.8a). If tape `i` holds the word `w`
from its head, with a blank right delimiter at relative position `|w|`, the
skip reaches `done` at exactly `|w| + 1` and not earlier, with the head of
tape `i` at `pos + |w| + 1` and nothing else changed. No left delimiter is
needed, and the cells beyond the delimiter are arbitrary. Up to the exit the
head of tape `i` stays within `[pos, pos + |w| + 1]`, and every other head is
fixed.

**Proof sketch.** The skip is the one-tape rightward walk (`Turing.skipTM_eq_walkTM`), so this
is `Turing.walkTM_run_ofCfg` at `moved := (· = i)`, `dir := .pos`, with the moved head's exact
position read as its interval. -/
theorem skipTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (w : List Symbol) (d : Cfg k Symbol SeekPhase x) (hstate : d.state = some .run)
    (hw : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (skipTM k i).runFrom d (w.length + 1) =
        { d with
          state := some .done
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i + w.length + 1) } ∧
      (∀ t < w.length + 1, ((skipTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ w.length + 1 →
        if j = i then
          ((skipTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + w.length + 1)
        else ((skipTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨h1, h2, h3⟩ := walkTM_run_ofCfg i (· = i) rfl .pos w d hstate
    (fun p hp => by simpa using hw p (by omega) (by omega))
  rw [skipTM_eq_walkTM]
  refine ⟨h1.trans ?_, h2, fun j t ht => ?_⟩
  · apply Cfg.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst hj
      simp
      ring
    · simp [hj]
  · rw [h3 j t ht]
    by_cases hj : j = i
    · subst hj
      simp [Finset.mem_Icc]
      omega
    · simp [hj]

/-- **R8.3, skip back** (design §12.8a). The inverse of `Turing.skipTM`: from
the first cell of a field, move the head of tape `i` to the first cell of the
previous field. `run` steps off the current cell, `gap` steps over the blank
separator, `back` walks left over the previous word, and its left delimiter
turns the head into `done`. Nothing is written. -/
def skipBackTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SeekPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run => tapeAction i 0 none .neg .gap
    | .gap => tapeAction i 0 none .neg .back
    | .back =>
      match w i with
      | some _ => tapeAction i 0 none .neg .back
      | none => tapeAction i 0 none .pos .done
    | .done => inputMoveAction 0 .done

/-- **R8.3, skip back, framed** (design §12.8a). If the delimited word `u` of
tape `i` ends one blank before the head, that is, `u` starts at
`pos - |u| - 1`, then skip back reaches `done` at exactly `|u| + 3` and not
earlier, with the head of tape `i` at `pos - |u| - 1` and nothing else
changed. The current cell and the cells left of `u`'s delimiter are
arbitrary. Up to the exit the head of tape `i` stays within
`[pos - |u| - 2, pos]`, and every other head is fixed. After
`Turing.skipTM_run_ofCfg` over `u`, this returns the head to where it was.

**Proof sketch.** Two unconditional left steps reach the last cell of `u`, or
its left delimiter when `u = []`. Then `|u|` left steps in `back` cross `u`,
and the delimiter at relative position `-1` is one right step into `done`. -/
theorem skipBackTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (u : List Symbol) (d : Cfg k Symbol SeekPhase x) (hstate : d.state = some .run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes i (d.workTapePos i - u.length - 1 + p) = FinTM.bufferTape u p) :
    (skipBackTM k i).runFrom d (u.length + 3) =
        { d with
          state := some .done
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i - u.length - 1) } ∧
      (∀ t < u.length + 3, ((skipBackTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ u.length + 3 →
        if j = i then
          ((skipBackTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - u.length - 2) (d.workTapePos j)
        else ((skipBackTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  let F := fun r : ℕ => catalogSeekCfg i d
    (if r = 0 then .run else if r = 1 then .gap else .back) (-(r : ℤ))
  let D : Cfg k Symbol SeekPhase x := { d with
    state := some .done
    workTapePos := Function.update d.workTapePos i (d.workTapePos i - u.length - 1) }
  have h0 : F 0 = d := by
    apply Cfg.ext <;> simp [F, catalogSeekCfg, hstate]
  have hF (r : ℕ) (hr : r < u.length + 2) : (skipBackTM k i).step (F r) = F (r + 1) := by
    rcases r with _ | r
    · simpa [F, SignType.cast] using
        catalog_seek_step (skipBackTM k i) i d .run .gap 0 .neg rfl
    rcases r with _ | r
    · simpa [F, SignType.cast] using
        catalog_seek_step (skipBackTM k i) i d .gap .back (-1) .neg rfl
    have hp0 : 0 ≤ (u.length : ℤ) - r - 1 := by omega
    have hp : ((u.length : ℤ) - r - 1).toNat < u.length := by omega
    have hs : (catalogSeekCfg i d .back (-((r + 2 : ℕ) : ℤ))).workTapeSymbols i =
        some u[((u.length : ℤ) - r - 1).toNat] := by
      have h := hu ((u.length : ℤ) - r - 1) (by omega) (by omega)
      rw [show d.workTapePos i - u.length - 1 + ((u.length : ℤ) - r - 1) =
        d.workTapePos i + (-((r + 2 : ℕ) : ℤ)) by omega] at h
      simpa only [catalogSeekCfg, Cfg.workTapeSymbols, Function.update_self,
        FinTM.bufferTape, if_pos hp0, List.getElem?_eq_getElem hp] using h
    have h := catalog_seek_step (skipBackTM k i) i d .back .back
      (-((r + 2 : ℕ) : ℤ)) .neg (by simp only [skipBackTM, hs])
    have hz : -((r + 2 : ℕ) : ℤ) + (SignType.neg : ℤ) = -((r + 3 : ℕ) : ℤ) := by
      simp only [SignType.cast]
      omega
    rw [hz] at h
    change (skipBackTM k i).step (catalogSeekCfg i d .back (-((r + 2 : ℕ) : ℤ))) =
      catalogSeekCfg i d .back (-((r + 3 : ℕ) : ℤ))
    exact h
  have hexit : (skipBackTM k i).step (F (u.length + 2)) = D := by
    have hs : (catalogSeekCfg i d .back (-((u.length + 2 : ℕ) : ℤ))).workTapeSymbols i = none := by
      have h := hu (-1) (by omega) (by omega)
      rw [show d.workTapePos i - u.length - 1 + (-1) =
        d.workTapePos i + (-((u.length + 2 : ℕ) : ℤ)) by omega] at h
      simpa [catalogSeekCfg, Cfg.workTapeSymbols] using h
    have h := catalog_seek_step (skipBackTM k i) i d .back .done
      (-((u.length + 2 : ℕ) : ℤ)) .pos (by simp only [skipBackTM, hs])
    change (skipBackTM k i).step (catalogSeekCfg i d .back (-((u.length + 2 : ℕ) : ℤ))) = D
    rw [h]
    apply Cfg.ext <;> simp [D, catalogSeekCfg, SignType.cast]
    congr 1
    omega
  have hD : (skipBackTM k i).step D = D := by
    rw [step_of_inputMoveAction (skipBackTM k i) D 0 rfl rfl, moveInputPos_zero]
  have result := catalog_pass_contract (skipBackTM k i) F D (u.length + 2) hF hexit hD
    (fun c => c.state ≠ some .done)
    (fun c => ∀ j : Fin k, if j = i then
      c.workTapePos j ∈ Finset.Icc (d.workTapePos j - u.length - 2) (d.workTapePos j)
      else c.workTapePos j = d.workTapePos j)
    (by intro r _; simp only [F, catalogSeekCfg]; split_ifs <;> simp)
    (by
      intro r hr j
      rcases eq_or_ne j i with rfl | hj
      · simp [F, catalogSeekCfg, Finset.mem_Icc]; omega
      · simp [F, catalogSeekCfg, hj])
    (by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [D, Finset.mem_Icc]; omega
      · simp [D, hj])
  rw [h0] at result
  exact ⟨result.1, result.2.1, fun j t ht => result.2.2 t ht j⟩

/-- Nonempty fields admit no adjacent blanks strictly before the terminal pair.
Proof sketch: an interior first-field cell is nonblank; its separator is followed by
the next field's first cell; beyond it, shift to the tail and use induction. -/
private theorem fieldsTape_no_double_blank {Γ : Type*} (ws : List (List Γ))
    (hws : ∀ u ∈ ws, u ≠ []) (z : ℤ) (hz : 0 ≤ z)
    (hend : z + 1 < (fieldOffset ws ws.length : ℤ)) :
    ¬(fieldsTape ws z = none ∧ fieldsTape ws (z + 1) = none) := by
  induction ws generalizing z with
  | nil => simp [fieldOffset] at hend; omega
  | cons u ws ih =>
    have hu : u ≠ [] := hws u (by simp)
    have hul : 0 < u.length := List.length_pos_iff.mpr hu
    have htail : ∀ v ∈ ws, v ≠ [] := fun v hv => hws v (by simp [hv])
    by_cases hin : z < u.length
    · intro hblank
      have h := fieldsTape_field (u :: ws) 0 (by simp) z (by omega) (by simpa using hin.le)
      simp only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero,
        zero_add, List.getElem_cons_zero] at h
      rw [h, FinTM.bufferTape, if_pos hz,
        List.getElem?_eq_getElem (by omega : z.toNat < u.length)] at hblank
      exact Option.noConfusion hblank.1
    · cases ws with
      | nil => simp [fieldOffset] at hend; omega
      | cons v ws =>
        have hoff := fieldOffset_cons_succ u (v :: ws) (v :: ws).length
        have hlen : (u :: v :: ws).length = (v :: ws).length + 1 := rfl
        rw [hlen, hoff] at hend
        by_cases he : z = (u.length : ℤ)
        · intro hblank
          have h := fieldsTape_field (v :: ws) 0 (by simp) 0 (by omega) (by simp)
          have hv : 0 < v.length := List.length_pos_iff.mpr (htail v (by simp))
          simp only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero,
            zero_add, List.getElem_cons_zero] at h
          rw [he, show (u.length : ℤ) + 1 = (u.length : ℤ) + 1 + 0 by omega,
            fieldsTape_cons_shift u v ws 0 (by omega), h] at hblank
          simpa [FinTM.bufferTape, List.getElem?_eq_getElem hv] using hblank.2
        · have hshift : 0 ≤ z - ((u.length : ℤ) + 1) := by omega
          have h := ih htail (z - ((u.length : ℤ) + 1)) hshift (by omega)
          intro hblank
          apply h
          constructor
          · rw [← fieldsTape_cons_shift u v ws _ (by omega)]
            convert hblank.1 using 1
            congr 1
            omega
          · rw [← fieldsTape_cons_shift u v ws _ (by omega)]
            convert hblank.2 using 1
            congr 1
            omega

/-- **R8.3, seek to the end of a table** (design §12.8a, decision O5). Move the
head of tape `i` right across blank-separated fields until two consecutive
blank cells, and stop on the second, where a further field would start.
`run` crosses field cells, `gap` follows a single blank, and a second blank
enters `done` without moving. Nothing is written. -/
def seekEndTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SeekPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some _ => tapeAction i 0 none .pos .run
      | none => tapeAction i 0 none .pos .gap
    | .gap =>
      match w i with
      | some _ => tapeAction i 0 none .pos .run
      | none => inputMoveAction 0 .done
    | q => inputMoveAction 0 q

/-- **R8.3, seek to the end, framed** (design §12.8a). Let tape `i` hold, from
its head, a nonempty list `ws` of nonempty fields in the field layout, followed
by two blank cells. Write `D = fieldOffset ws |ws|` for the span of the layout
plus one. Then the seek reaches `done` at exactly `D + 1` and not earlier, with
the head of tape `i` at `pos + D` and nothing else changed. The cells beyond
`pos + D` are arbitrary. Up to the exit the head stays within
`[pos, pos + D]`, and every other head is fixed. The fields must be nonempty,
since an empty field is a double blank; `ws ≠ []` excludes the empty table,
whose end is its start.

**Proof sketch.** Induct on `ws`. A field `u` is `|u|` right steps in `run`;
its terminating blank is one right step into `gap`; the next cell is the first
cell of the next field, one right step back into `run`, or the second blank,
one stationary step into `done`. The per-field cost `|u| + 1` sums to `D`. -/
theorem seekEndTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (ws : List (List Symbol)) (hne : ws ≠ []) (hws : ∀ u ∈ ws, u ≠ [])
    (d : Cfg k Symbol SeekPhase x) (hstate : d.state = some .run)
    (hw : ∀ p : ℤ, 0 ≤ p → p ≤ (fieldOffset ws ws.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = fieldsTape ws p) :
    (seekEndTM k i).runFrom d (fieldOffset ws ws.length + 1) =
        { d with
          state := some .done
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i + fieldOffset ws ws.length) } ∧
      (∀ t < fieldOffset ws ws.length + 1,
        ((seekEndTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ fieldOffset ws ws.length + 1 →
        if j = i then
          ((seekEndTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + fieldOffset ws ws.length)
        else ((seekEndTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  classical
  let L := fieldOffset ws ws.length
  let F := fun r : ℕ => catalogSeekCfg i d
    (if r = 0 then .run else if fieldsTape ws ((r : ℤ) - 1) = none then .gap else .run) r
  let D : Cfg k Symbol SeekPhase x := { d with
    state := some .done
    workTapePos := Function.update d.workTapePos i (d.workTapePos i + L) }
  have hlength : (joinFields ws).length + 1 = L := length_joinFields_add_one ws hne
  have hpos : 0 < L := by omega
  have endblank (p : ℤ) (hp : (L : ℤ) - 1 ≤ p) : fieldsTape ws p = none := by
    unfold fieldsTape
    split_ifs with h0
    · rw [List.getElem?_eq_none (by omega)]
      rfl
    · rfl
  have read (q : SeekPhase) (r : ℕ) (hr : r ≤ L) :
      (catalogSeekCfg i d q r).workTapeSymbols i = fieldsTape ws r := by
    simpa [catalogSeekCfg, Cfg.workTapeSymbols] using hw r (by omega) (by omega)
  have h0 : F 0 = d := by
    apply Cfg.ext <;> simp [F, catalogSeekCfg, hstate]
  have hF (r : ℕ) (hr : r < L) : (seekEndTM k i).step (F r) = F (r + 1) := by
    let q : SeekPhase := if r = 0 then .run else
      if fieldsTape ws ((r : ℤ) - 1) = none then .gap else .run
    have htr : (seekEndTM k i).tr q (catalogSeekCfg i d q r).inputSymbol
        (catalogSeekCfg i d q r).workTapeSymbols =
        tapeAction i 0 none .pos (if fieldsTape ws r = none then .gap else .run) := by
      cases hc : fieldsTape ws (r : ℤ) with
      | none =>
        have hq : q = .run := by
          by_cases hr0 : r = 0
          · simp [q, hr0]
          · have hp : fieldsTape ws ((r : ℤ) - 1) ≠ none := by
              intro hb
              exact fieldsTape_no_double_blank ws hws ((r : ℤ) - 1) (by omega)
                (by omega) ⟨hb, by simpa using hc⟩
            simp [q, hr0, hp]
        rw [hq]
        simp [seekEndTM, read _ r hr.le, hc]
      | some γ =>
        have hq : q = .run ∨ q = .gap := by
          dsimp [q]
          split_ifs <;> simp
        rcases hq with hq | hq <;> rw [hq] <;> simp [seekEndTM, read _ r hr.le, hc]
    have h := catalog_seek_step (seekEndTM k i) i d q
      (if fieldsTape ws r = none then .gap else .run) r .pos htr
    simpa [F, q, SignType.pos_eq_one,
      show ((r + 1 : ℕ) : ℤ) - 1 = r by omega] using h
  have hexit : (seekEndTM k i).step (F L) = D := by
    have hs : (F L).workTapeSymbols i = none := by
      simp only [F]
      rw [read _ L le_rfl, endblank L (by omega)]
    have hstateF : (F L).state = some .gap := by
      simp [F, catalogSeekCfg, Nat.ne_of_gt hpos, endblank _ le_rfl]
    rw [step_of_inputMoveAction (seekEndTM k i) (F L) (q' := .done) 0 hstateF
      (by simp only [seekEndTM, hs]), moveInputPos_zero]
    rfl
  have hD : (seekEndTM k i).step D = D := by
    rw [step_of_inputMoveAction (seekEndTM k i) D 0 rfl rfl, moveInputPos_zero]
  have result := catalog_pass_contract (seekEndTM k i) F D L hF hexit hD
    (fun c => c.state ≠ some .done)
    (fun c => ∀ j : Fin k, if j = i then
      c.workTapePos j ∈ Finset.Icc (d.workTapePos j) (d.workTapePos j + L)
      else c.workTapePos j = d.workTapePos j)
    (by intro r _; simp only [F, catalogSeekCfg]; split_ifs <;> simp)
    (by
      intro r hr j
      rcases eq_or_ne j i with rfl | hj
      · simp [F, catalogSeekCfg, Finset.mem_Icc]; omega
      · simp [F, catalogSeekCfg, hj])
    (by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [D, Finset.mem_Icc]
      · simp [D, hj])
  rw [h0] at result
  exact ⟨result.1, result.2.1, fun j t ht => result.2.2 t ht j⟩

/-- **R8.3, seek to the start of a table** (design §12.8a, decision O5). From
a nonblank cell, move the head of tape `i` left across blank-separated fields
until two consecutive blank cells, then return right to the first cell after
them. `run` crosses field cells, `gap` follows a single blank, a second blank
turns into `back`, and `back` steps right into `done`. Nothing is written. -/
def seekStartTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SeekPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some _ => tapeAction i 0 none .neg .run
      | none => tapeAction i 0 none .neg .gap
    | .gap =>
      match w i with
      | some _ => tapeAction i 0 none .neg .run
      | none => tapeAction i 0 none .pos .back
    | .back => tapeAction i 0 none .pos .done
    | .done => inputMoveAction 0 .done

/-- **R8.3, seek to the start, framed** (design §12.8a). Let the head of tape
`i` be on a nonblank cell, preceded by a list `ws` of nonempty fields in the
field layout, each followed by its blank separator, so that the layout of `ws`
starts at `pos - D` with `D = fieldOffset ws |ws|`, and preceded in turn by two
blank cells. Then the seek reaches `done` at exactly `D + 4` and not earlier,
with the head of tape `i` at `pos - D`, the start of the table, and nothing
else changed. At `ws = []` the head is already at the start, and the run takes
`4` steps. The cells from `pos + 1` on and before `pos - D - 2` are arbitrary.
Up to the exit the head stays within `[pos - D - 2, pos]`, and every other
head is fixed.

**Proof sketch.** The current cell is one left step in `run`. Then induct on
`ws` from its last field: its separator is one left step into `gap`, and each
of its cells one left step in `run`. The two blanks before the table are one
left step into `gap` and one right step into `back`, and `back` is one right
step into `done`. The left steps number `D + 2`. -/
theorem seekStartTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (ws : List (List Symbol)) (hws : ∀ u ∈ ws, u ≠ [])
    (d : Cfg k Symbol SeekPhase x) (hstate : d.state = some .run)
    (hcur : d.workTapes i (d.workTapePos i) ≠ none)
    (hw : ∀ p : ℤ, -2 ≤ p → p < (fieldOffset ws ws.length : ℤ) →
      d.workTapes i (d.workTapePos i - fieldOffset ws ws.length + p) = fieldsTape ws p) :
    (seekStartTM k i).runFrom d (fieldOffset ws ws.length + 4) =
        { d with
          state := some .done
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i - fieldOffset ws ws.length) } ∧
      (∀ t < fieldOffset ws ws.length + 4,
        ((seekStartTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ fieldOffset ws ws.length + 4 →
        if j = i then
          ((seekStartTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - fieldOffset ws ws.length - 2) (d.workTapePos j)
        else ((seekStartTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  classical
  let L := fieldOffset ws ws.length
  let phase := fun r : ℕ => if r = 0 then SeekPhase.run else
    if d.workTapes i (d.workTapePos i - r + 1) = none then .gap else .run
  let F := fun r : ℕ => if r ≤ L + 2 then catalogSeekCfg i d (phase r) (-(r : ℤ))
    else catalogSeekCfg i d .back (-(L : ℤ) - 1)
  let D : Cfg k Symbol SeekPhase x := { d with
    state := some .done
    workTapePos := Function.update d.workTapePos i (d.workTapePos i - L) }
  have first (hL : 0 < L) : fieldsTape ws 0 ≠ none := by
    cases ws with
    | nil => simp [L, fieldOffset] at hL
    | cons u us =>
      have hu : 0 < u.length := List.length_pos_iff.mpr (hws u (by simp))
      have h := fieldsTape_field (u :: us) 0 (by simp) 0 (by omega) (by simp)
      simp only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero,
        zero_add, List.getElem_cons_zero] at h
      rw [h]
      simp [FinTM.bufferTape, List.getElem?_eq_getElem hu]
  have blank (p : ℤ) (hp : p < 0) (hlo : -2 ≤ p) :
      d.workTapes i (d.workTapePos i - L + p) = none := by
    rw [hw p hlo (by omega)]
    simp [fieldsTape, show ¬0 ≤ p by omega]
  have noearly (r : ℕ) (hr : r ≤ L + 1) (hrpos : 0 < r) :
      ¬(d.workTapes i (d.workTapePos i - r) = none ∧
        d.workTapes i (d.workTapePos i - r + 1) = none) := by
    intro hb
    by_cases hr1 : r = 1
    · subst r
      exact hcur (by simpa using hb.2)
    have ht0 := hw ((L : ℤ) - r) (by omega) (by omega)
    have ht1 := hw ((L : ℤ) - r + 1) (by omega) (by omega)
    rw [show d.workTapePos i - L + ((L : ℤ) - r) = d.workTapePos i - r by omega] at ht0
    rw [show d.workTapePos i - L + ((L : ℤ) - r + 1) = d.workTapePos i - r + 1 by omega] at ht1
    have hb0 := ht0.symm.trans hb.1
    have hb1 := ht1.symm.trans hb.2
    by_cases he : r = L + 1
    · have hz : (L : ℤ) - r + 1 = 0 := by omega
      rw [hz] at hb1
      exact first (by omega) hb1
    · exact fieldsTape_no_double_blank ws hws ((L : ℤ) - r) (by omega) (by omega) ⟨hb0, hb1⟩
  have read (q : SeekPhase) (r : ℕ) :
      (catalogSeekCfg i d q (-(r : ℤ))).workTapeSymbols i =
        d.workTapes i (d.workTapePos i - r) := by
    simp [catalogSeekCfg, Cfg.workTapeSymbols, sub_eq_add_neg]
  have h0 : F 0 = d := by
    apply Cfg.ext <;> simp [F, phase, catalogSeekCfg, hstate]
  have hF (r : ℕ) (hr : r < L + 3) : (seekStartTM k i).step (F r) = F (r + 1) := by
    by_cases hreg : r < L + 2
    · let q' : SeekPhase := if d.workTapes i (d.workTapePos i - r) = none then .gap else .run
      have htr : (seekStartTM k i).tr (phase r) (catalogSeekCfg i d (phase r) (-(r : ℤ))).inputSymbol
          (catalogSeekCfg i d (phase r) (-(r : ℤ))).workTapeSymbols = tapeAction i 0 none .neg q' := by
        cases hc : d.workTapes i (d.workTapePos i - r) with
        | none =>
          have hq : phase r = .run := by
            by_cases hr0 : r = 0
            · simp [phase, hr0]
            · have hp : d.workTapes i (d.workTapePos i - r + 1) ≠ none := by
                intro hp
                exact noearly r (by omega) (by omega) ⟨hc, hp⟩
              simp [phase, hr0, hp]
          rw [hq]
          simp [seekStartTM, read, hc, q']
        | some γ =>
          have hq : phase r = .run ∨ phase r = .gap := by
            dsimp [phase]
            split_ifs <;> simp
          rcases hq with hq | hq <;> rw [hq] <;> simp [seekStartTM, read, hc, q']
      have h := catalog_seek_step (seekStartTM k i) i d (phase r) q' (-(r : ℤ)) .neg htr
      have hz : -(r : ℤ) + (SignType.neg : ℤ) = -((r + 1 : ℕ) : ℤ) := by
        simp [SignType.cast]
        omega
      rw [hz] at h
      have hp : phase (r + 1) = q' := by
        simp only [phase, show r + 1 ≠ 0 by omega, if_false]
        rw [show d.workTapePos i - ((r + 1 : ℕ) : ℤ) + 1 = d.workTapePos i - r by omega]
      simpa only [F, if_pos (show r ≤ L + 2 by omega),
        if_pos (show r + 1 ≤ L + 2 by omega), hp] using h
    · have he : r = L + 2 := by omega
      subst r
      have hphase : phase (L + 2) = .gap := by
        have hb := blank (-1) (by omega) (by omega)
        rw [show d.workTapePos i - L + (-1) = d.workTapePos i - ((L + 2 : ℕ) : ℤ) + 1 by omega] at hb
        simp only [Nat.cast_add, Nat.cast_ofNat] at hb
        simp [phase, hb]
      have hs : (catalogSeekCfg i d .gap (-((L + 2 : ℕ) : ℤ))).workTapeSymbols i = none := by
        rw [read]
        have hb := blank (-2) (by omega) (by omega)
        convert hb using 1
        congr 1
        omega
      have h := catalog_seek_step (seekStartTM k i) i d .gap .back (-((L + 2 : ℕ) : ℤ)) .pos
        (by simp only [seekStartTM, hs])
      have hz : -((L + 2 : ℕ) : ℤ) + (SignType.pos : ℤ) = -(L : ℤ) - 1 := by
        simp only [SignType.cast]
        omega
      rw [hz] at h
      simpa [F, hphase] using h
  have hexit : (seekStartTM k i).step (F (L + 3)) = D := by
    have h := catalog_seek_step (seekStartTM k i) i d .back .done (-(L : ℤ) - 1) .pos rfl
    simp only [F, show ¬L + 3 ≤ L + 2 by omega, if_false]
    rw [h]
    apply Cfg.ext <;> simp [D, catalogSeekCfg, SignType.cast]
    congr 1
  have hD : (seekStartTM k i).step D = D := by
    rw [step_of_inputMoveAction (seekStartTM k i) D 0 rfl rfl, moveInputPos_zero]
  have result := catalog_pass_contract (seekStartTM k i) F D (L + 3) hF hexit hD
    (fun c => c.state ≠ some .done)
    (fun c => ∀ j : Fin k, if j = i then
      c.workTapePos j ∈ Finset.Icc (d.workTapePos j - L - 2) (d.workTapePos j)
      else c.workTapePos j = d.workTapePos j)
    (by intro r _; dsimp [F]; split_ifs <;> simp [catalogSeekCfg, phase]; split_ifs <;> simp)
    (by
      intro r hr j
      rcases eq_or_ne j i with rfl | hj
      · dsimp [F]; split_ifs <;> simp [catalogSeekCfg, Finset.mem_Icc] <;> omega
      · simp only [if_neg hj]
        dsimp [F]
        split_ifs <;> simp [catalogSeekCfg, hj])
    (by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [D, Finset.mem_Icc]
      · simp [D, hj])
  rw [h0] at result
  exact ⟨result.1, result.2.1, fun j t ht => result.2.2 t ht j⟩

/-! ### R8.2 — the two-pass scan (G2 core) -/

/-- **Left-to-right Mealy transduction** (design §12.8a, R8.2). Run the
finite-state transducer `δ` over `w` from state `a`: each cell is rewritten
by `δ`'s output and the state advances. Returns the final state and the
rewritten word. -/
def mealyRun {A Γ : Type*} (δ : A → Γ → A × Γ) : A → List Γ → A × List Γ
  | a, [] => (a, [])
  | a, γ :: w =>
    let r := δ a γ
    let s := mealyRun δ r.1 w
    (s.1, r.2 :: s.2)

/-- Mealy runs split over an append (the per-cell step of both passes of the trace). -/
private theorem mealyRun_append {A Γ : Type*} (δ : A → Γ → A × Γ) (a : A) (l₁ l₂ : List Γ) :
    mealyRun δ a (l₁ ++ l₂) =
      ((mealyRun δ (mealyRun δ a l₁).1 l₂).1,
        (mealyRun δ a l₁).2 ++ (mealyRun δ (mealyRun δ a l₁).1 l₂).2) := by
  induction l₁ generalizing a with
  | nil => simp [mealyRun]
  | cons γ l ih => simp [mealyRun, ih]

/-- The structural induction used for Mealy invariants. Proof sketch: expose one
transducer step and pass its recursive result to the cons case. -/
private theorem mealyRun_induction {A Γ : Type*} (δ : A → Γ → A × Γ)
    (P : A → List Γ → A × List Γ → Prop)
    (hnil : ∀ a, P a [] (a, []))
    (hcons : ∀ a γ l r, P (δ a γ).1 l r → P a (γ :: l) (r.1, (δ a γ).2 :: r.2))
    (a : A) (l : List Γ) : P a l (mealyRun δ a l) := by
  induction l generalizing a with
  | nil => exact hnil a
  | cons γ l ih => exact hcons a γ l _ (ih (δ a γ).1)

/-- Mealy runs preserve length (the scan's rewritten interval is the word interval). -/
private theorem mealyRun_length {A Γ : Type*} (δ : A → Γ → A × Γ) (a : A) (l : List Γ) :
    (mealyRun δ a l).2.length = l.length := by
  refine mealyRun_induction δ (fun _ w r => r.2.length = w.length)
    (fun _ => rfl) ?_ a l
  intro b γ w r hr
  exact congrArg Nat.succ hr

/-- Extending a Mealy prefix reads the next input cell and emits the corresponding
cell of the full output. Proof sketch: split the input at that cell and use append. -/
private theorem mealyRun_next {A Γ : Type*} (δ : A → Γ → A × Γ) (a : A)
    (w : List Γ) (r : ℕ) (hr : r < w.length) :
    (mealyRun δ a (w.take (r + 1))).1 = (δ (mealyRun δ a (w.take r)).1 w[r]).1 ∧
      (mealyRun δ a w).2[r]'(by rw [mealyRun_length]; exact hr) =
        (δ (mealyRun δ a (w.take r)).1 w[r]).2 := by
  constructor
  · rw [List.take_succ_eq_append_getElem hr, mealyRun_append]
    rfl
  · have he : w = w.take r ++ w[r] :: w.drop (r + 1) := by
      rw [← List.drop_eq_getElem_cons hr, List.take_append_drop]
    have hl : (mealyRun δ a (w.take r)).2.length = r := by
      rw [mealyRun_length, List.length_take, Nat.min_eq_left hr.le]
    have hlookup : (mealyRun δ a w).2[r]? =
        some (δ (mealyRun δ a (w.take r)).1 w[r]).2 := by
      rw [congrArg (mealyRun δ a) he, mealyRun_append]
      simp only [mealyRun]
      rw [List.getElem?_append_right (by omega)]
      simp only [hl, Nat.sub_self, List.getElem?_cons_zero]
    have hrout : r < (mealyRun δ a w).2.length := by
      simpa only [mealyRun_length] using hr
    rw [List.getElem?_eq_getElem hrout] at hlookup
    exact Option.some.inj hlookup

/-- **The two-pass scan result** (design §12.8a, R8.2): transduce `w` left to
right by `δf` from `a₀`, then right to left by `δb` from the state the first
pass ends in. Returns the final state and the rewritten word, in its original
order. -/
def scanResult {A Γ : Type*} (δf δb : A → Γ → A × Γ) (a₀ : A) (w : List Γ) : A × List Γ :=
  let f := mealyRun δf a₀ w
  let b := mealyRun δb f.1 f.2.reverse
  (b.1, b.2.reverse)

/-- **Phase alphabet of the scan** (design §12.8a, R8.2), each phase carrying
the transducer state: the forward pass, the backward pass, and the live exit
anchors, one per final state. -/
inductive ScanPhase (A : Type) where
  /-- the forward pass -/
  | fwd (a : A)
  /-- the backward pass -/
  | bwd (a : A)
  /-- the live exit anchors, one per final transducer state -/
  | done (a : A)
deriving DecidableEq, Fintype

/-- **R8.2, the two-pass transducer scan** (design §12.8a; the G2 core of the
§13d revision). Rewrite the delimited word under the head of tape `i` cell by
cell, left to right by `δf` and then back by `δb`, carrying a finite state
from `a₀`. The right delimiter turns the head, and the left delimiter steps
right into `done a` with the final state `a` as the verdict. Fold, in-place
map, head-mark shifts and carry odometers are instances
(`Turing.scanResult_fold` and its siblings). -/
def scanTM {Γ : Type*} {A : Type} (k : ℕ) (i : Fin k) (δf δb : A → Γ → A × Γ) (a₀ : A) :
    MultiTapeTM k Γ (ScanPhase A) where
  q₀ := .fwd a₀
  tr := fun q _ w =>
    match q with
    | .fwd a =>
      match w i with
      | some γ => tapeAction i 0 (some (some (δf a γ).2)) .pos (.fwd (δf a γ).1)
      | none => tapeAction i 0 none .neg (.bwd a)
    | .bwd a =>
      match w i with
      | some γ => tapeAction i 0 (some (some (δb a γ).2)) .neg (.bwd (δb a γ).1)
      | none => tapeAction i 0 none .pos (.done a)
    | .done a => inputMoveAction 0 (.done a)

/-- **R8.2, scan, framed** (design §12.8a). From any configuration in the
forward phase at `a₀` whose tape `i` carries the delimited word `w`, the scan
reaches `done` at exactly `2|w| + 2` and no `done` anchor earlier. At that
point the control state is `done` of the final state of
`Turing.scanResult δf δb a₀ w`, the word interval `[pos, pos + |w|)` holds its
rewritten word, and every other cell, the head positions, the input position
and the output are unchanged. Up to the exit the head of tape `i` stays within
`[pos - 1, pos + |w|]`, and every other head is fixed.

**Proof sketch.** The `catalog_trace_run` skeleton, with the forward and
backward cell maps of the two Mealy passes in place of the sweeps'. Induct on
the cells for each pass: the forward pass takes `|w|` steps, writing
`mealyRun δf`'s outputs; the right delimiter turns the head in one step; the
backward pass takes `|w|` steps over the forward output in reverse, writing
`mealyRun δb`'s outputs; the left delimiter supplies the entry step. -/
theorem scanTM_run_ofCfg {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ} (i : Fin k)
    (δf δb : A → Γ → A × Γ) (a₀ : A) (w : List Γ) (d : Cfg k Γ (ScanPhase A) x)
    (hstate : d.state = some (.fwd a₀))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (scanTM k i δf δb a₀).runFrom d (2 * w.length + 2) =
        { d with
          state := some (.done (scanResult δf δb a₀ w).1)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (scanResult δf δb a₀ w).2 (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ a,
        ((scanTM k i δf δb a₀).runFrom d t).state ≠ some (.done a)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((scanTM k i δf δb a₀).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((scanTM k i δf δb a₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  let f := mealyRun δf a₀ w
  let b := fun r => mealyRun δb f.1 (f.2.reverse.take (w.length - r))
  let F : ℕ → Cfg k Γ (ScanPhase A) x := fun r => { d with
    state := some (.fwd (mealyRun δf a₀ (w.take r)).1)
    workTapes := fun j q =>
      if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (r : ℤ)
        then FinTM.bufferTape f.2 (q - d.workTapePos j) else d.workTapes j q
    workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) else 0 }
  let R : ℕ → Cfg k Γ (ScanPhase A) x := fun r => { d with
    state := some (.bwd (b r).1)
    workTapes := fun j => if j = i then
      wordPatch (d.workTapes j) (d.workTapePos j) (f.2.take r ++ (b r).2.reverse)
      else d.workTapes j
    workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) - 1 else 0 }
  let D : Cfg k Γ (ScanPhase A) x := { d with
    state := some (.done (scanResult δf δb a₀ w).1)
    workTapes := fun j q =>
      if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape (scanResult δf δb a₀ w).2 (q - d.workTapePos j)
        else d.workTapes j q }
  have fl : f.2.length = w.length := mealyRun_length δf a₀ w
  have ft : f.2.take w.length = f.2 := List.take_of_length_le (by omega)
  have bl (r : ℕ) : (b r).2.length = w.length - r := by
    simp [b, mealyRun_length, fl]
  have wl (r : ℕ) (hr : r ≤ w.length) :
      (f.2.take r ++ (b r).2.reverse).length = w.length := by
    simp only [List.length_append, List.length_take, List.length_reverse, bl, fl,
      Nat.min_eq_left hr]
    omega
  have h0 : F 0 = d := by
    apply Cfg.ext <;> simp [F, mealyRun, hstate]
    funext j q
    split_ifs <;> first | rfl | omega
  have hF (r : ℕ) (hr : r < w.length) :
      (scanTM k i δf δb a₀).step (F r) = F (r + 1) := by
    have hs : (F r).workTapeSymbols i = some w[r] := by
      simp only [F, Cfg.workTapeSymbols_eq, ↓reduceIte, true_and]
      rw [if_neg (by omega)]
      simpa only [FinTM.bufferTape_nat, List.getElem?_eq_getElem hr] using
        hw r (by omega) (by omega)
    have hn := mealyRun_next δf a₀ w r hr
    rw [step_of_tapeAction_write (scanTM k i δf δb a₀) (F r)
      (q' := .fwd (δf (mealyRun δf a₀ (w.take r)).1 w[r]).1) i 0
      (some (δf (mealyRun δf a₀ (w.take r)).1 w[r]).2) .pos rfl
      (by simp only [scanTM, hs])]
    apply Cfg.ext
    · simp only [F, hn.1]
    · simp [F]
    · funext j
      by_cases hj : j = i
      · subst j
        have ht := catalog_write_take (d.workTapes i) (d.workTapePos i) f.2 r
          (by simpa only [fl] using hr)
        simpa only [F, Function.update_self, ↓reduceIte, true_and, f, hn.2] using ht
      · simp [F, hj]
    · funext j
      by_cases hj : j = i
      · subst j
        simp [F, SignType.pos_eq_one]
        omega
      · simp [F, hj]
    · rfl
  have hturn : (scanTM k i δf δb a₀).step (F w.length) = R w.length := by
    have hs : (F w.length).workTapeSymbols i = none := by
      simp only [F, Cfg.workTapeSymbols_eq, ↓reduceIte, true_and]
      rw [if_neg (by omega)]
      simpa using hw w.length (by omega) (by omega)
    rw [step_of_tapeAction_move (scanTM k i δf δb a₀) (F w.length)
      (q := .fwd f.1) (q' := .bwd f.1) i 0 .neg
      (by simp [F, f]) (by simp only [scanTM, hs])]
    apply Cfg.ext
    · simp [R, b, mealyRun]
    · simp [F, R]
    · funext j q
      by_cases hj : j = i
      · subst j
        simp [F, R, b, mealyRun, wordPatch, fl, ft]
      · simp [F, R, hj]
    · funext j
      by_cases hj : j = i
      · subst j
        simp [F, R, SignType.pos_eq_one, SignType.neg_eq_neg_one, SignType.coe_one,
        SignType.coe_neg_one, SignType.coe_zero, sub_eq_add_neg, add_assoc]
      · simp [F, R, hj]
    · rfl
  have hR (r : ℕ) (hr : r < w.length) :
      (scanTM k i δf δb a₀).step (R (r + 1)) = R r := by
    have hrout : r < f.2.length := by omega
    have hb : b r = ((δb (b (r + 1)).1 f.2[r]).1,
        (b (r + 1)).2 ++ [(δb (b (r + 1)).1 f.2[r]).2]) := by
      have hi : w.length - (r + 1) < f.2.reverse.length := by simp only [List.length_reverse]; omega
      have he : f.2.reverse[w.length - (r + 1)] = f.2[r] := by
        rw [List.getElem_reverse]
        congr 1
        omega
      have hn : w.length - r = (w.length - (r + 1)) + 1 := by omega
      change mealyRun δb f.1 (f.2.reverse.take (w.length - r)) = _
      rw [hn, List.take_succ_eq_append_getElem hi, mealyRun_append]
      simp only [he, mealyRun]
      rfl
    have hword : f.2.take (r + 1) ++ (b (r + 1)).2.reverse =
        f.2.take r ++ f.2[r] :: (b (r + 1)).2.reverse := by
      rw [List.take_succ_eq_append_getElem hrout, List.append_assoc]
      rfl
    have hl : (f.2.take r).length = r := by simp [fl, Nat.min_eq_left hr.le]
    have hs : (R (r + 1)).workTapeSymbols i = some f.2[r] := by
      simp only [R, Cfg.workTapeSymbols_eq, ↓reduceIte]
      rw [show d.workTapePos i + (((r + 1 : ℕ) : ℤ) - 1) = d.workTapePos i + r by omega]
      unfold wordPatch
      rw [wl (r + 1) (by omega), if_pos (by omega)]
      rw [show d.workTapePos i + (r : ℤ) - d.workTapePos i = r by omega,
        FinTM.bufferTape_nat, hword, List.getElem?_append_right (by omega)]
      simp [hl]
    rw [step_of_tapeAction_write (scanTM k i δf δb a₀) (R (r + 1))
      (q' := .bwd (δb (b (r + 1)).1 f.2[r]).1) i 0
      (some (δb (b (r + 1)).1 f.2[r]).2) .neg rfl
      (by simp only [scanTM, hs])]
    apply Cfg.ext
    · simp [R, hb]
    · simp [R]
    · funext j
      by_cases hj : j = i
      · subst j
        have ht := catalog_write_middle (d.workTapes i) (d.workTapePos i)
          (f.2.take r) (b (r + 1)).2.reverse f.2[r] (δb (b (r + 1)).1 f.2[r]).2
        simpa only [R, Function.update_self, ↓reduceIte, hword, hl, hb,
          List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append,
          show d.workTapePos i + (((r + 1 : ℕ) : ℤ) - 1) = d.workTapePos i + r by omega]
          using ht
      · simp [R, hj]
    · funext j
      by_cases hj : j = i
      · subst j
        simp [R, SignType.pos_eq_one, SignType.neg_eq_neg_one, SignType.coe_one,
        SignType.coe_neg_one, SignType.coe_zero]
        omega
      · simp [R, hj]
    · rfl
  have hentry : (scanTM k i δf δb a₀).step (R 0) = D := by
    have hb0 : b 0 = mealyRun δb f.1 f.2.reverse := by
      dsimp [b]
      rw [List.take_of_length_le (by simp [fl])]
    have result : scanResult δf δb a₀ w = ((b 0).1, (b 0).2.reverse) := by
      rw [hb0]
      rfl
    have hs : (R 0).workTapeSymbols i = none := by
      simp only [R, Cfg.workTapeSymbols_eq, ↓reduceIte, Nat.cast_zero, zero_sub, wordPatch]
      rw [if_neg (by omega)]
      simpa only [sub_eq_add_neg, FinTM.bufferTape_left] using hw (-1) (by omega) (by omega)
    rw [step_of_tapeAction_move (scanTM k i δf δb a₀) (R 0)
      (q' := .done (b 0).1) i 0 .pos rfl (by simp only [scanTM, hs])]
    apply Cfg.ext
    · simp [D, result]
    · simp [R, D]
    · funext j q
      by_cases hj : j = i
      · subst j
        simp [R, D, wordPatch, result, bl]
      · simp [R, D, hj]
    · funext j
      by_cases hj : j = i
      · subst j
        simp [R, D, SignType.pos_eq_one]
      · simp [R, D, hj]
    · rfl
  have hD : (scanTM k i δf δb a₀).step D = D := by
    rw [step_of_inputMoveAction (scanTM k i δf δb a₀) D 0 rfl rfl, moveInputPos_zero]
  have trace (t : ℕ) : (scanTM k i δf δb a₀).runFrom d t =
      catalogTrace F R D w.length t := by
    rw [← h0]
    exact catalog_trace_run _ F R D _ hF hturn hR hentry hD t
  refine ⟨?_, ?_, ?_⟩
  · rw [trace]
    simp [catalogTrace, show ¬2 * w.length + 2 ≤ w.length by omega, D]
  · intro t ht a
    rw [trace]
    simp only [catalogTrace]
    split_ifs <;> simp_all [F, R]
    omega
  · intro j t ht
    rw [trace]
    simp only [catalogTrace]
    split_ifs <;> simp_all [F, R, D, Finset.mem_Icc] <;> omega

/-! ### The scan's instances -/

/-- **The identity step** (design §12.8a, R8.2): keep the state and the cell.
As the backward step, it makes a scan a single forward pass plus a return. -/
def scanKeep {A Γ : Type*} : A → Γ → A × Γ := fun a γ => (a, γ)

/-- **The fold step** (design §12.8a, R8.2): update the state by `δ` and keep
the cell. -/
def scanFold {A Γ : Type*} (δ : A → Γ → A) : A → Γ → A × Γ := fun a γ => (δ a γ, γ)

/-- **The map step** (design §12.8a, R8.2): keep the state and rewrite the cell
by `f`. -/
def scanMap {A Γ : Type*} (f : Γ → Γ) : A → Γ → A × Γ := fun a γ => (a, f γ)

/-- **The delay step** (design §12.8a, R8.2): read the mark `get γ` of the
cell into the state, and write the previous mark into the cell by `set`. As
the forward step it shifts the marks one cell right; as the backward step,
one cell left. -/
def scanShift {B Γ : Type*} (get : Γ → B) (set : Γ → B → Γ) : B → Γ → B × Γ :=
  fun b γ => (get γ, set γ b)

/-- **The carry step** (design §12.8a, R8.2): with the carry set, advance the
digit by `next` and keep the carry exactly when the digit was the top one
(`top`), which wraps; with the carry clear, keep the digit. -/
def scanCarry {Γ : Type*} (top : Γ → Bool) (next : Γ → Γ) : Bool → Γ → Bool × Γ :=
  fun c γ => if c then (top γ, next γ) else (false, γ)

/-- The identity step transduces nothing. -/
private theorem mealyRun_keep {A Γ : Type*} (a : A) (l : List Γ) : mealyRun scanKeep a l = (a, l) := by
  refine mealyRun_induction scanKeep (fun b w r => r = (b, w))
    (fun _ => rfl) ?_ a l
  intro b γ w r hr
  cases hr
  rfl

/-- With the identity return, a scan is its forward pass (four of the five identities
reduce to a `mealyRun` induction through this). -/
private theorem scanResult_keep {A Γ : Type*} (δf : A → Γ → A × Γ) (a₀ : A) (w : List Γ) :
    scanResult δf scanKeep a₀ w = mealyRun δf a₀ w := by
  simp [scanResult, mealyRun_keep]

/-- The one list identity `scanResult_shiftLeft` needs beyond `scanResult_shiftRight`:
the right shift of the reversed word, reversed back, is the left shift. -/
private theorem shiftLeft_list {B Γ : Type*} (get : Γ → B) (set : Γ → B → Γ) (b₀ : B)
    (w : List Γ) :
    (List.zipWith set w.reverse (b₀ :: w.reverse.map get)).reverse =
      List.zipWith set w (w.tail.map get ++ [b₀]) := by
  cases w with
  | nil => rfl
  | cons a w =>
    -- the reversed right shift reads one mark too many; `zipWith` drops it
    have h1 : List.zipWith set (a :: w).reverse (b₀ :: (a :: w).reverse.map get) =
        List.zipWith set (w.reverse ++ [a]) (b₀ :: w.reverse.map get) := by
      have h := List.zipWith_append (f := set) (l₁ := w.reverse ++ [a]) (l₁' := [])
        (l₂ := b₀ :: w.reverse.map get) (l₂' := [get a]) (by simp)
      simp only [List.append_nil, List.zipWith_nil_left] at h
      rw [← h]
      simp
    -- both lists now have length `|w| + 1`, so reversal commutes with `zipWith`
    have h2 : List.zipWith set (w.reverse ++ [a]) (b₀ :: w.reverse.map get) =
        (List.zipWith set (a :: w) (w.map get ++ [b₀])).reverse := by
      rw [List.reverse_zipWith (by simp)]
      simp
    rw [h1, h2, List.reverse_reverse]
    rfl

/-- Once the carry clears, every subsequent cell and the clear flag stay unchanged. -/
private theorem mealyRun_carry_clear {Γ : Type*} (top : Γ → Bool) (next : Γ → Γ)
    (w : List Γ) : mealyRun (scanCarry top next) false w = (false, w) := by
  induction w with
  | nil => rfl
  | cons γ w ih => simp [mealyRun, scanCarry, ih]

/-- **Scan instance, fold** (design §12.8a, R8.2). The scan by the fold step
and the identity return computes `w.foldl δ a₀` and leaves the word intact.
With `Turing.scanTM_run_ofCfg`, the fold's verdict is `done (w.foldl δ a₀)` at
exactly `2|w| + 2`.

**Proof sketch.** Generalize `a₀` and induct on `w`: the forward pass is
`(w.foldl δ a₀, w)`, and the identity backward pass returns its input. -/
theorem scanResult_fold {A Γ : Type*} (δ : A → Γ → A) (a₀ : A) (w : List Γ) :
    scanResult (scanFold δ) scanKeep a₀ w = (w.foldl δ a₀, w) := by
  rw [scanResult_keep]
  refine mealyRun_induction (scanFold δ) (fun b l r => r = (l.foldl δ b, l))
    (fun _ => rfl) ?_ a₀ w
  intro b γ l r hr
  simp only [scanFold, List.foldl_cons, hr]

/-- **Scan instance, identity** (the brief-inventory API, round 3; user 2026-10-17): the scan by
the identity step both ways returns its state and word unchanged,
`scanResult scanKeep scanKeep a₀ w = (a₀, w)`.

**Proof sketch.** The identity step is the fold by the constant update, so
`Turing.scanResult_fold` gives `(w.foldl (fun b _ => b) a₀, w)`, and that fold is `a₀`. -/
theorem scanResult_keep_keep {A Γ : Type*} (a₀ : A) (w : List Γ) :
    scanResult scanKeep scanKeep a₀ w = (a₀, w) := by
  have hf : ∀ b : A, w.foldl (fun b (_ : Γ) => b) b = b := by
    induction w with
    | nil => exact fun _ => rfl
    | cons γ w ih => exact fun b => ih b
  have h := scanResult_fold (fun b (_ : Γ) => b) a₀ w
  rw [hf] at h
  exact h

/-- **Scan instance, in-place map** (design §12.8a, R8.2). The scan by the map
step and the identity return rewrites the word to `w.map f`, with the state
unchanged.

**Proof sketch.** Generalize `a₀` and apply the shared Mealy induction: the forward
pass is `(a₀, w.map f)`, and the identity backward pass returns its input. -/
theorem scanResult_map {A Γ : Type*} (f : Γ → Γ) (a₀ : A) (w : List Γ) :
    scanResult (scanMap f) scanKeep a₀ w = (a₀, w.map f) := by
  rw [scanResult_keep]
  refine mealyRun_induction (scanMap f) (fun b l r => r = (b, l.map f))
    (fun _ => rfl) ?_ a₀ w
  intro b γ l r hr
  simp only [scanMap, List.map_cons, hr]

/-- **Scan instance, head-mark shift right** (design §12.8a, R8.2). The scan by
the delay step forward and the identity return writes into cell `j` the mark
of cell `j - 1`, and `b₀` into cell `0`. The final state is the mark of the
last cell, or `b₀` when `w = []`.

**Proof sketch.** Generalize `b₀` and induct on `w`: the first cell receives
`b₀`, and the tail is the shift of the tail from the first cell's mark. -/
theorem scanResult_shiftRight {B Γ : Type*} (get : Γ → B) (set : Γ → B → Γ) (b₀ : B)
    (w : List Γ) :
    scanResult (scanShift get set) scanKeep b₀ w =
      ((w.map get).getLast?.getD b₀, List.zipWith set w (b₀ :: w.map get)) := by
  rw [scanResult_keep]
  induction w generalizing b₀ with
  | nil => rfl
  | cons γ w ih =>
    simp only [mealyRun, scanShift, ih, List.map_cons, List.zipWith_cons_cons,
      List.getLast?_cons, Option.getD_some]

/-- **Scan instance, head-mark shift left** (design §12.8a, R8.2). The scan by
the identity forward pass and the delay step backward writes into cell `j`
the mark of cell `j + 1`, and `b₀` into the last cell. The final state is the
mark of cell `0`, or `b₀` when `w = []`.

**Proof sketch.** The forward pass is `(b₀, w)`. The backward pass is the
right shift of `w.reverse` from `b₀`, by the induction of
`Turing.scanResult_shiftRight`; reversing it gives the left shift. -/
theorem scanResult_shiftLeft {B Γ : Type*} (get : Γ → B) (set : Γ → B → Γ) (b₀ : B)
    (w : List Γ) :
    scanResult scanKeep (scanShift get set) b₀ w =
      ((w.map get).head?.getD b₀, List.zipWith set w (w.tail.map get ++ [b₀])) := by
  have h := scanResult_shiftRight get set b₀ w.reverse
  rw [scanResult_keep] at h
  simp only [scanResult, mealyRun_keep, h]
  rw [shiftLeft_list]
  simp only [List.map_reverse, List.getLast?_reverse]

/-- **Scan instance, carry odometer** (design §12.8a, R8.2). The scan by the
carry step from a set carry, with the identity return, is the little-endian
increment of a digit word: every top digit of the maximal top prefix wraps by
`next`, the first other digit advances by `next`, and the rest is kept. The
final carry is set exactly when every digit was top, that is, on overflow.

**Proof sketch.** Induct on `w`. A top first digit wraps and passes the carry
to the tail; any other first digit advances and clears the carry, after which
the carry step is the identity. -/
theorem scanResult_carry {Γ : Type*} (top : Γ → Bool) (next : Γ → Γ) (w : List Γ) :
    scanResult (scanCarry top next) scanKeep true w =
      (w.all top, (w.takeWhile top).map next ++ ((w.dropWhile top).take 1).map next ++
        (w.dropWhile top).drop 1) := by
  rw [scanResult_keep]
  induction w with
  | nil => rfl
  | cons γ w ih =>
    cases ht : top γ <;>
      simp [mealyRun, scanCarry, ht, mealyRun_carry_clear, ih]

end Turing
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

## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. The constructions and their specification API are
public shared surface, with local proof helpers for their intrinsic bounds.
Each gadget carries only the finiteness assumptions it needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
  The rewind head bounds `Turing.FinTM.rewind_scan_heads` and `rewind_heads` (every
  work head stays put throughout the rewind) moved here from `Build/Catalog` at
  MIG-1 stage S (2026-10-14).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state. Its space, `Turing.FinTM.branchTM_spaceUsed`: the selected machine's
  space plus one origin cell per idle tape.
* **Space from time** (`Turing.FinTM.ComputesInTime.spaceUsed_le`, MIG-1): a machine
  that halts within `T` steps visits at most `k · (T + 1)` work cells at every time.
* **Optional-write normalization** (`Turing.Action.apply_workTapes`, from
  `Configuration`): the raw action-application identity for work tapes.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.
* **Machine agreement** (`Turing.MultiTapeTM.AgreeOn`, `step_eq_of_agreeOn`,
  `runFrom_eq_of_agreeOn`): two tables agreeing on a set of control states run identically while
  the control stays inside it. `Turing.MultiTapeTM.agreeOn_iff` states the agreement as an
  equivalence (the ND inventory API, round 2).
* **Buffers** (`Turing.FinTM.bufferTape`): a word stored from cell `0`, blank elsewhere;
  `Turing.FinTM.bufferTape_eq` and `bufferTape_of_neg` (the ND inventory API, round 2).

**The specification API** (user, 2026-10-16): the fields of the buffered composite's two
configuration shapes, `Turing.FinTM.bufferedFirstCfg_*` and `bufferedSecondCfg_*`, as
equations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended.

**Proof sketch.** Induct on the number of steps, using the transition equation
and the state and output readers. No tape invariant is needed because the
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    rw [MultiTapeTM.runFrom_zero]
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_of_some hstate, htr]
    rw [hstep]
    constructor
    · simp only [Action.apply_state, emitAction, dif_pos (show t < w.length by omega)]
    · simp only [Action.apply_output, emitAction, dif_pos (show t < w.length by omega),
        Option.toList_some]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_of_some hstate, htr]
  simp [Action.apply_state, Action.apply_output, emitAction, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- The defining equation of `controlAction`:
`controlAction m q = ⟨m, fun _ => (none, 0), none, q⟩`. -/
theorem controlAction_def {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    (controlAction m q : Action k Bool S) =
      (⟨m, fun _ => (none, 0), none, q⟩) := rfl

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    rw [Cfg.inputSymbol_of_end (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape {Symbol : Type*} (w : List Symbol) (z : ℤ) : Option Symbol :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil {Symbol : Type*} : bufferTape (Symbol := Symbol) [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat {Symbol : Type*} (w : List Symbol) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left {Symbol : Type*} (w : List Symbol) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol_of_zero h0, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

-- Field equations for the two configuration embeddings.
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  Turing.FinTM.leftCfg
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  Turing.FinTM.rightCfg

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration.

**Proof sketch.** The input read is determined by the unchanged head position.
The left projection recovers the original work reads, so the action correspondence applies. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  cases hs : c.state with
  | none =>
    have hs' : (leftCfg f c tapes heads).state = none := by simp [leftCfg, hs]
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hs, htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols_eq, leftCfg]
    have hi : (leftCfg f c tapes heads).inputSymbol = c.inputSymbol := by
      rw [← bufferTape_inputSymbol (leftCfg f c tapes heads), ← bufferTape_inputSymbol c,
        leftCfg_inputPos]
    rw [hr, hi]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase.

**Proof sketch.** Recover the source input read from the shared head position
and the original work reads from the right tape block. Apply the right action correspondence. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  cases hs : c.state with
  | none =>
    have hs' : (rightCfg f c tapes heads).state = none := by simp [rightCfg, hs]
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hs, htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols_eq, rightCfg]
    have hi : (rightCfg f c tapes heads).inputSymbol = c.inputSymbol := by
      rw [← bufferTape_inputSymbol (rightCfg f c tapes heads), ← bufferTape_inputSymbol c,
        rightCfg_inputPos]
    rw [hr, hi]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- A branch union has the sum of the two component tape counts. -/
theorem branchTM_k (M₁ M₂ : FinTM Bool) (b : Bool) :
    (branchTM M₁ M₂ b).k = M₁.k + M₂.k := rfl

/-- A branch union's state type is the disjoint union of the component state types. -/
theorem branchTM_State (M₁ M₂ : FinTM Bool) (b : Bool) :
    (branchTM M₁ M₂ b).State = (M₁.State ⊕ M₂.State) := rfl

/-- The branch union selecting the second machine starts as that machine's initial
configuration in the right bank, with the first bank blank at the origin. -/
private lemma branchTM_initCfg_false (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (branchTM M₁ M₂ false).tm.initCfg x =
      rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
  rw [MultiTapeTM.initCfg_eq, MultiTapeTM.initCfg_eq]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp only [rightCfg, Cfg.init_state, Option.map_some]
    rfl
  · simp only [rightCfg, Cfg.init_inputPos]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> funext z <;>
      simp only [rightCfg, Cfg.init_workTapes, Fin.addCases_left, Fin.addCases_right]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [rightCfg, Cfg.init_workTapePos, Fin.addCases_left, Fin.addCases_right]
  · simp only [rightCfg, Cfg.init_output]

/-- The branch union selecting the first machine starts as that machine's initial
configuration in the left bank, with the second bank blank at the origin. -/
private lemma branchTM_initCfg_true (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (branchTM M₁ M₂ true).tm.initCfg x =
      leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
  rw [MultiTapeTM.initCfg_eq, MultiTapeTM.initCfg_eq]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp only [leftCfg, Cfg.init_state, Option.map_some]
    rfl
  · simp only [leftCfg, Cfg.init_inputPos]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> funext z <;>
      simp only [leftCfg, Cfg.init_workTapes, Fin.addCases_left, Fin.addCases_right]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [leftCfg, Cfg.init_workTapePos, Fin.addCases_left, Fin.addCases_right]
  · simp only [leftCfg, Cfg.init_output]

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    rw [computesInTime_iff, computesInTime_iff, branchTM_initCfg_false,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    rw [computesInTime_iff, computesInTime_iff, branchTM_initCfg_true,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- **Space from time**. If `M` halts on `x` with output `y` within `T` steps, then at every time
`t` its work tapes have visited at most `M.k · (T + 1)` cells in all. [AB09, Definition 4.1, and the
remark opening the proof of Theorem 4.2: a machine running in time `T` visits at most `T + 1` cells
of each tape.]

**Proof sketch.** After the halt the configuration no longer changes, so every head position at
any time `t` already occurs at some time `u ≤ T`. Each tape's visited set is therefore contained
in the image of `{0, …, T}`, which has at most `T + 1` elements; sum over the `k` tapes. -/
theorem ComputesInTime.spaceUsed_le {M : FinTM Bool} {x y : List Bool} {T : ℕ}
    (h : M.ComputesInTime x y T) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (T + 1) := by
  have hh := ((computesInTime_iff _ _ _ _).mp h).1
  have hsub (i : Fin M.k) :
      M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        M.tm.visitedByTapeHead (M.tm.initCfg x) T i := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    by_cases hu : u ≤ T
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    · have hr : M.tm.runFrom (M.tm.initCfg x) u =
          M.tm.runFrom (M.tm.initCfg x) T := by
        rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ hh]
      exact Finset.mem_image.mpr ⟨T, Finset.mem_range.mpr (by omega),
        congrArg (fun c => c.workTapePos i) hr.symm⟩
  calc
    _ ≤ ∑ _i : Fin M.k, (T + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_le_card (hsub i)).trans (by
        unfold MultiTapeTM.visitedByTapeHead
        exact (Finset.card_image_le).trans (by rw [Finset.card_range]))
    _ = _ := by simp

/-- **The branch union's space**. The branch union selecting `b` uses exactly the selected machine's
space plus one origin cell for each tape of the idle bank.

**Proof sketch.** The branch union runs the selected machine on its own bank (`leftCfg_run`,
`rightCfg_run`) and never moves the other bank's heads, whose visited sets stay the origin
singletons, while each selected tape visits exactly the cells of the corresponding tape of the
selected machine. Split the sum over the two banks with `Fin.sum_univ_add`. -/
theorem branchTM_spaceUsed (M₁ M₂ : FinTM Bool) (b : Bool) (x : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t =
      if b then M₁.tm.spaceUsed (M₁.tm.initCfg x) t + M₂.k
      else M₂.tm.spaceUsed (M₂.tm.initCfg x) t + M₁.k := by
  cases b with
  | false =>
    have hr (u : ℕ) : (branchTM M₁ M₂ false).tm.runFrom
        ((branchTM M₁ M₂ false).tm.initCfg x) u =
        rightCfg Sum.inr (M₂.tm.runFrom (M₂.tm.initCfg x) u)
          (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      rw [branchTM_initCfg_false]
      exact rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl) _ _ _ u
    -- The idle bank's heads never leave the origin.
    have hidle (j : Fin M₁.k) : (branchTM M₁ M₂ false).tm.visitedByTapeHead
        ((branchTM M₁ M₂ false).tm.initCfg x) t (Fin.castAdd M₂.k j) = {0} := by
      ext z
      rw [MultiTapeTM.mem_visitedByTapeHead_iff, Finset.mem_singleton]
      simp only [hr, rightCfg, Fin.addCases_left]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, Nat.zero_le _, h.symm⟩⟩
    -- The selected bank visits exactly the selected machine's cells.
    have hsel (j : Fin M₂.k) : (branchTM M₁ M₂ false).tm.visitedByTapeHead
        ((branchTM M₁ M₂ false).tm.initCfg x) t (Fin.natAdd M₁.k j) =
        M₂.tm.visitedByTapeHead (M₂.tm.initCfg x) t j := by
      ext z
      rw [MultiTapeTM.mem_visitedByTapeHead_iff, MultiTapeTM.mem_visitedByTapeHead_iff]
      simp only [hr, rightCfg, Fin.addCases_right]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
    change (∑ i : Fin (M₁.k + M₂.k), _) = _
    rw [Fin.sum_univ_add]
    simp only [MultiTapeTM.spaceUsedByTape_eq_card, hidle, hsel, Finset.card_singleton,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    exact Nat.add_comm _ _
  | true =>
    have hr (u : ℕ) : (branchTM M₁ M₂ true).tm.runFrom
        ((branchTM M₁ M₂ true).tm.initCfg x) u =
        leftCfg Sum.inl (M₁.tm.runFrom (M₁.tm.initCfg x) u)
          (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      rw [branchTM_initCfg_true]
      exact leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl) _ _ _ u
    have hsel (j : Fin M₁.k) : (branchTM M₁ M₂ true).tm.visitedByTapeHead
        ((branchTM M₁ M₂ true).tm.initCfg x) t (Fin.castAdd M₂.k j) =
        M₁.tm.visitedByTapeHead (M₁.tm.initCfg x) t j := by
      ext z
      rw [MultiTapeTM.mem_visitedByTapeHead_iff, MultiTapeTM.mem_visitedByTapeHead_iff]
      simp only [hr, leftCfg, Fin.addCases_left]
    have hidle (j : Fin M₂.k) : (branchTM M₁ M₂ true).tm.visitedByTapeHead
        ((branchTM M₁ M₂ true).tm.initCfg x) t (Fin.natAdd M₁.k j) = {0} := by
      ext z
      rw [MultiTapeTM.mem_visitedByTapeHead_iff, Finset.mem_singleton]
      simp only [hr, leftCfg, Fin.addCases_right]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, Nat.zero_le _, h.symm⟩⟩
    simp only [↓reduceIte]
    rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
    change (∑ i : Fin (M₁.k + M₂.k), _) = _
    rw [Fin.sum_univ_add]
    simp only [MultiTapeTM.spaceUsedByTape_eq_card, hidle, hsel, Finset.card_singleton,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  rw [controlAction_def, Action.apply.eq_1]
  simp only [SignType.coe_zero, add_zero, Option.toList_none, List.append_nil]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym := Cfg.inputSymbol_of_zero hz
      rw [MultiTapeTM.runFrom_one,
        MultiTapeTM.step_of_some hs, htr, hsym]
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        rw [MultiTapeTM.step_of_some hs, htr, hsym]
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- The rewind's mandatory first step: a left move into the scan state, which leaves the head
at most at the last input symbol, so that `rewind_scan` applies. -/
private lemma rewind_first_step {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    tm.step c = {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} ∧
      (moveInputPos c.inputPos .neg).val ≤ x.length := by
  refine ⟨by rw [MultiTapeTM.step_of_some hs, hstart, controlAction_apply], ?_⟩
  rw [moveInputPos_neg_val]
  have := c.inputPos.isLt
  omega

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  obtain ⟨hstep, hp⟩ := rewind_first_step tm start scan hstart cfg hs
  refine ⟨(moveInputPos cfg.inputPos .neg).val + 1 + 1, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step, hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- A quantitative refinement of `rewind_from_any`: its construction takes
at most the current input position plus two steps, preserving all work and output.
**Proof sketch.** The mandatory first left move puts the head at most at the
last input symbol. `rewind_scan` then takes exactly the new position plus one. -/
lemma timed_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  obtain ⟨hstep, hp⟩ := rewind_first_step tm start scan hstart c hs
  refine ⟨(moveInputPos c.inputPos .neg).val + 1 + 1, ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- **A native input rewind keeps every work head fixed** (public since the §12.8 fill), at
every prefix, including its dispatch step.

**Proof sketch.** Induct on the input position; each step is a `controlAction`. -/
theorem rewind_scan_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      ∀ u ≤ j + 1, (tm.runFrom cfg u).workTapePos = cfg.workTapePos := by
  intro j
  induction j with
  | zero =>
    intro cfg hs hj hp u hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · have hz : cfg.inputPos = 0 := Fin.ext hj
      have hi := Cfg.inputSymbol_of_zero hz
      rw [MultiTapeTM.runFrom_one,
        MultiTapeTM.step_of_some hs, htr, hi, controlAction_apply]
  | succ j ih =>
    intro cfg hs hj hp u hu
    cases u with
    | zero => rw [MultiTapeTM.runFrom_zero]
    | succ u =>
      have hi : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have he : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        rw [MultiTapeTM.step_of_some hs, htr, hi, controlAction_apply]
      rw [MultiTapeTM.runFrom_succ_eq_step, he]
      apply ih _ rfl _ (by omega) u (by omega)
      simp only [moveInputPos_neg_val]
      omega

/-- **The bounded rewind with its work heads fixed** (public since the §12.8 fill): it
reaches its destination with the input head at `1` within `pos + 2` steps, and every work head
stays put throughout.

**Proof sketch.** One start step, then `Turing.FinTM.rewind_scan` for the run and
`Turing.FinTM.rewind_scan_heads` for the heads. -/
theorem rewind_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} ∧
      ∀ u ≤ r, (tm.runFrom c u).workTapePos = c.workTapePos := by
  obtain ⟨hstep, hp⟩ := rewind_first_step tm start scan hstart c hs
  refine ⟨(moveInputPos c.inputPos .neg).val + 1 + 1, ?_, ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, rewind_scan tm scan dest hscan _ rfl hp]
  · intro u hu
    cases u with
    | zero => rw [MultiTapeTM.runFrom_zero]
    | succ u =>
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact rewind_scan_heads tm scan dest hscan (moveInputPos c.inputPos .neg).val _ rfl rfl hp u
        (by omega)

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- **The buffer, unfolded** (the ND inventory API, round 2; G2's consumer): cell `z` reads
`w[z.toNat]?` when `0 ≤ z`, and is blank otherwise. -/
theorem bufferTape_eq {Symbol : Type*} (w : List Symbol) (z : ℤ) :
    bufferTape w z = if 0 ≤ z then w[z.toNat]? else none :=
  rfl

/-- **Every negative cell is blank** (the ND inventory API, round 2): `bufferTape w z = none` for
`z < 0`. -/
theorem bufferTape_of_neg {Symbol : Type*} (w : List Symbol) {z : ℤ} (hz : z < 0) :
    bufferTape w z = none := by
  rw [bufferTape_eq, if_neg (by omega)]

/-- Appending one emitted symbol changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append {Symbol : Type*} (w : List Symbol) (b : Symbol) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- A boundary tag holds exactly when it is `false` at the left blank and `true` at the right blank:
`VirtualTag p b ↔ (p = 0 → b = false) ∧ (p = n + 1 → b = true)` (the specification API, the briefs'
pre-ship inventories, 2026-10-16). -/
theorem VirtualTag_iff {n : ℕ} (p : Fin (n + 2)) (b : Bool) :
    VirtualTag p b ↔ (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true) :=
  Iff.rfl

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    have hs := Cfg.inputSymbol_of_zero he
    cases m with
    | zero =>
      simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.zero_eq_zero]
    | neg =>
      simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.neg_eq_neg_one]
    | pos =>
      rw [he, moveInputPos_pos_of_ne_right _ (by simp)]
      simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs := Cfg.inputSymbol_of_end hr
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-! The buffered composite's tape count `M₁.k + (1 + M₂.k)` and state type, as equations (the
specification API, the briefs' pre-ship inventories, 2026-10-16): generated by `simps` without the
`simp` attribute, so that a consumer places the composite inside a host without unfolding it. -/
attribute [simps (config := { isSimp := false }) k State] bufferedCompTM

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hq]
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols_eq]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := by
      rw [← bufferTape_inputSymbol (bufferedFirstCfg M₁ M₂ c), ← bufferTape_inputSymbol c]
      rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    have hblank : bufferTape c.output (c.output.length : ℤ) = none := by
      rw [bufferTape_nat, List.getElem?_length]
    have hupdate : Function.update (bufferTape c.output) (c.output.length : ℤ) none =
        bufferTape c.output := by
      rw [← hblank, Function.update_eq_self]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [-Action.apply, Action.apply_state, bufferedFirstCfg]
    · simp [-Action.apply, Action.apply_inputPos, bufferedFirstCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapes, Cfg.workTapeSymbols_eq, Action.apply_output, ho, bufferTape_append, hupdate]
        · intro j; simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapePos]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapePos, Action.apply_output, ho]
        · intro j; simp [-Action.apply, bufferedFirstCfg, Action.apply_workTapePos]
    · simp [-Action.apply, bufferedFirstCfg, Action.apply_output]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-! The specification API (user, 2026-10-16): `Turing.FinTM.bufferedFirstCfg`'s fields as
equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false })] bufferedFirstCfg

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-! The specification API (user, 2026-10-16): `Turing.FinTM.bufferedSecondCfg`'s fields as
equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false })] bufferedSecondCfg

/-- **The second phase's work tapes at a composite index**: at an index `i` of the buffered
composite's own tape type, `bufferedSecondCfg`'s work tape is the block layout read at
`Fin.cast (bufferedCompTM_k M₁ M₂) i`. -/
theorem bufferedSecondCfg_workTapes_cast (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ)
    (i : Fin (bufferedCompTM M₁ M₂).k) :
    (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapes i =
      tapeBlocks tapes (bufferTape y) c.workTapes (Fin.cast (bufferedCompTM_k M₁ M₂) i) :=
  rfl

/-- **The second phase's heads at a composite index**: at an index `i` of the buffered
composite's own tape type, `bufferedSecondCfg`'s head is the block layout read at
`Fin.cast (bufferedCompTM_k M₁ M₂) i`. -/
theorem bufferedSecondCfg_workTapePos_cast (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ)
    (i : Fin (bufferedCompTM M₁ M₂).k) :
    (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapePos i =
      tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
        (Fin.cast (bufferedCompTM_k M₁ M₂) i) :=
  rfl

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := MultiTapeTM.step_of_some hq
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply_inputPos] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols_eq, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols_eq]
      rw [MultiTapeTM.step_of_some hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hc]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_
      · simp [-Action.apply, Action.apply_state, bufferedSecondCfg, a, m]
      · rw [Action.apply_inputPos]
        exact moveInputPos_zero _
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [-Action.apply, bufferedSecondCfg, Action.apply_workTapes, Cfg.workTapeSymbols_eq, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [-Action.apply, bufferedSecondCfg, Action.apply_workTapes, Cfg.workTapeSymbols_eq, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [-Action.apply, bufferedSecondCfg, Action.apply_workTapePos, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply_workTapePos,
              Action.apply_inputPos, tapeBlocks_buffer] using hm.1
          · intro j; simp [-Action.apply, bufferedSecondCfg, Action.apply_workTapePos, a]
      · simp [-Action.apply, Action.apply_output, bufferedSecondCfg, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting.

**Proof sketch.** The one-step correspondence preserves the set of times with a
valid arrival tag and matching configurations. The general invariant iterator
propagates the initial correspondence to every time. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  let P : Set ℕ := {u | ∃ tag, VirtualTag (M₂.tm.runFrom c u).inputPos tag ∧
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) u =
      bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c u) tag p tapes heads}
  have preserve : Set.MapsTo (fun u : ℕ => u + 1) P P := by
    intro u hu
    obtain ⟨tag, htag, he⟩ := hu
    obtain ⟨tag', htag', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ tag htag p tapes heads
    refine ⟨tag', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using htag'
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']
  have initial : 0 ∈ P := by
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_zero] using hb
    · simp only [MultiTapeTM.runFrom_zero]
  have endpoint := preserve.iterate t initial
  change t ∈ P
  simpa only [add_right_iterate, nsmul_eq_mul, mul_one, zero_add] using endpoint

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_one]
    rw [MultiTapeTM.step_of_some (by rfl)]
    simp only [bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols_eq,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    rw [MultiTapeTM.initCfg_eq]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp only [if_true, Action.apply_state, bufferedSecondCfg, Cfg.init_state, Option.map_some]
    · simp only [if_true, Action.apply_inputPos, moveInputPos_zero, bufferedSecondCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, -Action.apply, Action.apply_workTapes,
        Cfg.workTapeSymbols_eq]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          simp [-Action.apply, -Cfg.init, bufferedSecondCfg, Action.apply_workTapes,
            Cfg.workTapeSymbols_eq]
        · intro j
          funext z
          simp [-Action.apply, -Cfg.init, bufferedSecondCfg, Action.apply_workTapes,
            Cfg.workTapeSymbols_eq, Cfg.init_workTapes]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, -Action.apply, Action.apply_workTapePos]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [-Action.apply, -Cfg.init, bufferedSecondCfg, Action.apply_workTapePos,
            Cfg.init_inputPos, Cfg.init_workTapePos]
    · simp only [if_true, Action.apply_output, Option.toList_none, List.append_nil,
        bufferedSecondCfg, Cfg.init_output]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      rw [MultiTapeTM.step_of_some (by rfl)]
      simp only [bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols_eq,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_
      · exact Action.apply_state _ _
      · rw [Action.apply_inputPos]
        exact moveInputPos_zero _
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [-Action.apply, Action.apply_workTapes, Cfg.workTapeSymbols_eq]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [-Action.apply, Action.apply_workTapes,
            Cfg.workTapeSymbols_eq]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [-Action.apply, Action.apply_workTapePos]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [-Action.apply, Action.apply_workTapePos,
            sub_eq_add_neg]
      · exact Action.apply_output _ _
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    have hstate : (bufferedFirstCfg M₁ M₂ c).state = some (.inl none) := by
      simp [bufferedFirstCfg, hs]
    rw [MultiTapeTM.step_of_some hstate]
    simp only [bufferedFirstCfg, bufferedCompTM]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · exact Action.apply_state _ _
    · rw [Action.apply_inputPos]
      exact moveInputPos_zero _
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, -Action.apply, Action.apply_workTapes,
        Cfg.workTapeSymbols_eq]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, -Action.apply,
          Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, -Action.apply, Action.apply_workTapePos]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, -Action.apply,
          Action.apply_workTapePos, sub_eq_add_neg]
    · exact Action.apply_output _ _
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Use `Turing.MultiTapeTM.exists_first_halt` for the first halt by `t₁` and
transport the complete output `y` from the deadline. First-phase lockstep reaches that completed
configuration; the exact rewind lemma supplies `|y| + 2` more steps while retaining the first
block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hspec := (computesInTime_iff M₁ x y t₁).mp h₁
  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt M₁.tm (M₁.tm.initCfg x) hspec.1
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := by
    change (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none
    rw [heq]
    exact hspec.1
  have ho : c.output = y := by
    change (M₁.tm.runFrom (M₁.tm.initCfg x) t).output = y
    rw [heq]
    exact hspec.2
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t hlive]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM

/-! ### Machine-agreement transfer (§13, Z5)

Two machines over the same tape count and state type whose transition
tables agree on a set of control states run identically for as long as the
run's control stays inside that set. This is the `hagree` genre of
`Turing.capture_run`/`Turing.emit_run` made standalone: those lemmas carry
a per-state agreement hypothesis for one specific wrapper, re-proved ad hoc
at every host; the standalone form transfers whole runs between any two
agreeing tables (design `machine-library-design.md` §13, item Z5; decision
D-R3). First customers: the forwarding loop host of `Build/Loop.lean`
(whose fourteen phase lemmas are verbatim re-proofs of the capturing
host's, since the two tables agree on every non-body state) and the
guarded `clSlot_run` agreement sites of `CookLevin/Hardness.lean`. -/

namespace Turing.MultiTapeTM

/-- The two transition tables agree on every control state in `Q`: from any
such state, both machines take the identical action on identical reads.
Nothing is assumed about states outside `Q`, about `q₀`, or about
halting. -/
def AgreeOn {k : ℕ} {Symbol State : Type*} (M N : MultiTapeTM k Symbol State)
    (Q : Set State) : Prop :=
  ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work

/-- **The agreement, unfolded** (the ND inventory API, round 2; C1-WC's review): the tables agree
on `Q` iff `M.tr q inp work = N.tr q inp work` for every `q ∈ Q` and all reads. -/
theorem agreeOn_iff {k : ℕ} {Symbol State : Type*} (M N : MultiTapeTM k Symbol State)
    (Q : Set State) :
    M.AgreeOn N Q ↔ ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work :=
  Iff.rfl

/-- One step transfers across an agreement: if the configuration's control
state (when live) lies in the agreement set, both machines step it to the
same configuration. Halted configurations step to themselves on both sides.

**Proof sketch.** On `c.state = none` both steps are the identity. On
`c.state = some q` with `q ∈ Q`, unfold `step`: both sides apply the same
action `M.tr q c.inputSymbol c.workTapeSymbols = N.tr q …` to `c`. -/
theorem step_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (hq : ∀ q, c.state = some q → q ∈ Q) :
    N.step c = M.step c := by
  cases hs : c.state with
  | none => simp only [step_of_halt hs]
  | some q =>
    simp only [step, hs]
    rw [h q (hq q hs)]

/-- A whole run transfers across an agreement: if every control state the
`M`-run visits strictly before time `t` lies in the agreement set, the two
runs coincide at time `t` (and hence at every earlier time, by
instantiating `t`). The endpoint itself may leave the set or halt; no
liveness is assumed, and `t = 0` is the trivial case.

**Proof sketch.** Induct on `t`. The inductive hypothesis transfers the
run at `t`; the visit hypothesis at `u = t` puts its live control in `Q`,
so `step_eq_of_agreeOn` transfers the final step. Halted intermediate
configurations step identically on both sides without the hypothesis. -/
theorem runFrom_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) (hq : ∀ u < t, ∀ q, (M.runFrom c u).state = some q → q ∈ Q) :
    N.runFrom c t = M.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih (fun u hu => hq u (by omega)),
      runFrom_succ_eq_step']
    exact step_eq_of_agreeOn h _ (hq t (by omega))

end Turing.MultiTapeTM

namespace Turing.FinTM

/-- From a fixed configuration, a branch union has the same run for either Boolean
initial-state choice. Both machines are explicitly transported to their common tape
count and state type before comparing configurations. -/
theorem branchTM_runFrom_independent (M₁ M₂ : FinTM Bool) (b b' : Bool)
    {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x) (t : ℕ) :
    let view : Bool → MultiTapeTM (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) :=
      fun tag => by
        rw [← branchTM_k M₁ M₂ tag, ← branchTM_State M₁ M₂ tag]
        exact (branchTM M₁ M₂ tag).tm
    (view b).runFrom c t = (view b').runFrom c t := by
  exact MultiTapeTM.runFrom_eq_of_agreeOn (Q := Set.univ)
    (by
      rw [MultiTapeTM.agreeOn_iff]
      intro q _ inp work
      rfl)
    c t (fun _ _ q _ => Set.mem_univ q)

end Turing.FinTM
```
