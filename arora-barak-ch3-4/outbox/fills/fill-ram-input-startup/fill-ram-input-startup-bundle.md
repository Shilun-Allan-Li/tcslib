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

## ===== campaign/items/ram-tm/briefs/fill-ram-input-startup.md =====

# RAM fill (Codex), tier 2 job C: the input bit and the start-up (2 admissions, 2 files)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-input-startup`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

Two statements of tier 2, in two owned files:
1. **`Turing.exists_inputBitTM`** (`Build/InputBit.lean`): with a signed word `u` on tape `0` and
   `Nat.bits |x|` on tape `1`, write on tape `2` the word `1` if `0 ≤ u.toInt` and the input bit
   at `u.toInt` is `true`, and `0` otherwise. It reads the input in place: `O(W + |x|)` steps,
   work radius `O(W + log |x|)`. Job D cites it for `rdIn`.
2. **`WordRAM.Sim.exists_startup`** (`RAMSimulation/Sim/Startup.lean`): for any word-size
   witness `Mw`, a machine with the eight tapes of `WordRAM.Sim.Encodes` first, and `k'` more,
   that reaches a configuration encoding `XCfg.init W |x|` over the cells `{-1}`. It does so
   within `tw + C·(|x| + W² + 1)` steps and `sw + C·(W + log |x| + 1)` visited cells, where `Mw`
   writes `Nat.bits W` within `tw` steps and `sw` cells. Job E cites it.

Each has a proof sketch. Gate 162's auditor found both achievable (G162-19, G162-20).

## Route: the input bit

1. **The sign test** (`Turing.exists_wordSignTM`, job A): a negative position writes `0`.
2. **The range test `u.toInt < |x|`.** Compare the little-endian value of `u`'s bits with
   `Nat.bits |x|`. The words have different lengths: the longer one's excess bits decide when they
   are nonzero. Write this private comparator once.
3. **Otherwise seek.**
   - Copy `u` to a scratch tape and increment it once. The input head's position `p + 1` holds bit
     `p` (`Turing.Cfg`'s input positions are shifted by one). No overflow is possible: the sign
     bit is clear and `u.toInt < |x|`.
   - Seek with `Turing.exists_inputSeekTM` (`Build/InputCall`): position word on its tape `0`, a
     blank scratch tape as its tape `1`. Place its two tapes with `Turing.embedEmitTM` or
     `Contract.embed`. It gives `p ≤ |x| + 1`, time `C·(|w| + pos + p + 1)`, work envelope
     `C·(|w| + 1)`, and its work tapes restored.
4. **Write the word.** Read the bit under the input head, write `1` or `0` over the register
   (`Turing.exists_wordIntTM`, job A), clear the scratch tapes, and return the heads. The input
   head ends where the seek left it, the `∃ ip` of the statement.

At `W = 0` the register is the empty word, whatever the bit.

## Route: the start-up

The statement's sketch has the steps:
1. Run `Mw` silently, its output captured on a work tape (`Turing.embedSilentTM`,
   `Build/Embed`). Its run lemmas give the time `tw` and its tapes' visited cells.
2. Make the registers. Expand `Nat.bits W` into `W` zeros (`Turing.expandTM`, `Build/CounterLoop`,
   with the pattern `[false]`), copy them to tapes `2` to `4`, and extend tape `1` to `W + a`
   cells.
3. Rewind the input (`Turing.inputRewindTM`) and count `|x|` onto tape `5`
   (`Turing.exists_inputLengthTM`).
4. Install the table `[(keyBits a W (-1), bvBits (wd W |x|))]`:
   - the key, by `Turing.exists_wordIntTM` with `c = -1`;
   - the value, as the low `W` bits of `Nat.bits |x|` padded with zeros, which is `wd W |x|`
     read modulo `2^W`;
   - then `Turing.exists_keyAssignTM` (job B) into the empty table, or a direct layout write.
5. Return every head to its origin, and exit. The origins `o` are the statement's existential.

`TableOf` holds: `-1` is in range because `1 ≤ a`, and `initMem` is `0` elsewhere
(`WordRAM.initMem_def`).

**Space:** `Mw`'s tapes and the capture tape, whose `|Nat.bits W| + 1 ≤ W + 1` cells are visited,
plus `O(W + log |x|)` on the eight. Use `MultiTapeTM.spaceUsed` through
`Turing.seamCompTM_spaceUsed_le_add_ofCfg` and the embedding's visited-set lemmas.

## Owned files

- `TCSlib/Complexity/TuringMachine/Build/InputBit.lean`
- `TCSlib/Complexity/RAMSimulation/Sim/Startup.lean`

Statements byte-identical. Private helpers in each file. Both files may add imports of existing
`Build/*` modules; `Startup.lean` may also import `RAMSimulation/WordSize` if needed. List each
import with its reason.

## Admitted dependencies allowed

The statements of `Build/WordArith` (job A) and `Build/KeyTable` (job B). Nothing else.

## Downstream check

`RAMSimulation/Sim/Phases`, `RAMSimulation/Simulation`, `RAMSimulation/Classes` and the
facades.

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

## ===== TCSlib/Complexity/RAMSimulation/Sim/Startup.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.InputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: the start-up

Before the first instruction, the simulating machine computes the word size `W = W (|x|)` with
the word-size witness, prepares its eight tapes and installs the start memory: the cell `-1`
holds `|x|` modulo `2^W` and every other cell `0` (`WordRAM.initMem`). This file states that
start-up for any word-size witness `Mw`; its extra tapes hold `Mw`'s tapes, and its output, which
is captured on a work tape.

## Main results

* `WordRAM.Sim.exists_startup`: the start-up reaches a configuration encoding
  `XCfg.init W |x|` within `tw + O(|x| + W² + 1)` steps and `sw + O(W + log |x| + 1)` cells,
  where `Mw` writes `Nat.bits W` within `tw` steps and `sw` cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §4.1, space-constructible functions.)
-/

namespace WordRAM.Sim

open Turing

/-- **The start-up.** For `a ≥ 1`, an output mode `fn` and a word-size witness `Mw`, there is a
machine with the eight tapes of `WordRAM.Sim.Encodes` first and `k'` more, and a constant `C`, such
that: whenever `Mw`, run on `x`, writes `Nat.bits W` within `tw` steps having visited at most `sw`
work cells, the machine, started at its entry on `x` with blank tapes, reaches its exit at some
time `t ≤ tw + C·(|x| + W² + 1)`, not earlier, in a configuration whose first eight tapes encode
`XCfg.init W |x|` over the cells `{-1}` with some origins, having visited at most
`sw + C·(W + log |x| + 1)` work cells. [AB09, Exercise 1.9]

**Proof sketch.**
1. Run `Mw` with its output captured on a work tape (`Turing.embedSilentTM`, its tapes and the
   capture tape among the `k'`), within `tw` steps and `sw` cells, plus the capture's
   `|Nat.bits W| + 1` cells.
2. Make the three word registers and the key register: expand `Nat.bits W` into `W` cells of `0`
   (`Turing.expandTM` with the pattern `[false]`, `O(W)` steps plus the counter overhead), copy
   it to the other registers, and extend the key register by `a` cells.
3. Rewind the input head and count `|x|` onto tape `5` (`Turing.exists_inputLengthTM`, `O(|x|)`
   steps, `O(log |x|)` cells).
4. Install the table `[(keyBits a W (-1), bvBits (wd W |x|))]`: the key by the integer-constant
   row with `c = -1`, the value by copying the low `W` bits of `Nat.bits |x|` into a register
   padded with zeros (modulo `2^W`), then the keyed assignment into the empty table.
   `TableOf` holds: `-1` is in range because `a ≥ 1`, and `initMem` is `0` elsewhere.
5. Return every head to its origin, clear the scratch tapes, and exit.
Each stage after the first costs `O(|x| + W² + 1)` steps and `O(W + log |x| + 1)` cells. -/
theorem exists_startup (a : ℕ) (ha : 1 ≤ a) (fn : Bool) (Mw : FinTM Bool) :
    ∃ (k' : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (8 + k') Bool S) (entry exit : S) (C : ℕ),
      ∀ (x : List Bool) (W tw sw : ℕ), Mw.ComputesInTime x (Nat.bits W) tw →
        Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw →
        ∃ (t : ℕ) (o : Fin 8 → ℤ), t ≤ tw + C * (x.length + W ^ 2 + 1) ∧
          (∀ s < t, (R.runFrom (Turing.Cfg.init entry x) s).state ≠ some exit) ∧
          (R.runFrom (Turing.Cfg.init entry x) t).state = some exit ∧
          Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb k') o
            (R.runFrom (Turing.Cfg.init entry x) t) ∧
          R.spaceUsed (Turing.Cfg.init entry x) t ≤
            sw + C * (W + (Nat.bits x.length).length + 1) := by
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

## ===== TCSlib/Complexity/TuringMachine/Build/InputCall.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: modules on the native input (§12.8)

The two native-input modules of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3): a call of a function-level machine
on the native input at a clean seam (R8.5e), and a seek of the input head to a
position held in binary on a work tape (R8.5b). Both are `Bool` modules; a
rich host runs them lifted along its digit embedding
(`Turing.MultiTapeTM.liftSymbols`), with unchanged time and space.

**Status: §12.8 fill C (status update; refreshed at the A–C fill gate, minor 4).** The
input seek is proved with its restoration, first-exit and workspace clauses. The clean input
call is proved; it cites stream B's `Turing.inputCopyTM_run_ofCfg`, now proved, and its
interface remains time-only.

## Main results

* `Turing.FinTM.exists_inputCallTM` — compute `f` on the native input from a
  blank seam and install the result on tape `0` (proved; the copier
  `inputCopyTM_run_ofCfg` is a proved dependency; status refreshed at the A–C fill gate).
* `Turing.exists_inputSeekTM` — move the input head to the binary value on a
  counter tape, restoring every work tape (proved; fill-C status update).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape, whose
  head a work-tape counter can position; the space-bounded simulations of
  §4.1 locate the input head of a simulated configuration this way.)
-/

namespace Turing.FinTM

/-- On a blank seam, the public native copier installs exactly the argument seam.
It cites stream B's framed input-copy contract, which is proved. -/
private theorem inputCall_copy (k : ℕ) (hk : 0 < k) (x : List Bool) :
    (inputCopyTM k ⟨0, hk⟩).runFrom (Cfg.ofWords (input := x) SweepPhase.sweep (fun _ => []))
        (2 * x.length + 2) = Cfg.ofWords SweepPhase.done (stateWord k x) := by
  rw [(inputCopyTM_run_ofCfg ⟨0, hk⟩ _ rfl rfl).1]
  apply Cfg.ext <;> try rfl
  funext j z
  simp only [Cfg.ofWords, stateWord]
  by_cases hj : j = ⟨0, hk⟩
  · subst j
    simp only [true_and, zero_add, sub_zero, bufferTape_nil, if_true]
    unfold bufferTape
    by_cases hzero : 0 ≤ z <;> by_cases hlen : z < (x.length : ℤ) <;> simp [hzero, hlen]
  · have hjval : (j : ℕ) ≠ 0 := fun hz => hj (Fin.ext hz)
    simp [hj, hjval]

/-- **R8.5e, the clean call on the native input** (design §12.8a §3). For any
witness `M` computing `f` within `T`, there is a callable module with entry and
exit states and a positive tape count with the following contract. From the
blank seam `Cfg.ofWords entry` (every tape empty, input head at `1`, empty
output) over the native input `x`, the module reaches, at its first positive
visit to `exit`, exactly the seam with `f x` installed on tape `0`, within
`c·(T |x| + |x| + |f x| + 1)` steps. It is the function-level contract run at a
seam that the next phase of a host can consume.

**Proof sketch.** Seam-compose (`Turing.seamCompTM_run_ofCfg`) the input
copier on tape `0` (`Turing.inputCopyTM_run_ofCfg`, `2|x| + 2` steps, which
from the blank seam yields `Cfg.ofWords` with `x` on tape `0`) with the install
call of `Turing.FinTM.exists_installCallTM` on the argument `x`, whose
coefficient absorbs the copy and the dispatch step. The first-return clause is
`Turing.seamCompTM_firstReturn_ofCfg`, which also needs the callee's exit
excluded at time `0`; the install call's contract excludes it only at positive
times. So split on whether its entry equals its exit. If it does, first wrap it
by `Turing.seamReleaseTM`, whose `Turing.seamReleaseTM_firstReturn` supplies a
fresh entry. The positive tape count is the install call's. -/
theorem exists_inputCallTM (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ x : List Bool,
        ∃ t ≤ c * (T x.length + x.length + (f x).length + 1),
          0 < t ∧
          (∀ t', 0 < t' → t' < t →
            (C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t').state ≠
              some exit) ∧
          C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t =
            Cfg.ofWords exit (stateWord C.k (f x)) := by
  obtain ⟨C₀, en₀, ex₀, b, hk₀, hC₀⟩ := exists_installCallTM M f T hM
  -- Supply the time-zero cut once, then use the same copier and seam in both cases.
  have hcallee : ∃ (C : FinTM Bool) (en ex : C.State), 0 < C.k ∧
      ∀ x : List Bool, ∃ t ≤ b * (T x.length + x.length + (f x).length + 1),
        0 < t ∧
        (∀ u < t, (C.tm.runFrom (Cfg.ofWords (input := x) en (stateWord C.k x)) u).state ≠
          some ex) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) en (stateWord C.k x)) t =
          Cfg.ofWords ex (stateWord C.k (f x)) := by
    by_cases he : en₀ = ex₀
    · subst ex₀
      let C : FinTM Bool := ⟨C₀.k, Unit ⊕ C₀.State, seamReleaseTM C₀.tm en₀⟩
      refine ⟨C, Sum.inl (), Sum.inr en₀, hk₀, ?_⟩
      intro x
      obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC₀ x x
      have hr := seamReleaseTM_firstReturn C₀.tm en₀ rfl hpos hrun rfl hfirst
      exact ⟨t, ht, hpos, hr.2, hr.1⟩
    · refine ⟨C₀, en₀, ex₀, hk₀, ?_⟩
      intro x
      obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC₀ x x
      refine ⟨t, ht, hpos, ?_, hrun⟩
      intro u hu
      rcases Nat.eq_zero_or_pos u with rfl | hupos
      · simpa [Cfg.ofWords] using he
      · exact hfirst u hupos hu
  obtain ⟨C, en, ex, hk, hC⟩ := hcallee
  let D : FinTM Bool := ⟨C.k, SweepPhase ⊕ C.State,
    seamCompTM (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en⟩
  refine ⟨D, Sum.inl .sweep, Sum.inr ex, b + 3, hk, ?_⟩
  intro x
  obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC x
  have hcopy := inputCall_copy C.k hk x
  have hcut := (inputCopyTM_run_ofCfg (x := x) ⟨0, hk⟩
    (Cfg.ofWords SweepPhase.sweep (fun _ => [])) rfl rfl).2.1
  have hall := seamCompTM_run_ofCfg (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en
    hcopy rfl hcut hrun
  have hfirst' := seamCompTM_firstReturn_ofCfg (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en ex
    hcopy rfl hcut hrun rfl hfirst
  refine ⟨2 * x.length + 2 + 1 + t, ?_, by omega, (fun u _ hu => hfirst' u hu), hall⟩
  rw [Nat.add_mul]
  omega

end Turing.FinTM

namespace Turing

/-- The seek's rewind needs one additional left move after the public rewind returns at `1`:
there is no public native-input-head primitive with that exit convention. -/
private inductive InputSeekRw where
  | start | scan | left | done
deriving DecidableEq, Fintype

/-- The four-state input rewind; no public native-input-head primitive finishes at marker `0`.
The public `FinTM.rewind_heads` supplies its scan and all prefix work-head bounds. -/
private def inputSeekRewind : MultiTapeTM 2 Bool InputSeekRw where
  q₀ := .start
  tr := fun q inp _ => match q with
    | .start => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .left)
    | .left => FinTM.controlAction .neg (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- Rewind to the left marker, keeping all work heads fixed and excluding an earlier exit.

**Proof sketch.** Invoke the public rewind with exit `left`, then move left once.
Apply the public fixed-stop first-entry theorem to the stationary `done` control,
retaining the exact parked endpoint and the prefix work-head bounds. -/
private theorem inputSeekRewind_run {x : List Bool} (d : Cfg 2 Bool InputSeekRw x)
    (hd : d.state = some .start) :
    ∃ r ≤ d.inputPos.val + 3,
      inputSeekRewind.runFrom d r = { d with state := some .done, inputPos := 0 } ∧
      (∀ u < r, (inputSeekRewind.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ r, (inputSeekRewind.runFrom d u).workTapePos = d.workTapePos := by
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads inputSeekRewind .start .scan
    (some .left) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have hend : inputSeekRewind.runFrom d (r + 1) =
      { d with state := some .done, inputPos := 0 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.step_of_some rfl]
    change (FinTM.controlAction SignType.neg (some InputSeekRw.done)).apply
      ({ d with state := some .left, inputPos := 1 } : Cfg 2 Bool InputSeekRw x) = _
    rw [FinTM.controlAction_apply]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    rw [FinTM.moveInputPos_neg_val]
    rfl
  obtain ⟨u, hu, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    inputSeekRewind (fun q => q = .done) d {d with state := some .done, inputPos := 0} (r + 1)
    (by
      rintro z ⟨q, hq, rfl⟩
      rw [MultiTapeTM.step_of_some hq]
      change (FinTM.controlAction 0 (some InputSeekRw.done)).apply z = z
      rw [FinTM.controlAction_apply, moveInputPos_zero]
      cases z
      simp_all)
    ⟨.done, rfl, rfl⟩ hend
  refine ⟨u, by omega, he, (fun v hv hs => hcut v hv ⟨.done, hs, rfl⟩), ?_⟩
  intro v hv
  have hvr : v ≤ r + 1 := hv.trans hu
  by_cases hvr' : v ≤ r
  · exact hheads v hvr'
  · have : v = r + 1 := by omega
    subst v
    rw [hend]

/-- A seek round moves the input right once; there is no public native-input-head primitive
for the counter host's cyclic one-step body. -/
private def inputSeekStep : MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr := fun _ _ _ => inputMoveAction 1 ()

/-- The input-only seek body preserves the entire work bank and output at every prefix.

**Proof sketch.** Induct on the number of right moves, using the public input-action step. -/
private theorem inputSeekStep_run {x : List Bool} (c : Cfg 1 Bool Unit x)
    (hc : c.state = some ()) (r : ℕ) :
    inputSeekStep.runFrom c r =
      { c with inputPos := (fun p : Fin (x.length + 2) => moveInputPos p 1)^[r] c.inputPos } := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    rw [step_of_inputMoveAction inputSeekStep
      ({ c with inputPos := (fun p : Fin (x.length + 2) => moveInputPos p 1)^[r] c.inputPos })
      1 hc rfl, Function.iterate_succ_apply']
    simp only [hc]

/-- Before the right boundary is reached, repeated native right moves add their count. -/
private theorem inputSeek_right_value {n : ℕ} (p : Fin (n + 2)) (r : ℕ)
    (hr : p.val + r ≤ n + 1) :
    ((fun q : Fin (n + 2) => moveInputPos q 1)^[r] p).val = p.val + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply']
    change (moveInputPos _ SignType.pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by omega)]
    simp only
    omega

/-- Copy, marker rewind, binary countdown, and cleanup, joined by three public seams. -/
private def inputSeekMachine : MultiTapeTM 2 Bool
    (((SweepPhase ⊕ InputSeekRw) ⊕ CounterLoopState Unit) ⊕ SweepPhase) :=
  seamCompTM
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start)
      (Sum.inr .done) (counterLoopTM inputSeekStep () none) (.dec .run))
    (Sum.inr .done) (clearTM 2 1) .sweep

/-- The public seam visited-set inclusion transfers a common interval bound through dispatch.
This is used at all three seams of the seek, with intervals measured at its original heads. -/
private theorem inputSeek_seam_range {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (M₁ : MultiTapeTM 2 Bool S₁) (ex : S₁) (M₂ : MultiTapeTM 2 Bool S₂) (en : S₂)
    {c₀ c₁ : Cfg 2 Bool S₁ x} {t₁ t₂ : ℕ}
    (h₁ : M₁.runFrom c₀ t₁ = c₁) (hex : c₁.state = some ex)
    (hcut : ∀ u < t₁, (M₁.runFrom c₀ u).state ≠ some ex)
    (lo hi : Fin 2 → ℤ)
    (hleft : ∀ u ≤ t₁, ∀ j, (M₁.runFrom c₀ u).workTapePos j ∈ Finset.Icc (lo j) (hi j))
    (hright : ∀ u ≤ t₂, ∀ j,
      (M₂.runFrom (c₁.mapState fun _ => en) u).workTapePos j ∈ Finset.Icc (lo j) (hi j)) :
    ∀ u ≤ t₁ + 1 + t₂, ∀ j,
      ((seamCompTM M₁ ex M₂ en).runFrom (c₀.mapState Sum.inl) u).workTapePos j ∈
        Finset.Icc (lo j) (hi j) := by
  intro u hu j
  have hv := seamCompTM_visitedByTapeHead_ofCfg M₁ ex M₂ en (T₂ := t₂) h₁ hex hcut j
    (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩)
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
    rw [← heq]
    exact hleft v (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hv) j
  · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
    rw [← heq]
    exact hright v (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hv) j

/-- **R8.5b, the input seek** (design §12.8a §3). There is a two-tape `Bool`
module with entry and exit states with the following contract. Let tape `0`
hold, from its head, a delimited word `w` whose little-endian value `p` is a
valid input position, at most `|x| + 1`, and let tape `1` be blank. From the
entry, with the input head anywhere, the module reaches `exit` with the input
head at `p` within `C·(|w| + pos + p + 1)` steps, where `pos` is the starting
input position, and not earlier. Every work tape, every work head and the
output are restored. Up to the exit every work head stays within
`C·(|w| + 1)` cells of its entry position. So the module's work space is
`O(|w| + 1)`, however far the input head travels, and repeated calls compose.
A rich host runs it lifted on two dedicated digit tapes.

**Proof sketch.** Copy `w` to the scratch tape (`Turing.copyTM_run_ofCfg`,
`2|w| + 2`). Rewind the input head: `timed_rewind` returns it to position `1`
within `pos + 2` steps, and one further left move reaches the left end marker
`0`. Run `Turing.counterLoopTM` with the scratch copy as the
counter and the one-step round "input head right", `p` rounds
(`Turing.counterLoopTM_run_done`, `p + counterOverhead w (p + 1)`, at most
`5p + 2|w| + 2` by `Turing.counterOverhead_le`). The counter ends all `true`
with its head back; `Turing.clearTM_run_ofCfg` blanks it. The phases join by
R2 seams, whose dispatch steps add a constant. The work heads move only in the
copy, the counter loop and the clear, whose trajectory clauses keep each one
within `[pos - 1, pos + |w|]` of its tape. -/
theorem exists_inputSeekTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 2 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
        p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x, d.state = some entry →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + q) = FinTM.bufferTape w q) →
        (∀ q, d.workTapes 1 q = none) →
        ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((C * (w.length + 1) : ℕ) : ℤ)) ∧
          (R.runFrom d t).state = some exit ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
          (R.runFrom d t).workTapes = d.workTapes ∧ (R.runFrom d t).workTapePos = d.workTapePos ∧
          (R.runFrom d t).output = d.output := by
  refine ⟨_, inferInstance, inferInstance, inputSeekMachine,
    Sum.inl (Sum.inl (Sum.inl .sweep)), Sum.inr .done, 13, ?_⟩
  intro x p w hp hpx d hd hw hblank
  let d₀ : Cfg 2 Bool SweepPhase x :=
    ⟨some .sweep, d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  let d₁ : Cfg 2 Bool SweepPhase x :=
    { d₀ with
      state := some .done
      workTapes := fun j z => if j = 1 then FinTM.bufferTape w (z - d.workTapePos 1)
        else d.workTapes j z }
  have hcopy₀ := copyTM_run_ofCfg 0 1 (by decide) w d₀ rfl hw
  have hcopy : (copyTM 2 0 1).runFrom d₀ (2 * w.length + 2) = d₁ := by
    rw [hcopy₀.1]
    apply Cfg.ext <;> try rfl
    funext j z
    by_cases hj : j = 1
    · subst j
      simp only [d₀, d₁, true_and, if_true]
      by_cases hz : d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
      · simp [hz]
      · rw [if_neg hz, hblank]
        unfold FinTM.bufferTape
        split_ifs with hz₀
        · rw [List.getElem?_eq_none (by omega)]
        · rfl
    · simp [d₀, d₁, hj]
  let rw₀ := d₁.mapState (fun _ => InputSeekRw.start)
  obtain ⟨r, hr, hrewind, hrCut, hrHeads⟩ := inputSeekRewind_run rw₀ rfl
  let rw₁ : Cfg 2 Bool InputSeekRw x := { rw₀ with state := some .done, inputPos := 0 }
  let c : Cfg 1 Bool Unit x :=
    ⟨some (), 0, fun _ => d.workTapes 0, fun _ => d.workTapePos 0, d.output⟩
  let ct := fun z => FinTM.bufferTape w (z - d.workTapePos 1)
  have hct : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      ct (d.workTapePos 1 + z) = FinTM.bufferTape w z := by
    intro z _ _
    simp [ct]
  have hstart : rw₁.mapState (fun _ => CounterLoopState.dec FlagPhase.run) =
      counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1) := by
    rw [counter_cfg_eq]
    apply Cfg.ext <;> try rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
  have horbit (a : ℕ) : counterLoopOrbit inputSeekStep (fun _ => 1) c a =
      inputSeekStep.runFrom c a := rfl
  have hstate (a : ℕ) : (counterLoopOrbit inputSeekStep (fun _ => 1) c a).state = some () := by
    rw [horbit, inputSeekStep_run c rfl]
  have hround : ∀ a < p,
      (counterLoopOrbit inputSeekStep (fun _ => 1) c a).state = some () ∧
      0 < (1 : ℕ) ∧
      (∀ u, 0 < u → u < (1 : ℕ) →
        ∃ q, (inputSeekStep.runFrom (counterLoopOrbit inputSeekStep (fun _ => 1) c a) u).state =
          some q ∧ q ≠ () ∧ (none : Option Unit) ≠ some q) ∧
      (counterLoopOrbit inputSeekStep (fun _ => 1) c (a + 1)).state = some () := by
    intro a _
    exact ⟨hstate a, Nat.one_pos, fun u hu hu' => by omega, hstate (a + 1)⟩
  let l := p + counterOverhead w (p + 1)
  have hloop₀ := counterLoopTM_run_done inputSeekStep () none (fun _ => 1) c w ct
    (d.workTapePos 1) hct p hp hround l (by simp [l])
  let lc : Cfg 2 Bool (CounterLoopState Unit) x :=
    ⟨some .done, ⟨p, by omega⟩,
      (fun j z => if j = 1 then
        FinTM.bufferTape (List.replicate w.length true) (z - d.workTapePos 1)
        else d.workTapes j z), d.workTapePos, d.output⟩
  have hloop : (counterLoopTM inputSeekStep () none).runFrom
      (rw₁.mapState fun _ => .dec .run) l = lc := by
    rw [hstart, hloop₀.1, counter_cfg_eq, horbit, inputSeekStep_run c rfl]
    apply Cfg.ext <;> try rfl
    · apply Fin.ext
      simpa [c, lc] using inputSeek_right_value (0 : Fin (x.length + 2)) p (by simpa using hpx)
    · funext j z
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        change (if d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
          then some true else ct z) =
            FinTM.bufferTape (List.replicate w.length true) (z - d.workTapePos 1)
        by_cases hz : d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
        · simp [hz, FinTM.bufferTape,
            show (z - d.workTapePos 1).toNat < w.length by omega]
        · rw [if_neg hz]
          unfold ct FinTM.bufferTape
          split_ifs with hzero
          · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
          · rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
  have hlCut : ∀ u < l,
      ((counterLoopTM inputSeekStep () none).runFrom (rw₁.mapState fun _ => .dec .run) u).state ≠
        some .done := by
    rw [hstart]
    exact fun u hu => (hloop₀.2.1 u hu).1
  have hclear₀ := clearTM_run_ofCfg 1 (List.replicate w.length true)
    (lc.mapState fun _ => SweepPhase.sweep) rfl (by
      intro z _ _
      simp [lc, Cfg.mapState])
  let finish : Cfg 2 Bool SweepPhase x :=
    ⟨some .done, ⟨p, by omega⟩, d.workTapes, d.workTapePos, d.output⟩
  have hclear : (clearTM 2 1).runFrom (lc.mapState fun _ => .sweep)
      (2 * w.length + 2) = finish := by
    simpa only [List.length_replicate] using hclear₀.1.trans (by
      apply Cfg.ext <;> try rfl
      funext j z
      by_cases hj : j = 1
      · subst j
        simp only [lc, finish, Cfg.mapState, Option.map_some, List.length_replicate,
          true_and, if_true]
        rw [hblank]
        split_ifs with hz
        · rfl
        · unfold FinTM.bufferTape
          split_ifs with hzero
          · rw [List.getElem?_eq_none (by simp; omega)]
          · rfl
      · simp [lc, finish, Cfg.mapState, hj])
  have hcCut : ∀ u < 2 * w.length + 2,
      ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).state ≠ some .done := by
    simpa only [List.length_replicate] using hclear₀.2.1
  -- The three stationary dispatches preserve the original work-head intervals.
  have hcr := seamCompTM_run_ofCfg (copyTM 2 0 1) .done inputSeekRewind .start
    hcopy rfl hcopy₀.2.1 hrewind
  have hcrCut := seamCompTM_firstReturn_ofCfg (copyTM 2 0 1) .done inputSeekRewind .start .done
    hcopy rfl hcopy₀.2.1 hrewind rfl hrCut
  have hcl := seamCompTM_run_ofCfg
    (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
    (counterLoopTM inputSeekStep () none) (.dec .run) hcr rfl hcrCut hloop
  have hclCut := seamCompTM_firstReturn_ofCfg
    (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
    (counterLoopTM inputSeekStep () none) (.dec .run) .done hcr rfl hcrCut hloop rfl hlCut
  have hall := seamCompTM_run_ofCfg
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
      (counterLoopTM inputSeekStep () none) (.dec .run)) (Sum.inr .done)
    (clearTM 2 1) .sweep hcl rfl hclCut hclear
  have hallCut := seamCompTM_firstReturn_ofCfg
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
      (counterLoopTM inputSeekStep () none) (.dec .run)) (Sum.inr .done)
    (clearTM 2 1) .sweep .done hcl rfl hclCut hclear rfl hcCut
  have hdmap : ((d₀.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl = d := by
    apply Cfg.ext <;> try rfl
    simpa [d₀, Cfg.mapState] using hd.symm
  have hcSpan : ∀ u ≤ 2 * w.length + 2, ∀ j,
      ((copyTM 2 0 1).runFrom d₀ u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    have h := hcopy₀.2.2 j u hu
    fin_cases j <;> simpa [d₀] using h
  have hrSpan : ∀ u ≤ r, ∀ j, (inputSeekRewind.runFrom rw₀ u).workTapePos j ∈
      Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    rw [hrHeads u hu]
    simp [rw₀, d₁, d₀, Cfg.mapState, Finset.mem_Icc]
  have hlSpan : ∀ u ≤ l, ∀ j,
      ((counterLoopTM inputSeekStep () none).runFrom
        (rw₁.mapState fun _ => .dec .run) u).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    rw [hstart]
    fin_cases j
    · obtain ⟨a, v, _, hv⟩ := hloop₀.2.2.2 u hu
      have hh := hv 0
      rw [inputSeekStep_run _ (hstate a), horbit, inputSeekStep_run c rfl] at hh
      have hh' : ((counterLoopTM inputSeekStep () none).runFrom
          (counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1)) u).workTapePos 0 =
            d.workTapePos 0 := hh
      change ((counterLoopTM inputSeekStep () none).runFrom
        (counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1)) u).workTapePos 0 ∈
          Finset.Icc (d.workTapePos 0 - 1) (d.workTapePos 0 + (w.length : ℤ))
      rw [hh']
      simp [Finset.mem_Icc]
    · exact hloop₀.2.2.1 u hu
  have hclearSpan : ∀ u ≤ 2 * w.length + 2, ∀ j,
      ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    have h := hclear₀.2.2 j u (by simpa using hu)
    fin_cases j
    · change (if (0 : Fin 2) = 1 then _ else _) at h
      rw [if_neg (by decide)] at h
      have h' : ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos 0 =
          d.workTapePos 0 := h
      change ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos 0 ∈
        Finset.Icc (d.workTapePos 0 - 1) (d.workTapePos 0 + (w.length : ℤ))
      rw [h']
      simp [Finset.mem_Icc]
    · simpa [lc, Cfg.mapState] using h
  have hcrSpan := inputSeek_seam_range _ _ _ _ hcopy rfl hcopy₀.2.1 _ _ hcSpan hrSpan
  have hclSpan := inputSeek_seam_range _ _ _ _ hcr rfl hcrCut _ _ hcrSpan hlSpan
  have hallSpan := inputSeek_seam_range _ _ _ _ hcl rfl hclCut _ _ hclSpan hclearSpan
  rw [hdmap] at hall hallCut hallSpan
  refine ⟨((2 * w.length + 2 + 1 + r) + 1 + l) + 1 + (2 * w.length + 2), ?_,
    hallCut, ?_, ?_⟩
  · have ho := counterOverhead_le w
    rw [hp] at ho
    change r ≤ d.inputPos.val + 3 at hr
    dsimp [l]
    omega
  · intro u hu j
    have h := Finset.mem_Icc.mp (hallSpan u hu j)
    rw [abs_le]
    constructor <;> omega
  · change (inputSeekMachine.runFrom d _).state = _ ∧ _
    rw [show inputSeekMachine.runFrom d _ = finish.mapState Sum.inr from hall]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/InputLength.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the input length in binary (§12.8, R8.5c)

The native-input row R8.5c of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3, §12.8b): count the native input into a
little-endian binary word on a dedicated work tape, `Nat.bits |x|`, in linear
time and logarithmic work space. It is a `Bool` module; a rich host runs it
lifted along its digit embedding (`Turing.MultiTapeTM.liftSymbols`), with
unchanged time and space. The record template and the initial record
(`Build/RecordTable.lean`) take their position width from it, and the
space-constructibility witnesses of chapter 4 count with it.

**Status: proved.** The framed input-length contract is proved by a single
input pass with a binary counter, followed by the public input rewind.

## Design

* **Own module** (§12.8b decision proposal W1-5): the natural home is beside
  `Turing.exists_inputSeekTM` in `Build/InputCall.lean`, which an in-flight fill
  batch owns. This module imports only `Build/CounterLoop`, so the
  constructibility files can import it without the record layer; 12.2c may fold
  it into `Build/InputCall.lean`.
* **Framed output.** The dedicated tape need only be blank on the interval the
  word and its two delimiters occupy, so the module also runs on a tape that
  carries unrelated data elsewhere.
* **Input position.** The module starts with the input head at `1` and returns it
  there, as `Turing.inputCopyTM` and `Turing.inputFoldTM` do.

## Main results

* `Turing.exists_inputLengthTM` — write `Nat.bits |x|` on a dedicated tape
  (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1: a machine counts its input
  length in binary with a work-tape counter in `O(log n)` space; p. 79, the
  space-constructibility of `log n`.)
-/

namespace Turing

/-- The six phases of the single-pass input counter. -/
private inductive InputLengthPhase where
  | count | carry | back | returnStart | returnScan | done
  deriving DecidableEq, Fintype

/-- The framed counter's only hand-built table: there is no public input-driven
counter. Carry and work-head rewind implement the counting phase of Catalog's
`f2_counterTM`; the native-input return uses the public input-fold transition
and rewind contract.

**Fill appendix.** The input-advance step is separate from the carry, costing
one extra step per round. A round with `p` cleared digits therefore costs
`2*p + 3`; its cost plus twice the change in the true-bit count is five.
The exit is stationary so the least exit time has the same exact finish. -/
private def inputLengthMachine : MultiTapeTM 1 Bool InputLengthPhase where
  q₀ := .count
  tr := fun phase inp work =>
    match phase with
    | .count =>
      match inp with
      | some _ => inputMoveAction .pos .carry
      | none => inputMoveAction 0 .returnStart
    | .carry =>
      if work 0 = some true then tapeAction 0 0 (some (some false)) .pos .carry
      else tapeAction 0 0 (some (some true)) .neg .back
    | .back =>
      match work 0 with
      | some _ => tapeAction 0 0 none .neg .back
      | none => tapeAction 0 0 none .pos .count
    | .returnStart => FinTM.controlAction .neg (some .returnScan)
    | .returnScan =>
      ((inputFoldTM 1 (fun (_ : Unit) (_ : Bool) => ()) ()).tr (.bwd ()) inp work).mapState
        (fun q => match q with | .done _ => .done | _ => .returnScan)
    | .done => inputMoveAction 0 .done

/-- Splitting the canonical digits at their first zero also gives the successor's
canonical digits. The second alternative is the width-extension case.

**Proof sketch.** Binary induction removes the low digit. A zero ends the carry;
a one adds one cleared digit to the induction hypothesis. -/
private theorem inputLength_digits (n : ℕ) :
    ∃ p : ℕ, ∃ v : List Bool,
      (n.bits = List.replicate p true ++ false :: v ∨
        n.bits = List.replicate p true ∧ v = []) ∧
      (n + 1).bits = List.replicate p false ++ true :: v := by
  induction n using Nat.binaryRec' with
  | zero => exact ⟨0, [], Or.inr ⟨by simp, rfl⟩, by simp⟩
  | bit b n h ih =>
    cases b with
    | false =>
      refine ⟨0, n.bits, Or.inl ?_, ?_⟩
      · simpa using Nat.bits_append_bit n false h
      · simpa only [Nat.bit_val, Bool.toNat_false, Nat.add_zero,
          List.replicate_zero, List.nil_append] using Nat.bit1_bits n
    | true =>
      obtain ⟨p, v, old, next⟩ := ih
      refine ⟨p + 1, v, ?_, ?_⟩
      · rw [Nat.bits_append_bit n true h, List.replicate_succ]
        rcases old with old | ⟨old, rfl⟩
        · exact Or.inl (by simp [old])
        · exact Or.inr ⟨by simp [old], rfl⟩
      · have he : Nat.bit true n + 1 = 2 * (n + 1) := by
          simp [Nat.bit_val]; omega
        rw [he, Nat.bit0_bits (n + 1) (by omega), next, List.replicate_succ]
        rfl


/-- The split gives the potential change and the maximal visited offset. -/
private theorem inputLength_charge (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v) :
    (n + 1).bits.count true + p = n.bits.count true + 1 ∧
      p < (n + 1).bits.length := by
  rw [next]
  rcases old with old | ⟨old, rfl⟩ <;> simp [old, List.count_append, List.count_replicate] <;> omega

/-- A counter trace configuration. Only a prefix of the replacement word has
been written; all cells outside that prefix retain their entry values. -/
private def inputLengthCfg {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (s : InputLengthPhase) (ip : Fin (x.length + 2))
    (z : ℤ) : Cfg 1 Bool InputLengthPhase x :=
  { state := some s
    inputPos := ip
    workTapes := fun _ a =>
      if d.workTapePos 0 ≤ a ∧ a < d.workTapePos 0 + (r : ℤ)
      then FinTM.bufferTape w (a - d.workTapePos 0)
      else d.workTapes 0 a
    workTapePos := fun _ => d.workTapePos 0 + z
    output := d.output }

/-- The unwritten prefix with zero head offset leaves the data fields alone. -/
private theorem inputLengthCfg_zero {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (s : InputLengthPhase) (ip : Fin (x.length + 2)) :
    inputLengthCfg d w 0 s ip 0 = {d with state := some s, inputPos := ip} := by
  apply Cfg.ext <;> simp only [inputLengthCfg, Nat.cast_zero, add_zero]
  · funext j a
    have : j = 0 := Subsingleton.elim _ _
    subst j
    split_ifs with h
    · omega
    · rfl
  · funext j
    exact congrArg d.workTapePos (Subsingleton.elim _ _)

/-- Writing the next prefix cell follows the public framed-write identity.

**Proof sketch.** The one-tape action supplies the configuration update;
`catalog_write_take` supplies the entire tape equality, including its frame. -/
private theorem inputLength_write {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (hr : r < w.length) (s s' : InputLengthPhase)
    (ip : Fin (x.length + 2)) (m : SignType)
    (htr : inputLengthMachine.tr s
      (inputLengthCfg d w r s ip r).inputSymbol
      (inputLengthCfg d w r s ip r).workTapeSymbols =
        tapeAction 0 0 (some (some w[r])) m s') :
    inputLengthMachine.step (inputLengthCfg d w r s ip r) =
      inputLengthCfg d w (r + 1) s' ip ((r : ℤ) + m) := by
  rw [step_of_tapeAction_write _ _ 0 0 (some w[r]) m rfl htr]
  apply Cfg.ext
  · rfl
  · simp only [inputLengthCfg, moveInputPos_zero]
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [Function.update_self, inputLengthCfg] using
      catalog_write_take (d.workTapes 0) (d.workTapePos 0) w r hr
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, inputLengthCfg]
    omega
  · rfl


/-- One input symbol drives one framed increment, including width extension.

**Proof sketch.** The forward configurations replace successive low bits by
zeros; the first non-true cell is replaced by one on the turn. The return
configurations keep this prefix and move over its zeros to the left delimiter.
The two direct inductions concern this cyclic table, whose return state starts
the next round. At every intermediate time the head is between minus one and
`p`, relative to the entry head. -/
private theorem inputLength_round {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (hs : d.state = some .count) (hip : d.inputPos.val = n + 1) (hn : n < x.length)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (htape : ∀ a : ℤ, -1 ≤ a → a ≤ (n.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = FinTM.bufferTape n.bits a) :
    inputLengthMachine.runFrom d (2 * p + 3) =
        inputLengthCfg d (n + 1).bits (p + 1) .count
          (moveInputPos d.inputPos .pos) 0 ∧
      ∀ u ≤ 2 * p + 3,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (p : ℤ) := by
  let w := (n + 1).bits
  let ip := moveInputPos d.inputPos .pos
  let F := fun r : ℕ => inputLengthCfg d w r .carry ip r
  let R := fun r : ℕ => inputLengthCfg d w (p + 1) .back ip ((r : ℤ) - 1)
  let D := inputLengthCfg d w (p + 1) .count ip 0
  have plen : p < w.length := (inputLength_charge n p v old next).2
  have oldlen : p ≤ n.bits.length := by
    rcases old with h | ⟨h, _⟩ <;> simp [h]
  have fzero : inputLengthMachine.step d = F 0 := by
    have hi : d.inputSymbol = some x[n] := inputSymbolInner n (by omega) hn
    rw [step_of_inputMoveAction _ _ .pos hs (q' := .carry) (by
      simp [inputLengthMachine, hi])]
    exact (inputLengthCfg_zero d w .carry ip).symm
  have forward (r : ℕ) (hr : r < p) : inputLengthMachine.step (F r) = F (r + 1) := by
    have read : (F r).workTapeSymbols 0 = some true := by
      have cell := htape r (by omega) (by omega)
      have bit : n.bits[r]? = some true := by
        rcases old with h | ⟨h, _⟩ <;>
          simp [h, List.getElem?_append, hr]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat] using
        cell.trans (by simpa using bit)
    have digit : w[r] = false := by
      simp [w, next, hr]
    simpa only [F, Nat.cast_add, Nat.cast_one, SignType.cast] using
      inputLength_write d w r (by omega) .carry .carry ip .pos (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have turn : inputLengthMachine.step (F p) = R p := by
    have read : (F p).workTapeSymbols 0 ≠ some true := by
      have cell := htape p (by omega) (by omega)
      have bit : n.bits[p]? ≠ some true := by
        rcases old with h | ⟨h, _⟩ <;> simp [h]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, cell] using bit
    have digit : w[p] = true := by simp [w, next]
    simpa only [F, R, SignType.cast, sub_eq_add_neg] using
      inputLength_write d w p plen .carry .back ip .neg (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have backward (r : ℕ) (hr : r < p) : inputLengthMachine.step (R (r + 1)) = R r := by
    have read : (R (r + 1)).workTapeSymbols 0 = some false := by
      have digit : w[r]? = some false := by
        simp [w, next, List.getElem?_append, hr]
      simp [R, inputLengthCfg, Cfg.workTapeSymbols, show (r : ℤ) < p + 1 by omega,
        FinTM.bufferTape_nat, digit]
    rw [step_of_tapeAction_move _ _ 0 0 .neg rfl (q' := .back) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, SignType.cast]
    omega
  have entry : inputLengthMachine.step (R 0) = D := by
    have read : (R 0).workTapeSymbols 0 = none := by
      have cell := htape (-1) (by omega) (by omega)
      simpa [R, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_left] using cell
    rw [step_of_tapeAction_move _ _ 0 0 .pos rfl (q' := .count) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, D, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp [SignType.cast]
  have step_run (a : Cfg 1 Bool InputLengthPhase x) (u : ℕ) :
      inputLengthMachine.runFrom a (u + 1) =
        inputLengthMachine.step (inputLengthMachine.runFrom a u) :=
    MultiTapeTM.runFrom_succ_eq_step'
  have reachesF : ∀ r ≤ p, inputLengthMachine.runFrom d (r + 1) = F r := by
    intro r
    induction r with
    | zero => intro _; rw [Nat.zero_add, MultiTapeTM.runFrom_one]; exact fzero
    | succ r ih =>
      intro hr
      rw [step_run, ih (by omega), forward r (by omega)]
  have reachesR : ∀ r ≤ p, inputLengthMachine.runFrom d (p + 2 + r) = R (p - r) := by
    intro r
    induction r with
    | zero =>
      intro _
      simpa only [Nat.add_zero, Nat.sub_zero] using
        (show inputLengthMachine.runFrom d (p + 2) = R p by
          rw [show p + 2 = (p + 1) + 1 by omega, step_run,
            reachesF p le_rfl, turn])
    | succ r ih =>
      intro hr
      rw [show p + 2 + (r + 1) = (p + 2 + r) + 1 by omega,
        step_run, ih (by omega)]
      rw [show p - r = (p - (r + 1)) + 1 by omega, backward _ (by omega)]
  have finish : inputLengthMachine.runFrom d (2 * p + 3) = D := by
    rw [show 2 * p + 3 = (p + 2 + p) + 1 by omega,
      step_run, reachesR p le_rfl, Nat.sub_self, entry]
  refine ⟨finish, ?_⟩
  intro u hu
  by_cases hz : u = 0
  · subst u; simp
  by_cases hf : u ≤ p + 1
  · rw [show u = (u - 1) + 1 by omega, reachesF _ (by omega)]
    simp only [F, inputLengthCfg]
    constructor <;> omega
  by_cases hb : u ≤ 2 * p + 2
  · rw [show u = p + 2 + (u - (p + 2)) by omega, reachesR _ (by omega)]
    simp only [R, inputLengthCfg]
    constructor <;> omega
  · rw [show u = 2 * p + 3 by omega, finish]
    simp only [D, inputLengthCfg, add_zero]
    constructor <;> omega

/-- A completely written word agrees with its buffer throughout the originally
blank slot, including both delimiters. -/
private theorem inputLengthCfg_read {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (w : List Bool) (s : InputLengthPhase)
    (ip : Fin (x.length + 2)) (N : ℕ)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (N : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none)
    (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (N : ℤ)) :
    (inputLengthCfg d w w.length s ip 0).workTapes 0 (d.workTapePos 0 + a) =
      FinTM.bufferTape w a := by
  simp only [inputLengthCfg, add_sub_cancel_left]
  split_ifs with h
  · rfl
  · rw [blank a ha hb]
    by_cases hn : 0 ≤ a
    · have hw' : w.length ≤ a.toNat := by omega
      simp [FinTM.bufferTape, hn, List.getElem?_eq_none hw']
    · simp [FinTM.bufferTape, hn]

/-- Consecutive canonical counter words differ only in the overwritten carry
prefix; overwriting that prefix therefore composes the two exterior frames.

**Proof sketch.** Below the origin nothing is touched. Inside the new prefix
the two sides read the new word. Above it the old and new words have the same
suffix, and their upper boundaries agree there, even on width extension. -/
private theorem inputLengthCfg_merge {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (ip ip' : Fin (x.length + 2)) :
    inputLengthCfg (inputLengthCfg d n.bits n.bits.length .count ip 0)
        (n + 1).bits (p + 1) .count ip' 0 =
      inputLengthCfg d (n + 1).bits (n + 1).bits.length .count ip' 0 := by
  have plen : p < (n + 1).bits.length := (inputLength_charge n p v old next).2
  apply Cfg.ext <;> simp only [inputLengthCfg, add_zero]
  funext j a
  by_cases hlow : d.workTapePos 0 ≤ a
  · by_cases hpre : a < d.workTapePos 0 + ((p + 1 : ℕ) : ℤ)
    · have hnew : a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by omega
      simp only [hlow, hpre, hnew, and_self, ite_true]
    · have offset : p + 1 ≤ (a - d.workTapePos 0).toNat := by omega
      have sameEnd : a < d.workTapePos 0 + (n.bits.length : ℤ) ↔
          a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by
        rcases old with h | ⟨h, hv⟩
        · simp [h, next]
        · simp [h, next, hv]; omega
      have suffix : FinTM.bufferTape n.bits (a - d.workTapePos 0) =
          FinTM.bufferTape (n + 1).bits (a - d.workTapePos 0) := by
        simp only [FinTM.bufferTape, if_pos (by omega : 0 ≤ a - d.workTapePos 0)]
        rcases old with h | ⟨h, hv⟩
        · simp only [h, next, List.getElem?_append,
            List.length_replicate, if_neg (by omega : ¬(a - d.workTapePos 0).toNat < p)]
          rw [List.getElem?_cons, List.getElem?_cons]
          simp [show (a - d.workTapePos 0).toNat - p ≠ 0 by omega]
        · simp [h, next, hv, List.getElem?_eq_none, offset]; omega
      simp only [hlow, hpre, true_and, ite_false, sameEnd, suffix]
  · simp only [hlow, false_and, ite_false]

/-- Counting the first `n` input symbols preserves the exterior frame and pays
exactly five units per symbol after including twice the true-bit potential.

**Proof sketch.** Induct on the number of symbols. The framed round theorem
provides each physical segment, the digit split identifies its next canonical
word, and the frame-composition lemma joins it to the original configuration.
The potential equation telescopes, while both segments' head intervals fit the
new binary width. -/
private theorem inputLength_count {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (hs : d.state = some .count)
    (hip : d.inputPos = 1)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (x.length.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none) :
    ∀ n (hn : n ≤ x.length), ∃ t,
      t + 2 * n.bits.count true = 5 * n ∧
      inputLengthMachine.runFrom d t =
        inputLengthCfg d n.bits n.bits.length .count ⟨n + 1, by omega⟩ 0 ∧
      ∀ u ≤ t,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (n.bits.length : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_zero]
      simp only [Nat.zero_bits, List.length_nil, inputLengthCfg_zero]
      apply Cfg.ext <;> simp [hs, hip]
    · intro u hu
      have : u = 0 := by omega
      subst u
      simp
  | succ n ih =>
    intro hn
    obtain ⟨t, charge, reached, bounded⟩ := ih (by omega)
    obtain ⟨p, v, old, next⟩ := inputLength_digits n
    have accounting := inputLength_charge n p v old next
    let ip : Fin (x.length + 2) := ⟨n + 1, by omega⟩
    let c := inputLengthCfg d n.bits n.bits.length .count ip 0
    have oldwidth : n.bits.length ≤ x.length.bits.length :=
      Complexity.LogProg.length_bits_mono (show n ≤ x.length by omega)
    have newwidth : n.bits.length ≤ (n + 1).bits.length :=
      Complexity.LogProg.length_bits_mono (Nat.le_succ n)
    have field (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (n.bits.length : ℤ)) :
        c.workTapes 0 (c.workTapePos 0 + a) = FinTM.bufferTape n.bits a := by
      simpa only [c, inputLengthCfg, add_zero] using
        inputLengthCfg_read d n.bits .count ip x.length.bits.length blank a ha (by omega)
    have round := inputLength_round c n p v rfl rfl (by omega) old next field
    have inext : moveInputPos c.inputPos .pos = (⟨n + 1 + 1, by omega⟩ : Fin (x.length + 2)) := by
      rw [moveInputPos_pos_of_ne_right _ (by simp only [c, inputLengthCfg, ip]; omega)]
      rfl
    have ctime : inputLengthMachine.runFrom d t = c := reached
    refine ⟨t + (2 * p + 3), by omega, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, ctime, round.1, inext]
      exact inputLengthCfg_merge d n p v old next ip _
    · intro u hu
      by_cases before : u ≤ t
      · obtain ⟨lower, upper⟩ := bounded u before
        exact ⟨lower, by omega⟩
      · have localBound := round.2 (u - t) (by omega)
        rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, ctime]
        have hcpos : c.workTapePos 0 = d.workTapePos 0 := by simp [c, inputLengthCfg]
        rw [hcpos] at localBound
        exact ⟨localBound.1, by omega⟩

/-- **R8.5c, the input length** (design §12.8a §3, §12.8b). There is a `Bool`
module with an entry and an exit state and `K + 1` tapes with the following
contract. Start it at its entry with the input head at position `1`, tape `0`
blank on the `|bits |x|| + 2` cells from one left of its head to one right of
where the word will end, and the other tapes blank. It reaches its exit within
`C·(|x| + 1)` steps, and not earlier. At that point tape `0` holds
`Nat.bits |x|` from its head, and every other cell, every head, the input
position and the output are as they were. Up to the exit every work head stays
within `C·(|bits |x|| + 1)` cells of its entry position, so the work space is
logarithmic in `|x|` however far the input head travels. At `x = []` nothing is
written, since `Nat.bits 0 = []`.

**Proof sketch.** One pass over the input drives an in-place binary counter on
tape `0`. For each input symbol, move the input head right and increment the
counter: the carry turns the maximal `true` prefix to `false` and writes `true`
on the next cell, which is the blank just after the word when the counter
overflows, so the width grows by one cell exactly at the powers of two. A
return pass brings the counter head back to its first cell, guided by the
blank delimiter on its left. At the input's right end marker, walk the input
head back to position `1` (the `Turing.inputFoldTM_run_ofCfg` return) and exit.
The increments from `0` to `|x|` cost `Σ_v (2·p_v + 2)` for the true-prefix
lengths `p_v`, which telescopes against twice the number of `true` cells, as
in `Turing.counterOverhead_le_of_le` mirrored, so the total is linear in
`|x|`. Route: the counting phase is the transition table of Catalog's private
`f2_counterTM` without its emission, framed; no public input-driven loop host
exists (`Turing.counterLoopTM` needs its round count on a tape, which is what
is being computed), so the fill proves the framed round induction for this
table directly and records the pair with `f2_counterTM` for 12.2c, which can
re-derive `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` from this row.
The counter head stays in `[pos - 1, pos + |bits |x||]`. -/
theorem exists_inputLengthTM :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM (K + 1) Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} (d : Cfg (K + 1) Bool S x), d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((Nat.bits x.length).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((Nat.bits x.length).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + ((Nat.bits x.length).length : ℤ)
                  then FinTM.bufferTape (Nat.bits x.length) (q - d.workTapePos j)
                else d.workTapes j q } := by
  refine ⟨0, InputLengthPhase, inferInstance, inferInstance, inputLengthMachine,
    .count, .done, 6, ?_⟩
  intro x d hs hip blank _
  obtain ⟨t, charge, counted, countHeads⟩ := inputLength_count d hs hip blank x.length le_rfl
  let c := inputLengthCfg d x.length.bits x.length.bits.length .count
    (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0
  let back : Cfg 1 Bool InputLengthPhase x := {c with state := some .returnStart}
  have endSymbol : c.inputSymbol = none := by
    apply Cfg.inputSymbol_of_end
    rfl
  have turn : inputLengthMachine.step c = back := by
    rw [step_of_inputMoveAction _ _ 0 rfl (q' := .returnStart) (by
      simp [inputLengthMachine, endSymbol])]
    simp only [moveInputPos_zero]
    rfl
  obtain ⟨r, hr, returned, returnHeads⟩ := FinTM.rewind_heads inputLengthMachine
    .returnStart .returnScan (some .done) (by intros; rfl)
    (by
      intro inp work
      change (((inputFoldTM 1 (fun (_ : Unit) (_ : Bool) => ()) ()).tr
        (.bwd ()) inp work).mapState
        (fun q => match q with | .done _ => InputLengthPhase.done | _ => .returnScan)) = _
      rw [inputFoldTM_tr_bwd]
      cases inp <;> simp only [inputMoveAction_eq, FinTM.controlAction_def]
      all_goals
        change Action.mk _ _ _ _ = _
        simp only [Action.mapState_inputTape, Action.mapState_output,
          Action.mapState_state, Option.map_some]
        congr 1 <;> first | rfl | exact funext (Action.mapState_workTapes _ _)) back rfl
  have reachedBack : inputLengthMachine.runFrom d (t + 1) = back := by
    rw [MultiTapeTM.runFrom_succ_eq_step', counted]
    exact turn
  have finish : inputLengthMachine.runFrom d (t + 1 + r) =
      {back with state := some .done, inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, reachedBack, returned]
  have deadline : t + 1 + r ≤ 6 * (x.length + 1) := by
    have hr' : r ≤ x.length + 3 := by simpa [back, c, inputLengthCfg] using hr
    omega
  have heads (u : ℕ) (hu : u ≤ t + 1 + r) :
      d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
      (inputLengthMachine.runFrom d u).workTapePos 0 ≤
        d.workTapePos 0 + (x.length.bits.length : ℤ) := by
    by_cases h : u ≤ t
    · exact countHeads u h
    · have hu' : u - (t + 1) ≤ r := by omega
      rw [show u = t + 1 + (u - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, reachedBack, returnHeads _ hu']
      simp only [back, c, inputLengthCfg, add_zero]
      constructor <;> omega
  -- The public fixed-stop entry contract keeps the exact completed configuration.
  obtain ⟨first, firstLe, firstCut, firstEnd⟩ := MultiTapeTM.exists_first_entry_of_fixed
    inputLengthMachine (fun q => q = .done) d
    {back with state := some .done, inputPos := 1} (t + 1 + r)
    (by
      rintro z ⟨q, hq, rfl⟩
      rw [step_of_inputMoveAction _ _ 0 hq (q' := .done) rfl]
      simp only [moveInputPos_zero]
      apply Cfg.ext <;> simp [hq])
    ⟨.done, rfl, rfl⟩ finish
  have same : inputLengthMachine.runFrom d (t + 1 + r) =
      inputLengthMachine.runFrom d first := finish.trans firstEnd.symm
  refine ⟨first, firstLe.trans deadline, ?_, ?_, ?_⟩
  · intro u hu hs
    exact firstCut u hu ⟨.done, hs, rfl⟩
  · intro u hu j
    have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
    subst j
    obtain ⟨lower, upper⟩ := heads u (hu.trans firstLe)
    apply abs_le.mpr
    push_cast
    constructor <;> omega
  · rw [← same, finish]
    apply Cfg.ext
    · rfl
    · exact hip.symm
    · funext j a
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · funext j
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · rfl

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/InputRewind.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The input rewind as a machine

A small machine that returns the native input head to the first input cell: one step left, then
left while the head reads an input symbol, then one step right at the left blank, into a
stationary live state. From any configuration in its start state whose input head is at position
`p ≥ 1`, it reaches its last state at exactly time `p + 1`, not earlier, with the input head at
`1`, and leaves every work tape, every work head and the output unchanged at every time. A
machine that rewinds its input in one phase of a composite uses it as that phase.

Also, the composition of two state relabelings of a configuration is one relabeling.

## Main definitions

* `Turing.InputRewindPhase` — the rewind's three control states.
* `Turing.inputRewindTM` — the rewind over any number of work tapes.

## Main results

* `Turing.inputRewindTM_run` — the exact time, the first arrival at the last state, the
  endpoint, and the unchanged work tapes, heads and output.
* `Turing.inputRewindTM_step_done` — the last state is a stationary park.
* `Turing.Cfg.mapState_mapState` — relabeling twice is relabeling by the composite.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the input head and its moves.)
-/

namespace Turing

/-- **Relabeling twice is relabeling once**: renaming a configuration's states by `f` and then
by `g` renames them by `g ∘ f`.

**Proof sketch.** Compare the five fields through `Turing.Cfg.mapState`'s field equations; the
state is `Option.map_map`. -/
theorem Cfg.mapState_mapState {k : ℕ} {Symbol : Type*} {S₁ S₂ S₃ : Type*} {x : List Symbol}
    (c : Cfg k Symbol S₁ x) (f : S₁ → S₂) (g : S₂ → S₃) :
    (c.mapState f).mapState g = c.mapState (g ∘ f) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Option.map_map]
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext i q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext i
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]

/-- The input rewind's control states: the first left step, the scan, and the park. -/
inductive InputRewindPhase where
  /-- the first, unconditional left step -/
  | start
  /-- the scan left over the input symbols -/
  | scan
  /-- the stationary live park, reached with the input head at `1` -/
  | done
  deriving DecidableEq, Fintype

/-- **The input rewind**: one step left, then left while the input head reads a symbol, then one
step right at the left blank into the park, which stays put. It never writes, moves a work head or
emits. -/
def inputRewindTM (k : ℕ) : MultiTapeTM k Bool InputRewindPhase where
  q₀ := .start
  tr := fun q inp _ =>
    match q with
    | .start => FinTM.controlAction .neg (some .scan)
    | .scan =>
      match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- **The input rewind's run**: from a configuration in `start` whose input head is at
`p ≥ 1`, the machine is at `done` at exactly time `p + 1` and not earlier, with the input head at
`1` and everything else as it was; at every time up to then, its work tapes, work heads and output
are the start's.

**Proof sketch.** At time `r ≤ p` the configuration is the start's with the input head at
`p - r` (in `scan` for `r ≥ 1`): the first step moves left unconditionally, and each later step,
at `1 ≤ r < p`, reads an input symbol, since then `1 ≤ p - r ≤ |x|`, and moves left
(`Turing.FinTM.controlAction_apply`). At time `p` the head is on the left blank, and one step
right enters `done` at position `1`. -/
theorem inputRewindTM_run {k : ℕ} {x : List Bool} (d : Cfg k Bool InputRewindPhase x)
    (hstate : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    (inputRewindTM k).runFrom d (d.inputPos.val + 1) =
        { d with state := some .done, inputPos := 1 } ∧
      (∀ t < d.inputPos.val + 1, ((inputRewindTM k).runFrom d t).state ≠ some .done) ∧
      ∀ t ≤ d.inputPos.val + 1,
        ((inputRewindTM k).runFrom d t).workTapes = d.workTapes ∧
        ((inputRewindTM k).runFrom d t).workTapePos = d.workTapePos ∧
        ((inputRewindTM k).runFrom d t).output = d.output := by
  classical
  have hlt := d.inputPos.isLt
  -- the scan's trajectory
  let T : ℕ → Cfg k Bool InputRewindPhase x := fun r =>
    { d with
      state := some (if r = 0 then .start else .scan)
      inputPos := ⟨d.inputPos.val - r, by omega⟩ }
  have hT0 : T 0 = d := by
    refine Cfg.ext ?_ ?_ rfl rfl rfl
    · show some (if 0 = 0 then InputRewindPhase.start else .scan) = d.state
      rw [if_pos rfl, hstate]
    · refine Fin.ext ?_
      show d.inputPos.val - 0 = d.inputPos.val
      omega
  have hstep : ∀ r : ℕ, r ≤ d.inputPos.val - 1 → (inputRewindTM k).step (T r) = T (r + 1) := by
    intro r hr
    have hs : (T r).state = some (if r = 0 then .start else .scan) := rfl
    rw [MultiTapeTM.step_of_some hs]
    have htr : (inputRewindTM k).tr (if r = 0 then .start else .scan) (T r).inputSymbol
        (T r).workTapeSymbols = FinTM.controlAction .neg (some .scan) := by
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        rfl
      · rw [if_neg hr0]
        have hread : (T r).inputSymbol = some (x[d.inputPos.val - r - 1]'(by omega)) := by
          refine inputSymbolInner (d.inputPos.val - r - 1) ?_ (by omega)
          show d.inputPos.val - r = 1 + (d.inputPos.val - r - 1)
          omega
        rw [hread]
        rfl
    rw [htr, FinTM.controlAction_apply]
    refine Cfg.ext ?_ ?_ rfl rfl rfl
    · show some InputRewindPhase.scan = some (if r + 1 = 0 then .start else .scan)
      rw [if_neg (Nat.succ_ne_zero r)]
    · show moveInputPos (T r).inputPos .neg = (T (r + 1)).inputPos
      rw [moveInputPos_neg_of_ne_left _ (by
        intro h
        have hv : d.inputPos.val - r = 0 := by
          have hvv := congrArg Fin.val h
          simpa [T] using hvv
        omega)]
      exact Fin.ext (by show d.inputPos.val - r - 1 = d.inputPos.val - (r + 1); omega)
  have hrun : ∀ r : ℕ, r ≤ d.inputPos.val → (inputRewindTM k).runFrom d r = T r := by
    intro r hr
    induction r with
    | zero => rw [MultiTapeTM.runFrom_zero, hT0]
    | succ r ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep r (by omega)]
  have hfinal : (inputRewindTM k).step (T d.inputPos.val) =
      { d with state := some .done, inputPos := 1 } := by
    have hs : (T d.inputPos.val).state = some .scan := by
      show some (if d.inputPos.val = 0 then InputRewindPhase.start else .scan) = some .scan
      rw [if_neg (by omega)]
    rw [MultiTapeTM.step_of_some hs]
    have hzero : (T d.inputPos.val).inputPos = 0 := by
      refine Fin.ext ?_
      show d.inputPos.val - d.inputPos.val = (0 : Fin (x.length + 2)).val
      rw [Fin.val_zero]
      omega
    have hread : (T d.inputPos.val).inputSymbol = none := Cfg.inputSymbol_of_zero hzero
    have htr : (inputRewindTM k).tr .scan (T d.inputPos.val).inputSymbol
        (T d.inputPos.val).workTapeSymbols = FinTM.controlAction .pos (some .done) := by
      rw [hread]
      rfl
    rw [htr, FinTM.controlAction_apply]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    show moveInputPos (T d.inputPos.val).inputPos .pos = (1 : Fin (x.length + 2))
    rw [hzero, moveInputPos_pos_of_ne_right (0 : Fin (x.length + 2))
      (by rw [Fin.val_zero]; omega)]
    exact Fin.ext (by simp)
  have hend : (inputRewindTM k).runFrom d (d.inputPos.val + 1) =
      { d with state := some .done, inputPos := 1 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun d.inputPos.val le_rfl, hfinal]
  refine ⟨hend, ?_, ?_⟩
  · intro t ht
    rw [hrun t (by omega)]
    show some (if t = 0 then InputRewindPhase.start else .scan) ≠ some .done
    by_cases ht0 : t = 0
    · rw [if_pos ht0]; decide
    · rw [if_neg ht0]; decide
  · intro t ht
    rcases Nat.lt_or_ge t (d.inputPos.val + 1) with hlt' | hge
    · rw [hrun t (by omega)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show t = d.inputPos.val + 1 by omega, hend]
      exact ⟨rfl, rfl, rfl⟩

/-- **The park stays put**: at `done` the rewind's step changes nothing. -/
theorem inputRewindTM_step_done {k : ℕ} {x : List Bool} (c : Cfg k Bool InputRewindPhase x)
    (hc : c.state = some .done) : (inputRewindTM k).step c = c := by
  rw [MultiTapeTM.step_of_some hc]
  show (FinTM.controlAction 0 (some InputRewindPhase.done)).apply c = c
  rw [FinTM.controlAction_apply]
  refine Cfg.ext ?_ ?_ rfl rfl rfl
  · rw [hc]
  · exact moveInputPos_zero c.inputPos

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

## ===== TCSlib/Complexity/TuringMachine/Build/Seam.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CfgFacts
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: seam composition (R2)

The configuration-level sequencing layer of the machine-construction
library (`machine-library-design.md` §12, R2): sequential composition of
two controllers over **any tape alphabet and from arbitrary
configurations** (the `_ofCfg` theorems; alphabet-generic since §13d G1). If
`M₁` carries a configuration `c₀` to `c₁` within `T₁` under a first-return
cut, and `M₂` carries `c₁` to `c₂` within `T₂`, the dispatch-glued
composite carries `c₀` to `c₂` within `T₁ + 1 + T₂` — the explicit
constant is `1`, one silent stationary dispatch step at the seam. The
canonical `Turing.Cfg.ofWords` seams of
`TCSlib.Complexity.TuringMachine.Build.Convention` are the `Bool`
specialization (`Turing.seamCompTM_run` and its siblings). This is the generic form of the
per-batch dispatch gluing re-proved in every A-chain and emitter batch,
and it exists at the configuration level precisely because the emitter
round-1 finding stands: *function-level* contracts cannot deliver
clean-return seams, so composing `ComputesFunInTime` contracts can never
replace this combinator.

**Status: proved.** The composite is a real definition
(state-sum dispatch in `Turing.bufferedCompTM`'s style, kept minimal), and
every §12 contract is proved (§12 fill epoch F1, gate closed 2026-10-09). The
§12.8 two-exit row `Turing.seamCompTM₂_run_ofCfg` (R8.8) is proved from the left
prefix `Turing.seamCompTM_runFrom_left` and the existing right lockstep.
The **phase host** `Turing.phaseHostTM`, with `Turing.phaseHostTM_run` (proved), is the
finite-dispatch generalization: many phases and a redirect table, one dispatch step per
redirect (landed before the §12.8 fill for the record rows). Its start state is
`Turing.phaseHostTM_q₀`, its table off the redirects `Turing.phaseHostTM_tr_of_red_none` and at a
redirect `Turing.phaseHostTM_tr_of_red_some`, and `Turing.phaseHostTM_run_le` runs a last phase up
to its exit without a dispatch.

## Design

* The glue is a **state sum** `S₁ ⊕ S₂`: left states run `M₁`'s table,
  right states run `M₂`'s, and the designated left anchor `exit` takes one
  stationary, silent, write-free transition to the right anchor `entry`.
  Dispatch-on-anchor (rather than dispatch-on-halt) matches the ABI: seam
  contracts end at a **live** anchor (`Build/Loop.lean`'s `hstart`/
  `hround` shape), and the catalog routines of
  `TCSlib.Complexity.TuringMachine.Build.Catalog` exit at live anchors.
* The space clause is stated in the **sharp per-tape form** (frozen
  decision 12.1): the headline is per-tape containment of visited sets —
  the composite's visited set on every work tape is contained in the
  union of the phases' — which implies both the per-tape sum bound and
  the max bound for disjointly-owned tapes, stated as corollaries.

## Main definitions

* `Turing.seamCompTM` — the dispatch-glued composite of two machines over
  any alphabet; at `Bool`, its canonical use is between `Turing.Cfg.ofWords`
  seams.
* `Turing.seamCompTM₂` — a continuation on each of two exit anchors (§12.8,
  R8.8).

## Main results

* `Turing.seamCompTM_run` — seam-to-seam composition within
  `T₁ + 1 + T₂`.
* `Turing.seamCompTM_firstReturn` — the composite inherits a first-return
  cut at the final anchor, so composites **whose phases satisfy the stated
  cuts** chain (round-1 finding R3: the cut excludes positive
  entry-equals-exit calls — those route through the release adapter below).
* `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`,
  `Turing.seamCompTM_visitedByTapeHead_ofCfg` — the **general-configuration**
  composition (round-1 repair R2): phase two starts from phase one's
  returned configuration with only the control state replaced, so arbitrary
  frames, displaced inactive heads, and accumulated output cross the
  dispatch intact; the canonical `Cfg.ofWords` theorems are its instances.
* `Turing.seamReleaseTM`, `Turing.seamReleaseTM_firstReturn`,
  `Turing.seamReleaseTM_visitedByTapeHead` — the **fresh-entry/release
  adapter** (round-1 repair R3): the entry action executes unconditionally
  from a fresh start state, so a positive call that returns to its own
  anchor becomes seam-consumable.
* `Turing.seamCompTM_visitedByTapeHead` — per-tape visited-set
  containment (the headline space clause, decision 12.1).
* `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg` — the left
  prefix of a seam under a strict exit cut, and the two-exit composition
  (§12.8, R8.8; the latter a statement).
* `Turing.seamCompTM_runFrom_right` — the right segment after the dispatch, at any
  offset (promoted from the private `seamComp_right` at MIG-0b; set-valued exits need it).
* `Turing.seamReleaseTM_step_fresh`, `Turing.seamReleaseTM_step_inr`,
  `Turing.seamReleaseTM_runFrom_pos` — the release adapter's steps and its pointwise
  lockstep at every positive time (promoted from the private `seamRelease_*` lemmas at
  MIG-0b, design §16a item 5).
* `Turing.seamCompTM_spaceUsed_le_add_ofCfg` — the general-configuration sum bound on total
  space, with phase two's endpoint unconstrained.
* `Turing.seamCompTM_spaceUsedByTape_le_add`,
  `Turing.seamCompTM_spaceUsed_le_add`,
  `Turing.seamCompTM_spaceUsedByTape_le_max` — the sum and
  max-for-disjointly-owned-tapes corollaries.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; phase-sequenced simulations
  are the folklore engine of §1.4–§1.7.)
* [Balbach22] F. Balbach, *The Cook–Levin theorem*, Isabelle AFP entry
  `Cook_Levin`, 2022. (The composition-combinator architecture precedent,
  as in `TCSlib.Complexity.TuringMachine.Composition`.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model): the seam-composition shape is
  `StackRename`'s `executes_in_sum`.
-/

namespace Turing

variable {k : ℕ} {S₁ S₂ : Type*} {x : List Bool}

/-- **R2, the seam composite** (design §12; [Bon26], `executes_in_sum`).
The dispatch-glued sequential composite of `M₁` and `M₂`, over any tape
alphabet (at `Bool`, typically between `Turing.Cfg.ofWords` seams): states
are the sum `S₁ ⊕ S₂`, left states run
`M₁`'s transition table and right states `M₂`'s (each halting where its
phase halts), except that the designated left anchor `exit` takes one
stationary, silent, write-free dispatch step to the right anchor `entry`.
The composite starts at `M₁`'s initial state; a run launched at a left
seam anchor is the intended use. -/
def seamCompTM {Symbol : Type*} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) :
    MultiTapeTM k Symbol (S₁ ⊕ S₂) where
  q₀ := Sum.inl M₁.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      if s = exit then ⟨0, fun _ => (none, 0), none, some (Sum.inr entry)⟩
      else
        let a := M₁.tr s inp w
        ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inl⟩
    | Sum.inr s =>
      let a := M₂.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- At a right state, the seam composite uses the second machine's action with its
successor state injected into the right summand. -/
theorem seamCompTM_tr_inr {Symbol : Type*} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry q : S₂)
    (inp : Option Symbol) (work : Fin k → Option Symbol) :
    (seamCompTM M₁ exit M₂ entry).tr (Sum.inr q) inp work =
      (M₂.tr q inp work).mapState Sum.inr := by
  change Action.mk (M₂.tr q inp work).inputTape (M₂.tr q inp work).workTapes
    (M₂.tr q inp work).output ((M₂.tr q inp work).state.map Sum.inr) = _
  rw [← Action.mapState_inputTape Sum.inr (M₂.tr q inp work),
    ← funext (Action.mapState_workTapes Sum.inr (M₂.tr q inp work)),
    ← Action.mapState_output Sum.inr (M₂.tr q inp work),
    ← Action.mapState_state Sum.inr (M₂.tr q inp work)]

/-- Away from the exit, one left step is exactly the state-mapped source step,
including the absorbing halted case. -/
private lemma seamComp_step_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (M₁.step c).mapState Sum.inl := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    have hq : q ≠ exit := fun h => hc (hs.trans (congrArg some h))
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    dsimp only [seamCompTM]
    rw [if_neg hq]
    rfl

/-- Right steps commute with state mapping, even after a source halt.

**Proof sketch.** Renaming preserves the input and work reads. A halted configuration
stays fixed on both sides. For a live state, the right transition row and
`Cfg.mapState_apply` identify the two steps. -/
private lemma seamComp_step_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (c : Cfg k Symbol S₂ x) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
      (M₂.step c).mapState Sum.inr := by
  have hin : (c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).inputSymbol = c.inputSymbol :=
    Cfg.inputSymbol_congr _ _ (by rw [Cfg.mapState_inputPos])
  have hwork : (c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).workTapeSymbols = c.workTapeSymbols := by
    funext i
    rw [Cfg.workTapeSymbols_eq, Cfg.workTapeSymbols_eq,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt (cfg := c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂))
        (by rw [Cfg.mapState_state, hs, Option.map_none]),
      MultiTapeTM.step_of_halt hs]
  | some q =>
    rw [MultiTapeTM.step_of_some (cfg := c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂))
        (q := Sum.inr q) (by rw [Cfg.mapState_state, hs, Option.map_some]),
      MultiTapeTM.step_of_some hs, hin, hwork, seamCompTM_tr_inr]
    exact Cfg.mapState_apply Sum.inr _ c

/-- A stationary, silent, write-free action changes only the control field. -/
private lemma seam_stationary_apply {Symbol : Type*} {x : List Symbol} (c : Cfg k Symbol S₁ x) (q : S₁) :
    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
      { c with state := some q } := by
  simp [Action.apply]

/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
private lemma seamComp_dispatch {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state = some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (c.mapState fun _ => entry).mapState Sum.inr := by
  unfold MultiTapeTM.step
  simp only [Cfg.mapState, hc, Option.map_some]
  dsimp only [seamCompTM]
  rw [if_pos rfl, seam_stationary_apply]

/-- **R8.8, the left prefix of a seam** (design §12.8a; promoted from the
private `seamComp_left`, finding SC-4 of the §12.7 statement gate). If `M₁`,
started from an arbitrary configuration `c`, avoids its exit anchor at every
time strictly below `T`, then for every `t ≤ T` the composite started from the
left-mapped `c` is at the left-mapped `M₁` configuration at `t`. No endpoint
equation is required, and the endpoint itself is included. This is the
trajectory statement a host with two exits needs on the branch it does not
take.

**Proof sketch.** Induct on the time; the cut licenses the left-step
identity at every predecessor strictly before the endpoint. -/
theorem seamCompTM_runFrom_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c : Cfg k Symbol S₁ x} {T : ℕ}
    (hcut : ∀ t < T, (M₁.runFrom c t).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c.mapState Sum.inl) t =
      (M₁.runFrom c t).mapState Sum.inl := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      seamComp_step_left M₁ exit M₂ entry _ (hcut t (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']

/-- **The seam's right segment** (promoted from the private `seamComp_right` at MIG-0b, with its
universes and its proof; MIG-0a's export of the same name, over `Type`, is this statement's
instance): after the dispatch step, the composite runs the second machine in lockstep, for any
number of steps, from the first machine's endpoint with its state replaced by the second entry.
Set-valued exits need it.

**Proof sketch.** Split the run at the dispatch, use left lockstep and
the exit equation, then iterate the unconditional right-step identity. -/
theorem seamCompTM_runFrom_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + t) =
      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
    seamCompTM_runFrom_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
    (seamComp_step_right M₁ exit M₂ entry) _ t

/-- General endpoint composition, shared by the frozen public forms. -/
private lemma seamComp_run_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
  (seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
    (congrArg (Cfg.mapState Sum.inr) h₂)

/-- The right final anchor is absent before the total time.
**Proof sketch.** Through the left endpoint, constructor disjointness
excludes the anchor. Afterwards, right lockstep transports the phase-two
cut at the time remaining after dispatch. -/
private lemma seamComp_firstReturn_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  intro t ht
  by_cases hleft : t ≤ T₁
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
    intro heq
    apply hcut₂ (t - (T₁ + 1)) (by omega)
    change Option.map Sum.inr
      (M₂.runFrom (c₁.mapState fun _ => entry) (t - (T₁ + 1))).state =
        some (Sum.inr q₂) at heq
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
    exact hq.trans (congrArg some (Sum.inr.inj heq))

/-- Every visited position belongs to one of the two exact run segments.
**Proof sketch.** A time at most the left duration uses left lockstep.
Every later time is dispatch time plus a unique nonnegative offset, at
most the right duration; right lockstep supplies its image witness. -/
private lemma seamComp_visited_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  have ht' := Finset.mem_range.mp ht
  by_cases hleft : t ≤ T₁
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩

/-- **R2, seam-to-seam composition** (design §12;
[Bon26], `executes_in_sum`). If `M₁` carries the seam
`Cfg.ofWords start w₀` to the seam `Cfg.ofWords exit w₁` in exactly `T₁`
steps without visiting the anchor `exit` earlier (the first-return cut),
and `M₂` carries `Cfg.ofWords entry w₁` to `Cfg.ofWords q₂ w₂` in exactly
`T₂` steps, then the composite carries the left-mapped first seam to the
right-mapped last seam in exactly `T₁ + 1 + T₂` steps — the explicit
dispatch constant is `1`, not `O(1)`.

**Proof sketch.** Three segments composed with
`Turing.MultiTapeTM.runFrom_add`. (i) *Phase one lockstep*: on left
states other than the anchor, one composite step is the `Sum.inl`-mapped
`M₁` step; the cut guarantees the anchor is not visited before `T₁`, so
induction carries the left-mapped configuration to time `T₁`, where it is
`Cfg.ofWords (Sum.inl exit) w₁`. (ii) *Dispatch*: at the anchor the
composite takes the stationary silent step, and a stationary write-free
action fixes every tape, head, and the output of a seam configuration, so
time `T₁ + 1` is exactly `Cfg.ofWords (Sum.inr entry) w₁`. (iii) *Phase
two lockstep*: on right states one composite step is the
`Sum.inr`-mapped `M₂` step (`Turing.MultiTapeTM.runFrom_comm_of_step`),
carrying the seam to the right-mapped `Cfg.ofWords q₂ w₂` at time
`T₁ + 1 + T₂`. The degenerate case `T₁ = 0` (so `start = exit`,
`w₀ = w₁`) is covered because the dispatch step alone performs the
phase-one handover. -/
theorem seamCompTM_run [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) =
      Cfg.ofWords (Sum.inr q₂) w₂ := by
  have h₂' : M₂.runFrom
      ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry) T₂ =
        Cfg.ofWords q₂ w₂ := by
    simpa only [Cfg.ofWords_mapState] using h₂
  simpa only [Cfg.ofWords_mapState] using
    seamComp_run_general M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut h₂'

/-- **R2, the inherited first-return cut** (design
§12). Under the hypotheses of `seamCompTM_run`, if additionally `M₂` does
not visit its final anchor `q₂` strictly before `T₂`, then the composite
does not visit `Sum.inr q₂` strictly before `T₁ + 1 + T₂` — so a
composite is itself a seam-to-seam routine and chains under further
`seamCompTM` applications.

**Proof sketch.** Split the window. Before and at `T₁` the composite's
state is a left state (phase-one lockstep of `seamCompTM_run`), never
`Sum.inr q₂` by constructor disjointness. From `T₁ + 1` on, the
composite's state is the `Sum.inr` image of `M₂`'s state at the shifted
time (phase-two lockstep), and `Sum.inr` injectivity turns the `M₂` cut
into the composite cut; a mid-phase `M₂` halt is excluded because halting
absorbs and would contradict `h₂`'s live anchor at `T₂`. -/
theorem seamCompTM_firstReturn [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (Cfg.ofWords (input := x) entry w₁) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom
          (Cfg.ofWords (input := x) (Sum.inl start) w₀) t).state ≠
        some (Sum.inr q₂) := by
  have hcut₂' : ∀ t < T₂,
      (M₂.runFrom ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry)
        t).state ≠ some q₂ := by
    simpa only [Cfg.ofWords_mapState] using hcut₂
  simpa only [Cfg.ofWords_mapState] using
    seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ (Cfg.ofWords_state exit w₁) hcut hcut₂'

/-- **R2 space, the per-tape headline** (design §12,
frozen decision 12.1: the sharp per-tape form). On every work tape `i`,
the composite's visited set over the whole composed run is contained in
the union of the two phases' visited sets. This is the statement the sum
and max corollaries below both project from; it is deliberately the
containment itself, since downstream applications may depend on the
sharpness.

**Proof sketch.** Decompose the trajectory by the two lockstep segments
of `seamCompTM_run`: times `0, …, T₁` reproduce `M₁`'s head positions
(phase-one lockstep), time `T₁ + 1` is the dispatch step, which is
stationary — the head sits at the seam origin, already visited by both
phases' initial configurations — and times `T₁ + 1, …, T₁ + 1 + T₂`
reproduce `M₂`'s positions shifted by `T₁ + 1` (phase-two lockstep).
Every trajectory point therefore lies in one of the two phases' images;
conclude by `Finset.image` monotonicity over the split of
`Finset.range`. -/
theorem seamCompTM_visitedByTapeHead [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i ∪
        M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  simpa only [Cfg.ofWords_mapState] using
    seamComp_visited_general (T₂ := T₂) M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut i

/-- **R2′ space, the general per-tape headline**
(round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
on every work tape the composite's visited set over the composed run is
contained in the union of the two phases' visited sets — the
general-configuration form of `Turing.seamCompTM_visitedByTapeHead`, from
which the canonical corollaries project.

**Proof sketch.** As the canonical headline: the two lockstep segments
reproduce the phases' trajectories, and the dispatch step is stationary at
a point both phases' endpoint/start configurations already visit. -/
theorem seamCompTM_visitedByTapeHead_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i

/-- **R2′ space, the general sum bound**: under the hypotheses of
`Turing.seamCompTM_visitedByTapeHead_ofCfg` (phase one carries `c₀` to `c₁` in `T₁` steps,
first reaching the live anchor `exit` there), the composite's total space usage over `T₁ + 1 + T₂`
steps is at most phase one's up to `T₁` plus phase two's over `T₂` steps from `c₁` with its
control state replaced by `entry`. Phase two's endpoint is unconstrained (it may halt, or be no
seam), which the canonical `Turing.seamCompTM_spaceUsed_le_add` cannot express.

**Proof sketch.** On every tape, `Finset.card_le_card` on
`Turing.seamCompTM_visitedByTapeHead_ofCfg`, then `Finset.card_union_le`; sum over the tapes
(`Turing.MultiTapeTM.spaceUsed_eq_sum`, `Turing.MultiTapeTM.spaceUsedByTape_eq_card`). -/
theorem seamCompTM_spaceUsed_le_add_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed (c₀.mapState Sum.inl) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed c₀ T₁ + M₂.spaceUsed (c₁.mapState fun _ => entry) T₂ := by
  rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card,
    MultiTapeTM.spaceUsedByTape_eq_card]
  exact (Finset.card_le_card (seamCompTM_visitedByTapeHead_ofCfg M₁ exit M₂ entry
    (T₂ := T₂) h₁ hexit hcut i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the per-tape sum corollary** (design
§12, decision 12.1). On every work tape, the composite's space usage is
at most the sum of the phases' space usages on that tape.

**Proof sketch.** `Finset.card_le_card` on
`seamCompTM_visitedByTapeHead`, then `Finset.card_union_le`. -/
theorem seamCompTM_spaceUsedByTape_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i +
        M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  exact (Finset.card_le_card
    (seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the total sum corollary** (design
§12). The composite's total space usage is at most the sum of the
phases' total space usages.

**Proof sketch.** The `Cfg.ofWords` instance of `seamCompTM_spaceUsed_le_add_ofCfg`: renaming a
seam's state gives the seam at the renamed state (`Turing.Cfg.ofWords_mapState`). -/
theorem seamCompTM_spaceUsed_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed (Cfg.ofWords (input := x) start w₀) T₁ +
        M₂.spaceUsed (Cfg.ofWords (input := x) entry w₁) T₂ := by
  simpa only [Cfg.ofWords_mapState] using seamCompTM_spaceUsed_le_add_ofCfg (T₂ := T₂)
    M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut

/-- **R2 space, the max corollary for disjointly-owned tapes** (spec, fill
pending — design §12, frozen decision 12.1: the sharpest available form).
If one of the two phases is *idle* on tape `i` — its visited set is the
seam-origin singleton `{0}` — then the composite's space usage on `i` is
bounded by the **max** of the phases' usages, not their sum. Under a
tape-ownership discipline (each work tape owned by one phase, the other
phase never moving its head there) this gives per-tape space equal to the
owner's, which is what the chapter-4 consumers depend on.

**Proof sketch.** From `seamCompTM_visitedByTapeHead` the composite's
visited set is contained in the union, and the idle side's singleton
`{0}` is already contained in the other side's visited set — a seam
configuration has every head at the origin, so `0` is in every phase's
visited set at every horizon. The union collapses to the non-idle side's
set; `Finset.card_le_card` and `le_max_left/right` finish. -/
theorem seamCompTM_spaceUsedByTape_le_max [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k)
    (hown : M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i
        = {0} ∨
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i = {0}) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      max (M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i)
        (M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i) := by
  have hzero₁ : (0 : ℤ) ∈
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₁), rfl⟩
  have hzero₂ : (0 : ℤ) ∈
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₂), rfl⟩
  have hsub := seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂
    w₀ w₁ w₂ T₁ T₂ h₁ hcut h₂ i
  rcases hown with hown | hown
  · rw [hown, Finset.union_eq_right.mpr
      (Finset.singleton_subset_iff.mpr hzero₂)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_right _ _)
  · rw [hown, Finset.union_eq_left.mpr
      (Finset.singleton_subset_iff.mpr hzero₁)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_left _ _)

/-- **R2′, general-configuration seam-to-seam composition** (spec, fill
pending — round-1 repair R2): the `Cfg.ofWords` restriction of
`Turing.seamCompTM_run` is lifted. If `M₁` carries an arbitrary
configuration `c₀` to `c₁` in exactly `T₁` steps, first reaching the anchor
`exit` there, and `M₂` carries `c₁` **with only the control state replaced
by `entry`** to `c₃` in `T₂` steps, then the composite carries the
`Sum.inl`-mapped `c₀` to the `Sum.inr`-mapped `c₃` in exactly
`T₁ + 1 + T₂` steps: the dispatch step is stationary, silent, and
write-free, so displaced inactive heads, noncanonical tape contents, the
input position, and **accumulated output** all cross it intact — exactly
the seams the round-1 audit exhibited (`emitterP2_relocate_run`'s arbitrary
frames, `exists_emitCallTM`'s nonempty output) that no `Cfg.ofWords`
endpoint can describe. The canonical `seamCompTM_run` is the
`Cfg.ofWords` instance.

**Proof sketch.** Identical three-segment decomposition to
`seamCompTM_run` — phase-one `Sum.inl` lockstep under the cut, one
dispatch step, phase-two `Sum.inr` lockstep via `Cfg.mapState_apply` —
with the single new observation that a stationary write-free action fixes
**every** field of an arbitrary configuration, not only a canonical one
(`Turing.Action.apply` componentwise). Fill obligations, named: the two
lockstep inductions over `Cfg.mapState`, the dispatch-step field check,
and the `ofWords` specialization recovering the canonical theorem. -/
theorem seamCompTM_run_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) =
      c₃.mapState Sum.inr := by
  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂

/-- **R2′, the general inherited first-return cut**
(round-1 repair R2): under the hypotheses of
`Turing.seamCompTM_run_ofCfg`, if `M₂` first reaches `q₂` at `T₂`, the
composite first reaches `Sum.inr q₂` at `T₁ + 1 + T₂`.

**Proof sketch.** As `seamCompTM_firstReturn`, over the general lockstep
segments: left times produce `Sum.inl` states, right times the
`Sum.inr`-mapped `M₂` states at shifted time, and injectivity of the
constructors transports the cuts. -/
theorem seamCompTM_firstReturn_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  exact seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ hexit hcut hcut₂

/-- **R8.8, the two-exit seam** (design §12.8a). Attach a continuation to each
of two exit anchors of a host: `M₁` after `e₁` and `M₂` after `e₂`, by nesting
two `Turing.seamCompTM`s. The host `M₀` with two live anchors is typically
`Turing.counterLoopTM` with its `done` and `escape`. -/
def seamCompTM₂ {Symbol : Type*} {S₀ : Type*} [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂) :
    MultiTapeTM k Symbol ((S₀ ⊕ S₁) ⊕ S₂) :=
  seamCompTM (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂

/-- **R8.8, the two-exit seam, general configurations** (design §12.8a).
Suppose the host `M₀`, from an arbitrary configuration `c₀`, reaches `c₁` at
exactly `T₀` and meets neither of the distinct anchors `e₁`, `e₂` earlier.
If `c₁` is at `e₁`, then for every `t` the two-exit composite at `T₀ + 1 + t`
is `M₁`'s run, from `c₁` with only the control state replaced by `entry₁`, at
`t`, mapped into the composite's states; the `M₂` summand is never entered.
Symmetrically, if `c₁` is at `e₂`, the composite at `T₀ + 1 + t` is `M₂`'s run
from `c₁` at `entry₂`. The dispatch costs one stationary step in either branch,
and the continuation runs unboundedly, halting included, so its own first-return
and trajectory statements transfer.

**Proof sketch.** Branch `e₁`: the outer seam's left machine is the inner
composite, whose states stay away from the outer exit `Sum.inl e₂`: before
`T₀` by the cut, at `T₀` because `e₁ ≠ e₂`, and afterwards because they are
`Sum.inr` states or halted. So `Turing.seamCompTM_runFrom_left` for the outer
seam reduces the run to the inner composite's, which `Turing.seamCompTM_run_ofCfg`
and the right lockstep of the inner seam evaluate. Branch `e₂`: the inner
composite reaches `Sum.inl e₂` at `T₀` by `Turing.seamCompTM_runFrom_left`,
never having met `e₁`, and the outer dispatch and right lockstep finish. -/
theorem seamCompTM₂_run_ofCfg {Symbol : Type*} {S₀ : Type*} {x : List Symbol}
    [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (he : e₁ ≠ e₂)
    (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₀ x} {T₀ : ℕ}
    (h₀ : M₀.runFrom c₀ T₀ = c₁)
    (hcut : ∀ t < T₀, (M₀.runFrom c₀ t).state ≠ some e₁ ∧ (M₀.runFrom c₀ t).state ≠ some e₂) :
    (c₁.state = some e₁ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        ((M₁.runFrom (c₁.mapState fun _ => entry₁) t).mapState Sum.inr).mapState Sum.inl) ∧
    (c₁.state = some e₂ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        (M₂.runFrom (c₁.mapState fun _ => entry₂) t).mapState Sum.inr) := by
  constructor
  · intro h1 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hinner : ∀ s, (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl)
        (T₀ + 1 + s) = (M₁.runFrom (c₁.mapState fun _ => entry₁) s).mapState Sum.inr :=
      fun s => seamCompTM_run_ofCfg M₀ e₁ M₁ entry₁ h₀ h1 hcut₁ rfl
    have hcutO : ∀ s < T₀ + 1 + t, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      by_cases hle : s ≤ T₀
      · rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hle] at h
        rcases Nat.lt_or_ge s T₀ with hlt | hge
        · exact (hcut s hlt).2 (by simpa [Cfg.mapState] using h)
        · obtain rfl : s = T₀ := by omega
          rw [h₀] at h
          exact he (by simpa [Cfg.mapState, h1] using h)
      · obtain ⟨r, rfl⟩ : ∃ r, s = T₀ + 1 + r := ⟨s - (T₀ + 1), by omega⟩
        rw [hinner r] at h
        simp [Cfg.mapState] at h
    have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO (T₀ + 1 + t) le_rfl
    rw [hinner t] at h
    exact h
  · intro h2 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hin : (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl) T₀ =
        c₁.mapState Sum.inl := by
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ T₀ le_rfl, h₀]
    have hcutO : ∀ s < T₀, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hs.le] at h
      exact (hcut s hs).2 (by simpa [Cfg.mapState] using h)
    have hmap : ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState (fun _ => entry₂) :
        Cfg k Symbol S₂ x) = c₁.mapState (fun _ => entry₂) := by
      apply Cfg.ext <;> simp [Cfg.mapState, h2]
    have h := seamCompTM_run_ofCfg (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂ hin
      (by simp [Cfg.mapState, h2]) hcutO
      (rfl : M₂.runFrom ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState fun _ => entry₂) t = _)
    rw [hmap] at h
    exact h

variable {S : Type*}

/-- **R3′, the fresh-entry/release adapter** (round-1 repair R3). The seam
combinator dispatches at its exit anchor **before** that state's action, so
a positive call that starts and ends at one anchor cannot be cut
(`seamCompTM_firstReturn`'s cut is contradictory at zero — the round-1
finding, witnessed by `exists_installCallTM`/`exists_emitCallTM`'s
strictly-positive interior promises and `emitterP2_call_segment`'s
execute-first discipline). The adapter runs `M` on states `Unit ⊕ S` with a
fresh start `Sum.inl ()` that executes the anchor's action
**unconditionally**, after which control lives in the `Sum.inr` copy — so
the *first re-arrival* at `Sum.inr anchor` is a genuine positive-time
event a seam can consume as its left exit. -/
def seamReleaseTM {Symbol : Type*} (M : MultiTapeTM k Symbol S) (anchor : S) :
    MultiTapeTM k Symbol (Unit ⊕ S) where
  q₀ := Sum.inl ()
  tr := fun q inp w =>
    match q with
    | Sum.inl _ =>
      let a := M.tr anchor inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
    | Sum.inr s =>
      let a := M.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- **The release's fresh step** (promoted from the private `seamRelease_fresh_step` at MIG-0b):
from a configuration at the anchor, the release adapter's fresh state applies the anchor's action,
and the resulting state is right-tagged. There is no dispatch step. -/
theorem seamReleaseTM_step_fresh {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) :
    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
      (M.step c).mapState Sum.inr := by
  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
  rfl

/-- **The release's right-tagged steps** (promoted from the private `seamRelease_step_right` at
MIG-0b): on a right-tagged configuration, a step of the release adapter is the source step,
right-tagged; a halted configuration stays halted. -/
theorem seamReleaseTM_step_inr {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) :
    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
      (M.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- **The pointwise release lockstep** (design §16a item 5; promoted from the private
`seamRelease_run_pos` at MIG-0b, with its universes and its proof): started at its fresh state
over a configuration at the anchor, the release adapter is, at every positive time, the source
run with its states right-tagged. This also covers a source that halts or never returns.

**Proof sketch.** Execute the fresh step once (`Turing.seamReleaseTM_step_fresh`), then iterate
the right-step identity (`Turing.seamReleaseTM_step_inr`). -/
theorem seamReleaseTM_runFrom_pos {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
      (M.runFrom c t).mapState Sum.inr := by
  cases t with
  | zero => omega
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step, seamReleaseTM_step_fresh M anchor c hc,
      MultiTapeTM.runFrom_succ_eq_step]
    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
      (seamReleaseTM_step_inr M anchor) _ t

/-- **R3′, the positive first return through the adapter** (spec, fill
pending — round-1 repair R3): if `M`, started at its anchor, first
re-visits the anchor at a strictly positive time `T`, then the adapter,
started at its fresh state over the same configuration, reaches
`Sum.inr anchor` first at exactly `T`, over the `Sum.inr`-transported run.
The audit's S7 check is the smallest case: a two-step write-then-return
call executes both source actions before any seam dispatch can fire.

**Proof sketch.** The fresh step applies the anchor's action verbatim
(`Cfg.mapState_apply` at the constant relabeling), after which every step
is `Sum.inr`-lockstep with `M`'s run; the first-visit clause is the
transported cut, with time zero excluded by the fresh constructor
(`Sum.inl ≠ Sum.inr`). Fill obligations, named: the fresh-step equation,
the lockstep induction, and the cut transport. -/
theorem seamReleaseTM_firstReturn {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S) (anchor : S)
    {c c' : Cfg k Symbol S x} {T : ℕ}
    (hc : c.state = some anchor) (hT : 0 < T) (h : M.runFrom c T = c')
    (hc' : c'.state = some anchor)
    (hcut : ∀ t, 0 < t → t < T → (M.runFrom c t).state ≠ some anchor) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) T =
        c'.mapState Sum.inr ∧
      ∀ t < T,
        ((seamReleaseTM M anchor).runFrom
            (c.mapState fun _ => Sum.inl ()) t).state ≠
          some (Sum.inr anchor) := by
  constructor
  · rw [seamReleaseTM_runFrom_pos M anchor c hc T hT, h]
  · intro t ht
    by_cases htpos : 0 < t
    · rw [seamReleaseTM_runFrom_pos M anchor c hc t htpos]
      intro heq
      apply hcut t htpos ht
      change Option.map Sum.inr (M.runFrom c t).state =
        some (Sum.inr anchor) at heq
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
      exact hq.trans (congrArg some (Sum.inr.inj heq))
    · have htzero : t = 0 := by omega
      simp [htzero, Cfg.mapState, hc]

/-- **R3′ space** (round-1 repair R3): the adapter's
visited sets equal `M`'s at every time and on every tape — the trajectories
coincide step for step.

**Proof sketch.** Every adapter step applies the very action `M` applies at
the corresponding state (the fresh step at the anchor, `Sum.inr` steps at
their carried state), so the head trajectories agree; project
`seamReleaseTM_firstReturn`'s lockstep. -/
theorem seamReleaseTM_visitedByTapeHead {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) {c : Cfg k Symbol S x} (hc : c.state = some anchor)
    (t : ℕ) (i : Fin k) :
    (seamReleaseTM M anchor).visitedByTapeHead
        (c.mapState fun _ => Sum.inl ()) t i =
      M.visitedByTapeHead c t i := by
  unfold MultiTapeTM.visitedByTapeHead
  apply Finset.image_congr
  intro s _
  dsimp only
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [seamReleaseTM_runFrom_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
    rfl

/-! ### The phase host: finite dispatch over many phases (§12.8 fill)

`Turing.seamCompTM` dispatches one exit and `Turing.seamCompTM₂` two. A module that branches
on finite data, or repeats a row a data-dependent but bounded number of times, needs one host
over a finite family of phases with a redirect table. -/

/-- **The phase host** (design §12.8a, record rows; §12.8 fill). Phase `i` runs `M i`. A
state that `red` maps to `some q` takes one stationary, silent dispatch step to `q`; every
other state follows its phase's table. With two phases and one redirect it is the seam
discipline of `Turing.seamCompTM`. -/
def phaseHostTM {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : MultiTapeTM k Γ (Σ i, Ph i) where
  q₀ := q0
  tr := fun q inp w =>
    match red q.1 q.2 with
    | some q' => ⟨0, fun _ => (none, 0), none, some q'⟩
    | none => ((M q.1).tr q.2 inp w).mapState (Sigma.mk q.1)

/-- **The phase host's table off the redirects**: at a state `s` of phase `i` that `red` does
not redirect, the host takes phase `i`'s action, with the successor state tagged by `i`. -/
theorem phaseHostTM_tr_of_red_none {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) (s : Ph i) (hs : red i s = none)
    (inp : Option Γ) (w : Fin k → Option Γ) :
    (phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ((M i).tr s inp w).mapState (Sigma.mk i) := by
  simp only [phaseHostTM, hs]

/-- **The phase host's start state** is the given `q0`. -/
theorem phaseHostTM_q₀ {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : (phaseHostTM M q0 red).q₀ = q0 :=
  rfl

/-- **The phase host's table at a redirect**: at a state `s` of phase `i` that `red` redirects to
`q'`, the host takes one silent step to `q'`, moving no head and writing nothing. -/
theorem phaseHostTM_tr_of_red_some {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) (s : Ph i) {q' : Σ i, Ph i}
    (hs : red i s = some q') (inp : Option Γ) (w : Fin k → Option Γ) :
    (phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ⟨0, fun _ => (none, 0), none, some q'⟩ := by
  simp only [phaseHostTM, hs]

/-- **The phase lemma for a last phase.** Run phase `i` from `c` for `T` steps, with no
redirect strictly before `T`. Then, up to and including `T`, the host is the phase run with
states tagged by `i`. Unlike `Turing.phaseHostTM_run`, nothing is assumed of the state at `T`:
it may be a live exit that `red` does not redirect, so this serves a host's last phase.

**Proof sketch.** On every state reached before `T` the host's table is the tagged phase table
(`Turing.phaseHostTM_tr_of_red_none`), so the agreement transfer
`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` gives the run up to `T`. -/
theorem phaseHostTM_run_le {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c : Cfg k Γ (Ph i) x) (T : ℕ)
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    ∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i) := by
  intro u hu
  exact MultiTapeTM.runFrom_mapState_of_agreeOn (M i) (phaseHostTM M q0 red)
    ⟨Sigma.mk i, sigma_mk_injective⟩ (fun s => red i s = none)
    (fun s hs inp work => phaseHostTM_tr_of_red_none M q0 red i s hs inp work)
    c u (fun v hv s hs => hguard v (by omega) s hs)

/-- **The phase lemma** (§12.8 fill). Run phase `i` from `c` for `T` steps to `c'`, ending in
a state that `red` redirects to `q'`, with no redirect earlier. Then, up to `T`, the host is
the phase run with states tagged by `i`; one dispatch step later it is `c'` with only its
control replaced by `q'`.

**Proof sketch.** The prefix up to `T` is `Turing.phaseHostTM_run_le`. The dispatch is one step,
read through `Turing.MultiTapeTM.step_of_some`, the host's table at the redirected exit, and the
field equations of `Turing.Action.apply` and `Turing.Cfg.mapState`. No seam induction is
repeated. -/
theorem phaseHostTM_run {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c c' : Cfg k Γ (Ph i) x) (T : ℕ) (h : (M i).runFrom c T = c') (s' : Ph i)
    (hs' : c'.state = some s') (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    (∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i)) ∧
      (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) (T + 1) =
        c'.mapState (fun _ => q') := by
  have hpre := phaseHostTM_run_le M q0 red i c T hguard
  refine ⟨hpre, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hpre T le_rfl, h]
  have hst : (c'.mapState (Sigma.mk i)).state = some ⟨i, s'⟩ := by
    rw [Cfg.mapState_state, hs']
    rfl
  have htr : (phaseHostTM M q0 red).tr ⟨i, s'⟩ (c'.mapState (Sigma.mk i)).inputSymbol
      (c'.mapState (Sigma.mk i)).workTapeSymbols = ⟨0, fun _ => (none, 0), none, some q'⟩ := by
    simp only [phaseHostTM, hred]
  rw [MultiTapeTM.step_of_some hst, htr]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Action.apply_state, Cfg.mapState_state, hs']
    rfl
  · rw [Action.apply_inputPos, moveInputPos_zero, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    show Function.update ((c'.mapState (Sigma.mk i)).workTapes j)
      ((c'.mapState (Sigma.mk i)).workTapePos j)
      ((c'.mapState (Sigma.mk i)).workTapes j ((c'.mapState (Sigma.mk i)).workTapePos j)) q = _
    rw [Function.update_eq_self, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Action.apply_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    exact add_zero _
  · rw [Action.apply_output, Cfg.mapState_output, Cfg.mapState_output]
    exact List.append_nil _


end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Bool
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.CodeParser

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: counter-driven loops (§12.7)

The §12.7 increment of the machine-construction library
(`machine-library-design.md` §12.7): a loop whose number of rounds is a
little-endian binary counter **read from a tape**, running a body whose
state lives on **persistent, arbitrarily positioned tapes**. Every public
loop host of `Build/Loop.lean` instead runs a number of rounds fixed by the
input length, between canonical `Turing.Cfg.ofWords` seams. The consumers
are the two-tape uniform machine-code scheme (`Codes2Tape`), the EXPCOM
simulation, the nondeterministic time hierarchy (a fused countdown at
linear overhead) and the space hierarchy's configuration-count clock.

**Status update (§12.8 fill, R8.0b/R8.6).** All contracts in this file are proved.
The expansion proof cites `Turing.writeAdvTM_run_ofCfg` (`Build/Scan`, proved by the §12.8
stream-B fill), so nothing in this file is proved modulo an admission (R8.0b gate round 1,
note F14: doc-only refresh after the combined tree was checked).
**Alphabet update (R8.0b).** The shared loop machinery now admits any tape alphabet,
with binary digits embedded into its dedicated counter tape.

## Design (decisions 12.7.1–12.7.6, user 2026-10-10)

* **Symbol transport** (`Turing.MultiTapeTM.mapWorkSymbols`). A machine
  conjugated by a permutation of the work-tape alphabet runs as the
  original, cell for cell, from every configuration. This is the generic
  route of decision 12.7.4, so the decrement proof never copies the
  increment proof.
* **C1, decrement** (`Turing.decrementTM`). It is defined as
  `Turing.incrementTM` conjugated by bit complement, and its framed
  contracts are the §12.6 increment contracts transported.
* **C2, the counter-driven host** (`Turing.counterLoopTM`). The body's `k`
  tapes are embedded by R1 along `Fin.castSucc`, and the counter is the
  dedicated last tape (12.7.1). Arriving at the anchor starts a decrement,
  and success re-enters the body at the anchor, with no dispatch steps.
  Underflow leaves through the live anchor `done`; reaching the optional
  designated body exit leaves through the live anchor `escape` (12.7.2).
  A consumer branches on the two exits with `Turing.seamCompTM`; with no
  exit (`none`), `escape` is unreachable.
* **R8.0b, rich alphabets.** `Turing.counterLoopTMVia` transports the one-tape
  decrement through the symbol overlay and R1. Both generic contracts use the
  single round induction; the Bool contracts follow by identity-table agreement.
* **Round cost** (12.7.3). Each round from body configuration `c` lasts
  the **exact** time `τ c`. A round-indexed cost is the special case of
  `τ` along the orbit, and a uniform bound is the corollary
  `Turing.counterLoop_time_le`.
* **Amortized time** (12.7.6). The total is stated exactly over the whole
  run. The decrements' share, `Turing.counterOverhead`, is at most four
  steps per round plus one sweep of the counter.

## Main definitions

* `Turing.MultiTapeTM.mapWorkSymbols` — conjugation by a work-tape symbol
  permutation, with `Turing.Action.mapWorkSymbols` and
  `Turing.Cfg.mapWorkSymbols`.
* `Turing.decFixed`, `Turing.decrementTM` — fixed-width decrement, as a
  word function and as a machine.
* `Turing.counterWord`, `Turing.counterOverhead` — the counter after `r`
  decrements, and the exact cost of the first `r` decrements, valid as a
  physical cost for `r ≤ value + 1` (the counter word freezes at zero,
  while the machine wraps).
* `Turing.CounterLoopState`, `Turing.counterLoopTM`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
  configurations, and the body's round-start configurations.
* `Turing.lastEmb`, `Turing.counterLoopTMVia` — the last-tape embedding and
  the rich-alphabet counter host.
* `Turing.expandTM` — the expansion (§12.8, R8.6): the counter loop whose
  round is the advancing writer `Turing.writeAdvTM`.

## Main results


* `Turing.MultiTapeTM.mapWorkSymbols_runFrom` — symbol transport.
* `Turing.decrementTM_run_succ_ofCfg`, `Turing.decrementTM_run_underflow_ofCfg`
  — the framed decrement contracts, in the §12.6 shape.
* `Turing.counterWord_length`, `Turing.counterWord_value`,
  `Turing.counterOverhead_le_of_le`, `Turing.counterOverhead_le` — counter
  arithmetic, including the amortized bound.
* `Turing.counterWord_succ` — the counter word's successor case (the brief-inventory API,
  round 3: the unfolding ledger of `Build/CfgRecord`).
* `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
  host's exact whole-run contracts, with no earlier exit, the counter
  head's range, and the body heads' trajectory.
* `Turing.counterLoopTMVia_run_done`, `Turing.counterLoopTMVia_run_escape` —
  the rich-alphabet whole-run contracts, preserving the arbitrary rich frame.
* `Turing.counterLoop_time_le` — the uniform per-round bound.
* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per
  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).
* MIG-0b, over the round layer of `Build/Contract/Basic`:
  `Turing.counterLoopTMVia_done_witness`, `Turing.counterLoopTMVia_escape_witness` (the host
  segments with the shared round-and-offset witness) and their `_segment` corollaries;
  `Turing.counterLoopCfg_body` (the host layout as an R1 reconstruction); and the
  contract-level compositions `Turing.RoundContract.counterLoopDone` and
  `Turing.RoundContract.counterLoopEscape`, with their `_traj` joint trajectories and their
  `_pre`, `_time`, `_post`, `_lo`, `_hi` field equations (the brief-inventory API's gate,
  finding 2).
* `Turing.foldr_bit_eq_ofDigits`, `Turing.counterValue_bits` — the counter value of a word is its
  binary value, and the counter word `t.bits` has value `t` (H1 harvest landing).
* `Turing.counterValue_eq` — the counter value as an equation (the ND inventory API, round 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1–§3.2 and §4.1: the hierarchy
  arguments run a universal machine for a bounded number of steps under a
  step counter; this file is that counter as a reusable machine.)

**Fill appendix (§12.7).** All ten contracts are proved. Decrement is transported from increment once; `counter_rounds` is the single
round induction used by both host contracts. Its final state is unrestricted,
so it covers returning prefixes and the last escaping round with the same
trajectory invariant. The amortization proofs use the audit's bit-count
potential, as recorded in their fill appendices.
-/

namespace Turing

section SymbolTransport

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the symbols an action writes on its work tapes along an
equivalence. Input movement, output and successor state are unchanged. -/
def Action.mapWorkSymbols (e : Symbol ≃ Symbol) (a : Action k Symbol State) :
    Action k Symbol State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output
  state := a.state

/-- Rename every work-tape cell of a configuration along an equivalence;
blank cells stay blank. -/
def Cfg.mapWorkSymbols {input : List Symbol} (e : Symbol ≃ Symbol)
    (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  { c with workTapes := fun j p => (c.workTapes j p).map e }

/-- Conjugate a machine by a work-tape symbol permutation: read the work
tapes through `e.symm` and write through `e`. The input tape and the output
are not renamed. -/
def MultiTapeTM.mapWorkSymbols (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) : MultiTapeTM k Symbol State where
  q₀ := M.q₀
  tr := fun q inp work => (M.tr q inp fun j => (work j).map e.symm).mapWorkSymbols e

/-- One step commutes with work-symbol conjugation, including writes into the frame.
**Proof sketch.** Inverse decoding cancels the equivalence at each read.
On the written cell the renamed update stores the renamed symbol; off that
cell the original tape is retained. The remaining configuration fields agree. -/
private lemma counter_work_step (M : MultiTapeTM k Symbol State) (e : Symbol ≃ Symbol)
    {input : List Symbol} (d : Cfg k Symbol State input) :
    (M.mapWorkSymbols e).step (d.mapWorkSymbols e) = (M.step d).mapWorkSymbols e := by
  cases hs : d.state with
  | none => simp [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
  | some s =>
    have reads : (fun j => ((d.workTapeSymbols j).map e).map e.symm) =
        d.workTapeSymbols := by
      funext j
      cases d.workTapeSymbols j <;> simp
    simp only [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
    change ((M.tr s d.inputSymbol (fun j =>
        ((d.workTapeSymbols j).map e).map e.symm)).mapWorkSymbols e).apply
        (d.mapWorkSymbols e) = _
    rw [reads]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Action.apply, Action.mapWorkSymbols, Cfg.mapWorkSymbols]
    cases hw : (M.tr s d.inputSymbol d.workTapeSymbols).workTapes j |>.1 with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      by_cases hp : p = d.workTapePos j
      · subst p; simp
      · simp [Function.update_of_ne hp]

/-- **Symbol transport** (design §12.7, decision 12.7.4). From every
configuration and at every time, the conjugated machine runs as the original
with every work-tape cell renamed.

**Proof sketch.** One step: the conjugate reads `e.symm (e s) = s`, so it
chooses the original's action; writing renamed symbols commutes with
`Function.update`; heads, input position, output and state are copied. Then
`Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem MultiTapeTM.mapWorkSymbols_runFrom (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) :
    (M.mapWorkSymbols e).runFrom (c.mapWorkSymbols e) t =
      (M.runFrom c t).mapWorkSymbols e := by
  exact MultiTapeTM.runFrom_comm_of_step (fun d => d.mapWorkSymbols e)
    (counter_work_step M e) c t

end SymbolTransport

/-! ## C1 — decrement -/

/-- Little-endian fixed-width binary decrement with explicit underflow, the
mirror of `Turing.incFixed`: `decFixed w` is the predecessor word of the same
length, or `none` when `w` is all `false`, that is, has value zero. Width zero
underflows immediately. -/
def decFixed : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest => (decFixed rest).map (true :: ·)

/-- The empty word has no predecessor: `decFixed [] = none` (the specification API, the briefs'
pre-ship inventories, 2026-10-16). -/
theorem decFixed_nil : decFixed [] = none :=
  rfl

/-- A leading `true` becomes `false`: `decFixed (true :: w) = some (false :: w)` (the specification
API, the briefs' pre-ship inventories, 2026-10-16). -/
theorem decFixed_true_cons (w : List Bool) : decFixed (true :: w) = some (false :: w) :=
  rfl

/-- A leading `false` becomes `true` and borrows from the rest:
`decFixed (false :: w) = (decFixed w).map (true :: ·)` (the specification API, the briefs' pre-ship
inventories, 2026-10-16). -/
theorem decFixed_false_cons (w : List Bool) :
    decFixed (false :: w) = (decFixed w).map (true :: ·) :=
  rfl

/-- Complement exchanges the word-level carry and borrow recursions. -/
private lemma counter_dec_complement (w : List Bool) :
    decFixed w = (incFixed (w.map not)).map (List.map not) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [decFixed, incFixed, ih, List.map_map, Function.comp_def]

/-- Complementing work cells twice restores an arbitrary configuration. -/
private lemma counter_complement_twice {k : ℕ} {S : Type} {x : List Bool}
    (d : Cfg k Bool S x) :
    (d.mapWorkSymbols Equiv.boolNot).mapWorkSymbols Equiv.boolNot = d := by
  apply Cfg.ext <;> try rfl
  funext j p
  simp [Cfg.mapWorkSymbols, Option.map_map, Function.comp_def]

/-- Complementation of a buffered word preserves its blank delimiters. -/
private lemma counter_buffer_complement (w : List Bool) (p : ℤ) :
    FinTM.bufferTape (w.map not) p = (FinTM.bufferTape w p).map not := by
  exact FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p

/-- **R3, decrement** (design §12.7, C1). In-place little-endian fixed-width
binary decrement on tape `i`. The borrow pass flips `false` cells to `true`
moving right. The first `true` flips to `false` and selects the success
verdict. Running off the width (all `false`, value zero) selects the
underflow verdict, leaving the wrapped all-`true` word. The return pass
carries the verdict to the live `done` anchor at the origin.

It is defined as `Turing.incrementTM` conjugated by bit complement, so its
contracts are the increment's, transported by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`. -/
def decrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase :=
  (incrementTM k i).mapWorkSymbols Equiv.boolNot

/-- Every decrement run is one complemented increment run, including its frame. -/
private lemma counter_decrement_run {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool FlagPhase x) (t : ℕ) :
    (decrementTM k i).runFrom d t =
      ((incrementTM k i).runFrom (d.mapWorkSymbols Equiv.boolNot) t).mapWorkSymbols
        Equiv.boolNot := by
  simpa only [decrementTM, counter_complement_twice] using
    (incrementTM k i).mapWorkSymbols_runFrom Equiv.boolNot
      (d.mapWorkSymbols Equiv.boolNot) t

/-- **Decrement, framed success with exact borrow cost** (design §12.7, C1;
the mirror of `Turing.incrementTM_run_succ_ofCfg`). Let the delimited word `w`
on tape `i` have a predecessor at its width, `decFixed w = some v`, and let
`q = (w.takeWhile not).length` be its number of leading `false` cells. Then
the routine reaches the success anchor at exactly `2q + 2` and not earlier,
with the word interval holding `v` and everything else unchanged. Up to the
exit the head stays within `[pos - 1, pos + q]`.

**Proof sketch.** Complement the configuration's work tapes. The result
carries `w.map not`, whose successor is `v.map not` (`decFixed` is `incFixed`
conjugated by `not`) and whose `true` prefix has length `q`. Apply
`Turing.incrementTM_run_succ_ofCfg`, transport back by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`, and use that complementing
twice is the identity and that `FinTM.bufferTape` commutes with `map not`. -/
theorem decrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : decFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * (w.takeWhile not).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile not).length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile not).length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile not).length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = some (v.map not) := by
    have h := congrArg (Option.map (List.map not)) hv
    simpa [counter_dec_complement, Option.map_map, List.map_map, Function.comp_def] using h
  have hf : ∀ p : ℤ, -1 ≤ p → p ≤ ((w.map not).length : ℤ) →
      (d.mapWorkSymbols Equiv.boolNot).workTapes i
        ((d.mapWorkSymbols Equiv.boolNot).workTapePos i + p) =
          FinTM.bufferTape (w.map not) p := by
    intro p hl hr
    simpa [Cfg.mapWorkSymbols, counter_buffer_complement] using
      congrArg (Option.map not) (hw p hl (by simpa using hr))
  have hp : ((w.map not).takeWhile id).length = (w.takeWhile not).length := by
    simp [List.takeWhile_map, Function.comp_def]
  obtain ⟨he, hc, hh⟩ := incrementTM_run_succ_ofCfg i (w.map not) (v.map not)
    hv' (d.mapWorkSymbols Equiv.boolNot) hstate hf
  rw [hp] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Cfg.mapWorkSymbols, List.length_map]
    split_ifs <;> simp [counter_buffer_complement, Option.map_map, Function.comp_def]
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hc
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-- **Decrement, framed underflow** (design §12.7, C1; the mirror of
`Turing.incrementTM_run_overflow_ofCfg`). If the delimited word `w` on tape
`i` has no predecessor at its width (`decFixed w = none`, that is, it is all
`false`), the routine reaches the underflow anchor at exactly `2|w| + 2` and
not earlier. The word interval then holds `|w|` copies of `true`, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`.

**Proof sketch.** As the success case, through
`Turing.incrementTM_run_overflow_ofCfg`: the complemented word is all `true`,
so `incFixed` overflows, and the wrapped all-`false` word complements back to
all `true`. -/
theorem decrementTM_run_underflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : decFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length true) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = none := by
    simpa only [counter_dec_complement, Option.map_eq_none_iff] using hv
  obtain ⟨he, hc, hh⟩ := incrementTM_run_overflow_ofCfg i (w.map not) hv'
    (d.mapWorkSymbols Equiv.boolNot) hstate (by
      intro p hl hr
      change (d.workTapes i (d.workTapePos i + p)).map Equiv.boolNot = _
      rw [hw p hl (by simpa using hr), counter_buffer_complement]
      rfl)
  simp only [List.length_map] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    have hb := counter_buffer_complement (List.replicate w.length false)
      (p - d.workTapePos j)
    simp only [Cfg.mapWorkSymbols]
    split_ifs
    · simpa using hb.symm
    · simp [Option.map_map, Function.comp_def]
  · intro t ht b
    exact (hc t ht b) ∘ (by simp only [counter_decrement_run, Cfg.mapWorkSymbols]; exact id)
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-- **The decrement ignores its input** (B6-F1 promotion): its transition does not depend on
the input symbol it reads. This is the input-obliviousness that the symbol overlay transport
`Turing.MultiTapeTM.liftSymbols_runFrom_over` asks of a table.

**Proof sketch.** The increment's table ignores its input argument, and the conjugation by
complement passes that argument through unchanged; both sides are the same term (`rfl`). -/
theorem decrementTM_tr_input {k : ℕ} (i : Fin k) (q : FlagPhase) (inp inp' : Option Bool)
    (work : Fin k → Option Bool) :
    (decrementTM k i).tr q inp work = (decrementTM k i).tr q inp' work :=
  rfl

/-- **The decrement's actions keep the input head and write no blank** (B6-F1 promotion): every
action of the table has input move `0`, and every cell it writes receives a digit. The second
half is the blank-freeness that `Turing.MultiTapeTM.liftSymbols_runFrom_over` asks of a table;
the first keeps a host's input head fixed during a decrement.

**Proof sketch.** The conjugated table is the increment's action with its writes mapped by
complement; the increment never moves the input head and writes either nothing or a digit.
Split on the phase and the scanned cell. -/
theorem decrementTM_tr_action {k : ℕ} (i : Fin k) (q : FlagPhase) (inp : Option Bool)
    (work : Fin k → Option Bool) :
    ((decrementTM k i).tr q inp work).inputTape = 0 ∧
      ∀ j, (((decrementTM k i).tr q inp work).workTapes j).1 ≠ some none := by
  unfold decrementTM MultiTapeTM.mapWorkSymbols Action.mapWorkSymbols
  cases q <;> dsimp only [incrementTM] <;> (try split) <;>
    exact ⟨rfl, fun j => by by_cases hj : j = i <;> simp [hj]⟩

/-- **The decoded shadow of a counter start meets the decrement's preconditions**: for the
one-tape start holding the digits `w.map e` delimited at `cp`, its `Bool` shadow is in the
working phase and holds `w` delimited at its head.

**Proof sketch.** The shadow keeps the state and the heads, and its cells are the decoded cells
(`Turing.Cfg.decodeSymbols_state`, `_workTapes`, `_workTapePos`); decoding the digits gives back
`w` (`Turing.FinTM.bufferTape_map_decode`). -/
theorem decrementTM_shadow_pre {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (ip : Fin (x.length + 2)) (out : List Γ) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let D : Cfg 1 Γ FlagPhase x := ⟨some .run, ip, fun _ => ct, fun _ => cp, out⟩
    (Cfg.decodeSymbols e D).state = some .run ∧
      ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        (Cfg.decodeSymbols e D).workTapes 0 ((Cfg.decodeSymbols e D).workTapePos 0 + p) =
          FinTM.bufferTape w p := by
  intro D
  refine ⟨Cfg.decodeSymbols_state e D, fun p lo hi => ?_⟩
  rw [Cfg.decodeSymbols_workTapes, Cfg.decodeSymbols_workTapePos]
  show (ct (cp + p)).bind (decodeBool e) = _
  rw [hw p lo hi, FinTM.bufferTape_map_decode]

/-- **The lifted decrement runs as the overlay of the decrement's run on the shadow**, from any
rich start.

**Proof sketch.** The rich start is the overlay of its shadow on itself
(`Turing.Cfg.liftOver_decodeSymbols`); the overlay transport
`Turing.MultiTapeTM.liftSymbols_runFrom_over` applies, its side conditions being
`Turing.decrementTM_tr_input` and the blank-freeness half of `Turing.decrementTM_tr_action`. -/
theorem decrementTM_liftSymbols_runFrom {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (D : Cfg 1 Γ FlagPhase x) (t : ℕ) :
    ((decrementTM 1 0).liftSymbols e).runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom (Cfg.decodeSymbols e D) t) := by
  conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
  exact MultiTapeTM.liftSymbols_runFrom_over e (decrementTM 1 0) (decrementTM_tr_input 0)
    (fun q inp work j => (decrementTM_tr_action 0 q inp work).2 j) _ D (Cfg.decodeSymbols e D) t

/-! ## Counter arithmetic -/

/-- The counter word after `r` decrements. A decrement at value zero leaves
the word unchanged here; the machine's underflow wrap is stated in the host
contract. -/
def counterWord (w : List Bool) (r : ℕ) : List Bool :=
  (fun u => (decFixed u).getD u)^[r] w

/-- **The counter word before any decrement** is the word itself (B6-F1 promotion).

**Proof sketch.** The zeroth iterate of the optional decrement is the identity (`rfl`). -/
theorem counterWord_zero (w : List Bool) : counterWord w 0 = w :=
  rfl

/-- **One more decrement** (the brief-inventory API, round 3; user 2026-10-17): the counter word
after `r + 1` decrements is one optional decrement of the word after `r`,
`counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r)`. -/
theorem counterWord_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- The cost sum of the first `r` decrements along the frozen word orbit
`Turing.counterWord`: the decrement of the word `u` costs
`2 * (u.takeWhile not).length + 2`, which is also the underflow cost
`2|u| + 2` when `u` is all `false`. Because `counterWord` freezes at value
zero while the machine wraps on underflow, the sum equals the physical
countdown's cost only through its first underflow, that is for
`r ≤ value + 1`. That range covers every use in this file (§12.7 statement
gate, SC-1). -/
def counterOverhead (w : List Bool) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, (2 * ((counterWord w j).takeWhile not).length + 2)

/-- **No decrement costs nothing** (B6-F1 promotion): the cost of the first `0` decrements
is `0`.

**Proof sketch.** An empty sum (`Finset.sum_range_zero`). -/
theorem counterOverhead_zero (w : List Bool) : counterOverhead w 0 = 0 :=
  Finset.sum_range_zero _

/-- **One more decrement adds its own cost** (B6-F1 promotion): the first `r + 1` decrements
cost the first `r` plus `2 · |takeWhile not (counterWord w r)| + 2`, the cost of decrementing the
`r`-th frozen word.

**Proof sketch.** Split the last summand off the sum (`Finset.sum_range_succ`). -/
theorem counterOverhead_succ (w : List Bool) (r : ℕ) :
    counterOverhead w (r + 1) =
      counterOverhead w r + (2 * ((counterWord w r).takeWhile not).length + 2) :=
  Finset.sum_range_succ _ _

/-- A borrow either detects an all-false word or preserves width, subtracts one,
and changes the true-bit potential by its false-prefix length.
**Proof sketch.** Induct on the word. A true low bit stops the borrow; a false
low bit propagates it and gains one true bit. -/
lemma counter_dec_spec (w : List Bool) :
    match decFixed w with
    | none => w = List.replicate w.length false
    | some v => v.length = w.length ∧
        Nat.ofDigits 2 (w.map Bool.toNat) = Nat.ofDigits 2 (v.map Bool.toNat) + 1 ∧
        v.count true + 1 = w.count true + (w.takeWhile not).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true => simp [decFixed, Nat.ofDigits_cons, Nat.add_comm]
    | false =>
      cases hd : decFixed w with
      | none =>
        simp only [hd] at ih
        simpa [decFixed, hd, List.replicate_succ] using congrArg (false :: ·) ih
      | some v =>
        simp only [hd] at ih
        rcases ih with ⟨hl, hv, hc⟩
        simp [decFixed, hd, Nat.ofDigits_cons, hl]
        omega

/-- **The decrement keeps the width:** `decFixed w = some v → |v| = |w|`, the width clause of
`Turing.counter_dec_spec`'s successful branch.

**Proof sketch.** Specialize `Turing.counter_dec_spec` at `w`; its match reduces by `h`. -/
theorem decFixed_length {w v : List Bool} (h : decFixed w = some v) : v.length = w.length := by
  have hs := counter_dec_spec w
  simp only [h] at hs
  exact hs.1

/-- The next frozen counter word is obtained by one optional decrement. -/
private lemma counter_word_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- Underflow occurs exactly at binary value zero, including padded words. -/
lemma counter_dec_zero (w : List Bool) :
    decFixed w = none ↔ Nat.ofDigits 2 (w.map Bool.toNat) = 0 := by
  have hs := counter_dec_spec w
  cases hd : decFixed w with
  | none =>
    simp only [hd] at hs
    simp only [true_iff]
    conv_lhs => rw [hs]
    simp
  | some v =>
    simp only [hd] at hs
    simp only [reduceCtorEq, false_iff]
    omega

/-- Decrements preserve the counter's width.

**Proof sketch.** `decFixed` preserves length, by induction on the word, and
`Option.getD` keeps the word otherwise; induct on `r`. -/
theorem counterWord_length (w : List Bool) (r : ℕ) :
    (counterWord w r).length = w.length := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [counter_word_succ]
    have hs := counter_dec_spec (counterWord w r)
    cases hd : decFixed (counterWord w r) with
    | none => simpa [hd] using ih
    | some v =>
      rw [hd] at hs
      simpa [hd] using hs.1.trans ih

/-- Each of the first `value w` decrements lowers the little-endian value by
one.

**Proof sketch.** For a word of positive value, `decFixed` succeeds and its
result has value one less, by induction on the word: a leading `true`
loses weight one, and a leading `false` borrows from the rest with weight
two. Induct on `r`. -/
theorem counterWord_value (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    Nat.ofDigits 2 ((counterWord w r).map Bool.toNat) =
      Nat.ofDigits 2 (w.map Bool.toNat) - r := by
  induction r with
  | zero => simp [counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_succ]
    cases hb : decFixed (counterWord w r) with
    | none =>
      have hz := (counter_dec_zero _).mp hb
      omega
    | some v =>
      simp only [hb] at hs
      simp only [Option.getD_some]
      omega

/-- Before exhaustion, the physical predecessor is the next frozen word. -/
lemma counter_word_decrement (w : List Bool) (r : ℕ)
    (hr : r < Nat.ofDigits 2 (w.map Bool.toNat)) :
    decFixed (counterWord w r) = some (counterWord w (r + 1)) := by
  have hv := counterWord_value w r (by omega)
  rw [counter_word_succ]
  cases hd : decFixed (counterWord w r) with
  | none => have hz := (counter_dec_zero _).mp hd; omega
  | some v => rfl

/-- Successful borrow costs telescope against twice the number of true bits.
**Proof sketch.** At each step the borrow specification equates the new
potential plus four with the old potential plus the exact decrement cost.
Add this equality to the induction hypothesis. -/
private lemma counter_potential (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r + 2 * w.count true =
      4 * r + 2 * (counterWord w r).count true := by
  induction r with
  | zero => simp [counterOverhead, counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_decrement w r (by omega)] at hs
    simp only [counterOverhead, Finset.sum_range_succ]
    change (counterOverhead w r + (2 * (List.takeWhile not (counterWord w r)).length + 2)) +
      2 * w.count true = 4 * (r + 1) + 2 * (counterWord w (r + 1)).count true
    omega

/-- **Prefix amortization.** The first `r` decrements, for `r` at most the
counter's value, cost at most `4r + 2|w|`.

**Proof sketch.** The `j`th decrement acts on a word of value `n - j`
(`Turing.counterWord_value`), where `n` is the counter's value, and its
`false` prefix is the number of trailing zero bits of that value. Summed over
`r` consecutive values below `2^|w|`, the trailing zeros total
`ν₂(r!) + ν₂(binom) ≤ (r - 1) + (|w| - 1)` by Legendre and Kummer, so the
cost is at most `4r + 2|w| - 4` once `r ≥ 1`.

**Fill proof appendix.** The binding statement-gate route replaces the
number-theoretic sketch above by the exact telescoping identity proved in
`counter_potential`. Twice the count of true bits is the potential; its
terminal value is bounded by twice the preserved word length. -/
theorem counterOverhead_le_of_le (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r ≤ 4 * r + 2 * w.length := by
  have hp := counter_potential w r hr
  have hc : (counterWord w r).count true ≤ w.length :=
    (List.count_le_length).trans_eq (counterWord_length w r)
  omega

/-- At exhaustion the fixed-width word is all false, retaining any padding. -/
private lemma counter_word_exhausted (w : List Bool) :
    counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)) =
      List.replicate w.length false := by
  have hz := counterWord_value w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  simp only [Nat.sub_self] at hz
  have hs := counter_dec_spec (counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)))
  rw [(counter_dec_zero _).mpr hz] at hs
  simpa only [counterWord_length] using hs

/-- **Whole-run amortization** (design §12.7, decision 12.7.6). Counting a
counter of value `n` down to zero and through the final underflow costs at
most `4n + 2|w| + 2`.

**Proof sketch.** The successful decrements act on the values `n, …, 1`,
whose trailing zeros sum to `n - s₂(n) ≤ n` (Legendre), so they cost at most
`4n`. The final word is all `false` (`Turing.counterWord_value`), so the
underflow sweep costs `2|w| + 2` (`Turing.counterWord_length`).

**Fill proof appendix.** Use `counter_potential` at exhaustion, where the
remaining true-bit count is zero, then add the full underflow sweep.
No Legendre or Kummer theorem is used. -/
theorem counterOverhead_le (w : List Bool) :
    counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) ≤
      4 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2 := by
  have hp := counter_potential w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  rw [counter_word_exhausted] at hp
  simp [List.count_replicate] at hp
  have hs : counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) =
      counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat)) + (2 * w.length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, counter_word_exhausted]
  omega

/-! ## C2 — the counter-driven host -/

/-- Control of the counter-driven host (design §12.7, C2): a body state, a
decrement phase, or one of the two live exit anchors. -/
inductive CounterLoopState (S : Type) where
  /-- running the body -/
  | body (s : S)
  /-- running the decrement on the counter tape -/
  | dec (f : FlagPhase)
  /-- the live exit anchor after the counter underflows -/
  | done
  /-- the live exit anchor after the body reaches its designated exit -/
  | escape
deriving DecidableEq

instance counterLoopStateFintype (S : Type) [Fintype S] :
    Fintype (CounterLoopState S) := derive_fintype% _

/-- Where a body transition lands in the host. Arriving at the anchor `a`
starts the next decrement; arriving at the designated exit leaves through
`escape`; every other body state is kept. -/
def counterLoopRedirect {S : Type} [DecidableEq S] (a : S) (exit : Option S)
    (s : S) : CounterLoopState S :=
  if s = a then .dec .run else if exit = some s then .escape else .body s

/-- Where a decrement transition lands in the host. The success anchor
re-enters the body at `a`, the underflow anchor is the host's `done`, and the
working phases are kept. -/
def counterLoopDecExit {S : Type} (a : S) : FlagPhase → CounterLoopState S
  | .done true => .body a
  | .done false => .done
  | f => .dec f

/-- **C2, the counter-driven loop host** (design §12.7). The body `M` runs on
the first `k` tapes, embedded by `Turing.embedEmitTM` along `Fin.castSucc`
with its emissions forwarded, and the counter is the last tape. The host
starts with a decrement. Each successful decrement re-enters the body at the
anchor `a`, and each arrival at `a` starts the next decrement, with no
dispatch steps in between. Underflow leaves through the live anchor `done`;
reaching the optional exit leaves through the live anchor `escape`. Both
anchors are stationary. -/
def counterLoopTM {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) : MultiTapeTM (k + 1) Bool (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((decrementTM (k + 1) (Fin.last k)).tr f inp work).mapState (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- Select the last host tape as a one-tape bank (design §12.8a, R8.0b).
**Proof sketch.** The singleton domain makes the constant last-tape map injective. -/
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

/-- **The last-tape embedding sends its one index to the last tape** (B6-F1 promotion).

**Proof sketch.** Definitional (`rfl`). -/
theorem lastEmb_apply (k : ℕ) (i : Fin 1) : lastEmb k i = Fin.last k :=
  rfl

/-- Run a rich-alphabet body with an embedded binary counter on the last tape
(design §12.8a, R8.0b).
**Proof sketch.** R1 forwards the body and the symbol-lifted one-tape decrement;
the existing redirections connect the phases without dispatch steps. -/
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- A host configuration with host state `q`: the body configuration `c` on
the first `k` tapes (its own state field is ignored), the counter tape `ct`
with its head at `cp` as the last tape, and the body's output as the host's
output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
with the counter as the ambient frame. -/
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- The body configurations at the starts of successive rounds: round `r`
starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
steps. Since MIG-0b it is an abbreviation of the core's round orbit `Turing.roundOrbit`
(`Build/Contract/Basic`), the iterate `(fun c => M.runFrom c (τ c))^[r] c`; a proof that
unfolds it unfolds `Turing.roundOrbit` too. -/
abbrev counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) :
    Cfg k Symbol S x :=
  roundOrbit M τ c r

/-! ### Shared phase and prefix invariants -/

/-- The host layout over any tape alphabet.
**Proof sketch.** R1 identifies the selected body bank and the last-tape frame. -/
private lemma counter_layout {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Symbol Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
  apply Cfg.ext <;> try rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.1
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.2
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i

/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
host configuration is the body bank followed by its counter tape.

**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`).

**Re-derivation appendix (R8.0b).** Instantiate the generic private layout at the Bool alphabet. -/
theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ :=
  counter_layout q c ct cp

/-- Injective successor redirection for the decrement's five controls. -/
private lemma counter_dec_injective {S : Type} (a : S) :
    Function.Injective (counterLoopDecExit a) := by
  intro f g h
  cases f <;> cases g <;> (try casesm* Bool) <;> simp_all [counterLoopDecExit]

/-- Anchor priority still gives an injective body-state redirection. -/
private lemma counter_redirect_injective {S : Type} [DecidableEq S]
    (a : S) (exit : Option S) : Function.Injective (counterLoopRedirect a exit) := by
  intro s t h
  by_cases hs : s = a
  · subst s
    by_cases ht : t = a
    · exact ht.symm
    · simp only [counterLoopRedirect, ht, if_false] at h
      split_ifs at h
  · by_cases ht : t = a
    · subst t; simp only [counterLoopRedirect, hs, if_false] at h
      split_ifs at h
    · simp only [counterLoopRedirect, hs, ht, if_false] at h
      split_ifs at h <;> simp_all

/-- Common trajectory data for a finite host segment, with a chosen set of
permitted body-head vectors. -/
private def counterSpan {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
    (R : (Fin k → ℤ) → Prop) : Prop :=
  (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
    (H.runFrom z u).state ≠ some .escape) ∧
  (∀ u ≤ t, (H.runFrom z u).workTapePos (Fin.last k) ∈
    Finset.Icc (cp - 1) (cp + (width : ℤ))) ∧
  (∀ u ≤ t, R (fun j => (H.runFrom z u).workTapePos j.castSucc))

/-- `counterSpan` is the segment layer at the counter loop's parameters: the segment
(`Turing.Segment`) from `z` to its run endpoint over both exits, whose head relation puts the
counter head in its interval and the body heads in `R`. Concatenation and weakening are
`Turing.Segment.trans` and `Turing.Segment.mono` through this bridge. -/
private lemma counterSpan_iff_segment {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
    (R : (Fin k → ℤ) → Prop) :
    counterSpan H z t cp width R ↔
      Segment H {some .done, some .escape}
        (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (width : ℤ)) ∧
          R fun j => p j.castSucc)
        z (H.runFrom z t) t := by
  rw [Turing.segment_iff]
  exact ⟨fun ⟨hc, hh, hr⟩ => ⟨rfl, fun u hu hm => Or.elim hm (hc u hu).1 (hc u hu).2,
      fun u hu => ⟨hh u hu, hr u hu⟩⟩,
    fun ⟨_, hc, hp⟩ =>
      ⟨fun u hu => ⟨fun h => hc u hu (Or.inl h), fun h => hc u hu (Or.inr h)⟩,
        fun u hu => (hp u hu).1, fun u hu => (hp u hu).2⟩⟩

/-- Equal-width patches overwrite the same interval: `Turing.wordPatch_twice`. -/
private lemma counter_patch_twice {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (hv : v.length = u.length) :
    wordPatch (wordPatch ct cp u) cp v = wordPatch ct cp v :=
  wordPatch_twice ct cp u v hv

/-- Replacing a framed word by an equal-width word keeps both blank delimiters:
`Turing.wordPatch_frame`. -/
private lemma counter_patch_frame {Γ : Type} (w v : List Γ) (ct : ℤ → Option Γ) (cp : ℤ)
    (hv : v.length = w.length)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      wordPatch ct cp v (cp + p) = FinTM.bufferTape v p :=
  wordPatch_frame ct cp w v hv hw

/-- A decrement phase uses the proved framed contract and guarded state transport.
**Proof sketch.** Decode the rich one-tape start, apply the landed success or
underflow contract, and read back through the public symbol overlay. Its input
obliviousness and absence of blank writes preserve arbitrary rich frame cells.
R1 puts this run on the last tape; injective guarded state transport supplies
the host's verdict cut and the two head trajectories. -/
private lemma counter_debit {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let cost := 2 * (w.takeWhile not).length + 2
    let v := (decFixed w).getD (List.replicate w.length true)
    let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
      counterLoopCfg (some q) c (wordPatch ct cp (v.map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
  let D : Cfg 1 Γ FlagPhase x :=
    ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩
  let z := Cfg.decodeSymbols e D
  let v := (decFixed w).getD (List.replicate w.length true)
  let cost := 2 * (w.takeWhile not).length + 2
  let N := (decrementTM 1 0).liftSymbols e
  let E := embedEmitTM (lastEmb k) N
  let bank (d : Cfg 1 Γ FlagPhase x) := embedEmitCfg (lastEmb k)
    (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d
  have layout (d : Cfg 1 Γ FlagPhase x) : bank d =
      ⟨d.state, d.inputPos, Fin.lastCases (d.workTapes 0) c.workTapes,
        Fin.lastCases (d.workTapePos 0) c.workTapePos, d.output⟩ := by
    apply embedEmitCfg_eq (lastEmb k) _ _ [] d _ rfl rfl (List.nil_append _)
    · intro i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [lastEmb_apply]
    · intro j hj
      refine Fin.lastCases (fun hl => ?_) (fun i _ => ?_) j hj
      · exact absurd ⟨0, lastEmb_apply k 0⟩ hl
      · simp
  have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      z.workTapes 0 (z.workTapePos 0 + p) = FinTM.bufferTape w p :=
    (decrementTM_shadow_pre e c.inputPos c.output w ct cp hw).2
  -- The only decrement facts are the landed framed contracts, on the decoded shadow.
  have spec :
      (decrementTM 1 0).runFrom z cost =
        {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
          if j = 0 ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
      (∀ t < cost, ∀ b, ((decrementTM 1 0).runFrom z t).state ≠ some (.done b)) ∧
      (∀ t ≤ cost, ((decrementTM 1 0).runFrom z t).workTapePos 0 ∈
        Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
    cases hd : decFixed w with
    | none =>
      have hs := counter_dec_spec w
      rw [hd] at hs
      have hp : (w.takeWhile not).length = w.length := by
        conv_lhs => rw [hs]
        simp
      obtain ⟨he, hc, hh⟩ :=
        decrementTM_run_underflow_ofCfg 0 w hd z (Cfg.decodeSymbols_state e D) hz
      refine ⟨by simpa [cost, v, hd, hp] using he,
        by simpa [cost, hp] using hc, ?_⟩
      intro t ht
      simpa [z, D, Cfg.decodeSymbols_workTapePos] using hh 0 t (by simpa [cost, hp] using ht)
    | some u =>
      obtain ⟨he, hc, hh⟩ :=
        decrementTM_run_succ_ofCfg 0 w u hd z (Cfg.decodeSymbols_state e D) hz
      refine ⟨by simpa [v, hd] using he, hc, ?_⟩
      intro t ht
      have h := hh 0 t ht
      simp only [ite_true, Finset.mem_Icc, z, D, Cfg.decodeSymbols_workTapePos] at h ⊢
      have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
      exact ⟨h.1, by
        have upper : ((decrementTM 1 0).runFrom z t).workTapePos 0 ≤
            cp + ((w.takeWhile not).length : ℤ) := h.2
        omega⟩
  have rich (t : ℕ) : N.runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t) :=
    decrementTM_liftSymbols_runFrom e D t
  let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
  have start : (bank D).mapState emb = counterLoopCfg (some (.dec .run)) c ct cp := by
    rw [layout, counter_layout]
    apply Cfg.ext
    · simp only [Cfg.mapState_state]; rfl
    · simp only [Cfg.mapState_inputPos]; rfl
    · funext i p; simp only [Cfg.mapState_workTapes]; rfl
    · funext i; simp only [Cfg.mapState_workTapePos]; rfl
    · simp only [Cfg.mapState_output]; rfl
  have run (t : ℕ) (ht : t ≤ cost) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
        (bank (Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t))).mapState emb := by
    rw [← start]
    have h := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun f => ∀ b, f ≠ .done b) (by
        intro f hf inp work
        cases f with
        | run => rfl
        | rewind b => rfl
        | done b => exact False.elim (hf b rfl)) (bank D) t (by
          intro u hu f hf b he
          rw [show E.runFrom (bank D) u = bank (N.runFrom D u) from
            embedEmitTM_runFrom (lastEmb k) N _ _ [] D u, rich, layout] at hf
          simp only [Cfg.liftOver_state] at hf
          exact spec.2.1 u (by omega) b (hf.trans (congrArg some he)))
    rw [h, show E.runFrom (bank D) t = bank (N.runFrom D t) from
      embedEmitTM_runFrom (lastEmb k) N _ _ [] D t, rich]
  have vl : v.length = w.length := by
    have hs := counter_dec_spec w
    cases hd : decFixed w <;> simp [v, hd] at *
    exact hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run cost le_rfl, spec.1, layout, counter_layout]
    apply Cfg.ext
    · cases hd : decFixed w <;> simp [Cfg.mapState_state, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.liftOver_state,
        Cfg.liftOver_inputPos, Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos,
        Cfg.liftOver_output, Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes,
        Cfg.liftSymbols_output,
        emb, counterLoopDecExit]
    · apply Fin.ext
      simp only [Cfg.mapState_inputPos, Cfg.liftOver_inputPos, z, Cfg.decodeSymbols_inputPos, D]
    · funext j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Fin.lastCases_last]
        rw [Cfg.liftOver_workTapes]
        simp only [z, Cfg.decodeSymbols_workTapes, Cfg.decodeSymbols_workTapePos]
        change (if (if True ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
            then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)) =
              (ct p).bind (decodeBool e) then ct p
            else (if True ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
              then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)).map e) =
          wordPatch ct cp (v.map e) p
        simp only [true_and, wordPatch_apply, List.length_map, vl, FinTM.bufferTape_map]
        by_cases hp : cp ≤ p ∧ p < cp + (w.length : ℤ)
        · simp only [if_pos hp]
          split_ifs with he
          · have hn : (p - cp).toNat < v.length := by omega
            have hb : FinTM.bufferTape v (p - cp) = some v[(p - cp).toNat] := by
              have h0 : ((p - cp).toNat : ℤ) = p - cp := Int.toNat_of_nonneg (by omega)
              nth_rw 1 [← h0]
              rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem hn]
            cases hct : ct p with
            | none => simp [hct, hb] at he
            | some γ =>
              have decoded : decodeBool e γ = some v[(p - cp).toNat] := by
                simpa only [hct, hb, Option.bind_some] using he.symm
              simp only [hb, Option.map_some, decodeBool_eq_some e γ _ decoded]
          · rfl
        · simp only [if_neg hp, if_true]
      · simp only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Fin.lastCases_castSucc]
    · funext i
      simp only [Cfg.mapState_workTapePos, Cfg.liftOver_workTapePos, z,
        Cfg.decodeSymbols_workTapePos]
      rfl
    · simp [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
        Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.liftOver_state, Cfg.liftOver_inputPos,
        Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos, Cfg.liftOver_output,
        Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes, Cfg.liftSymbols_output, z,
        Cfg.decodeSymbols_state, Cfg.decodeSymbols_inputPos, Cfg.decodeSymbols_workTapes,
        Cfg.decodeSymbols_workTapePos, Cfg.decodeSymbols_output, D]
  · intro t ht
    rw [run t (by omega), layout]
    have hc := spec.2.1 t ht
    cases hs : ((decrementTM 1 0).runFrom z t).state with
    | none => simp [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
        Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.liftOver_state, Cfg.liftOver_inputPos,
        Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos, Cfg.liftOver_output,
        Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes, Cfg.liftSymbols_output, hs]
    | some f =>
      cases f with
      | run => simp [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.liftOver_state,
          Cfg.liftOver_inputPos, Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos,
          Cfg.liftOver_output, Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes,
          Cfg.liftSymbols_output, hs, emb, counterLoopDecExit]
      | rewind b =>
        simp [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
            Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.liftOver_state,
            Cfg.liftOver_inputPos, Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos,
            Cfg.liftOver_output, Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes,
            Cfg.liftSymbols_output, hs, emb, counterLoopDecExit]
      | done b => exact False.elim (hc b hs)
  · intro t ht
    rw [run t ht, layout]
    simpa only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
        Cfg.mapState_workTapePos, Cfg.mapState_output, Fin.lastCases_last, Cfg.liftOver_state,
        Cfg.liftOver_inputPos, Cfg.liftOver_workTapes, Cfg.liftOver_workTapePos,
        Cfg.liftOver_output, Cfg.liftSymbols_inputPos, Cfg.liftSymbols_workTapes,
        Cfg.liftSymbols_output] using
      spec.2.2 t ht
  · intro t ht j
    rw [run t ht, layout]
    simp only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
        Cfg.mapState_workTapePos, Cfg.mapState_output, Fin.lastCases_castSucc]

/-- The body phase executes its entry action once, then uses guarded transport.
**Proof sketch.** The entry action reads the forwarding embedding. After that
step, all strict intermediate states avoid both redirections, and the RB5
transport lemma applies. R1 identifies every transported configuration and
therefore preserves the counter frame and all body-head trajectories. -/
private lemma counter_body {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (ct : ℤ → Option Γ) (cp : ℤ) (width t : ℕ)
    (hc : c.state = some a) (ht : 0 < t)
    (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
      s ≠ a ∧ exit ≠ some s) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
      counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
        (M.runFrom c t) ct cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.body a)) c ct cp)
      t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
  let E := embedEmitTM Fin.castSuccEmb M
  let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
  let emb : S ↪ CounterLoopState S :=
    ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
  have first : (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
      (E.runFrom ec 1).mapState emb := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.runFrom_one]
    have hec : ec.state = some a := hc
    simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
    rfl
  have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
        counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
          (M.runFrom c u) ct cp := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun s => s ≠ a ∧ exit ≠ some s)
      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTMVia, E])
      (E.runFrom ec 1) n (by
        intro v hv s hs
        have he := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c (1 + v)
        change E.runFrom ec (1 + v) = _ at he
        rw [MultiTapeTM.runFrom_add] at he
        have hstate := congrArg Cfg.state he
        change (E.runFrom (E.runFrom ec 1) v).state = (M.runFrom c (1 + v)).state at hstate
        obtain ⟨s', hs', ha, hx⟩ := hmid (1 + v) (by omega) (by omega)
        have eqs : s = s' := Option.some.inj (hs.symm.trans (hstate.trans hs'))
        simpa [eqs] using And.intro ha hx)
    rw [tr, ← MultiTapeTM.runFrom_add]
    change (E.runFrom ec (1 + n)).mapState emb = _
    rw [show E.runFrom ec (1 + n) =
      embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] (M.runFrom c (1 + n)) from
      embedEmitTM_runFrom Fin.castSuccEmb M _ _ [] c (1 + n)]
    rfl
  refine ⟨run t ht le_rfl, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counterLoopCfg]
    · rw [run u (by omega) (by omega)]
      obtain ⟨s, hs, ha, hx⟩ := hmid u (by omega) hu
      simp [counterLoopCfg, hs, counterLoopRedirect, ha, hx]
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counter_layout, Finset.mem_Icc]
    · rw [run u (by omega) hu]
      simp [counter_layout, Finset.mem_Icc]
  · intro u hu
    refine ⟨u, hu, ?_⟩
    by_cases hz : u = 0
    · subst u; simp [counter_layout]
    · rw [run u (by omega) hu]
      simp [counter_layout]

/-- At the identity embedding the generic and Bool hosts have the same table.
**Proof sketch.** Compute R1 on its public last-tape embedding, cancel the
identity symbol lift, and compare the decrement tables field by field. -/
private lemma counter_refl_agree {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) :
    (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn
      (counterLoopTM M a exit) Set.univ := by
  have action_eq {k : ℕ} {Sy Q : Type} {A B : Action k Sy Q}
      (h1 : A.inputTape = B.inputTape) (h2 : A.workTapes = B.workTapes)
      (h3 : A.output = B.output) (h4 : A.state = B.state) : A = B := by
    cases A; cases B; simp_all
  have lift_refl (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) :
      ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool)).tr f inp work =
        (decrementTM 1 0).tr f inp work := by
    have hd : ∀ o : Option Bool, o.bind (decodeBool (Function.Embedding.refl Bool)) = o := by
      intro o; cases o with
      | none => rfl
      | some b => cases b <;> rfl
    simp only [MultiTapeTM.liftSymbols, hd]
    cases ((decrementTM 1 0).tr f inp work) with
    | mk i w o s =>
      simp only [Action.liftSymbols]
      congr 1
      · funext j
        cases w j with
        | mk a m => cases a with
          | none => rfl
          | some b => cases b <;> rfl
      · cases o <;> rfl
  have embed_last {k : ℕ} {Sy Q : Type} (N : MultiTapeTM 1 Sy Q) (q : Q)
      (inp : Option Sy) (work : Fin (k + 1) → Option Sy) :
      (embedEmitTM (lastEmb k) N).tr q inp work =
        ⟨(N.tr q inp fun _ => work (Fin.last k)).inputTape,
          fun j => if j = Fin.last k then (N.tr q inp fun _ => work (Fin.last k)).workTapes 0
            else (none, 0),
          (N.tr q inp fun _ => work (Fin.last k)).output,
          (N.tr q inp fun _ => work (Fin.last k)).state⟩ := by
    apply action_eq
    · rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [if_true]
        conv_lhs => whnf
        split
        · rename_i i h
          rw [Subsingleton.elim i 0]
          rfl
        · rename_i h
          revert h
          show ((List.finRange 1).find? fun i => decide ((lastEmb k) i = Fin.last k)) = none → _
          simp [lastEmb]
      · simp only [Fin.castSucc_ne_last, if_false]
        conv_lhs => whnf
        split
        · rename_i i' h
          revert h
          show ((List.finRange 1).find? fun i' => decide ((lastEmb k) i' = Fin.castSucc i)) =
            some i' → _
          simp only [lastEmb, Function.Embedding.coeFn_mk, (Fin.castSucc_ne_last i).symm,
            decide_false]
          intro h
          rw [List.find?_eq_none.mpr (fun _ _ => by simp)] at h
          cases h
        · rfl
    · rfl
    · rfl
  have dec_refl (k : ℕ) (f : FlagPhase) (inp : Option Bool)
      (work : Fin (k + 1) → Option Bool) :
      (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool))).tr
          f inp work =
        (decrementTM (k + 1) (Fin.last k)).tr f inp work := by
    rw [embed_last, lift_refl]
    apply action_eq
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · funext j
      rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
        split_ifs <;> simp_all
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
  intro q _ inp work
  cases q with
  | body s => rfl
  | dec f => exact congrArg (Action.mapState (counterLoopDecExit a)) (dec_refl k f inp work)
  | done => rfl
  | escape => rfl

/-- The shared round invariant, with the final body state left unrestricted.
Returning prefixes are exactly the configurations before the next decrement.
**Proof sketch.** Induct once on the number of rounds. The current word has
positive value, so the framed decrement succeeds. Append its transported
segment and the forwarding body segment. Equal-width overwrites keep the
original counter frame, and the two cost recurrences give the exact elapsed
time. Earlier starts at the anchor supply all returns needed by the induction. -/
private lemma counter_rounds {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s)) :
    let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
      counterLoopCfg (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
        (counterLoopOrbit M τ c n) (wordPatch ct cp ((counterWord w n).map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      elapsed cp w.length (fun p => ∃ r u,
        ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
      Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
    have hpatch : wordPatch ct cp ((counterWord w 0).map e) = ct := by
      change wordPatch ct cp (w.map e) = ct
      exact wordPatch_self ct cp (w.map e) (by simpa only [List.length_map] using hw)
    rw [hpatch]
    refine ⟨by simp only [counterLoopOrbit, roundOrbit_zero], ?_, ?_, ?_⟩
    · intro u hu; omega
    · intro u hu; have hz : u = 0 := by omega
      subst u; simp [counter_layout, Finset.mem_Icc]
    · intro u hu; have hz : u = 0 := by omega
      subst u
      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_layout, counterLoopOrbit, roundOrbit_zero]⟩
  | succ n ih =>
    obtain ⟨before, span⟩ := ih (by omega) (fun r hr => hround r (by omega))
    obtain ⟨ha, ht, hg⟩ := hround n (by omega)
    have control : (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit)) =
        some (CounterLoopState.dec FlagPhase.run) := by
      split_ifs <;> simp [ha, counterLoopRedirect]
    rw [control] at before
    let cn := counterLoopOrbit M τ c n
    let wn := counterWord w n
    let pn := wordPatch ct cp (wn.map e)
    let nextTape := wordPatch ct cp ((counterWord w (n + 1)).map e)
    let cost := 2 * (wn.takeWhile not).length + 2
    have hd := counter_word_decrement w n (by omega)
    have hf := counter_patch_frame (w.map e) (wn.map e) ct cp
      (by simp [List.length_map, wn, counterWord_length]) (by simpa using hw)
    obtain ⟨debit, ds⟩ := counter_debit e M a exit cn wn pn cp (by simpa using hf)
    change decFixed wn = some (counterWord w (n + 1)) at hd
    simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
    rw [counter_patch_twice ct cp (wn.map e) ((counterWord w (n + 1)).map e)
      (by simp only [List.length_map, wn, counterWord_length])] at debit
    obtain ⟨body, bs⟩ := counter_body e M a exit cn nextTape cp w.length (τ cn) ha ht hg
    have round : (counterLoopTMVia e M a exit).runFrom
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
        counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
          (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
      rw [MultiTapeTM.runFrom_add, debit, body]
      rw [show counterLoopOrbit M τ c (n + 1) = M.runFrom cn (τ cn) from
        roundOrbit_succ M τ c n]
    have rs : counterSpan (counterLoopTMVia e M a exit)
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
        (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
      have h₁ : counterSpan (counterLoopTMVia e M a exit)
          (counterLoopCfg (some (.dec .run)) cn pn cp) cost cp w.length
          (fun p => ∀ j, p j = cn.workTapePos j) := by
        simpa only [List.length_map, wn, counterWord_length] using ds
      have s₁ := (counterSpan_iff_segment ..).1 h₁
      rw [debit] at s₁
      rw [counterSpan_iff_segment, MultiTapeTM.runFrom_add, debit]
      refine (s₁.mono subset_rfl ?_).trans ((counterSpan_iff_segment ..).1 bs)
      exact fun p hp => ⟨hp.1, 0, Nat.zero_le _, by simpa using hp.2⟩
    have time : (∑ r ∈ Finset.range (n + 1), τ (counterLoopOrbit M τ c r)) +
        counterOverhead w (n + 1) =
        ((∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r)) + counterOverhead w n) +
          (cost + τ cn) := by
      simp [counterOverhead, Finset.sum_range_succ, cost, wn, cn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    dsimp only
    rw [time]
    refine ⟨?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, before, round]
      rfl
    · have s₁ := (counterSpan_iff_segment ..).1 span
      rw [before] at s₁
      rw [counterSpan_iff_segment, MultiTapeTM.runFrom_add, before]
      refine (s₁.mono subset_rfl ?_).trans
        (((counterSpan_iff_segment ..).1 rs).mono subset_rfl ?_)
      · rintro p ⟨hc, r, u, hr, heads⟩
        refine ⟨hc, r, u, Or.inl ?_, heads⟩
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · exact ⟨by omega, hu⟩
        · exact ⟨by omega, Nat.zero_le _⟩
      · rintro p ⟨hc, u, hu, heads⟩
        exact ⟨hc, n, u, Or.inl ⟨by omega, hu⟩, heads⟩

/-- The rich-alphabet counter host returns after all rounds
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction and append the
transported final underflow sweep. -/
theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨before, span⟩ := counter_rounds e M a exit τ c w ct cp hw d (by omega)
    (fun r hr => ⟨(hround r hr).1, (hround r hr).2.1, (hround r hr).2.2.1⟩)
  have control : (if d = 0 then some (.dec .run) else
      (counterLoopOrbit M τ c d).state.map (counterLoopRedirect a exit)) =
      some (CounterLoopState.dec FlagPhase.run) := by
    by_cases hz : d = 0
    · simp [hz]
    · have ret := (hround (d - 1) (by omega)).2.2.2
      rw [show d - 1 + 1 = d by omega] at ret
      simp [hz, ret, counterLoopRedirect]
  rw [control] at before
  let wd := counterWord w d
  have width : wd.length = w.length := counterWord_length w d
  have empty : wd = List.replicate w.length false := by
    simpa only [hd] using counter_word_exhausted w
  have under : decFixed wd = none := (counter_dec_zero wd).mpr (by simp [empty])
  have framed := counter_patch_frame (w.map e) (wd.map e) ct cp
    (by simpa using width) (by simpa using hw)
  obtain ⟨debit, ds⟩ := counter_debit e M a exit (counterLoopOrbit M τ c d) wd
    (wordPatch ct cp (wd.map e)) cp (by simpa using framed)
  simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
    width] at debit
  rw [counter_patch_twice ct cp (wd.map e) ((List.replicate w.length true).map e)
    (by simp [width])] at debit
  have fill : wordPatch ct cp ((List.replicate w.length true).map e) =
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) := by
    rw [List.map_replicate]
    exact wordPatch_replicate ct cp w.length (e true)
  rw [fill] at debit
  have time : (∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) +
      counterOverhead w (d + 1) =
      ((∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) + counterOverhead w d) +
        (2 * (wd.takeWhile not).length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, wd, Nat.add_assoc]
  rw [time]
  refine ⟨?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, before, debit]
  · rw [width, ← before] at ds
    have s := ((counterSpan_iff_segment ..).1 span).trans
      (((counterSpan_iff_segment ..).1 ds).mono subset_rfl fun p hp =>
        ⟨hp.1, d, 0, Or.inr ⟨rfl, rfl⟩, by simpa using hp.2⟩)
    rw [← MultiTapeTM.runFrom_add] at s
    exact (counterSpan_iff_segment (R := fun p => ∃ r u,
      ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) ..).2 s

/-- The rich-alphabet counter host takes an early body exit
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction; its unrestricted
last body state redirects to the designated escape. -/
theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨he, hs⟩ := counter_rounds e M a (some ex) τ c w ct cp hw (r₀ + 1)
    (by omega) (by
      intro r hr
      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
      refine ⟨ha, ht, ?_⟩
      intro u hu hut
      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
  refine ⟨?_, hs.1, hs.2.1, ?_⟩
  · have hpatch : ∀ u : List _, wordPatch ct cp u = fun q =>
        if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q :=
      fun u => funext (wordPatch_apply ct cp u)
    simp only [hpatch] at he
    simp only [List.length_map, counterWord_length] at he
    simpa [hexit, hea, counterLoopRedirect] using he
  · simpa only [Nat.lt_succ_iff] using hs.2.2

/-- **The counter-driven loop, every round returns** (design §12.7, C2).
Start the host at its decrement phase, with body configuration `c` and the
delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
anchor, the exit and halting in between, and returns to `a`. Then the host
reaches `done` at exactly `T`: the `d` round times plus the exact decrement
overhead, including the final underflow sweep. Its body part is the orbit
after `d` rounds, its counter is all `true`, and its counter head is back at
`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
some point of some round. With `exit = none`, the hypotheses do not mention an
exit at all.

**Proof sketch.** Induct on the round. Each decrement is
`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
redirection is applied at the exit step. Each round is the R1 run
`Turing.embedEmitTM_runFrom` with its states renamed by
`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
step while the body's next state is neither the anchor nor the exit, which
the round hypothesis guarantees before the final step; the final step is the
redirection. The counter word before round
`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
costs add to `Turing.counterOverhead w (d + 1)`.

**Re-derivation appendix (R8.0b).** Apply the generic returning contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a exit).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a exit) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  simp only [z5]
  exact counterLoopTMVia_run_done (Function.Embedding.refl Bool) M a exit τ c w ct cp hw'
    d hd hround T hT

/-- **The counter-driven loop, early exit** (design §12.7, C2). As
`Turing.counterLoopTM_run_done`, except that round `r₀`, below the counter's
value, ends at the designated exit `e ≠ a` while every earlier round returns
to `a`. Then the host reaches `escape` at exactly the `r₀ + 1` round times plus
the cost of the `r₀ + 1` decrements before them. Its body part is the orbit
after round `r₀`, and its counter holds `Turing.counterWord w (r₀ + 1)`.
Earlier, neither exit anchor occurs, and the trajectory clauses hold as in
the returning case.

**Proof sketch.** The induction of `Turing.counterLoopTM_run_done`, stopped at
round `r₀`: every decrement before it succeeds, since `r₀` is below the value
(`Turing.counterWord_value`), and the redirection sends round `r₀`'s final
step to `escape`.

**Re-derivation appendix (R8.0b).** Apply the generic escape contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a (some e)).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a (some e)).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a (some e)) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  have h := counterLoopTMVia_run_escape (Function.Embedding.refl Bool) M a e hea τ c w ct cp
    hw' r₀ hr₀ hround hexit T hT
  simp only [Function.Embedding.coe_refl, List.map_id] at h
  simp only [z5]
  exact h

/-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
the `d` rounds costs at most `B`, the returning run's exact time is at most
`d·B + 4d + 2|w| + 2`.

**Proof sketch.** Bound the round sum termwise by `B`
(`Finset.sum_le_card_nsmul`) and the decrement share by
`Turing.counterOverhead_le`. -/
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range d)
    (fun r => τ (counterLoopOrbit M τ c r)) B
    (fun r hr => hB r (Finset.mem_range.mp hr))
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hc := counterOverhead_le w
  rw [hd] at hc
  calc
    _ ≤ d * B + (4 * d + 2 * w.length + 2) :=
      Nat.add_le_add (by simpa using hsum) hc
    _ = _ := by omega

/-! ## R8.6 — the expansion (§12.8) -/

/-- **R8.6, the expansion** (design §12.8a). The counter loop whose round is
the advancing writer: with a counter of value `d` on the last tape, it writes
the pattern `pat` on tape `i` `d` times, contiguously from the head, and leaves
the head after the last copy. Its uses are lengths given in binary: the
window halves of a record, of length `d·|pat|` for a radius counter `d`. -/
def expandTM (k : ℕ) (i : Fin k) (pat : List Bool) :
    MultiTapeTM (k + 1) Bool (CounterLoopState (Fin (pat.length + 1))) :=
  counterLoopTM (writeAdvTM k i pat) 0 none

/-- **R8.6, the expansion, framed** (design §12.8a). Start the expansion at its
decrement phase with body configuration `c` at the writer's state `0` and the
delimited counter word `w`, of value `d`, at `cp`. It reaches `done` at exactly
`d·(|pat| + 1) + counterOverhead w (d + 1)` and neither exit anchor earlier.
At that point the interval `[pos, pos + d·|pat|)` of tape `i` holds `d` copies
of `pat`, whatever it held before, the head of tape `i` is at `pos + d·|pat|`,
the counter is all `true` with its head back at `cp`, and every other cell,
every other head, the input position and the output are unchanged. Throughout,
the counter head stays within `[cp - 1, cp + |w|]`, the head of tape `i`
within `[pos, pos + d·|pat|]`, and every other body head is fixed.

**Proof sketch.** Apply `Turing.counterLoopTM_run_done` with the constant round
time `τ := |pat| + 1`. The round hypotheses are `Turing.writeAdvTM_run_ofCfg`
at the orbit's `r`-th configuration, which by induction on `r` has `r` copies
of `pat` written from `pos` and its head at `pos + r·|pat|`. The round sum is
`d·(|pat| + 1)`. The head clauses follow from the loop's trajectory clause and
the writer's. -/
theorem expandTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfg (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) := by
  let M := writeAdvTM k i pat
  let τ : Cfg k Bool (Fin (pat.length + 1)) x → ℕ := fun _ => pat.length + 1
  let finish (r : ℕ) : Cfg k Bool (Fin (pat.length + 1)) x :=
    { c with
      workTapes := fun j q =>
        if j = i ∧ c.workTapePos j ≤ q ∧
            q < c.workTapePos j + ((r * pat.length : ℕ) : ℤ)
          then FinTM.bufferTape (List.replicate r pat).flatten (q - c.workTapePos j)
        else c.workTapes j q
      workTapePos := Function.update c.workTapePos i
        (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) }
  -- This induction concerns only the advancing writer's orbit, not the loop host.
  have orbit (r : ℕ) : counterLoopOrbit M τ c r = finish r := by
    induction r with
    | zero =>
      change c = finish 0
      apply Cfg.ext <;> try rfl
      · funext j q
        simp [finish]
      · funext j
        by_cases hj : j = i <;> simp [finish, hj]
    | succ r ih =>
      have step := (writeAdvTM_run_ofCfg i pat (finish r) hc).1
      rw [show counterLoopOrbit M τ c (r + 1) =
        M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) from
        Function.iterate_succ_apply' _ _ _, ih]
      change (writeAdvTM k i pat).runFrom (finish r) (pat.length + 1) = finish (r + 1)
      rw [step]
      have length : (List.replicate r pat).flatten.length = r * pat.length := by simp
      have append : (List.replicate (r + 1) pat).flatten =
          (List.replicate r pat).flatten ++ pat := by
        rw [List.replicate_succ', List.flatten_append]
        simp
      apply Cfg.ext
      · exact hc.symm
      · rfl
      · funext j q
        by_cases hj : j = i
        · subst j
          simp only [finish, Function.update_self, true_and, Nat.add_mul, Nat.one_mul,
            Nat.cast_add, append]
          by_cases hnew : c.workTapePos i + ((r * pat.length : ℕ) : ℤ) ≤ q ∧
              q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)
          · have hwhole : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
            simp only [hnew, hwhole]
            have h0 : 0 ≤ q - c.workTapePos i := by omega
            have h1 : 0 ≤ q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) := by omega
            have hn : ¬ (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
              rw [length]; omega
            simp only [FinTM.bufferTape, h0, h1, if_true, List.getElem?_append, hn, if_false]
            rw [show (q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ))).toNat =
              (q - c.workTapePos i).toNat - (List.replicate r pat).flatten.length by
                rw [length]; omega]
            simp only [and_self, if_true]
          · simp only [hnew, if_false]
            by_cases hold : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ)
            · have hwhole : c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
              have h0 : 0 ≤ q - c.workTapePos i := by omega
              have hn : (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
                rw [length]; omega
              simp only [hold, hwhole, FinTM.bufferTape, h0, List.getElem?_append, hn, if_true]
            · have hwhole : ¬ (c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ))) := by omega
              simp only [hold, hwhole, if_false]
        · simp [finish, hj]
      · funext j
        by_cases hj : j = i
        · subst j
          simp [finish, Nat.add_mul, Nat.cast_add, add_assoc]
        · simp [finish, hj]
      · rfl
  have state (r : ℕ) : (counterLoopOrbit M τ c r).state = some 0 := by
    rw [orbit]; exact hc
  have rounds : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some 0 ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ 0 ∧ (none : Option (Fin (pat.length + 1))) ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some 0 := by
    intro r hr
    have spec := writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)
    refine ⟨state r, Nat.succ_pos _, ?_, state (r + 1)⟩
    intro u hu hut
    change u < pat.length + 1 at hut
    have live := MultiTapeTM.runFrom_state_ne_none_of_le M (counterLoopOrbit M τ c r)
      (pat.length + 1) (by rw [spec.1]; simp) u (by omega)
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp live
    refine ⟨s, hs, ?_, Option.noConfusion⟩
    intro he
    exact spec.2.1 u hu hut (hs.trans (congrArg some he))
  obtain ⟨he, hcut, hcounter, hbody⟩ := counterLoopTM_run_done M 0 none τ c w ct cp hw d hd
    rounds (d * (pat.length + 1) + counterOverhead w (d + 1)) (by simp [τ])
  refine ⟨?_, hcut, hcounter, ?_⟩
  · rw [orbit] at he
    exact he
  · intro t ht j
    obtain ⟨r, u, hr, heads⟩ := hbody t ht
    have spec := (writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)).2.2
    have hu : u ≤ pat.length + 1 := by
      rcases hr with h | ⟨rfl, rfl⟩
      · exact h.2
      · omega
    have hh := spec j u hu
    rw [heads j]
    by_cases hj : j = i
    · subst j
      simp only [ite_true, orbit, finish, Function.update_self, Finset.mem_Icc] at hh ⊢
      rcases hr with ⟨hr, _⟩ | ⟨rfl, rfl⟩
      · have hrd : (r + 1) * pat.length ≤ d * pat.length := Nat.mul_le_mul_right _ hr
        rw [Nat.add_mul, Nat.one_mul] at hrd
        exact ⟨by omega, by omega⟩
      · simpa only [MultiTapeTM.runFrom_zero, Function.update_self, le_refl, and_true,
          le_add_iff_nonneg_right] using (Int.natCast_nonneg (r * pat.length))
    · simpa [hj, orbit, finish] using hh

end Turing

/-! ## The counter loop over the round layer (MIG-0b; design §16a item 2)

The counter loop's **body** interface is the round layer of `Build/Contract/Basic`
(`Turing.counterLoopOrbit` is an abbreviation of `Turing.roundOrbit`); its **host** runs are
segments with a joint relation. Below: the host segments derived from the public
`counterLoopTMVia_run_done` and `_run_escape` with round-layer hypotheses on the body rounds,
keeping the public theorems' shared round-and-offset witness for all body heads, their exact
endpoints, the counter interval and liveness (`_witness`), and their corollaries with a body
relation (`_segment`); the host layout as an R1 reconstruction; and the contract-level
compositions `Turing.RoundContract.counterLoopDone` and `counterLoopEscape`, with their
shared-witness joint trajectories. -/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **The counter loop's segment with the shared witness, returning rounds** (fit test of the
segment, round and joint-trajectory layers against `Turing.counterLoopTMVia_run_done`; MIG-0a
gate, round 2). If the first `d` rounds of the body orbit are returning rounds with escape set
`{exit}`, the host run is a segment ending at `done`, live and off both exits before its end. Its
joint relation is the public theorem's, unweakened: the counter head in its interval, and **one**
round `r` and offset `u` at which **every** body head is the body's own.

**Proof sketch.** The round cut, read in the rows' form (`Turing.Round.cut_some`), gives the
public theorem's round hypothesis; its conclusion is the segment, and the live endpoint adds
liveness (`Turing.Segment.live`). -/
theorem counterLoopTMVia_done_witness {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r < d, Round M a {exit} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)) ∧ (roundOrbit M τ c (r + 1)).state = some a) :
    Segment (counterLoopTMVia e M a exit) {none, some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r < d ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
  have hr : ∀ r < d,
      (roundOrbit M τ c r).state = some a ∧ 0 < τ (roundOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (roundOrbit M τ c r) →
        ∃ s, (M.runFrom (roundOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ exit ≠ some s) ∧
      (roundOrbit M τ c (r + 1)).state = some a := by
    intro r hr
    obtain ⟨hR, hret⟩ := hround r hr
    refine ⟨hR.1, hR.2.1, fun u hu hut => ?_, hret⟩
    obtain ⟨s, hs, hsa, hsE⟩ := hR.cut_some u hu hut
    exact ⟨s, hs, hsa, fun h' => hsE (h' ▸ rfl)⟩
  obtain ⟨hrun, hcut, hctr, hbody⟩ :=
    counterLoopTMVia_run_done e M a exit τ c w ct cp hw d hd hr _ rfl
  have h : Segment (counterLoopTMVia e M a exit) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r < d ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
    rw [Turing.segment_iff]
    refine ⟨hrun, fun t ht hm => ?_, fun t ht => ⟨hctr t ht, hbody t ht⟩⟩
    rcases hm with hm | hm
    · exact (hcut t ht).1 hm
    · exact (hcut t ht).2 hm
  exact h.live (Option.some_ne_none _)

/-- **The counter loop's segment, returning rounds, with the body relation**: the corollary of
`Turing.counterLoopTMVia_done_witness` in which the shared witness is used up: the body heads
satisfy the rounds' relation `P` at every time.

**Proof sketch.** At the witness, the body heads are those of round `r` at offset `u`, where `P`
holds by round `r`'s relation, or of the start of round `d`, which is the end of round `d - 1`
(or the start `c` when `d = 0`). -/
theorem counterLoopTMVia_done_segment {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) {P : (Fin k → ℤ) → Prop}
    (h0 : P c.workTapePos)
    (hround : ∀ r < d, Round M a {exit} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)) ∧ (roundOrbit M τ c (r + 1)).state = some a) :
    Segment (counterLoopTMVia e M a exit) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        P fun j => p j.castSucc)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
  refine (counterLoopTMVia_done_witness e M a exit τ c w ct cp hw d hd hround).mono
    (Set.subset_insert _ _) fun p ⟨hc, r, u, hru, hj⟩ => ⟨hc, ?_⟩
  have hP : P (M.runFrom (roundOrbit M τ c r) u).workTapePos := by
    rcases hru with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
    · exact (hround r hr).1.2.2.2.2.2 u hu
    · rcases Nat.eq_zero_or_pos r with rfl | hpos
      · exact h0
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hR := (hround r' (by omega)).1
        have hend := hR.2.2.2.2.2 _ le_rfl
        rw [hR.2.2.1] at hend
        exact hend
  have he : (fun j : Fin k => p j.castSucc) = (M.runFrom (roundOrbit M τ c r) u).workTapePos :=
    funext hj
  rw [he]
  exact hP

/-- **The counter loop's segment with the shared witness, escaping round** (fit test against
`Turing.counterLoopTMVia_run_escape`): rounds `0` to `r₀` of the body orbit are rounds with escape
`{some ex}`, round `r₀` escaping, with `r₀` below the counter's value. Then the host run is a
segment ending at `escape`, live and off both exits before its end, with the public theorem's
joint relation: the counter interval and one shared round and offset for all body heads.

**Proof sketch.** The round cut gives the public escape theorem's hypothesis; its conclusion is
the segment, and the live endpoint adds liveness. -/
theorem counterLoopTMVia_escape_witness {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat)) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r ≤ r₀, Round M a {some ex} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)))
    (hexit : (roundOrbit M τ c (r₀ + 1)).state = some ex) :
    Segment (counterLoopTMVia e M a (some ex)) {none, some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r ≤ r₀ ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
  have hr : ∀ r ≤ r₀,
      (roundOrbit M τ c r).state = some a ∧ 0 < τ (roundOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (roundOrbit M τ c r) →
        ∃ s, (M.runFrom (roundOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex) := by
    intro r hr
    obtain ⟨hc, ht, -, -, -, -⟩ := hround r hr
    refine ⟨hc, ht, fun u hu hut => ?_⟩
    obtain ⟨s, hs, hsa, hsE⟩ := (hround r hr).cut_some u hu hut
    exact ⟨s, hs, hsa, fun h => hsE (by rw [h]; rfl)⟩
  obtain ⟨hrun, hcut, hctr, hbody⟩ := counterLoopTMVia_run_escape e M a ex hea τ c w ct cp hw r₀
    hr₀ hr hexit _ rfl
  have h : Segment (counterLoopTMVia e M a (some ex)) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r ≤ r₀ ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
    rw [Turing.segment_iff]
    refine ⟨hrun, fun t ht hm => ?_, fun t ht => ⟨hctr t ht, hbody t ht⟩⟩
    rcases hm with hm | hm
    · exact (hcut t ht).1 hm
    · exact (hcut t ht).2 hm
  exact h.live (Option.some_ne_none _)

/-- **The counter loop's segment, escaping round, with the body relation**: the corollary of
`Turing.counterLoopTMVia_escape_witness` with the shared witness used up.

**Proof sketch.** At the witness, the body heads lie in a round, where `P` holds, or at the end
of round `r₀`. -/
theorem counterLoopTMVia_escape_segment {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat)) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r ≤ r₀, Round M a {some ex} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)))
    (hexit : (roundOrbit M τ c (r₀ + 1)).state = some ex) :
    Segment (counterLoopTMVia e M a (some ex)) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        P fun j => p j.castSucc)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
  refine (counterLoopTMVia_escape_witness e M a ex hea τ c w ct cp hw r₀ hr₀ hround hexit).mono
    (Set.subset_insert _ _) fun p ⟨hc, r, u, hru, hj⟩ => ⟨hc, ?_⟩
  have hP : P (M.runFrom (roundOrbit M τ c r) u).workTapePos := by
    rcases hru with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
    · exact (hround r hr).2.2.2.2.2 u hu
    · have hR := hround r₀ le_rfl
      have hend := hR.2.2.2.2.2 _ le_rfl
      rw [hR.2.2.1] at hend
      exact hend
  have he : (fun j : Fin k => p j.castSucc) = (M.runFrom (roundOrbit M τ c r) u).workTapePos :=
    funext hj
  rw [he]
  exact hP

/-- The body configuration of a counter-loop host configuration: the first `k` tapes and heads,
the input position and the output, at the body anchor `a`. -/
def counterLoopBody {S : Type} {x : List Γ} (a : S) (d : Cfg (k + 1) Γ (CounterLoopState S) x) :
    Cfg k Γ S x :=
  ⟨some a, d.inputPos, fun j => d.workTapes j.castSucc, fun j => d.workTapePos j.castSucc,
    d.output⟩

/-! The body configuration's fields, as equations (the specification API, the briefs' pre-ship
inventories, 2026-10-16): generated by `simps` without the `simp` attribute. -/
attribute [simps (config := { isSimp := false })] counterLoopBody

/-- **The counter-loop host layout is an R1 reconstruction** (a seventh member of the family:
`CounterLoop`'s private `counter_layout`, `Build/CounterLoop.lean:650`): every host configuration
is the counter-loop configuration of its body, its counter tape and its counter head.

**Proof sketch.** `Turing.counterLoopCfg` is the forwarding embedding along `Fin.castSucc`,
relabelled and with its state replaced. `Turing.embedEmitCfg_eq` identifies the embedding with
`d`'s tapes and heads: the selected ones are the body's, and the only unselected tape is the
last, which is the counter. -/
theorem counterLoopCfg_body {S : Type} {x : List Γ} (a : S)
    (d : Cfg (k + 1) Γ (CounterLoopState S) x) :
    counterLoopCfg d.state (counterLoopBody a d) (d.workTapes (Fin.last k))
      (d.workTapePos (Fin.last k)) = d := by
  have hlast : ∀ j : Fin (k + 1), j ∉ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) →
      j = Fin.last k := by
    intro j hj
    induction j using Fin.lastCases with
    | last => rfl
    | cast i => exact absurd ⟨i, rfl⟩ hj
  have h := embedEmitCfg_eq (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
    (fun _ => d.workTapes (Fin.last k)) (fun _ => d.workTapePos (Fin.last k)) []
    (counterLoopBody a d)
    (⟨some a, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ : Cfg (k + 1) Γ S x)
    rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)
    (fun j hj => by rw [hlast j hj]; exact ⟨rfl, rfl⟩)
  unfold counterLoopCfg
  rw [h]
  rfl

/-- The value of a counter word. -/
def counterValue (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat)

/-- **The counter value, unfolded** (the ND inventory API, round 2; C1-R's escalation E1):
`counterValue w = Nat.ofDigits 2 (w.map Bool.toNat)`, the form of the hosted loop's value
hypothesis (`Turing.StepBlock.hostedLoopTM_run`'s `ht`). -/
theorem counterValue_eq (w : List Bool) : counterValue w = Nat.ofDigits 2 (w.map Bool.toNat) :=
  rfl

/-- **The counter value is the parser's binary value**: the `foldr` of `Nat.bit` over a word, its
value as a little-endian binary numeral (`Turing.codeBitsNat`), is `Nat.ofDigits 2` of its bits,
the value `Turing.counterValue` that the counter loop counts down. (Moved unchanged, as a public
lemma, from the private `canonBits_value` of `TuringMachine/CodeSimulator.lean`, whose canonizer
still uses it.)

**Proof sketch.** `Nat.ofDigits 2` is a `foldr` of `b + 2·n` over the mapped digits; fuse the
map into the fold, and `b.toNat + 2·n` is `Nat.bit b n`. -/
theorem foldr_bit_eq_ofDigits (w : List Bool) :
    w.foldr Nat.bit 0 = Nat.ofDigits 2 (w.map Bool.toNat) := by
  rw [Nat.ofDigits_eq_foldr, List.foldr_map]
  have step : (fun (bit : Bool) (tail : ℕ) => (bit.toNat : ℕ) + 2 * tail) = Nat.bit := by
    funext bit tail
    cases bit <;> simp [Nat.bit, Nat.add_comm]
  simpa only [Nat.cast_id] using
    congrArg (fun f : Bool → ℕ → ℕ => w.foldr f 0) step.symm

/-- **The counter word of `t` has value `t`**: the canonical little-endian binary word `t.bits`,
used as a counter word, has `Turing.counterValue` exactly `t` (`0` for the empty word). It is the
value hypothesis of the counter loop's contracts (`Turing.counterLoopTM_run_done`, and
`Turing.StepBlock.loopTM_run`'s `ht`) for the deadline counter `bits t`.

**Proof sketch.** The counter value is the parser's binary value (`foldr_bit_eq_ofDigits`), and
binary reconstruction inverts `Nat.bits` (`Turing.codeBitsNat_bits`). -/
theorem counterValue_bits (t : ℕ) : counterValue t.bits = t := by
  rw [counterValue, ← foldr_bit_eq_ofDigits]
  exact codeBitsNat_bits t

/-- **The counter loop over a round contract, every round returning** (design §16a item 2; the
contract-level composition over the round layer). The index is the body data `i` and the counter
word `w`. An admissible host start holds `w`, delimited, at its counter head, and every one of
the `value w` rounds of the body orbit from its body (each round lasting the round contract's
time) is admissible and returns. The host then reaches `done` at the public theorem's exact time,
with the orbit after `value w` rounds as its body and the counter filled with `true`. The counter
head stays in `[cp - 1, cp + |w|]`, and the body heads in the hull of the rounds' envelopes and
the final body head (`Turing.RoundContract.hullLo`, `hullHi`).

**Proof sketch.** A segment to a first exit, so `Turing.Contract.ofSegment`. The host start is the
counter-loop configuration of its body (`Turing.counterLoopCfg_body`). The orbit's rounds are
rounds under the hull box (`Turing.RoundContract.orbit_round`) and return, so
`Turing.counterLoopTMVia_done_segment` gives the segment, with the counter interval and the hull
box on the body heads, which combine into the host box (`Turing.headBox_lastCases`). The endpoint
is at `done`. -/
noncomputable def RoundContract.counterLoopDone {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a : S} {exit : Option S} {ι : Type} {x : List Γ}
    (R : RoundContract M a {exit} ι x) :
    Contract (counterLoopTMVia e M a exit) (.dec .run) {some .done, some .escape}
      (ι × List Bool) x :=
  Contract.ofSegment
    (fun p d =>
      (∀ q : ℤ, -1 ≤ q → q ≤ (p.2.length : ℤ) →
        d.workTapes (Fin.last k) (d.workTapePos (Fin.last k) + q) =
          FinTM.bufferTape (p.2.map e) q) ∧
      ∀ r < counterValue p.2,
        R.pre p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) ∧
        (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a)
    (fun p d => ∑ r ∈ Finset.range (counterValue p.2),
      R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) +
      counterOverhead p.2 (counterValue p.2 + 1))
    (fun p d => counterLoopCfg (some .done)
      (roundOrbit M (R.time p.1) (counterLoopBody a d) (counterValue p.2))
      (fun q => if d.workTapePos (Fin.last k) ≤ q ∧
          q < d.workTapePos (Fin.last k) + (p.2.length : ℤ)
        then some (e true) else d.workTapes (Fin.last k) q)
      (d.workTapePos (Fin.last k)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ) (d.workTapePos (Fin.last k) - 1)
      (R.hullLo p.1 (counterLoopBody a d) (counterValue p.2)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ)
      (d.workTapePos (Fin.last k) + (p.2.length : ℤ))
      (R.hullHi p.1 (counterLoopBody a d) (counterValue p.2)))
    (fun p d hd hp => by
      have hc : (counterLoopBody a d).state = some a := rfl
      have hpre := fun r hr => (hp.2 r hr).1
      have hret : ∀ r, r + 1 < counterValue p.2 →
          (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a :=
        fun r hr => (hp.2 r (by omega)).2
      have hseg := counterLoopTMVia_done_segment e M a exit (R.time p.1) (counterLoopBody a d)
        p.2 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hp.1 (counterValue p.2) rfl
        (R.orbit_start p.1 _ hc _ hpre hret) (fun r hr =>
          ⟨R.orbit_round p.1 _ hc _ hpre hret r hr, by
            rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret r hr)
              (hpre r hr)]
            exact (hp.2 r hr).2⟩)
      rw [← hd, counterLoopCfg_body] at hseg
      exact hseg.mono subset_rfl fun q hq => headBox_lastCases hq.1 hq.2)
    (fun _ _ _ _ => Set.mem_insert _ _)

/-- **The counter loop over a round contract, escaping at round `r₀`** (the contract-level
composition over the round layer). The index is the body data, the counter word and the escaping
round `r₀`, below the counter's value. Rounds `0` to `r₀` of the body orbit are admissible, the
first `r₀` return and round `r₀` escapes. The host reaches `escape` at the public theorem's exact
time, with the orbit after `r₀ + 1` rounds as its body and the counter decremented `r₀ + 1`
times; the envelope is the hull of the `r₀ + 1` round boxes, as in
`Turing.RoundContract.counterLoopDone`.

**Proof sketch.** As for `Turing.RoundContract.counterLoopDone`, through
`Turing.counterLoopTMVia_escape_segment`; the escape is the endpoint of round `r₀`, the next orbit
point. -/
noncomputable def RoundContract.counterLoopEscape {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a ex : S} (hea : ex ≠ a) {ι : Type} {x : List Γ}
    (R : RoundContract M a {some ex} ι x) :
    Contract (counterLoopTMVia e M a (some ex)) (.dec .run) {some .done, some .escape}
      (ι × List Bool × ℕ) x :=
  Contract.ofSegment
    (fun p d =>
      (∀ q : ℤ, -1 ≤ q → q ≤ (p.2.1.length : ℤ) →
        d.workTapes (Fin.last k) (d.workTapePos (Fin.last k) + q) =
          FinTM.bufferTape (p.2.1.map e) q) ∧
      p.2.2 < counterValue p.2.1 ∧
      (∀ r < p.2.2 + 1, R.pre p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∧
      (∀ r, r + 1 < p.2.2 + 1 →
        (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a) ∧
      (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) p.2.2)).state = some ex)
    (fun p d => ∑ r ∈ Finset.range (p.2.2 + 1),
      R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) +
      counterOverhead p.2.1 (p.2.2 + 1))
    (fun p d => counterLoopCfg (some .escape)
      (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1))
      (fun q => if d.workTapePos (Fin.last k) ≤ q ∧
          q < d.workTapePos (Fin.last k) + (p.2.1.length : ℤ)
        then FinTM.bufferTape ((counterWord p.2.1 (p.2.2 + 1)).map e)
          (q - d.workTapePos (Fin.last k))
        else d.workTapes (Fin.last k) q)
      (d.workTapePos (Fin.last k)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ) (d.workTapePos (Fin.last k) - 1)
      (R.hullLo p.1 (counterLoopBody a d) (p.2.2 + 1)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ)
      (d.workTapePos (Fin.last k) + (p.2.1.length : ℤ))
      (R.hullHi p.1 (counterLoopBody a d) (p.2.2 + 1)))
    (fun p d hd hp => by
      obtain ⟨hw, hr₀, hpre, hret, hesc⟩ := hp
      have hc : (counterLoopBody a d).state = some a := rfl
      have hexit : (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1)).state =
          some ex := by
        rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret p.2.2 (by omega))
          (hpre p.2.2 (by omega))]
        exact hesc
      have hseg := counterLoopTMVia_escape_segment e M a ex hea (R.time p.1)
        (counterLoopBody a d) p.2.1 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hw
        p.2.2 hr₀ (fun r hr => R.orbit_round p.1 _ hc _ hpre hret r (by omega)) hexit
      rw [← hd, counterLoopCfg_body] at hseg
      exact hseg.mono subset_rfl fun q hq => headBox_lastCases hq.1 hq.2)
    (fun _ _ _ _ => Set.mem_insert_of_mem _ rfl)

/-! The brief-inventory API (user 2026-10-16; its gate, finding 2): the two contract-level
counter loops' data fields as equations, generated by `simps!` (their bodies are
`Turing.Contract.ofSegment` applications) without the `simp` attribute. -/
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  RoundContract.counterLoopDone RoundContract.counterLoopEscape

/-- **The counter loop's contract keeps the shared witness** (MIG-0a gate, round 2): the
contract-level joint trajectory of `Turing.RoundContract.counterLoopDone` is the public theorem's
relation, one round `r` and offset `u` at which every body head is the body's own, beyond the
per-tape hull that its envelope states.

**Proof sketch.** The same segment as the contract's, with the unweakened relation
(`Turing.counterLoopTMVia_done_witness`), from the host start rewritten as the counter-loop
configuration of its body. -/
theorem RoundContract.counterLoopDone_traj {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a : S} {exit : Option S} {ι : Type} {x : List Γ}
    (R : RoundContract M a {exit} ι x) :
    (R.counterLoopDone e).Traj fun p d q => ∃ r u,
      ((r < counterValue p.2 ∧
          u ≤ R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∨
        (r = counterValue p.2 ∧ u = 0)) ∧
      ∀ j : Fin k, q j.castSucc =
        (M.runFrom (roundOrbit M (R.time p.1) (counterLoopBody a d) r) u).workTapePos j := by
  intro p d hd hp u hu
  have hc : (counterLoopBody a d).state = some a := rfl
  have hpre := fun r hr => (hp.2 r hr).1
  have hret : ∀ r, r + 1 < counterValue p.2 →
      (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a :=
    fun r hr => (hp.2 r (by omega)).2
  have hseg := counterLoopTMVia_done_witness e M a exit (R.time p.1) (counterLoopBody a d)
    p.2 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hp.1 (counterValue p.2) rfl
    (fun r hr =>
      ⟨R.orbit_round p.1 _ hc _ hpre hret r hr, by
        rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret r hr)
          (hpre r hr)]
        exact (hp.2 r hr).2⟩)
  rw [← hd, counterLoopCfg_body] at hseg
  rw [Turing.segment_iff] at hseg
  exact (hseg.2.2 u hu).2

/-- **The escaping counter loop's contract keeps the shared witness**: as
`Turing.RoundContract.counterLoopDone_traj`, for `Turing.RoundContract.counterLoopEscape`.

**Proof sketch.** The contract's segment with the unweakened relation
(`Turing.counterLoopTMVia_escape_witness`). -/
theorem RoundContract.counterLoopEscape_traj {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a ex : S} (hea : ex ≠ a) {ι : Type} {x : List Γ}
    (R : RoundContract M a {some ex} ι x) :
    (R.counterLoopEscape e hea).Traj fun p d q => ∃ r u,
      ((r ≤ p.2.2 ∧ u ≤ R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∨
        (r = p.2.2 + 1 ∧ u = 0)) ∧
      ∀ j : Fin k, q j.castSucc =
        (M.runFrom (roundOrbit M (R.time p.1) (counterLoopBody a d) r) u).workTapePos j := by
  intro p d hd hp u hu
  obtain ⟨hw, hr₀, hpre, hret, hesc⟩ := hp
  have hc : (counterLoopBody a d).state = some a := rfl
  have hexit : (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1)).state =
      some ex := by
    rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret p.2.2 (by omega))
      (hpre p.2.2 (by omega))]
    exact hesc
  have hseg := counterLoopTMVia_escape_witness e M a ex hea (R.time p.1)
    (counterLoopBody a d) p.2.1 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hw
    p.2.2 hr₀ (fun r hr => R.orbit_round p.1 _ hc _ hpre hret r (by omega)) hexit
  rw [← hd, counterLoopCfg_body] at hseg
  rw [Turing.segment_iff] at hseg
  exact (hseg.2.2 u hu).2

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
