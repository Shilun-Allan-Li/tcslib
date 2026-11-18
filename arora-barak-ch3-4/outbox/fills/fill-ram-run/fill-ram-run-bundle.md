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

## ===== campaign/items/ram-tm/briefs/fill-ram-run.md =====

# RAM fill (Codex), tier 2 job E: the simulation (`Simulation`, the 2 targets)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-run`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/Simulation.lean` states stage 2: a program `P` of the extended
word RAM is simulated by one `FinTM Bool` (`WordRAM.exists_simulation`) and by one `FinNDTM Bool`
(`WordRAM.exists_ndSimulation`), within `simTime` steps and `simSpace` cells. The statements
were gated on 2026-10-14 and are frozen. **This job proves both**, from the interfaces of
PR #372:
- `WordRAM.Sim.exists_startup` (job C);
- `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase` (job D).

They are sorried at your base and cited as stated. Once jobs A–D land, the two targets and the
nine class corollaries of `RAMSimulation/Classes` are unconditional.

## The argument

Gate 162's pack, "How the interfaces give the frozen bounds", gives it, and the auditor checked
it (G162-23). In outline:

1. **The machine.**
   - **Phases.** Choose `a` from `P`, larger than the bit length of every address written in `P`,
     so `ImmBound a ins` for every instruction. Index the phases by (position `p ≤ |P|`,
     parity). Position `|P|` is the "past the end" phase, which rejects.
   - **Dispatch.** A phase at `p` with exit `next` redirects to `p + 1`, and with `jump` to
     `jumpTarget ins`; targets past `|P|` go to `|P|`. Every redirect flips the parity, so a
     `bltz` to its own position never redirects a phase to itself (`Contract.inPhase` needs
     `q.1 ≠ p`). Verdict phases halt, through `Turing.phaseHostTM_run_le`.
   - **Embedding.** The start-up machine has `8 + k'` tapes. Place each eight-tape phase on its
     first eight tapes. Deterministic phases use `Turing.embedEmitTM` with `Fin.castAddEmb k'`.
     For nondeterministic ones, form the `NDTM` whose transition under `b` is that of
     `embedEmitTM σ (N.fixChoice b)`; its `fixChoice b` is then the embedded deterministic
     machine. Prove `Encodes` transport through the embedding once (`Cfg.select`,
     `embedEmitCfg_*`).
   - **The host.** Use `Turing.NDTM.phaseHostND` (`Build/NDHost`) over the start-up and the
     phases. `phaseHostND_fixChoice` makes its `fixChoice b` the deterministic `phaseHostTM` of
     the phases' `fixChoice b`.
2. **The master induction**, on the `XStepsIn` run of `HaltsWithin` (readers
   `WordRAM.XStepsIn.succ_iff`, `haltsWithin_iff`). Take a choice word `w` and the stream `ρ` of
   its bits at the coin phases' entries. After the start-up and `i` phases, the configuration
   encodes the `i`-th RAM configuration, over the cells `T_i = {-1} ∪` those touched so far, so
   `|T_i| ≤ f + 1`.
   - **Coin phases.** Take the entry's choice explicitly (G162-21).
   - **Everything else.** Transitions agree and the entry is never re-entered, so each slice runs
     deterministically: `Turing.NDTM.runWith_eq_fixChoice_runFrom` and
     `spaceUsedWith_eq_fixChoice_spaceUsed` (`Nondeterministic`, `NondeterministicSpace`). The
     NL compiler's `Complexity.LogProg.ndtm_runWith_eq_runFrom`
     (`SpaceComplexity/Machines/NARMCompile`) is a worked precedent of this shape.
3. **The bounds.**
   - **Time:**
     - the start-up takes at most `TW n + C₀·(n + W² + 1)` steps;
     - each phase takes at most `C₁·((f + 2)·(W + 1) + W² + n + 1)`, plus one dispatch step;
     - with `t ≥ 1` (`HaltsWithin` has `n < t`), the total is at most `simTime`
       (`WordRAM.simTime_eq`).
   - **Space:**
     - the start-up visits at most `SW n + C₀·(W + |bits n| + 1)` cells;
     - afterwards each of the eight tapes stays within its origin
       `± C₁·((f + 2)·(W + 1) + |bits n| + 1)`;
     - the extra tapes never move;
     - with `|bits n| ≤ logSpace n` (`Complexity.logSpace_eq`), the total is at most `simSpace`.
   - Use `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`, and for branches
     `Complexity.LogProg.spaceUsedWith_le_of_ranges`. After the halt,
     `ComputesInTime.spaceUsed_le_of_halt` and `spaceUsedWith_append_of_halt` hold the bound.
4. **The targets.**
   - **`exists_simulation`:** `M = N.fixChoice false`. Its runs are those of the all-`false` word,
     whose stream reads like `ρ = []`: every `ρ.getD k false` is `false`. In verdict mode the
     output is `[v]` (`exists_verdictPhase`); in function mode it is `c.out`.
   - **`exists_ndSimulation`:**
     - every branch of length `T` is the run of some stream, so the uniform hypothesis bounds it
       and it halts;
     - an accepting stream gives an accepting branch, with its bits at the coin entries, padded;
     - an accepting branch gives a stream whose run accepts, by `WordRAM.HaltsWithin.unique`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/Simulation.lean`: the two targets' bodies and sketches, and the
  module docstring. Repair its stale line references here: `phaseHostTM` is at `Seam.lean:886`,
  `exists_inputSeekTM` at `InputCall.lean:291`, `embedSilentTM` at `Embed.lean:253`. Better, name
  declarations instead of lines. Drop "proofs pending" when both are proved.
- **New files** under `TCSlib/Complexity/RAMSimulation/Sim/`, named `Run*.lean` (for example
  `RunHost.lean` for the host and embedding, and `RunInduction.lean` for the induction). Their
  declarations are public in `WordRAM.Sim`, per the tier 2 addendum. `Simulation.lean` imports
  them. Add each to the `RAMSimulation.lean` facade's imports and contents: you may edit the
  facade for that only.

## Admitted dependencies allowed

`WordRAM.Sim.exists_startup`, `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase`,
which in turn reach jobs A–C's statements; those may appear in the walk too. Nothing else, and in
particular nothing from `Build/RecordTable`.

## Downstream check

`RAMSimulation/Classes` and the facades. With this job, `Classes`' nine corollaries reach only
tier 2's statements.

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

## ===== TCSlib/Complexity/TuringMachine/Build/NDHost.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.InputRewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic phase host, the choice writer, and the guess-then-run assembly

The nondeterministic part of the construction layer that the guess-first route needs (user
decision 1 of 2026-10-13; the C1 design note §3.1, §3.4). The universal NDTM and the
diagonalizer of `TCSlib.Complexity.Diagonalization.NTimeHierarchy` guess their whole choice word
up front, with one small nondeterministic leaf, and then run deterministically.

## Design

* **The ND phase host** `Turing.NDTM.phaseHostND` is `Turing.phaseHostTM` over nondeterministic
  phases, deterministic phases entering as `Turing.MultiTapeTM.toNDTM`. Each of its two slices
  is the deterministic phase host of the phases' slices (`Turing.NDTM.phaseHostND_fixChoice`,
  through the phase host's field equations), and a phase runs inside it along every word
  (`Turing.NDTM.phaseHostND_run`, from the transfer `Turing.NDTM.runWith_mapState_of_agreeOn`).
* **Never put a choice inside a round body.** A host whose correctness is a per-step lockstep
  (the phase host, Z1, the R1 embedding, renaming) lifts to NDTMs slice by slice. A host that
  composes multi-step rounds (`Turing.counterLoopTMVia`, the step clock) does not: a branch
  mixes slices across rounds. So no nondeterministic counter loop is built (statement note
  SC-3 of design §12.7 is closed by this route); choices are guessed by the writer below, before
  any round host runs.
* **The choice writer** `Turing.ndWriterTM` is the guessed flavor of a choice source (H5's
  device family): on one tape, while its controller does not stop it (and, in the bounded
  flavor, while the cell under the head is nonblank), it writes its choice bit and moves right.
  Under a general controller, control is choice-dependent: the successor `δ q b`, and with it
  every later stop, depends on the bit. In the trivial-controller, never-stop instance of the
  bounded flavor (`Turing.ndWriterTM_run_block`), the two choices differ only in the written
  symbol, so its timing is branch-independent. The bounded flavor serves the universal NDTM and
  the diagonalizer; the controller flavor, the linear normal form's display guess.
* **The guess-then-run assembly** `Turing.guessCtlRunTM` composes the phase host over a
  deterministic setup, a choice writer (its controller and flavor as parameters), a rewind by the
  catalog's `Turing.skipTM` and `Turing.skipBackTM`, a deterministic run ending in a live verdict,
  and a verdict leaf (ruling 2 of the C1 host-contracts gate). `Turing.guessRunTM` is its instance
  with the bounded writer and the trivial controller. Its contract identifies the writer's word,
  transfers the deterministic phases, and gives all-branch halting and exact-budget acceptance; with
  the interpreter core run silently (`Turing.embedSilentTM`), the core's precondition and live
  verdicts (`Turing.guessRunTM_silent_spec`).
* **The controller-stopped instance** of `Turing.guessCtlRunTM`, the unbounded writer over a tape
  blank from its head on: the guess ends when the
  controller stops, after a number of bits that depends on the bits. Its contract gives the
  handoff, the whole branch through the run's verdict, and acceptance in both directions; a
  halted branch has passed a stop of the controller (`Turing.guessCtlRunTM_stop_of_halted`).
  There is no all-branch halting: a stream that never stops the controller never ends the guess.

## Main definitions

* `Turing.NDTM.phaseHostND` — the nondeterministic phase host.
* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
* `Turing.GuessRunPhase`, `Turing.GuessRunPhase.CtlState`, `Turing.guessCtlRunPhases`,
  `Turing.guessCtlRunRed`, `Turing.guessCtlRunTM` — the guess-then-run host over a writer.
  [AB09, §2.1.2, proof of Theorem 2.6]
* `Turing.GuessRunPhase.State`, `Turing.guessRunPhases`, `Turing.guessRunRed`,
  `Turing.guessRunTM` — its bounded, trivial-controller instance.
* `Turing.guessRunCfg`, `Turing.streamStartCfg` — the run's entry configuration after a guess,
  and the interpreter core's start configuration.

## Main results

* `Turing.NDTM.phaseHostND_fixChoice`, `Turing.NDTM.phaseHostND_run` (proved).
* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (proved).
* `Turing.ndWriterTM_run_controller` — the controller-stopped flavor's contract (proved).
* `Turing.guessRunTM_runWith_handoff`, `Turing.guessRunTM_runWith_handoff_state`,
  `Turing.guessRunTM_runWith_live`, `Turing.guessRunTM_runWith`,
  `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff` — the guess-then-run assembly
  (proved); `Turing.guessRunTM_runWith_setup_halt` — a halting setup (proved).
* `Turing.guessRunCfg_clean`, `Turing.guessRunTM_silent_spec` (proved) — the interpreter
  core's interface: precondition, emission capture, live verdicts.
* `Turing.guessCtlRunTM_runWith_handoff`, `Turing.guessCtlRunTM_runWith`,
  `Turing.guessCtlRunTM_stop_of_halted`, `Turing.guessCtlRunTM_accepts_of`,
  `Turing.guessCtlRunTM_stream_of_accepts` — the controller-stopped instance (proved).
* The fields of the two configurations `Turing.guessRunCfg_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output` and `Turing.streamStartCfg_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output` (the ND inventory API, C1's pre-ship inventory, 2026-10-17).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step; the proof of Theorem 2.6: guess a string, then verify it
  deterministically; Exercise 2.6.)
-/

namespace Turing.NDTM

variable {k : ℕ} {Γ : Type}

/-- **The nondeterministic phase host**: `Turing.phaseHostTM` over nondeterministic phases.
Its states are the tagged phase states. A state that `red` maps to `some q` takes one
stationary, silent dispatch step to `q` under either choice; every other state of phase `i`
follows phase `i`'s two transition functions, with successors tagged by `i`. Deterministic
phases enter as `Turing.MultiTapeTM.toNDTM`. (A host of the construction layer; [AB09,
§2.1.2].) -/
def phaseHostND {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :
    NDTM k Γ (Σ i, Ph i) where
  q₀ := q0
  tr := fun b q inp w =>
    match red q.1 q.2 with
    | some q' => ⟨0, fun _ => (none, 0), none, some q'⟩
    | none => ((M q.1).tr b q.2 inp w).mapState (Sigma.mk q.1)

/-- **Each slice of the ND phase host is a deterministic phase host**: fixing the choice `b`
in `Turing.NDTM.phaseHostND` gives `Turing.phaseHostTM` over the phases' slices at `b`.

**Proof sketch.** Compare the two fields. The start states agree (`Turing.NDTM.fixChoice_q₀`,
`Turing.phaseHostTM_q₀`). For the tables, split on the redirect: at a redirected state both
dispatch to its target (`Turing.phaseHostTM_tr_of_red_some`); elsewhere both take the phase's
slice action with the successor tagged (`Turing.phaseHostTM_tr_of_red_none`,
`Turing.NDTM.fixChoice_tr`). A machine is determined by its two fields. -/
theorem phaseHostND_fixChoice {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (b : Bool) :
    (phaseHostND M q0 red).fixChoice b = phaseHostTM (fun i => (M i).fixChoice b) q0 red := by
  have hq : ((phaseHostND M q0 red).fixChoice b).q₀ =
      (phaseHostTM (fun i => (M i).fixChoice b) q0 red).q₀ := by
    rw [NDTM.fixChoice_q₀, phaseHostTM_q₀]
    rfl
  have ht : ((phaseHostND M q0 red).fixChoice b).tr =
      (phaseHostTM (fun i => (M i).fixChoice b) q0 red).tr := by
    funext q inp w
    obtain ⟨i, s⟩ := q
    rw [NDTM.fixChoice_tr]
    cases h : red i s with
    | none =>
      rw [phaseHostTM_tr_of_red_none _ _ _ i s h, NDTM.fixChoice_tr]
      simp only [phaseHostND, h]
    | some q' =>
      rw [phaseHostTM_tr_of_red_some _ _ _ i s h]
      simp only [phaseHostND, h]
  calc (phaseHostND M q0 red).fixChoice b
      = ⟨((phaseHostND M q0 red).fixChoice b).q₀, ((phaseHostND M q0 red).fixChoice b).tr⟩ := rfl
    _ = ⟨(phaseHostTM (fun i => (M i).fixChoice b) q0 red).q₀,
          (phaseHostTM (fun i => (M i).fixChoice b) q0 red).tr⟩ := by rw [hq, ht]
    _ = phaseHostTM (fun i => (M i).fixChoice b) q0 red := rfl

/-- **The ND phase lemma** (the nondeterministic counterpart of `Turing.phaseHostTM_run`). Let
phase `i` run under the word `w` from `c` to `c'`, ending at a state `s'` that `red` redirects
to `q'`, and reaching no redirected state before. Then inside the host, every prefix of `w`
drives the tagged phase run from the tagged `c`, and one further choice, either bit, performs
the dispatch to `q'` with every other field of `c'` unchanged.

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn` along `Sigma.mk i`, with the good
states those that `red` does not redirect; the final dispatch is one explicit step. -/
theorem phaseHostND_run {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c c' : Cfg k Γ (Ph i) x) (w : List Bool) (h : (M i).runWith w c = c') (s' : Ph i)
    (hs' : c'.state = some s') (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < w.length, ∀ s, ((M i).runWith (w.take u) c).state = some s →
      red i s = none) (b : Bool) :
    (∀ u ≤ w.length, (phaseHostND M q0 red).runWith (w.take u) (c.mapState (Sigma.mk i)) =
        ((M i).runWith (w.take u) c).mapState (Sigma.mk i)) ∧
      (phaseHostND M q0 red).runWith (w ++ [b]) (c.mapState (Sigma.mk i)) =
        c'.mapState (fun _ => q') := by
  let emb : Ph i ↪ (Σ i, Ph i) := ⟨Sigma.mk i, sigma_mk_injective⟩
  have hagree : ∀ (b : Bool) (s : Ph i), red i s = none → ∀ inp work,
      (phaseHostND M q0 red).tr b (emb s) inp work =
        ((M i).tr b s inp work).mapState emb := by
    intro b s hs inp work
    simp only [phaseHostND, emb, Function.Embedding.coeFn_mk, hs]
  have hpre : ∀ u ≤ w.length,
      (phaseHostND M q0 red).runWith (w.take u) (c.mapState (Sigma.mk i)) =
        ((M i).runWith (w.take u) c).mapState (Sigma.mk i) := by
    intro u hu
    exact runWith_mapState_of_agreeOn (M i) (phaseHostND M q0 red) emb
      (fun s => red i s = none) hagree c (w.take u) (by
        intro v hv s hs
        rw [List.length_take] at hv
        rw [List.take_take, Nat.min_eq_left (by omega)] at hs
        exact hguard v (by omega) s hs)
  refine ⟨hpre, ?_⟩
  rw [runWith_append]
  have hw := hpre w.length le_rfl
  rw [List.take_length, h] at hw
  rw [hw, runWith_cons, runWith_nil]
  have hst : (c'.mapState (Sigma.mk i)).state = some ⟨i, s'⟩ := by
    simp [Cfg.mapState, hs']
  unfold stepWith
  rw [hst]
  simp only [phaseHostND, hred]
  apply Cfg.ext <;> simp [Cfg.mapState, hs']

end Turing.NDTM

namespace Turing

/-- Control of the choice writer: running with a controller state `q`, or `done` (the live exit
anchor). -/
inductive NDWriterState (Q : Type) where
  /-- writing, with controller state `q` -/
  | run (q : Q)
  /-- the live exit anchor -/
  | done
  deriving DecidableEq

/-- **The choice writer** (H5's choice device, guessed flavor). An NDTM with `k` work tapes and
writer tape `j`. In state `run q`: if the controller asks to stop (`stop q`), or, in the
`bounded` flavor, the cell under the head of tape `j` is blank, it moves to `done` without
moving or writing; otherwise it writes its choice bit `b` on tape `j`, moves that head right,
and updates the controller to `δ q b`. `done` is a silent, stationary, live self-loop. Under a
general controller the choice also selects the successor `δ q b`, so control is
choice-dependent; with the trivial controller that never stops, the two choices differ only in
the written symbol. The controller type `Q` need not be finite. No input move, no output.
[AB09, §2.1.2: the choice at each step] -/
def ndWriterTM (k : ℕ) (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) : NDTM k Bool (NDWriterState Q) where
  q₀ := .run q₀
  tr := fun b q _ w =>
    match q with
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .run q =>
      if stop q || (bounded && (w j).isNone) then ⟨0, fun _ => (none, 0), none, some .done⟩
      else ⟨0, fun i => if i = j then (some (some b), 1) else (none, 0), none,
        some (.run (δ q b))⟩

/-- The configuration after writing the word `s`, in the writer state `q`, before testing the
next cell. -/
private def wr_cfg {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (s : List Bool) :
    Cfg k Bool (NDWriterState Q) x :=
  { c with
    state := some q
    workTapes := Function.update c.workTapes j (fun p =>
      if c.workTapePos j ≤ p ∧ p < c.workTapePos j + s.length then
        FinTM.bufferTape s (p - c.workTapePos j)
      else c.workTapes j p)
    workTapePos := Function.update c.workTapePos j (c.workTapePos j + s.length) }

/-- Extending a written interval by one bit is a single update at its right boundary.

**Proof sketch.** At the boundary use the buffer's append equation. Off the boundary the
update is inert, and the two integer interval tests agree. -/
private theorem wr_tape_append (t : ℤ → Option Bool) (a : ℤ) (s : List Bool) (b : Bool) :
    Function.update (fun p => if a ≤ p ∧ p < a + s.length then
      FinTM.bufferTape s (p - a) else t p) (a + s.length) (some b) =
    fun p => if a ≤ p ∧ p < a + (s ++ [b]).length then
      FinTM.bufferTape (s ++ [b]) (p - a) else t p := by
  funext p
  rw [FinTM.bufferTape_append]
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  by_cases hp : p = a + s.length
  · subst p
    rw [Function.update_self, if_pos (by omega)]
    rw [show a + (s.length : ℤ) - a = s.length by omega, Function.update_self]
  · rw [Function.update_of_ne hp]
    have hoff : p - a ≠ (s.length : ℤ) := by omega
    rw [Function.update_of_ne hoff]
    by_cases h : a ≤ p ∧ p < a + s.length
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- The empty written prefix in the start state gives the original configuration. -/
private theorem wr_cfg_nil {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (hc : c.state = some q) :
    wr_cfg j c q [] = c := by
  apply Cfg.ext
  · exact hc.symm
  · rfl
  · funext i p
    have hempty : ¬ (c.workTapePos j ≤ p ∧ p < c.workTapePos j) := by omega
    by_cases hi : i = j <;> simp [wr_cfg, hi, hempty]
  · funext i
    by_cases hi : i = j <;> simp [wr_cfg, hi]
  · rfl

/-- The next cell of the block still has its original symbol. -/
private theorem wr_cfg_scan {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (s : List Bool) :
    (wr_cfg j c q s).workTapeSymbols j = c.workTapes j (c.workTapePos j + s.length) := by
  rw [Cfg.workTapeSymbols_eq]
  simp only [wr_cfg, Function.update_self, lt_self_iff_false, and_false, if_false]

/-- One writer step from the written-prefix configuration in the controller state `q`: if the
controller stops, or (bounded flavor) the next cell is blank, the stationary exit `done`;
otherwise the written prefix extended by the choice bit, the controller updated by it, and the
writer's head one cell further right.

**Proof sketch.** Read the live step through `Turing.NDTM.stepWith_of_some` and the writer's
test at the next cell (`wr_cfg_scan`), then the applied action through its field equations. On
both branches the input head and the output are unchanged. On the exit the action is stationary
and writes nothing; otherwise the buffer append equation (`wr_tape_append`) gives the written
tape and the head moves by one. -/
private theorem wr_cfg_stepWith {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : Q) (s : List Bool) (b : Bool) :
    (ndWriterTM k j q₀ δ stop bounded).stepWith b (wr_cfg j c (.run q) s) =
      if (stop q || (bounded && (c.workTapes j (c.workTapePos j + s.length)).isNone)) = true then
        wr_cfg j c .done s
      else wr_cfg j c (.run (δ q b)) (s ++ [b]) := by
  rw [NDTM.stepWith_of_some (q := .run q) (by rfl)]
  simp only [ndWriterTM, wr_cfg_scan]
  split_ifs with hcell <;> apply Cfg.ext <;>
    first
    | (rw [Action.apply_state]; try rfl)
    | (rw [Action.apply_inputPos]; exact moveInputPos_zero _)
    | (rw [Action.apply_output]; simp only [Option.toList_none, List.append_nil, wr_cfg])
    | skip
  · funext i
    rw [Action.apply_workTapes]
    simp only [Option.getD_none, Cfg.workTapeSymbols_eq, Function.update_eq_self]
    rfl
  · funext i
    rw [Action.apply_workTapePos]
    simp only [SignType.coe_zero, add_zero]
    rfl
  · funext i
    rw [Action.apply_workTapes]
    by_cases hi : i = j
    · subst i
      simp only [wr_cfg, Function.update_self, ↓reduceIte, Option.getD_some]
      exact wr_tape_append (c.workTapes j) (c.workTapePos j) s b
    · simp only [wr_cfg, if_neg hi, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self, Function.update_of_ne hi]
  · funext i
    rw [Action.apply_workTapePos]
    by_cases hi : i = j
    · subst i
      simp only [wr_cfg, Function.update_self, ↓reduceIte, SignType.coe_one,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    · simp only [wr_cfg, Function.update_of_ne hi, if_neg hi, SignType.coe_zero, add_zero]

/-- While the writer does not stop (its controller does not stop it, and, bounded, the next cell
is nonblank), every prefix of the word drives it to the written-prefix configuration, in the
controller state that the prefix reaches.

**Proof sketch.** Induct on the prefix length. The writer does not stop at the state the prefix
so far reaches, so the one-step lemma appends the next choice bit and updates the controller by
it; `List.foldl` over the extended prefix is that update. -/
private theorem wr_prefix_gen {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (u : ℕ) (hw : u ≤ w.length)
    (hlive : ∀ i < u, (stop ((w.take i).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + i)).isNone)) = false) :
    (ndWriterTM k j q₀ δ stop bounded).runWith (w.take u) c =
      wr_cfg j c (.run ((w.take u).foldl δ q)) (w.take u) := by
  revert hw hlive
  induction u with
  | zero =>
    intro _ _
    rw [List.take_zero, NDTM.runWith_nil, List.foldl_nil, wr_cfg_nil j c _ hc]
  | succ u ih =>
    intro hw hlive
    have hlt : u < w.length := by omega
    have hlen : (w.take u).length = u := List.length_take_of_le (by omega)
    rw [List.take_succ_eq_append_getElem hlt, NDTM.runWith_append,
      ih (by omega) (fun i hi => hlive i (by omega)), NDTM.runWith_cons, NDTM.runWith_nil,
      wr_cfg_stepWith, hlen, if_neg (by simp [hlive u (by omega)]), List.foldl_append,
      List.foldl_cons, List.foldl_nil]

/-- Every prefix that fits in the nonblank block drives the bounded writer with the trivial
controller to the written-prefix configuration (`wr_prefix_gen`). -/
private theorem wr_prefix {k : ℕ} (j : Fin k) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Unit) x) (hc : c.state = some (.run ()))
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → c.workTapes j (c.workTapePos j + p) ≠ none)
    (w : List Bool) (u : ℕ) (hu : u ≤ m) (hw : u ≤ w.length) :
    (ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith (w.take u) c =
      wr_cfg j c (.run ()) (w.take u) :=
  wr_prefix_gen j () (fun _ _ => ()) (fun _ => false) true c () hc w u hw (fun i hi => by
    cases h : c.workTapes j (c.workTapePos j + i) with
    | none => exact absurd h (hblock i (by omega))
    | some _ => rfl)

/-- **The writer's first stop.** If along the word `w` the writer first stops after `m` written
bits (its controller, or, bounded, the next cell, stops it at `m` and at no `i < m`), with
`m < |w|`, then the prefix `w.take (m + 1)` writes `w.take m` from the head and reaches `done`,
every other field unchanged, and no prefix of length at most `m` reaches `done`.

**Proof sketch.** `wr_prefix_gen` up to `m`, then one step of `wr_cfg_stepWith`, whose test holds
at `m`; the prefixes up to `m` are at `run`. -/
private theorem wr_run_first_stop {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (m : ℕ) (hm : m < w.length)
    (hlive : ∀ i < m, (stop ((w.take i).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + i)).isNone)) = false)
    (hstop : (stop ((w.take m).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + m)).isNone)) = true) :
    (ndWriterTM k j q₀ δ stop bounded).runWith (w.take (m + 1)) c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ i ≤ m, ((ndWriterTM k j q₀ δ stop bounded).runWith (w.take i) c).state ≠ some .done := by
  have hlen : (w.take m).length = m := List.length_take_of_le hm.le
  constructor
  · rw [List.take_succ_eq_append_getElem hm, NDTM.runWith_append,
      wr_prefix_gen j q₀ δ stop bounded c q hc w m hm.le hlive, NDTM.runWith_cons,
      NDTM.runWith_nil, wr_cfg_stepWith, hlen, if_pos hstop]
    simp only [wr_cfg, hlen]
  · intro i hi
    rw [wr_prefix_gen j q₀ δ stop bounded c q hc w i (by omega)
      (fun i' hi' => hlive i' (by omega))]
    simp only [wr_cfg, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- **The bounded choice writer's contract.** Start the bounded writer with the trivial
controller at `run ()` over a nonblank block of `m` cells of tape `j` from its head, followed by
a blank. Then every choice word `w` of length `m + 1` overwrites the block with its first `m`
bits, leaves the head of tape `j` just after the block, and reaches `done`; every other field is
unchanged. No shorter word reaches `done`. So the guessed stream is exactly `w.take m`, on every
branch at the same time `m + 1`, and every stream of length `m` is guessed (by `s ++ [b]`).
[AB09, §2.1.2]

**Proof sketch.** Induct on the first `m` steps: at step `u < m` the head of tape `j` is at cell
`u` of the block, which still holds its original nonblank symbol, so the writer writes `w[u]`
and moves right, keeping state `run ()`. At step `m` the head reads the blank after the block,
and the writer moves to `done` without moving. Before step `m + 1` the state is `run ()`. -/
theorem ndWriterTM_run_block {k : ℕ} (j : Fin k) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Unit) x) (hc : c.state = some (.run ()))
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → c.workTapes j (c.workTapePos j + p) ≠ none)
    (hend : c.workTapes j (c.workTapePos j + m) = none)
    (w : List Bool) (hw : w.length = m + 1) :
    (ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith w c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ w' : List Bool, w'.length < m + 1 →
      ((ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith w' c).state ≠
        some .done := by
  have hfirst := wr_run_first_stop j () (fun _ _ => ()) (fun _ => false) true c () hc w m (by omega)
    (fun i hi => by
      cases h : c.workTapes j (c.workTapePos j + i) with
      | none => exact absurd h (hblock i hi)
      | some _ => rfl)
    (by simp [hend])
  rw [List.take_of_length_le (show w.length ≤ m + 1 by omega)] at hfirst
  refine ⟨hfirst.1, ?_⟩
  intro w' hw'
  have hrun := wr_prefix j c hc m hblock w' w'.length (by omega) le_rfl
  rw [List.take_length] at hrun
  rw [hrun]
  simp only [wr_cfg, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- While the controller has not stopped, every prefix of the word drives the controller-stopped
writer to the written-prefix configuration, in the controller state that the prefix reaches
(`wr_prefix_gen`). -/
private theorem wr_prefix_controller {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q)
    (δ : Q → Bool → Q) (stop : Q → Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (u : ℕ) (hw : u ≤ w.length)
    (hlive : ∀ i < u, stop ((w.take i).foldl δ q) = false) :
    (ndWriterTM k j q₀ δ stop false).runWith (w.take u) c =
      wr_cfg j c (.run ((w.take u).foldl δ q)) (w.take u) :=
  wr_prefix_gen j q₀ δ stop false c q hc w u hw (fun i hi => by simp [hlive i hi])

/-- **The controller-stopped choice writer's contract.** Start the writer, unbounded, at `run q`
on any tape `j`. Let a choice word `w` first stop the controller after `m` written bits: the
controller state after writing `w.take i` is `(w.take i).foldl δ q`, which does not stop for
`i < m` and stops at `m`, with `m < |w|`. Then the prefix `w.take (m + 1)` overwrites the `m`
cells of tape `j` from its head with `w.take m`, leaves the head just after them and reaches
`done`, every other field unchanged; and no prefix of length at most `m` reaches `done`. The
writer ignores the cells it overwrites, so the tape may hold anything there. [AB09, §2.1.2]

**Proof sketch.** Induct on `i ≤ m` (`wr_prefix_controller`): after `w.take i` the configuration
is the block update with `w.take i`, the head at `c.workTapePos j + i`, state
`run ((w.take i).foldl δ q)`. At `i < m` the controller does not stop, so the writer writes
`w[i]` and moves right; at `m` it stops and moves to `done` without moving. -/
theorem ndWriterTM_run_controller {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x) (q : Q)
    (hc : c.state = some (.run q)) (w : List Bool) (m : ℕ) (hm : m < w.length)
    (hlive : ∀ i < m, stop ((w.take i).foldl δ q) = false)
    (hstop : stop ((w.take m).foldl δ q) = true) :
    (ndWriterTM k j q₀ δ stop false).runWith (w.take (m + 1)) c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ i ≤ m, ((ndWriterTM k j q₀ δ stop false).runWith (w.take i) c).state ≠ some .done :=
  wr_run_first_stop j q₀ δ stop false c q hc w m hm (fun i hi => by simp [hlive i hi])
    (by simp [hstop])

end Turing

/-! ## The guess-then-run assembly

The universal NDTM and the diagonalizer of `TCSlib.Complexity.Diagonalization.NTimeHierarchy`
share one shape (user decision 1 of 2026-10-13; ruling 2 of the C1 host-contracts gate). A
deterministic setup leaves a nonblank block of `m` cells on a stream tape; the bounded choice
writer overwrites it with `m` choice bits; the stream head is rewound; a deterministic run ends in
one of two live verdict states; and a verdict leaf emits the verdict bit and halts. This is a
composition of the present host `Turing.NDTM.phaseHostND` over six phases, with the catalog's
`Turing.skipTM` and `Turing.skipBackTM` as the rewind: no new host. Deterministic phases enter as
`Turing.MultiTapeTM.toNDTM`, so the writer is the only choice-dependent phase, and a branch is
determined by the `m` bits it writes. The host is defined once over the writer
(`Turing.guessCtlRunTM`, the writer's controller and flavor as parameters), and its handoff and
the rest of a branch are proved once for any writer whose run on the stream is known;
`Turing.guessRunTM` is the instance with the bounded writer and the trivial controller, and the
controller-stopped instance is the next section's.

* `Turing.guessRunTM_runWith_handoff`: every word of length `TP + 2m + 9` drives the host to the
  run's entry, with the block overwritten by the word's `m` bits after its first `TP + 1` (the
  writer's word, identified) and every head where the setup left it.
* `Turing.guessRunTM_runWith_live`: no shorter word halts the host;
  `Turing.guessRunTM_runWith_handoff_state`: at the handoff itself the host is live, at the run's
  entry.
* `Turing.guessRunTM_runWith_setup_halt`: a setup that halts before its exit halts the host,
  unguessed.
* `Turing.guessRunTM_runWith`: the whole branch, through the run's first verdict, halted by time
  `TP + 2m + TQ + 11` with the verdict bit appended to the output; later choices are absorbed.
* `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff`: all-branch halting, and
  exact-budget acceptance in both directions.
* `Turing.guessRunCfg_clean`, `Turing.guessRunTM_silent_spec`: the interface of the interpreter
  core `Turing.exists_ndInterpreterCore`. From a clean setup the run's entry is the core's start
  configuration, silently embedded (`Turing.embedSilentTM` captures the core's emissions), and
  the core's live verdicts become the host's.

Every theorem here is proved. The writer's contract `Turing.ndWriterTM_run_block` is proved by
one induction over the written prefix (C1-W, 2026-10-17); the seven theorems that pass the
writer use it, and `Turing.guessRunTM_runWith_setup_halt` and `Turing.guessRunCfg_clean` do not.
-/

namespace Turing

/-- The choice writer's control states are finite when the controller's are: `NDWriterState Q`
is equivalent to `Option Q` (`run q ↦ some q`, `done ↦ none`). Needed to bundle the
guess-then-run host as a `Turing.FinNDTM`. -/
instance NDWriterState.instFintype {Q : Type} [Fintype Q] : Fintype (NDWriterState Q) :=
  Fintype.ofEquiv (Option Q)
    { toFun := fun o => match o with
        | some q => .run q
        | none => .done
      invFun := fun s => match s with
        | .run q => some q
        | .done => none
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-- **The phases of the guess-then-run host**, in run order: the deterministic setup, the bounded
choice writer, one step right past the guessed block, the rewind of the writer's tape to the
block's start, the deterministic run up to a live verdict, and the verdict emission. (Technical
glue: the phase index of `Turing.guessRunTM`.) -/
inductive GuessRunPhase where
  /-- the deterministic setup -/
  | pre
  /-- the bounded choice writer -/
  | guess
  /-- one step right, past the blank after the guessed block -/
  | skip
  /-- the rewind of the writer's tape to the block's start -/
  | back
  /-- the deterministic run, up to a live verdict -/
  | run
  /-- the verdict emission -/
  | out
  deriving DecidableEq, Fintype

/-- **The control states of each phase of the guess-then-run host over a writer with controller
states `Q`**: the setup's `SP`; the writer's `Turing.NDWriterState Q`; the seek phases
`Turing.SeekPhase` for the step right and for the rewind; the run's `SQ`; and the verdict bit for
the emission. -/
def GuessRunPhase.CtlState (SP SQ Q : Type) : GuessRunPhase → Type
  | .pre => SP
  | .guess => NDWriterState Q
  | .skip => SeekPhase
  | .back => SeekPhase
  | .run => SQ
  | .out => Bool

/-- Each phase's state type is finite when the setup's, the run's and the controller's are. -/
instance GuessRunPhase.instFintypeCtlState {SP SQ Q : Type} [Fintype SP] [Fintype SQ]
    [Fintype Q] : (i : GuessRunPhase) → Fintype (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => inferInstanceAs (Fintype SP)
  | .guess => inferInstanceAs (Fintype (NDWriterState Q))
  | .skip => inferInstanceAs (Fintype SeekPhase)
  | .back => inferInstanceAs (Fintype SeekPhase)
  | .run => inferInstanceAs (Fintype SQ)
  | .out => inferInstanceAs (Fintype Bool)

/-- Each phase's state type has decidable equality when the setup's, the run's and the
controller's have. -/
instance GuessRunPhase.instDecidableEqCtlState {SP SQ Q : Type} [DecidableEq SP]
    [DecidableEq SQ] [DecidableEq Q] :
    (i : GuessRunPhase) → DecidableEq (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => inferInstanceAs (DecidableEq SP)
  | .guess => inferInstanceAs (DecidableEq (NDWriterState Q))
  | .skip => inferInstanceAs (DecidableEq SeekPhase)
  | .back => inferInstanceAs (DecidableEq SeekPhase)
  | .run => inferInstanceAs (DecidableEq SQ)
  | .out => inferInstanceAs (DecidableEq Bool)

/-! The state family's fibers, one per phase: the reading of `Turing.GuessRunPhase.CtlState`. -/

/-- The setup phase's states are the setup's. -/
theorem GuessRunPhase.ctlState_pre (SP SQ Q : Type) : GuessRunPhase.CtlState SP SQ Q .pre = SP :=
  rfl

/-- The guess phase's states are the writer's. -/
theorem GuessRunPhase.ctlState_guess (SP SQ Q : Type) :
    GuessRunPhase.CtlState SP SQ Q .guess = NDWriterState Q := rfl

/-- The step right's states are a seek's. -/
theorem GuessRunPhase.ctlState_skip (SP SQ Q : Type) :
    GuessRunPhase.CtlState SP SQ Q .skip = SeekPhase := rfl

/-- The rewind's states are a seek's. -/
theorem GuessRunPhase.ctlState_back (SP SQ Q : Type) :
    GuessRunPhase.CtlState SP SQ Q .back = SeekPhase := rfl

/-- The run phase's states are the run's. -/
theorem GuessRunPhase.ctlState_run (SP SQ Q : Type) : GuessRunPhase.CtlState SP SQ Q .run = SQ :=
  rfl

/-- The verdict leaf's states are the verdict bits. -/
theorem GuessRunPhase.ctlState_out (SP SQ Q : Type) :
    GuessRunPhase.CtlState SP SQ Q .out = Bool := rfl

/-- **The control states of each phase of the guess-then-run host**: those of
`Turing.GuessRunPhase.CtlState` with the trivial controller, the writer's
`Turing.NDWriterState Unit` in the guess phase. -/
def GuessRunPhase.State (SP SQ : Type) : GuessRunPhase → Type :=
  GuessRunPhase.CtlState SP SQ Unit

/-- Each phase's state type is finite when the setup's and the run's are. -/
instance GuessRunPhase.instFintypeState {SP SQ : Type} [Fintype SP] [Fintype SQ] :
    (i : GuessRunPhase) → Fintype (GuessRunPhase.State SP SQ i) :=
  GuessRunPhase.instFintypeCtlState (Q := Unit)

/-- Each phase's state type has decidable equality when the setup's and the run's have. -/
instance GuessRunPhase.instDecidableEqState {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ] :
    (i : GuessRunPhase) → DecidableEq (GuessRunPhase.State SP SQ i) :=
  GuessRunPhase.instDecidableEqCtlState (Q := Unit)

/-- **The phase machines of the guess-then-run host over a writer.** The setup `P` and the run
`V`, as `Turing.MultiTapeTM.toNDTM` (both choices apply their one transition function); the choice
writer `Turing.ndWriterTM` on tape `j` with the controller `q₀`, `δ`, `stop` and the flavor
`bounded`; `Turing.skipTM` and `Turing.skipBackTM` on tape `j`, as `toNDTM`; and the verdict leaf,
which in state `b` emits `b` and halts under either choice, moving no head and writing nothing.
The leaf is hand-built: the construction layer has no public emit-and-halt row for plain machines
(`Turing.OracleTM.answerAction` is the oracle machines' one), so its one transition is written
here, as in the hand-built deciders of the library. -/
def guessCtlRunPhases {k : ℕ} {SP SQ Q : Type} (P : MultiTapeTM k Bool SP) (j : Fin k)
    (q₀ : Q) (δ : Q → Bool → Q) (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) :
    (i : GuessRunPhase) → NDTM k Bool (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => P.toNDTM
  | .guess => ndWriterTM k j q₀ δ stop bounded
  | .skip => (skipTM k j).toNDTM
  | .back => (skipBackTM k j).toNDTM
  | .run => V.toNDTM
  | .out => ⟨false, fun _ b _ _ => ⟨0, fun _ => (none, 0), some b, none⟩⟩

section GuessCtlRunPhases

variable {k : ℕ} {SP SQ Q : Type} (P : MultiTapeTM k Bool SP) (j : Fin k) (q₀ : Q)
  (δ : Q → Bool → Q) (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ)

/-! The phases, one per phase: the reading of `Turing.guessCtlRunPhases`. -/

/-- The setup phase is the setup, run as an NDTM. -/
theorem guessCtlRunPhases_pre : guessCtlRunPhases P j q₀ δ stop bounded V .pre = P.toNDTM := rfl

/-- The guess phase is the choice writer on tape `j`. -/
theorem guessCtlRunPhases_guess :
    guessCtlRunPhases P j q₀ δ stop bounded V .guess = ndWriterTM k j q₀ δ stop bounded := rfl

/-- The step right is `Turing.skipTM` on tape `j`, run as an NDTM. -/
theorem guessCtlRunPhases_skip :
    guessCtlRunPhases P j q₀ δ stop bounded V .skip = (skipTM k j).toNDTM := rfl

/-- The rewind is `Turing.skipBackTM` on tape `j`, run as an NDTM. -/
theorem guessCtlRunPhases_back :
    guessCtlRunPhases P j q₀ δ stop bounded V .back = (skipBackTM k j).toNDTM := rfl

/-- The run phase is the deterministic run, run as an NDTM. -/
theorem guessCtlRunPhases_run : guessCtlRunPhases P j q₀ δ stop bounded V .run = V.toNDTM := rfl

/-- The verdict leaf: in state `b` it emits `b` and halts under either choice, moving no head and
writing nothing. -/
theorem guessCtlRunPhases_out :
    guessCtlRunPhases P j q₀ δ stop bounded V .out =
      ⟨false, fun _ b _ _ => ⟨0, fun _ => (none, 0), some b, none⟩⟩ := rfl

end GuessCtlRunPhases

/-- **The phase machines of the guess-then-run host.** The setup `P` and the run `Q`, as
`Turing.MultiTapeTM.toNDTM` (both choices apply their one transition function); the bounded choice
writer `Turing.ndWriterTM` on tape `j` with the trivial controller that never stops (the instance of
`Turing.ndWriterTM_run_block`): the instance of `Turing.guessCtlRunPhases`; `Turing.skipTM` and
`Turing.skipBackTM` on tape `j`, as `toNDTM`; and the verdict leaf, which in state `b` emits `b` and
halts under either choice, moving no head and writing nothing. The leaf is hand-built: the
construction layer has no public emit-and-halt row for plain machines
(`Turing.OracleTM.answerAction` is the oracle machines' one), so its one transition is written here,
as in the hand-built deciders of the library. -/
def guessRunPhases {k : ℕ} {SP SQ : Type} (P : MultiTapeTM k Bool SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) :
    (i : GuessRunPhase) → NDTM k Bool (GuessRunPhase.State SP SQ i) :=
  guessCtlRunPhases P j () (fun _ _ => ()) (fun _ => false) true Q

/-- **The redirects of the guess-then-run host over a writer.** The setup's exit `pexit`
dispatches to the writer's start `run q₀`; the writer's `done` to the start of the step right;
its `done` to the start of the rewind; the rewind's `done` to the run's entry `qentry`; the run's
verdict `acc` to the leaf's `true`, and `rej` to its `false` (`acc` is tested first). No other
state is redirected, so a halt of the run is the host's halt. Each redirect is one stationary,
silent step of the host under either choice (`Turing.NDTM.phaseHostND`). -/
def guessCtlRunRed {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ] (pexit : SP) (q₀ : Q)
    (qentry acc rej : SQ) :
    (i : GuessRunPhase) → GuessRunPhase.CtlState SP SQ Q i →
      Option (Σ i, GuessRunPhase.CtlState SP SQ Q i)
  | .pre, s => if s = pexit then some ⟨.guess, NDWriterState.run q₀⟩ else none
  | .guess, .done => some ⟨.skip, SeekPhase.run⟩
  | .guess, .run _ => none
  | .skip, .done => some ⟨.back, SeekPhase.run⟩
  | .skip, .run => none
  | .skip, .gap => none
  | .skip, .back => none
  | .back, .done => some ⟨.run, qentry⟩
  | .back, .run => none
  | .back, .gap => none
  | .back, .back => none
  | .run, s => if s = acc then some ⟨.out, true⟩ else if s = rej then some ⟨.out, false⟩
      else none
  | .out, _ => none

section GuessCtlRunRed

variable {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ] (pexit : SP) (q₀ : Q)
  (qentry acc rej : SQ)

/-! The redirects, covering every phase and state: the reading of `Turing.guessCtlRunRed`. -/

/-- The setup's exit dispatches to the writer's start; no other setup state is redirected. -/
theorem guessCtlRunRed_pre (s : SP) :
    guessCtlRunRed pexit q₀ qentry acc rej .pre s =
      if s = pexit then some ⟨.guess, NDWriterState.run q₀⟩ else none := rfl

/-- The writer's `done` dispatches to the step right. -/
theorem guessCtlRunRed_guess_done :
    guessCtlRunRed pexit q₀ qentry acc rej .guess .done = some ⟨.skip, SeekPhase.run⟩ := rfl

/-- A running writer state is not redirected. -/
theorem guessCtlRunRed_guess_run (q : Q) :
    guessCtlRunRed pexit q₀ qentry acc rej .guess (.run q) = none := rfl

/-- The step right's `done` dispatches to the rewind; no other seek state is redirected. -/
theorem guessCtlRunRed_skip (s : SeekPhase) :
    guessCtlRunRed pexit q₀ qentry acc rej .skip s =
      if s = .done then some ⟨.back, SeekPhase.run⟩ else none := by
  cases s <;> rfl

/-- The rewind's `done` dispatches to the run's entry; no other seek state is redirected. -/
theorem guessCtlRunRed_back (s : SeekPhase) :
    guessCtlRunRed pexit q₀ qentry acc rej .back s =
      if s = .done then some ⟨.run, qentry⟩ else none := by
  cases s <;> rfl

/-- The run's verdicts dispatch to the leaf, `acc` tested first; no other run state is
redirected. -/
theorem guessCtlRunRed_run (s : SQ) :
    guessCtlRunRed pexit q₀ qentry acc rej .run s =
      if s = acc then some ⟨.out, true⟩ else if s = rej then some ⟨.out, false⟩ else none := rfl

/-- The verdict leaf is not redirected. -/
theorem guessCtlRunRed_out (b : Bool) : guessCtlRunRed pexit q₀ qentry acc rej .out b = none := rfl

end GuessCtlRunRed

/-- **The redirects of the guess-then-run host.** The setup's exit `pexit` dispatches to the
writer's start `run ()`; the writer's `done` to the start of the step right; its `done` to the start
of the rewind; the rewind's `done` to the run's entry `qentry`; the run's verdict `acc` to the
leaf's `true`, and `rej` to its `false` (`acc` is tested first). No other state is redirected, so a
halt of the run is the host's halt. Each redirect is one stationary, silent step of the host under
either choice (`Turing.NDTM.phaseHostND`). The instance of `Turing.guessCtlRunRed` at `q₀ := ()`. -/
def guessRunRed {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ] (pexit : SP)
    (qentry acc rej : SQ) :
    (i : GuessRunPhase) → GuessRunPhase.State SP SQ i →
      Option (Σ i, GuessRunPhase.State SP SQ i) :=
  guessCtlRunRed pexit () qentry acc rej

/-- **The guess-then-run host over a writer.** The nondeterministic phase host
`Turing.NDTM.phaseHostND` over `Turing.guessCtlRunPhases P j q₀ δ stop bounded V` with the
redirects `Turing.guessCtlRunRed pexit q₀ qentry acc rej`, started at the setup's initial state.
The setup `P` runs to its exit `pexit`; the writer guesses bits on tape `j` from that tape's head
until it stops (its controller stops it, or, bounded, it meets a blank); the step right
`Turing.skipTM` and the rewind `Turing.skipBackTM` follow, which, when the stream has a blank on
each side (the run lemmas' hypotheses), take one step and return the head of tape `j` to the
stream's start; the run `V` starts at
`qentry` and runs to a live verdict, `acc` or `rej`; the verdict leaf emits `true` or `false` and
halts. Every phase but the writer is deterministic, so a branch is determined by the writer's
bits. The bounded, trivial-controller instance is `Turing.guessRunTM`. [AB09, §2.1.2: an NDTM
writes down a guessed string, then runs a deterministic verifier] -/
def guessCtlRunTM {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) :
    NDTM k Bool (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
  NDTM.phaseHostND (guessCtlRunPhases P j q₀ δ stop bounded V) ⟨.pre, P.q₀⟩
    (guessCtlRunRed pexit q₀ qentry acc rej)

/-- **The guess-then-run host.** The nondeterministic phase host `Turing.NDTM.phaseHostND` over
`Turing.guessRunPhases P j Q` with the redirects `Turing.guessRunRed pexit qentry acc rej`,
started at the setup's initial state. The setup `P` runs to its exit `pexit`; the bounded choice
writer guesses the block on tape `j` from that tape's head; one step right and the rewind
`Turing.skipBackTM` return the head of tape `j` to the block's start; the run `Q` starts at
`qentry` and runs to a live verdict, `acc` or `rej`; the verdict leaf emits `true` or `false`
and halts. If `Q` halts on its own, so does the host. Every phase but the writer is
deterministic, so a branch is determined by the writer's bits. A composition of the present host
with catalog rows (ruling 2 of the C1 host-contracts gate), not a new host. [AB09, §2.1.2, proof
of Theorem 2.6: an NDTM writes down a guessed string, then runs a deterministic verifier]

It is `Turing.guessCtlRunTM` with the bounded writer and the trivial controller. -/
def guessRunTM {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) : NDTM k Bool (Σ i, GuessRunPhase.State SP SQ i) :=
  guessCtlRunTM P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej

/-- **The run's entry configuration after a guess.** The configuration `c` in state `q`, with
the `|s|` cells of tape `j` from its head overwritten by `s`; the input head, every other tape,
every head (that of tape `j` included) and the output are `c`'s. -/
def guessRunCfg {k : ℕ} {S S' : Type} {z : List Bool} (c : Cfg k Bool S z) (j : Fin k)
    (s : List Bool) (q : S') : Cfg k Bool S' z :=
  ⟨some q, c.inputPos,
    Function.update c.workTapes j (fun p =>
      if c.workTapePos j ≤ p ∧ p < c.workTapePos j + s.length then
        FinTM.bufferTape s (p - c.workTapePos j)
      else c.workTapes j p),
    c.workTapePos, c.output⟩

/-! The handoff configuration's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: the state is `some q`, tape `j` holds `s` from its head with every
other cell `c`'s, and the input head, every other tape, every head and the output are `c`'s. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  guessRunCfg

/-- **The interpreter core's start configuration**: state `q`, input head on the first symbol
of `z`, the stream `s` on tape `j` from cell `0`, every other tape blank, every head at `0`,
empty output. It is the configuration `start` of `Turing.exists_ndInterpreterCore`, verbatim. -/
def streamStartCfg {K : ℕ} {S : Type} (z : List Bool) (j : Fin K) (q : S) (s : List Bool) :
    Cfg K Bool S z :=
  ⟨some q, 1, fun i => if i = j then FinTM.bufferTape s else fun _ => none, fun _ => 0, []⟩

/-! The start configuration's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: state `some q`, input head `1`, tape `j` the buffer of `s` and every
other tape blank, every head `0`, output `[]`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  streamStartCfg

/-- A word longer than `L` splits as its first `L` bits, one bit, and the rest. -/
private theorem guessRun_split (L : ℕ) (w : List Bool) (h : L < w.length) :
    ∃ (a : List Bool) (b : Bool) (r : List Bool), w = a ++ [b] ++ r ∧ a.length = L := by
  refine ⟨w.take L, w[L], w.drop (L + 1), ?_, by simp; omega⟩
  rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons h,
    List.take_append_drop]

/-- A writer's endpoint over a renamed configuration, through the renaming's field equations:
`done`, the `m` cells from the head overwritten by `s`, the head after them, every other field
the original's.

**Proof sketch.** Field by field: the state is the update's; the input head and the output are
the original's (`Turing.Cfg.mapState_inputPos`, `_output`); the tapes and heads are the
original's as functions (`Turing.Cfg.mapState_workTapes`, `_workTapePos`), inside the update. -/
private theorem gr_writer_end {k : ℕ} {S Q : Type} {z : List Bool} (cP : Cfg k Bool S z)
    (f : S → NDWriterState Q) (j : Fin k) (s : List Bool) (m : ℕ) :
    ({ cP.mapState f with
        state := some .done
        workTapes := Function.update (cP.mapState f).workTapes j (fun p =>
          if (cP.mapState f).workTapePos j ≤ p ∧ p < (cP.mapState f).workTapePos j + m then
            FinTM.bufferTape s (p - (cP.mapState f).workTapePos j)
          else (cP.mapState f).workTapes j p)
        workTapePos := Function.update (cP.mapState f).workTapePos j
          ((cP.mapState f).workTapePos j + m) } : Cfg k Bool (NDWriterState Q) z) =
      ⟨some .done, cP.inputPos, Function.update cP.workTapes j (fun p =>
          if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + m then
            FinTM.bufferTape s (p - cP.workTapePos j)
          else cP.workTapes j p),
        Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩ := by
  have hwt : (cP.mapState f).workTapes = cP.workTapes :=
    funext fun i => funext (Cfg.mapState_workTapes f cP i)
  have hwp : (cP.mapState f).workTapePos = cP.workTapePos :=
    funext (Cfg.mapState_workTapePos f cP)
  apply Cfg.ext
  · rfl
  · exact Cfg.mapState_inputPos f cP
  · show Function.update (cP.mapState f).workTapes j _ = _
    rw [hwt, hwp]
  · show Function.update (cP.mapState f).workTapePos j _ = _
    rw [hwp]
  · exact Cfg.mapState_output f cP

/-- The handoff of the guess-then-run host over any writer, given the writer's run on the
word's stream segment: from the setup's dispatch, `m + 1` bits reach `done` with the `m` bits
written from the head and the head after them, and no shorter prefix reaches `done`. Both
writers' contracts give this hypothesis.

**Proof sketch.** Split the word into the setup's `TP` bits and a dispatch bit, the writer's
`m + 1` bits and a dispatch bit, the step right's bit and a dispatch bit, and the rewind's `m + 3`
bits and a dispatch bit. Each phase is one application of `Turing.NDTM.phaseHostND_run`: the
setup's branch is its run (`Turing.MultiTapeTM.toNDTM_runWith`), with no redirect before `TP`;
the writer's branch is the hypothesis, whose second clause is the guard; the step right is
`Turing.skipTM_run_ofCfg` over the empty word (the cell after the stream is blank); the rewind is
`Turing.skipBackTM_run_ofCfg` over the stream (the cells before and after it are blank). Each
phase's endpoint, renamed (`Turing.Cfg.mapState_mapState`), is the next phase's start; the last is
the entry configuration, by the renaming's field equations. -/
private theorem gr_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9)
    (hW : (ndWriterTM k j q₀ δ stop bounded).runWith ((w.drop (TP + 1)).take (m + 1))
        (cP.mapState (fun _ => NDWriterState.run q₀)) =
      ⟨some .done, cP.inputPos, Function.update cP.workTapes j (fun p =>
          if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + m then
            FinTM.bufferTape ((w.drop (TP + 1)).take m) (p - cP.workTapePos j)
          else cP.workTapes j p),
        Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩)
    (hWg : ∀ u < m + 1, ((ndWriterTM k j q₀ δ stop bounded).runWith
        (((w.drop (TP + 1)).take (m + 1)).take u)
        (cP.mapState (fun _ => NDWriterState.run q₀))).state ≠ some .done) :
    (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  classical
  -- the five segments of the word
  obtain ⟨a₁, b₁, r₁, rfl, ha₁⟩ := guessRun_split TP w (by omega)
  have hr₁ : r₁.length = 2 * m + 8 := by simp [ha₁] at hw; omega
  obtain ⟨a₂, b₂, r₂, rfl, ha₂⟩ := guessRun_split (m + 1) r₁ (by omega)
  have hr₂ : r₂.length = m + 6 := by simp at hr₁; omega
  obtain ⟨a₃, b₃, r₃, rfl, ha₃⟩ := guessRun_split 1 r₂ (by omega)
  have hr₃ : r₃.length = m + 4 := by simp at hr₂; omega
  obtain ⟨a₄, b₄, r₄, rfl, ha₄⟩ := guessRun_split (m + 3) r₃ (by omega)
  have hr₄ : r₄ = [] := by simp at hr₃; exact List.eq_nil_of_length_eq_zero (by omega)
  subst hr₄
  have hpre : ∀ i ≤ m + 1, ((a₁ ++ [b₁] ++ (a₂ ++ [b₂] ++ (a₃ ++ [b₃] ++ (a₄ ++ [b₄] ++ []))))
      |>.drop (TP + 1) |>.take i) = a₂.take i := by
    intro i hi
    rw [List.drop_left' (by simp [ha₁])]
    rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega)]
  rw [hpre m (by omega)]
  have hW' := hW
  rw [hpre (m + 1) le_rfl, List.take_of_length_le (show a₂.length ≤ m + 1 by omega),
    hpre m (by omega)] at hW'
  have hWg' : ∀ u < m + 1, ((ndWriterTM k j q₀ δ stop bounded).runWith (a₂.take u)
      (cP.mapState (fun _ => NDWriterState.run q₀))).state ≠ some .done := fun u hu => by
    have := hWg u hu
    rwa [hpre (m + 1) le_rfl, List.take_of_length_le (show a₂.length ≤ m + 1 by omega)] at this
  set s := a₂.take m with hs_def
  have hslen : s.length = m := by simp [s, ha₂]
  set M := guessCtlRunPhases P j q₀ δ stop bounded V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN]
  set H := NDTM.phaseHostND M ⟨GuessRunPhase.pre, P.q₀⟩ red with hH
  have hinit : H.initCfg z = (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) := by
    rw [NDTM.initCfg_eq, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state, Option.map_some]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext i p
      rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext i
      rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  -- phase 1: the setup, then one dispatch
  have h1 : H.runWith (a₁ ++ [b₁]) ((P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre)) =
      cP.mapState (fun _ =>
        (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) := by
    refine (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.pre (P.initCfg z) cP a₁ ?_
      pexit hPexit _ ?_ ?_ b₁).2
    · show P.toNDTM.runWith a₁ (P.initCfg z) = cP
      rw [MultiTapeTM.toNDTM_runWith, ha₁, hP]
    · show (if pexit = pexit then _ else none) = _
      simp
    · intro u hu s' hs'
      change (P.toNDTM.runWith (a₁.take u) (P.initCfg z)).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
      have hne := hPfirst u (by omega)
      show (if s' = pexit then _ else none) = none
      rw [if_neg]
      rintro rfl
      exact hne hs'
  -- phase 2: the controller-stopped writer, then one dispatch
  let cW : Cfg k Bool (NDWriterState Q) z := cP.mapState (fun _ => NDWriterState.run q₀)
  have hcW : cP.mapState (fun _ =>
      (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cW.mapState (Sigma.mk GuessRunPhase.guess) := by
    rw [Cfg.mapState_mapState]; rfl
  -- the writer's endpoint, named, through the renaming's field equations
  let tW : ℤ → Option Bool := fun p =>
    if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + (m : ℤ) then
      FinTM.bufferTape s (p - cP.workTapePos j)
    else cP.workTapes j p
  let cW' : Cfg k Bool (NDWriterState Q) z :=
    ⟨some .done, cP.inputPos, Function.update cP.workTapes j tW,
      Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩
  have hX : (ndWriterTM k j q₀ δ stop bounded).runWith a₂ cW = cW' := hW'
  have h2 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.guess cW cW' a₂ hX
    NDWriterState.done rfl ⟨.skip, SeekPhase.run⟩ rfl (by
      intro u hu s' hs'
      cases s' with
      | done => exact absurd hs' (hWg' u (by omega))
      | run _ => rfl) b₂).2
  -- phase 3: one step right, onto the cell after the stream's right blank, then one dispatch
  let cS : Cfg k Bool SeekPhase z := cW'.mapState (fun _ => SeekPhase.run)
  have hcS : cW'.mapState (fun _ =>
      (⟨.skip, SeekPhase.run⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cS.mapState (Sigma.mk GuessRunPhase.skip) := by
    rw [Cfg.mapState_mapState]; rfl
  have hS := skipTM_run_ofCfg (x := z) j ([] : List Bool) cS
    (by simp only [cS, Cfg.mapState_state]; rfl) (by
    intro p h0 h1
    have hp : p = 0 := by simp at h1; omega
    subst hp
    simp [cS, cW', tW, Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hend])
  let cS' : Cfg k Bool SeekPhase z :=
    { cS with
      state := some .done
      workTapePos := Function.update cS.workTapePos j
        (cS.workTapePos j + ([] : List Bool).length + 1) }
  have h3 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.skip cS cS' a₃ (by
      show (skipTM k j).toNDTM.runWith a₃ cS = cS'
      rw [MultiTapeTM.toNDTM_runWith, ha₃]
      exact hS.1)
    SeekPhase.done rfl ⟨.back, SeekPhase.run⟩ rfl (by
      intro u hu s' hs'
      change ((skipTM k j).toNDTM.runWith (a₃.take u) cS).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith] at hs'
      have hne := hS.2.1 (a₃.take u).length (by simp; omega)
      cases s' with
      | done => exact absurd hs' hne
      | run => rfl
      | gap => rfl
      | back => rfl) b₃).2
  -- phase 4: the rewind over the guessed stream, then one dispatch into the deterministic run
  let cB : Cfg k Bool SeekPhase z := cS'.mapState (fun _ => SeekPhase.run)
  have hcB : cS'.mapState (fun _ =>
      (⟨.back, SeekPhase.run⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cB.mapState (Sigma.mk GuessRunPhase.back) := by
    rw [Cfg.mapState_mapState]; rfl
  have hBpos : cB.workTapePos j = cP.workTapePos j + m + 1 := by
    simp [cB, cS', cS, cW', Cfg.mapState_inputPos, Cfg.mapState_workTapePos,
      Cfg.mapState_output]
  have hB := skipBackTM_run_ofCfg (x := z) j s cB
    (by simp only [cB, Cfg.mapState_state]; rfl) (by
    intro p h0 h1
    rw [hBpos, hslen]
    have harg : cP.workTapePos j + m + 1 - m - 1 + p = cP.workTapePos j + p := by ring
    rw [harg]
    simp only [cB, cS', cS, cW', Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Function.update_self]
    simp only [tW]
    by_cases hin : 0 ≤ p ∧ p < (m : ℤ)
    · rw [if_pos (by omega)]
      congr 1
      ring
    · rw [if_neg (by omega)]
      rw [hslen] at h1
      rcases (show p = -1 ∨ p = (m : ℤ) by omega) with rfl | rfl
      · rw [FinTM.bufferTape_left, ← hleft]
        congr 1
      · rw [hend, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)])
  let cB' : Cfg k Bool SeekPhase z :=
    { cB with
      state := some .done
      workTapePos := Function.update cB.workTapePos j (cB.workTapePos j - s.length - 1) }
  have h4 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.back cB cB' a₄ (by
      show (skipBackTM k j).toNDTM.runWith a₄ cB = cB'
      rw [MultiTapeTM.toNDTM_runWith, ha₄, ← hslen]
      exact hB.1)
    SeekPhase.done rfl ⟨.run, qentry⟩ rfl (by
      intro u hu s' hs'
      change ((skipBackTM k j).toNDTM.runWith (a₄.take u) cB).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith] at hs'
      have hne := hB.2.1 (a₄.take u).length (by simp; omega)
      cases s' with
      | done => exact absurd hs' hne
      | run => rfl
      | gap => rfl
      | back => rfl) b₄).2
  -- the chain
  rw [hinit, NDTM.runWith_append, h1, hcW, NDTM.runWith_append, h2]
  erw [hcS]
  rw [NDTM.runWith_append, h3]
  erw [hcB]
  rw [List.append_nil, h4]
  apply Cfg.ext
  · simp only [cB', Cfg.mapState_state, guessRunCfg_state, Option.map_some]
  · simp only [cB', cB, cS', cS, cW', Cfg.mapState_inputPos, guessRunCfg_inputPos]
  · funext i p
    simp only [cB', cB, cS', cS, cW', tW, Cfg.mapState_workTapes, guessRunCfg_workTapes, hslen]
  · funext i
    simp only [cB', cB, cS', cS, cW', Cfg.mapState_workTapePos, guessRunCfg_workTapePos,
      Function.update_apply, hslen, List.length_nil]
    split_ifs with h
    · subst h
      omega
    · rfl
  · simp only [cB', cB, cS', cS, cW', Cfg.mapState_output, guessRunCfg_output]


/-- The rest of a branch of the guess-then-run host over any writer, from its handoff: the run
`V` up to its first verdict, one dispatch, and the verdict leaf; later choices are absorbed.

**Proof sketch.** `Turing.NDTM.phaseHostND_run` for the run phase: its branch is the
deterministic run (`Turing.MultiTapeTM.toNDTM_runWith`), its first verdict the redirected exit,
and the earlier states, none a verdict, the guard. One step of the verdict leaf
(`Turing.NDTM.stepWith_of_some` and the action's field equations) emits the bit and halts, and
absorption (`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
private theorem gr_runWith_of_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (cP : Cfg k Bool SP z) (s : List Bool) (TQ : ℕ)
    (hverd : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (L : ℕ) (w : List Bool)
    (hH : (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith (w.take L)
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      (guessRunCfg cP j s qentry).mapState (Sigma.mk GuessRunPhase.run))
    (hw : L + TQ + 2 ≤ w.length) :
    let d := V.runFrom (guessRunCfg cP j s qentry) TQ
    (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  intro d
  set M := guessCtlRunPhases P j q₀ δ stop bounded V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [← List.take_append_drop L w, NDTM.runWith_append, hH, hN]
  -- the deterministic run up to its verdict, then one dispatch into the verdict leaf
  obtain ⟨a, b, r, hv, ha⟩ := guessRun_split TQ (w.drop L) (by simp; omega)
  have hr : 1 ≤ r.length := by
    have := congrArg List.length hv
    simp [ha] at this
    omega
  obtain ⟨b', r', rfl⟩ : ∃ b' r', r = b' :: r' := by
    cases r with
    | nil => simp at hr
    | cons b' r' => exact ⟨b', r', rfl⟩
  obtain ⟨sv, hsv, hred⟩ : ∃ sv, d.state = some sv ∧
      red GuessRunPhase.run sv = some ⟨.out, decide (d.state = some acc)⟩ := by
    rcases hverd with h | h
    · have h' : d.state = some acc := h
      exact ⟨acc, h', by simp [red, guessCtlRunRed, h']⟩
    · have h' : d.state = some rej := h
      by_cases hra : rej = acc
      · subst hra
        exact ⟨rej, h', by simp [red, guessCtlRunRed, h']⟩
      · exact ⟨rej, h', by simp [red, guessCtlRunRed, h', hra]⟩
  have hQ := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.run
    (guessRunCfg cP j s qentry) d a (by
      show V.toNDTM.runWith a (guessRunCfg cP j s qentry) = d
      rw [MultiTapeTM.toNDTM_runWith, ha]) sv hsv _ hred (by
      intro u hu s' hs'
      change (V.toNDTM.runWith (a.take u) (guessRunCfg cP j s qentry)).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
      have hne := hfirst u (by omega)
      show (if s' = acc then _ else if s' = rej then _ else none) = none
      rw [if_neg (fun h => hne.1 (by rw [← h]; exact hs')),
        if_neg (fun h => hne.2 (by rw [← h]; exact hs'))]) b).2
  rw [hv, NDTM.runWith_append, hQ, NDTM.runWith_cons]
  -- the verdict leaf emits the verdict bit and halts; the rest of the word is absorbed
  have hout : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).stepWith b'
      (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
    have hst : (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))).state =
        some ⟨.out, decide (d.state = some acc)⟩ := by
      rw [Cfg.mapState_state, hsv]
      rfl
    rw [NDTM.stepWith_of_some hst]
    have hwt : ∀ i, (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))).workTapes i = d.workTapes i := fun i =>
      funext (Cfg.mapState_workTapes _ d i)
    apply Cfg.ext <;> (try funext i) <;> (try funext p) <;>
      simp only [NDTM.phaseHostND, red, guessCtlRunRed, M, guessCtlRunPhases, hwt,
        Action.apply_state, Action.apply_inputPos, Action.apply_workTapes, Action.apply_workTapePos,
        Action.apply_output, Action.mapState_state, Action.mapState_inputTape,
        Action.mapState_workTapes, Action.mapState_output, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
        Cfg.workTapeSymbols_eq, Function.update_eq_self, moveInputPos_zero, Option.map_none,
        Option.toList_some, Option.getD_none, SignType.coe_zero, add_zero]
  erw [hout]
  rw [NDTM.runWith_of_halt _ rfl]


/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on
`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with a nonblank block of
`m` cells of tape `j` from its head, a blank just after the block and a blank just before it.
Then every choice word `w` of length `TP + 2m + 9` drives the host to the run's entry
configuration `Turing.guessRunCfg cP j s qentry`, tagged by the run phase, where `s` is the `m`
bits of `w` after its first `TP + 1`: the block holds `s`, the head of tape `j` is back at the
block's start, and every other field is `cP`'s. The time is `TP` for the setup, `1` per dispatch
(four), `m + 1` for the writer, `1` for the step right and `m + 3` for the rewind. The first
`TP + 1` bits and the writer's last bit are ignored, and every stream of length `m` is the
stream of some word. [AB09, §2.1.2, proof of Theorem 2.6]

**Proof sketch.** Split `w` into the setup's `TP` bits and a dispatch bit, the writer's `m + 1`
bits and a dispatch bit, the step right's bit and a dispatch bit, and the rewind's `m + 3` bits
and a dispatch bit. Each phase is one application of `Turing.NDTM.phaseHostND_run`. The setup's
branch is its run (`Turing.MultiTapeTM.toNDTM_runWith`), with no redirect before `TP`. The
writer's branch is `Turing.ndWriterTM_run_block`, whose second clause is the guard. The step right
is `Turing.skipTM_run_ofCfg` over the empty word (the cell after the block is blank). The rewind
is `Turing.skipBackTM_run_ofCfg` over `s` (the cells before and after the block are blank). Each
phase's endpoint, renamed, is the next phase's start; the last is the entry configuration, the
head of tape `j` restored. -/
theorem guessRunTM_runWith_handoff {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9) :
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  have hst : (cP.mapState (fun _ => NDWriterState.run ())).state = some (NDWriterState.run ()) := by
    rw [Cfg.mapState_state, hPexit]; rfl
  obtain ⟨hW1, hW2⟩ := ndWriterTM_run_block j (cP.mapState (fun _ => NDWriterState.run ())) hst m
    (fun p hp => by rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]; exact hblock p hp)
    (by rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]; exact hend)
    ((w.drop (TP + 1)).take (m + 1)) (by simp; omega)
  rw [List.take_take, Nat.min_eq_left (by omega)] at hW1
  refine gr_handoff P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej TP cP hP
    hPexit hPfirst m hend hleft w hw ?_ ?_
  · rw [hW1, gr_writer_end]
  · intro u hu
    exact hW2 _ (by simp; omega)

/-- **No branch halts before the handoff.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, every choice word shorter than `TP + 2m + 9` leaves the host
live. So a budget below the handoff time accepts nothing, whatever the run does.

**Proof sketch.** Pad the word to length `TP + 2m + 9`. If its branch had halted, absorption
(`Turing.NDTM.runWith_of_halt`) would keep it halted, but the padded word reaches the live entry
configuration (`Turing.guessRunTM_runWith_handoff`). -/
theorem guessRunTM_runWith_live {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length < TP + 2 * m + 9) :
    ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state ≠ none := by
  intro h
  have hh := guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m
    hblock hend hleft (w ++ List.replicate (TP + 2 * m + 9 - w.length) false)
    (by simp; omega)
  rw [NDTM.runWith_append, NDTM.runWith_of_halt _ h] at hh
  rw [hh] at h
  simp [guessRunCfg, Cfg.mapState] at h

/-- **At the handoff the host is live, at the run's entry.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, every choice word of length exactly `TP + 2m + 9` leaves the
host in the state `⟨run, qentry⟩`: live, and at the run's entry. With
`Turing.guessRunTM_runWith_live` (every shorter word), the host is live at every length up to
the handoff.

**Proof sketch.** The state field of the configuration that
`Turing.guessRunTM_runWith_handoff` gives. -/
theorem guessRunTM_runWith_handoff_state {k : ℕ} {SP SQ : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool} (TP : ℕ)
    (cP : Cfg k Bool SP z) (hP : P.runFrom (P.initCfg z) TP = cP)
    (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9) :
    ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state =
      some ⟨GuessRunPhase.run, qentry⟩ := by
  rw [guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock
    hend hleft w hw]
  rfl

/-- **The whole branch.** Under the setup hypotheses of `Turing.guessRunTM_runWith_handoff`,
let `s` be a stream of length `m`, and let the run `Q` from the entry configuration
`Turing.guessRunCfg cP j s qentry` reach a verdict state, `acc` or `rej`, first at time `TQ`, in
the configuration `d`. Then every choice word whose `m` bits after its first `TP + 1` are `s`,
of length at least `TP + 2m + TQ + 11`, halts the host with `d`'s input head, tapes and heads, and
with output `d`'s output followed by the verdict bit (`true` iff `d` is at `acc`). The branch
is halted by time `TP + 2m + TQ + 11`: the handoff, the run, one dispatch and the leaf's
emitting step.
Choices after the stream are ignored. The run's own emissions stay in the output; capturing them
is the caller's choice (`Turing.guessRunTM_silent_spec`). [AB09, §2.1.2]

**Proof sketch.** `Turing.guessRunTM_runWith_handoff` on the first `TP + 2m + 9` bits. Then
`Turing.NDTM.phaseHostND_run` for the run phase: its branch is the deterministic run
(`Turing.MultiTapeTM.toNDTM_runWith`), its first verdict the redirected exit, and the earlier
states, none a verdict, the guard. One step of the verdict leaf emits the bit and halts, and
absorption (`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
theorem guessRunTM_runWith {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (s : List Bool) (hs : s.length = m) (TQ : ℕ)
    (hverd : (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool) (hws : (w.drop (TP + 1)).take m = s)
    (hw : TP + 2 * m + TQ + 11 ≤ w.length) :
    let d := Q.runFrom (guessRunCfg cP j s qentry) TQ
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  -- through the guess and the rewind
  have hH := guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m
    hblock hend hleft (w.take (TP + 2 * m + 9)) (by simp; omega)
  have hs' : ((w.take (TP + 2 * m + 9)).drop (TP + 1)).take m = s := by
    rw [← hws, List.drop_take, List.take_take]
    congr 1
    omega
  rw [hs'] at hH
  exact gr_runWith_of_handoff P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej
    cP s TQ hverd hfirst (TP + 2 * m + 9) w hH (by omega)

/-- **A setup that halts before its exit.** If the setup `P` halts on `z` at time `TP` without
being at its exit `pexit` before, then every choice word of length at least `TP` leaves the host
in `P`'s halted configuration, tagged by the setup phase: the host halts without guessing, with
`P`'s output. (For inputs that a consumer rejects outright, such as the diagonalizer's non-unary
inputs.) [AB09, §2.1.2]

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn_det` with `P` as the deterministic
source along the setup phase's tag, the good states being those other than `pexit`, where the
host redirects nothing and so follows `P`'s transitions, renamed; then absorption
(`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
theorem guessRunTM_runWith_setup_halt {k : ℕ} {SP SQ : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool} (TP : ℕ)
    (hhalt : (P.runFrom (P.initCfg z) TP).state = none)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (w : List Bool) (hw : TP ≤ w.length) :
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      (P.runFrom (P.initCfg z) TP).mapState (Sigma.mk GuessRunPhase.pre) := by
  set M := guessRunPhases P j Q
  set red := guessRunRed pexit qentry acc rej
  have hN : guessRunTM P pexit j Q qentry acc rej = NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN]
  let emb : SP ↪ (Σ i, GuessRunPhase.State SP SQ i) :=
    ⟨fun s => ⟨GuessRunPhase.pre, s⟩, fun a b h => sigma_mk_injective h⟩
  have hpre := NDTM.runWith_mapState_of_agreeOn_det P (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
    (fun s => s ≠ pexit) (by
      intro b s hs inp work
      have hr : red GuessRunPhase.pre s = none := by
        show (if s = pexit then _ else none) = none
        rw [if_neg hs]
      change (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b ⟨GuessRunPhase.pre, s⟩ inp work = _
      simp only [NDTM.phaseHostND, hr]
      rfl)
    (P.initCfg z) (w.take TP) (by
      intro u hu s hs
      rw [List.length_take, Nat.min_eq_left hw] at hu
      rintro rfl
      exact hPfirst u hu hs)
  rw [List.length_take, Nat.min_eq_left hw] at hpre
  rw [← List.take_append_drop TP w, NDTM.runWith_append]
  erw [hpre]
  rw [NDTM.runWith_of_halt _ (by
    show Option.map _ (P.runFrom (P.initCfg z) TP).state = none
    rw [hhalt]
    rfl)]
  rfl

/-- **All-branch halting.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, if for every stream `s` of length `m` the run from the entry
configuration `Turing.guessRunCfg cP j s qentry` reaches a verdict first at some time at most
`T`, then every branch of the host on `z` halts within `TP + 2m + T + 11`
(`Turing.NDTM.HaltsWithin`). [AB09, §2.1.2: every branch halts within the bound]

**Proof sketch.** A word of that length has some stream as its `m` bits after its first
`TP + 1`; `Turing.guessRunTM_runWith` at that stream's verdict time gives a halted branch. -/
theorem guessRunTM_haltsWithin {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none) (T : ℕ)
    (hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      ((Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
        (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
      ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) :
    (guessRunTM P pexit j Q qentry acc rej).HaltsWithin z (TP + 2 * m + T + 11) := by
  intro w hw
  obtain ⟨TQ, hTQ, hv, hf⟩ := hQ ((w.drop (TP + 1)).take m) (by simp; omega)
  rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
    hleft _ (by simp; omega) TQ hv hf w rfl (by omega)]

/-- **Exact-budget acceptance, both directions.** Under the hypotheses of
`Turing.guessRunTM_haltsWithin`, at every budget `B` at least `TP + 2m + T + 11`: some choice word
of length exactly `B` halts the host with output exactly `[true]` (the shape of
`Turing.FinNDTM.AcceptsWithin`) iff some stream `s` of length `m` makes the run's first verdict
`acc`, with an empty output at that time. A stream whose first verdict state is `rej` and
different from `acc`, or whose run's output (the setup's emissions included) is nonempty at the
verdict, gives no accepting branch; when `acc = rej` that verdict accepts, since the leaf tests
`acc` first.
[AB09, §2.1.2, proof of Theorem 2.6]

**Proof sketch.** Forward: take the accepting word's stream; by `Turing.guessRunTM_runWith` at
that stream's verdict time, the output is the run's output followed by the verdict bit, which is
`[true]` only if the run's output is empty and the verdict is `acc`. Backward: the word made of
`TP + 1` bits `false`, then `s`, then `false` up to length `B`, has stream `s`; the first verdict
time is unique, hence at most `T`, and `Turing.guessRunTM_runWith` gives the output
`[] ++ [true]`. -/
theorem guessRunTM_accepts_iff {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none) (T : ℕ)
    (hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      ((Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
        (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
      ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (B : ℕ) (hB : TP + 2 * m + T + 11 ≤ B) :
    (∃ w : List Bool, w.length = B ∧
      ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state = none ∧
      ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).output = [true]) ↔
    ∃ s : List Bool, s.length = m ∧ ∃ TQ : ℕ,
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∧
      (∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) ∧
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).output = [] := by
  constructor
  · rintro ⟨w, hw, -, hout⟩
    have hslen : ((w.drop (TP + 1)).take m).length = m := by simp; omega
    obtain ⟨TQ, hTQ, hv, hf⟩ := hQ _ hslen
    rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
      hleft _ hslen TQ hv hf w rfl (by omega)] at hout
    have hlen := congrArg List.length hout
    simp only [List.length_append, List.length_singleton] at hlen
    have hnil : (Q.runFrom (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry) TQ).output =
        [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, List.nil_append, List.singleton_inj, decide_eq_true_iff] at hout
    exact ⟨_, hslen, TQ, hout, hf, hnil⟩
  · rintro ⟨s, hslen, TQ', hacc, hf', hnil⟩
    obtain ⟨TQ, hTQ, hv, hf⟩ := hQ s hslen
    have heq : TQ' = TQ := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (hf TQ' h).1 hacc
      · rcases hv with hv | hv
        · exact (hf' TQ h).1 hv
        · exact (hf' TQ h).2 hv
    subst heq
    let w := List.replicate (TP + 1) false ++ s ++ List.replicate (B - (TP + 1 + m)) false
    have hwlen : w.length = B := by simp [w, hslen]; omega
    have hws : (w.drop (TP + 1)).take m = s := by
      simp only [w, List.append_assoc]
      rw [List.drop_left' (by simp), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    refine ⟨w, hwlen, ?_⟩
    rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
      hleft s hslen TQ' (Or.inl hacc) hf' w hws (by omega)]
    simp [hacc, hnil]

/-- **The core's precondition at the handoff.** Let the setup end clean: in a state `q`, with
the input head on the first symbol, every tape blank except tape `ι jR`, which holds a block `blk`
blank outside the cells `0, …, m - 1`, every head at `0`, and an empty output. Then, for every
stream `s` of length `m`, the run's entry configuration in state `entry` is the core's start
configuration `Turing.streamStartCfg z jR entry s`, silently embedded along `ι` with the capture
tape `cap` outside the selection (`Turing.embedSilentCfg` with a blank frame, heads at `0`, an
empty capture word and an empty host output). This is the clean-bank, head and output
precondition of `Turing.exists_ndInterpreterCore`, delivered by the guess and the rewind.

**Proof sketch.** Field by field. The state and the input head are `entry` and `1` on both
sides. A selected tape `ι a` is the core's tape `a` (`Turing.embedSilentCfg_selected_tape`): at
`a = jR` the overwritten block is `bufferTape s`, since `blk` is blank outside the block and so is
`bufferTape s`; elsewhere both are blank. The capture tape holds the empty capture word with its
head at `0` (`Turing.embedSilentCfg_cap`); every other unselected tape is the blank frame
(`Turing.embedSilentTM_frame` at time `0`). Heads are `0`; outputs are
empty. -/
theorem guessRunCfg_clean {K k : ℕ} {SP SR : Type} {z : List Bool} (ι : Fin K ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (jR : Fin K) (blk : ℤ → Option Bool) (m : ℕ)
    (hblk : ∀ p : ℤ, (p < 0 ∨ (m : ℤ) ≤ p) → blk p = none) (q : SP) (entry : SR)
    (s : List Bool) (hs : s.length = m) :
    guessRunCfg (⟨some q, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ :
        Cfg k Bool SP z) (ι jR) s entry =
      embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (streamStartCfg z jR entry s) := by
  classical
  -- a one-state machine whose frame lemma at time `0` reads the unselected tapes
  let M0 : MultiTapeTM K Bool SR :=
    ⟨entry, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  have hframe := (embedSilentTM_frame ι cap hcap M0 (fun _ _ => none) (fun _ => 0) [] []
    (streamStartCfg z jR entry s) 0).1
  simp only [MultiTapeTM.runFrom_zero] at hframe
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hi
      rw [embedSilentCfg_selected_tape]
      simp only [guessRunCfg, streamStartCfg]
      by_cases ha : a = jR
      · subst ha
        rw [Function.update_self, if_pos rfl]
        funext p
        simp only [Function.update_self, zero_add, sub_zero, hs]
        by_cases hp : 0 ≤ p ∧ p < (m : ℤ)
        · rw [if_pos hp]
        · rw [if_neg hp, hblk p (by omega)]
          simp only [FinTM.bufferTape]
          split_ifs with h0
          · symm
            exact List.getElem?_eq_none (by rw [hs]; omega)
          · rfl
      · have hne : ι a ≠ ι jR := fun h => ha (ι.injective h)
        rw [Function.update_of_ne hne, Function.update_of_ne hne, if_neg ha]
    · by_cases hc : i = cap
      · subst hc
        have hne : i ≠ ι jR := fun h => hi ⟨jR, h.symm⟩
        simp only [guessRunCfg, Function.update_of_ne hne]
        -- the capture tape holds the empty capture word
        rw [(embedSilentCfg_cap ι i hcap (fun _ _ => none) (fun _ => 0) [] []
          (streamStartCfg z jR entry s)).1]
        simp [streamStartCfg]
      · have hne : i ≠ ι jR := fun h => hi ⟨jR, h.symm⟩
        simp only [guessRunCfg, Function.update_of_ne hne]
        exact ((hframe i hi hc).1).symm
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hi
      rw [embedSilentCfg_selected_pos]
      rfl
    · by_cases hc : i = cap
      · subst hc
        -- the capture head sits after the empty capture word
        rw [(embedSilentCfg_cap ι i hcap (fun _ _ => none) (fun _ => 0) [] []
          (streamStartCfg z jR entry s)).2]
        simp [guessRunCfg, streamStartCfg]
      · exact ((hframe i hi hc).2).symm
  · rfl

/-- **Guess, then run the interpreter core** (the assembly `Turing.exists_timed_universal_NDTM`'s
sketch names). Let `R` be a `K`-tape machine with an entry state `entry` and live verdicts `acc`
and `rej`, run silently on the host tapes selected by `ι`, its emissions captured on a tape
`cap` outside the selection (`Turing.embedSilentTM`). Let the setup `P` reach its exit `pexit`
first at time `TP`, clean: input head on the first symbol, every tape blank except tape `ι jR`,
which is nonblank exactly at the cells `0, …, m - 1`, every head at `0`, empty output. Suppose
that for every stream `s` of length `m`, `R` from its start configuration
`Turing.streamStartCfg z jR entry s` reaches a verdict first within `T`. Then the host `N` halts
on every branch within `TP + 2m + T + 11`, and at every budget `B` at least that, `N` has a branch
of length exactly `B` halting with output exactly `[true]` iff some stream `s` of length `m`
makes `R`'s first verdict `acc`. `R`'s own output is never examined: the capture makes the host's
output exactly the verdict bit. [AB09, §2.1.2, proof of Theorem 2.6; Exercise 2.6]

**Proof sketch.** The setup's endpoint satisfies the block hypotheses of
`Turing.guessRunTM_runWith_handoff` (nonblank inside the block, blank at `m` and at `-1`). By
`Turing.guessRunCfg_clean` the entry configuration is `R`'s start, silently embedded, so the
run's states are `R`'s and its output stays empty (`Turing.embedSilentTM_runFrom`). Conclude by
`Turing.guessRunTM_haltsWithin` and `Turing.guessRunTM_accepts_iff`, whose output condition then
holds. -/
theorem guessRunTM_silent_spec {K k : ℕ} {SP SR : Type} [DecidableEq SP] [DecidableEq SR]
    (ι : Fin K ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι) (jR : Fin K)
    (R : MultiTapeTM K Bool SR) (entry acc rej : SR)
    (P : MultiTapeTM k Bool SP) (pexit : SP) {z : List Bool} (TP m : ℕ)
    (blk : ℤ → Option Bool) (hblk : ∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < m)
    (hP : P.runFrom (P.initCfg z) TP =
      ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit) (T : ℕ)
    (hR : ∀ s : List Bool, s.length = m → ∃ TR ≤ T,
      ((R.runFrom (streamStartCfg z jR entry s) TR).state = some acc ∨
        (R.runFrom (streamStartCfg z jR entry s) TR).state = some rej) ∧
      ∀ u < TR, (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some rej) :
    let N := guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej
    N.HaltsWithin z (TP + 2 * m + T + 11) ∧
      ∀ B : ℕ, TP + 2 * m + T + 11 ≤ B →
        ((∃ w : List Bool, w.length = B ∧ (N.runWith w (N.initCfg z)).state = none ∧
            (N.runWith w (N.initCfg z)).output = [true]) ↔
          ∃ s : List Bool, s.length = m ∧ ∃ TR : ℕ,
            (R.runFrom (streamStartCfg z jR entry s) TR).state = some acc ∧
            ∀ u < TR, (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some acc ∧
              (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some rej) := by
  intro N
  set cP : Cfg k Bool SP z :=
    ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ with hcP
  have hout : ∀ p : ℤ, (p < 0 ∨ (m : ℤ) ≤ p) → blk p = none := by
    intro p hp
    by_contra h
    have := (hblk p).mp h
    omega
  have hblock : ∀ p : ℕ, p < m → cP.workTapes (ι jR) (cP.workTapePos (ι jR) + p) ≠ none := by
    intro p hp
    simp only [cP, Function.update_self, zero_add]
    exact (hblk p).mpr ⟨by omega, by omega⟩
  have hend : cP.workTapes (ι jR) (cP.workTapePos (ι jR) + m) = none := by
    simp only [cP, Function.update_self, zero_add]
    exact hout m (Or.inr le_rfl)
  have hleft : cP.workTapes (ι jR) (cP.workTapePos (ι jR) - 1) = none := by
    simp only [cP, Function.update_self, zero_sub]
    exact hout (-1) (Or.inl (by omega))
  -- the handoff is the silently embedded start of `R`, and the embedded run is `R`'s
  have hrun : ∀ (s : List Bool), s.length = m → ∀ u : ℕ,
      (embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u =
        embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (R.runFrom (streamStartCfg z jR entry s) u) := by
    intro s hs u
    rw [hcP, guessRunCfg_clean ι cap hcap jR blk m hout pexit entry s hs]
    exact embedSilentTM_runFrom ι cap hcap R _ _ [] [] _ u
  have hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      (((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) TQ).state =
          some acc ∨
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) TQ).state =
          some rej) ∧
      ∀ u < TQ,
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u).state ≠ some acc ∧
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u).state ≠
          some rej := by
    intro s hs
    obtain ⟨TR, hTR, hv, hf⟩ := hR s hs
    refine ⟨TR, hTR, ?_, ?_⟩
    · rw [hrun s hs]
      exact hv
    · intro u hu
      rw [hrun s hs]
      exact hf u hu
  refine ⟨guessRunTM_haltsWithin P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej TP cP
    hP rfl hPfirst m hblock hend hleft T hQ, fun B hB => ?_⟩
  rw [guessRunTM_accepts_iff P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej TP cP
    hP rfl hPfirst m hblock hend hleft T hQ B hB]
  constructor
  · rintro ⟨s, hs, TQ, hacc, hf, -⟩
    refine ⟨s, hs, TQ, ?_, ?_⟩
    · rw [hrun s hs] at hacc
      exact hacc
    · intro u hu
      have h := hf u hu
      rw [hrun s hs] at h
      exact h
  · rintro ⟨s, hs, TR, hacc, hf⟩
    refine ⟨s, hs, TR, ?_, ?_, ?_⟩
    · rw [hrun s hs]
      exact hacc
    · intro u hu
      rw [hrun s hs]
      exact hf u hu
    · rw [hrun s hs]
      rfl

end Turing

/-! ## The controller-stopped guess-then-run assembly

The instance of `Turing.guessCtlRunTM` with the unbounded writer under a controller. The
setup leaves the stream tape blank from its head on; the writer guesses bits until its controller
stops, after a number of bits that depends on the bits; the stream head is rewound; a
deterministic run ends in one of two live verdict states; and the verdict leaf emits the verdict
bit and halts. A guessed display of unknown length has this shape (the linear normal form,
`TCSlib.Complexity.ClassNP.NDNormalForm`).

* `Turing.guessCtlRunTM_runWith_handoff`: a word whose stream first stops the controller after
  `m` bits drives the host to the run's entry at time `TP + 2m + 9`, the stream on the tape.
* `Turing.guessCtlRunTM_runWith`: the whole branch, through the run's first verdict.
* `Turing.guessCtlRunTM_stop_of_halted`: a halted branch has passed a stop of the controller.
* `Turing.guessCtlRunTM_accepts_of`, `Turing.guessCtlRunTM_stream_of_accepts`: acceptance,
  forward at every budget beyond the branch's time, and backward.

There is no all-branch halting lemma: a stream that never stops the controller never ends the
guess.
-/

namespace Turing

/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on
`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with tape `j` blank from
its head on and just before it. Let the `m` bits of the word `w` after its first `TP + 1` first
stop the controller: the controller state after `i` of them does not stop for `i < m` and stops
at `m`. Then a word of length `TP + 2m + 9` drives the host to the run's entry configuration
`Turing.guessRunCfg cP j s qentry`, tagged by the run phase, where `s` is those `m` bits. The
time is that of `Turing.guessRunTM_runWith_handoff`: `TP` for the setup, `1` per dispatch (four),
`m + 1` for the writer, `1` for the step right and `m + 3` for the rewind.
[AB09, §2.1.2]

**Proof sketch.** As for `Turing.guessRunTM_runWith_handoff`, one application of
`Turing.NDTM.phaseHostND_run` per phase, with `Turing.ndWriterTM_run_controller` for the writer:
its second clause is the guard. The blank tape gives the step right's blank after the stream and
the rewind's blank before it. -/
theorem guessCtlRunTM_runWith_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (m : ℕ) (w : List Bool) (hw : w.length = TP + 2 * m + 9)
    (hlive : ∀ i < m, stop (((w.drop (TP + 1)).take i).foldl δ q₀) = false)
    (hstop : stop (((w.drop (TP + 1)).take m).foldl δ q₀) = true) :
    (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  have hst : (cP.mapState (fun _ => NDWriterState.run q₀)).state = some (NDWriterState.run q₀) := by
    rw [Cfg.mapState_state, hPexit]; rfl
  obtain ⟨hW1, hW2⟩ := ndWriterTM_run_controller j q₀ δ stop
    (cP.mapState (fun _ => NDWriterState.run q₀)) q₀ hst (w.drop (TP + 1)) m (by simp; omega)
    hlive hstop
  refine gr_handoff P pexit j q₀ δ stop false V qentry acc rej TP cP hP hPexit hPfirst m
    (hblank m) hleft w hw ?_ ?_
  · rw [hW1, gr_writer_end]
  · intro u hu
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact hW2 u (by omega)

/-- **The whole branch.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the stream `s` of length `m` first stop the controller at its end, and let the run `V` from
the entry configuration `Turing.guessRunCfg cP j s qentry` reach a verdict state, `acc` or `rej`,
first at time `TQ`, in the configuration `d`. Then every choice word whose `m` bits after its
first `TP + 1` are `s`, of length at least `TP + 2m + TQ + 11`, halts the host with `d`'s input
head, tapes and heads, and with output `d`'s output followed by the verdict bit (`true` iff `d` is
at `acc`). Choices after the stream are ignored. [AB09, §2.1.2]

**Proof sketch.** `Turing.guessCtlRunTM_runWith_handoff` on the first `TP + 2m + 9` bits, whose
stream is `s`. Then, as for `Turing.guessRunTM_runWith`, `Turing.NDTM.phaseHostND_run` for the
run phase up to its first verdict, one step of the verdict leaf, and absorption
(`Turing.NDTM.runWith_of_halt`) for the remaining choices. -/
theorem guessCtlRunTM_runWith {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (m : ℕ) (s : List Bool) (hs : s.length = m)
    (hslive : ∀ i < m, stop ((s.take i).foldl δ q₀) = false)
    (hsstop : stop (s.foldl δ q₀) = true) (TQ : ℕ)
    (hverd : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool) (hws : (w.drop (TP + 1)).take m = s)
    (hw : TP + 2 * m + TQ + 11 ≤ w.length) :
    let d := V.runFrom (guessRunCfg cP j s qentry) TQ
    (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  -- the stream of the handoff word
  have hseg : ∀ i ≤ m, ((w.take (TP + 2 * m + 9)).drop (TP + 1)).take i = s.take i := by
    intro i hi
    rw [← hws, List.drop_take, List.take_take, List.take_take]
    congr 1
    omega
  -- through the guess and the rewind
  have hH := guessCtlRunTM_runWith_handoff P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft m (w.take (TP + 2 * m + 9)) (by simp; omega)
    (fun i hi => by rw [hseg i hi.le]; exact hslive i hi)
    (by rw [hseg m le_rfl, ← hs, List.take_length]; exact hsstop)
  rw [hseg m le_rfl, ← hs, List.take_length, hs] at hH
  exact gr_runWith_of_handoff P pexit j q₀ δ stop false V qentry acc rej cP s TQ hverd hfirst
    (TP + 2 * m + 9) w hH (by omega)

/-- **A halted branch has passed a stop of the controller.** Under the setup hypotheses of
`Turing.guessCtlRunTM_runWith_handoff` (only the setup's run to its exit), if the host halts on
the choice word `w`, then the bits of `w` after its first `TP + 1` first stop the controller after
some `m` of them, with at least one more bit of `w` after those `m`. A branch whose bits never stop
the controller is still guessing: it has not halted. [AB09, §2.1.2]

**Proof sketch.** Otherwise the controller does not stop after any `i < |w| − (TP + 1)` of those
bits (by strong induction, each such `i` would be a first stop). If `w` has at most `TP` bits, the
host is in the setup phase, live (`Turing.NDTM.phaseHostND_run`'s prefix clause; the setup is live
before its exit). Otherwise, after the setup and its dispatch the host follows the writer on the
remaining bits (`Turing.NDTM.runWith_mapState_of_agreeOn`, the writer's states being redirected
only at `done`), and the writer is still at `run` (`wr_prefix_controller`): live again. -/
theorem guessCtlRunTM_stop_of_halted {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (w : List Bool)
    (hhalt : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none) :
    ∃ m, TP + 1 + m < w.length ∧
      (∀ i < m, stop (((w.drop (TP + 1)).take i).foldl δ q₀) = false) ∧
      stop (((w.drop (TP + 1)).take m).foldl δ q₀) = true := by
  classical
  by_contra hno
  push_neg at hno
  set M := guessCtlRunPhases P j q₀ δ stop false V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN] at hhalt
  have hinit : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).initCfg z =
      (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) := by
    rw [NDTM.initCfg_eq, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state, Option.map_some]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext i p
      rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext i
      rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  rw [hinit] at hhalt
  -- the setup is live up to its exit
  have hPlive : ∀ u ≤ TP, (P.runFrom (P.initCfg z) u).state ≠ none := by
    intro u hu h
    have := hPexit
    rw [← hP, show TP = u + (TP - u) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ h] at this
    rw [h] at this
    exact Option.noConfusion this
  by_cases hshort : w.length ≤ TP
  · -- still in the setup: the host follows the setup, which is live
    let emb : GuessRunPhase.CtlState SP SQ Q GuessRunPhase.pre ↪
        (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
      ⟨Sigma.mk GuessRunPhase.pre, sigma_mk_injective⟩
    have hagree : ∀ (b : Bool) (q : SP), (fun s => red GuessRunPhase.pre s = none) q →
        ∀ inp work, (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b (emb q) inp work =
          ((M GuessRunPhase.pre).tr b q inp work).mapState emb := by
      intro b q hq inp work
      simp only [NDTM.phaseHostND, emb, Function.Embedding.coeFn_mk, hq]
    have hrun := NDTM.runWith_mapState_of_agreeOn (M GuessRunPhase.pre)
      (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
      (fun s => red GuessRunPhase.pre s = none) hagree (P.initCfg z) w (by
        intro u hu s' hs'
        change (P.toNDTM.runWith (w.take u) (P.initCfg z)).state = some s' at hs'
        rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
        have hne := hPfirst u (by omega)
        show (if s' = pexit then _ else none) = none
        rw [if_neg]
        rintro rfl
        exact hne hs')
    rw [show (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) = (P.initCfg z).mapState emb
      from rfl, hrun] at hhalt
    change ((P.toNDTM.runWith w (P.initCfg z)).mapState _).state = none at hhalt
    rw [MultiTapeTM.toNDTM_runWith] at hhalt
    simp only [Cfg.mapState_state] at hhalt
    exact hPlive w.length hshort (Option.map_eq_none_iff.mp hhalt)
  · -- after the setup: the host follows the writer, which has not stopped
    push_neg at hshort
    obtain ⟨a₁, b₁, r, hw, ha₁⟩ := guessRun_split TP w hshort
    have hdrop : w.drop (TP + 1) = r := by
      rw [hw, List.drop_left' (by simp [ha₁])]
    rw [hdrop] at hno
    -- no stop along the remaining bits
    have hnostop : ∀ i < r.length, stop ((r.take i).foldl δ q₀) = false := by
      intro i hi
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        exact Bool.eq_false_iff.mpr (hno i (by rw [hw]; simp [ha₁]; omega)
          (fun i' hi' => ih i' hi' (by omega)))
    -- the setup and its dispatch
    have h1 : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).runWith (a₁ ++ [b₁])
        ((P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre)) =
        cP.mapState (fun _ =>
          (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) := by
      refine (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.pre (P.initCfg z) cP a₁ ?_
        pexit hPexit _ ?_ ?_ b₁).2
      · show P.toNDTM.runWith a₁ (P.initCfg z) = cP
        rw [MultiTapeTM.toNDTM_runWith, ha₁, hP]
      · show (if pexit = pexit then _ else none) = _
        simp
      · intro u hu s' hs'
        change (P.toNDTM.runWith (a₁.take u) (P.initCfg z)).state = some s' at hs'
        rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
        have hne := hPfirst u (by omega)
        show (if s' = pexit then _ else none) = none
        rw [if_neg]
        rintro rfl
        exact hne hs'
    let cW : Cfg k Bool (NDWriterState Q) z := cP.mapState (fun _ => NDWriterState.run q₀)
    have hcW : cP.mapState (fun _ =>
        (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
        cW.mapState (Sigma.mk GuessRunPhase.guess) := by
      rw [Cfg.mapState_mapState]; rfl
    have hWst : cW.state = some (NDWriterState.run q₀) := by simp [cW, Cfg.mapState_state, hPexit]
    have hwr : ∀ u ≤ r.length, (ndWriterTM k j q₀ δ stop false).runWith (r.take u) cW =
        wr_cfg j cW (.run ((r.take u).foldl δ q₀)) (r.take u) := fun u hu =>
      wr_prefix_controller j q₀ δ stop cW q₀ hWst r u hu (fun i hi => hnostop i (by omega))
    let emb : GuessRunPhase.CtlState SP SQ Q GuessRunPhase.guess ↪
        (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
      ⟨Sigma.mk GuessRunPhase.guess, sigma_mk_injective⟩
    have hagree : ∀ (b : Bool) (q : NDWriterState Q),
        (fun s => red GuessRunPhase.guess s = none) q → ∀ inp work,
        (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b (emb q) inp work =
          ((M GuessRunPhase.guess).tr b q inp work).mapState emb := by
      intro b q hq inp work
      simp only [NDTM.phaseHostND, emb, Function.Embedding.coeFn_mk, hq]
    have hrun := NDTM.runWith_mapState_of_agreeOn (M GuessRunPhase.guess)
      (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
      (fun s => red GuessRunPhase.guess s = none) hagree cW r (by
        intro u hu s' hs'
        change ((ndWriterTM k j q₀ δ stop false).runWith (r.take u) cW).state = some s' at hs'
        rw [hwr u hu.le] at hs'
        simp only [wr_cfg, Option.some.injEq] at hs'
        subst hs'
        rfl)
    rw [hw, NDTM.runWith_append, h1, hcW,
      show cW.mapState (Sigma.mk GuessRunPhase.guess) = cW.mapState emb from rfl, hrun] at hhalt
    change (((ndWriterTM k j q₀ δ stop false).runWith r cW).mapState _).state = none at hhalt
    rw [show r = r.take r.length from (List.take_length).symm, hwr r.length le_rfl] at hhalt
    simp [wr_cfg, Cfg.mapState_state] at hhalt

/-- **Acceptance, forward.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the stream `s` first stop the controller at its end, and let the run `V` from
`Turing.guessRunCfg cP j s qentry` reach `acc` first at time `TQ`, not at `rej` before, with an
empty output. Then at every budget `B` at least `TP + 2|s| + TQ + 11`, some choice word of length
exactly `B` halts the host with output exactly `[true]` (the shape of
`Turing.FinNDTM.AcceptsWithin`). [AB09, §2.1.2]

**Proof sketch.** The word of `TP + 1` bits `false`, then `s`, then `false` up to length `B`, has
stream `s`; `Turing.guessCtlRunTM_runWith` gives the output `[] ++ [true]`. -/
theorem guessCtlRunTM_accepts_of {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (s : List Bool) (hslive : ∀ i < s.length, stop ((s.take i).foldl δ q₀) = false)
    (hsstop : stop (s.foldl δ q₀) = true) (TQ : ℕ)
    (hacc : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (hnil : (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [])
    (B : ℕ) (hB : TP + 2 * s.length + TQ + 11 ≤ B) :
    ∃ w : List Bool, w.length = B ∧
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none ∧
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).output =
          [true] := by
  let w := List.replicate (TP + 1) false ++ s ++ List.replicate (B - (TP + 1 + s.length)) false
  have hwlen : w.length = B := by simp [w]; omega
  have hws : (w.drop (TP + 1)).take s.length = s := by
    simp only [w, List.append_assoc]
    rw [List.drop_left' (by simp), List.take_left' rfl]
  have hrun := guessCtlRunTM_runWith P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft s.length s rfl hslive hsstop TQ (Or.inl hacc) hfirst w hws
    (by omega)
  refine ⟨w, hwlen, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]
    show (V.runFrom (guessRunCfg cP j s qentry) TQ).output ++
      [decide ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)] = [true]
    rw [hnil, hacc]
    simp

/-- **Acceptance, backward.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the run `V` reach a verdict, `acc` or `rej`, from the entry configuration of every stream that
first stops the controller at its end. If some choice word halts the host with output exactly
`[true]`, then some such stream makes `V`'s first verdict `acc`, with an empty output at that time.
[AB09, §2.1.2]

**Proof sketch.** The halted branch has passed a stop of the controller
(`Turing.guessCtlRunTM_stop_of_halted`); its stream `s` is the bits before it. Pad the word past
`TP + 2|s| + TQ + 11`: by absorption (`Turing.NDTM.runWith_of_halt`) the padded branch is the same
halted configuration, and `Turing.guessCtlRunTM_runWith` gives its output, `V`'s output followed
by the verdict bit. That is `[true]` only if `V`'s output is empty and the verdict is `acc`. -/
theorem guessCtlRunTM_stream_of_accepts {k : ℕ} {SP SQ Q : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q)
    (δ : Q → Bool → Q) (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (hV : ∀ s : List Bool, (∀ i < s.length, stop ((s.take i).foldl δ q₀) = false) →
      stop (s.foldl δ q₀) = true → ∃ TQ : ℕ,
        ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
          (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
        ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
          (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool)
    (hhalt : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none)
    (hout : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).output = [true]) :
    ∃ s : List Bool, (∀ i < s.length, stop ((s.take i).foldl δ q₀) = false) ∧
      stop (s.foldl δ q₀) = true ∧ ∃ TQ : ℕ,
        (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∧
        (∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
          (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) ∧
        (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [] := by
  obtain ⟨m, hm, hl, hst⟩ := guessCtlRunTM_stop_of_halted P pexit j q₀ δ stop V qentry acc rej
    TP cP hP hPexit hPfirst w hhalt
  set s := (w.drop (TP + 1)).take m with hs_def
  have hslen : s.length = m := by simp [s]; omega
  have hslive : ∀ i < s.length, stop ((s.take i).foldl δ q₀) = false := by
    intro i hi
    rw [hslen] at hi
    rw [hs_def, List.take_take, Nat.min_eq_left hi.le]
    exact hl i hi
  obtain ⟨TQ, hverd, hfirst⟩ := hV s hslive hst
  let w' := w ++ List.replicate (TP + 2 * m + TQ + 11) false
  have hws : (w'.drop (TP + 1)).take m = s := by
    simp only [w']
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  have hrun := guessCtlRunTM_runWith P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft m s hslen (fun i hi => hslive i (by omega)) hst TQ hverd hfirst w' hws
    (by simp [w'])
  have habs : (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w'
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) := by
    simp only [w']
    rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
  rw [← habs, hrun] at hout
  have hlen := congrArg List.length hout
  simp only [List.length_append, List.length_singleton] at hlen
  have hnil : (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  change (V.runFrom (guessRunCfg cP j s qentry) TQ).output ++
    [decide ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)] = [true] at hout
  rw [hnil, List.nil_append, List.singleton_inj, decide_eq_true_iff] at hout
  exact ⟨s, hslive, hst, TQ, hout, hfirst, hnil⟩

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

## ===== TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Nondeterministic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space usage of nondeterministic machines

The space measure for binary-choice NDTMs, mirroring the deterministic
`Turing.MultiTapeTM.visitedByTapeHead`/`spaceUsedByTape`/`spaceUsed` along
choice-word runs: the cells a work-tape head visits during the run under a given
choice word, summed over the work tapes. This is the campaign convention for
[AB09, Definition 4.1]'s nondeterministic clause — **visited** cells, the same
measure as the deterministic `SPACE` ([AB09]'s own wording switches to "nonblank"
locations for `NSPACE`; the split and the convention are recorded in
`TCSlib.Complexity.SpaceComplexity.Basic`). The class `Complexity.NSPACE` built on
this measure lives in `TCSlib.Complexity.SpaceComplexity.NSPACE`.

## Main definitions

* `Turing.NDTM.visitedWith` — the set of cells visited by one work-tape head
  along the run under a choice word (prefixes included).
* `Turing.NDTM.spaceUsedWith` — total visited cells, summed over work tapes.
  [AB09, Definition 4.1, nondeterministic clause, visited-cells convention]

## Main results

* `Turing.NDTM.spaceUsedWith_eq_fixChoice_spaceUsed` — such a branch uses exactly the slice's
  space (statement gated 2026-10-14; proved from `Turing.NDTM.runWith_eq_fixChoice_runFrom`).
* `Turing.NDTM.visitedWith_nil` — the empty run visits the starting positions.
* `Turing.MultiTapeTM.toNDTM_spaceUsedWith` — the embedded deterministic machine's
  space under any choice word is the deterministic space at that time (proved;
  the measure-transfer obligation behind `SPACE ⊆ NSPACE`).
* `Turing.NDTM.spaceUsedWith_append_of_halt` — once a branch has halted, extending
  the choice word does not change the space (proved; the invariance that makes
  the exact-length quantifier in `Complexity.NSPACE` sufficient).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace NDTM

/-- The cells visited by the head of work tape `i` along the run of `tm` under the
choice word `w` from `cfg`: the head positions after every prefix of `w` (the empty
prefix included, so the starting position always counts) — the nondeterministic
counterpart of `Turing.MultiTapeTM.visitedByTapeHead`. -/
def visitedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) (i : Fin k) : Finset ℤ :=
  (Finset.range (w.length + 1)).image fun j => (tm.runWith (w.take j) cfg).workTapePos i

/-- The space used by `tm` along the run under the choice word `w` from `cfg`: the
number of visited cells, summed over the work tapes — the nondeterministic
counterpart of `Turing.MultiTapeTM.spaceUsed`, for one branch. The input tape
(read-only) and the output tape (append-only) do not count.
[AB09, Definition 4.1, nondeterministic clause, visited-cells convention] -/
def spaceUsedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) : ℕ :=
  ∑ i, (tm.visitedWith w cfg i).card

/-- The empty choice word visits exactly the starting position of each head. -/
@[simp]
lemma visitedWith_nil (tm : NDTM k Symbol State) (cfg : Cfg k Symbol State input)
    (i : Fin k) : tm.visitedWith [] cfg i = {cfg.workTapePos i} := by
  simp [visitedWith]

/-- Extending a choice word preserves every position visited by its prefixes,
without any halting hypothesis.

**Proof sketch.** An old prefix index is still in the larger range, and taking
that many bits of the extended word gives the same prefix. -/
private lemma visitedWith_subset_append (tm : NDTM k Symbol State) (w w' : List Bool)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    tm.visitedWith w cfg i ⊆ tm.visitedWith (w ++ w') cfg i := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  have hjle : j ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    simp only [List.length_append]
    omega
  · rw [List.take_append_of_le_length hjle]

/-- **Space stabilizes at halting**: if the branch under `w` has halted, running
under any extension `w ++ w'` visits no further cells, so the space is unchanged.
This is why `Complexity.NSPACE` may quantify over choice words of one exact
length: all-branch halting at that length freezes every branch's space.

**Proof sketch.** For `j ≤ |w|` the prefixes agree (`List.take_append_of_le_length`
-style splitting); for `j > |w|`, `(w ++ w').take j = w ++ w'.take (j - |w|)`,
`Turing.NDTM.runWith_append` factors the run through the halted configuration,
and `Turing.NDTM.runWith_of_halt` freezes it, so the head position equals the one
at prefix `w`. The two images therefore coincide (`Finset.image_congr` after
splitting `Finset.range`), tape by tape.

**Fill appendix (C1a; short-prefix argument).** The private lemma
`visitedWith_subset_append` proves the old visited set is included in the new
one without a halting hypothesis: every old index remains in the longer range,
and the corresponding prefixes agree. In particular, a shorter choice word
can be padded to any prescribed larger length without losing visited cells.
The reverse inclusion uses the halted final position for every longer prefix.
The implementation uses `Finset.Subset.antisymm` and `Finset.mem_image` for
these inclusions, since the two image domains differ. -/
theorem spaceUsedWith_append_of_halt (tm : NDTM k Symbol State) {w : List Bool}
    {cfg : Cfg k Symbol State input} (h : (tm.runWith w cfg).state = none)
    (w' : List Bool) : tm.spaceUsedWith (w ++ w') cfg = tm.spaceUsedWith w cfg := by
  unfold spaceUsedWith
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    by_cases hjle : j ≤ w.length
    · refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
      rw [List.take_append_of_le_length hjle]
    · refine Finset.mem_image.mpr ⟨w.length, Finset.mem_range.mpr (by omega), ?_⟩
      rw [List.take_length, List.take_append, List.take_of_length_le (by omega),
        runWith_append, runWith_of_halt _ h]
  · exact visitedWith_subset_append tm w w' cfg i

end NDTM

/-- The embedded deterministic machine's space along any choice word is its
deterministic space at the corresponding time: `toNDTM` ignores its choices
(`Turing.MultiTapeTM.toNDTM_runWith`), so the visited sets coincide prefix by
prefix. The measure-transfer obligation behind `Complexity.SPACE_subset_NSPACE`.

**Proof sketch.** Fix a tape `i`. For every `j ≤ |w|`,
`tm.toNDTM.runWith (w.take j) cfg = tm.runFrom cfg j` by
`Turing.MultiTapeTM.toNDTM_runWith` and `List.length_take_of_le`, so the images
defining `Turing.NDTM.visitedWith` and `Turing.MultiTapeTM.visitedByTapeHead`
agree pointwise on `Finset.range (|w| + 1)` (`Finset.image_congr`), and the card
sums agree. -/
theorem MultiTapeTM.toNDTM_spaceUsedWith (tm : MultiTapeTM k Symbol State)
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.spaceUsedWith w cfg = tm.spaceUsed cfg w.length := by
  unfold NDTM.spaceUsedWith MultiTapeTM.spaceUsed
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  apply Finset.image_congr
  intro j hj
  change (tm.toNDTM.runWith (w.take j) cfg).workTapePos i =
    (tm.runFrom cfg j).workTapePos i
  rw [MultiTapeTM.toNDTM_runWith,
    List.length_take_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

end Turing

namespace Turing.NDTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- **The space of such a branch is the deterministic space.** Under the hypothesis of
`runWith_eq_fixChoice_runFrom`, the branch of `tm` under `w` visits exactly the cells that the
slice `tm.fixChoice b` visits in `|w|` steps: `spaceUsedWith w cfg` is
`(tm.fixChoice b).spaceUsed cfg |w|`. [AB09, Definition 4.1, nondeterministic clause]

**Proof sketch.** `visitedWith w cfg i` is the image of the runs under the prefixes `w.take j`,
`j ≤ |w|`; each prefix satisfies the hypothesis, so by `runWith_eq_fixChoice_runFrom` its run is
`(tm.fixChoice b).runFrom cfg j` (`List.length_take`). That is the image defining
`MultiTapeTM.visitedByTapeHead cfg |w| i`; sum over the tapes (`spaceUsed`). -/
theorem spaceUsedWith_eq_fixChoice_spaceUsed (tm : NDTM k Symbol State) (b : Bool)
    (w : List Bool) (cfg : Cfg k Symbol State input)
    (hagree : ∀ j < w.length, ∀ q : State, ((tm.fixChoice b).runFrom cfg j).state = some q →
      tm.tr false q = tm.tr true q) :
    tm.spaceUsedWith w cfg = (tm.fixChoice b).spaceUsed cfg w.length := by
  unfold spaceUsedWith MultiTapeTM.spaceUsed
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  apply Finset.image_congr
  intro j hj
  have hjw : j ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (tm.runWith (w.take j) cfg).workTapePos i = ((tm.fixChoice b).runFrom cfg j).workTapePos i
  rw [runWith_eq_fixChoice_runFrom tm b (w.take j) cfg (fun j' hj' q hq =>
      hagree j' (by rw [List.length_take] at hj'; omega) q hq),
    List.length_take_of_le hjw]

end Turing.NDTM
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARM
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compiling nondeterministic abstract register machines

The compiled nondeterministic machine of a nondeterministic abstract register machine `A`
(`Complexity.LogProg.ncompileTM`) is a `Turing.NDTM` whose two transition functions agree with
the compiled deterministic machine `M_β` of `A.detPart β` (the deterministic instructions, with
`ret β` at the `choose` labels) everywhere except at the start states of the `choose`
fragments, where the choice bit selects the target label by a pure control move.

At a `choose` start state `M_β` halts at once, writing `β`. So a run of `M_β` that ends live,
or halted with an answer other than `β`, never passes through a `choose` start state before
its end, and every branch of the nondeterministic machine follows it
(`Complexity.LogProg.ndtm_runWith_eq_runFrom`, `avoid_of_live`, `avoid_of_halt`). Choosing
`β` opposite to the answer of a halting deterministic step, no instruction-level simulation
has to be redone for `choose`: each deterministic abstract step is simulated by
`Complexity.LogProg.arm_step` / `arm_run` and `Complexity.LogProg.compile_correct_from`
(`Complexity.LogProg.ndet_live`, `Complexity.LogProg.ndet_halt`), and each `choose` is one
control step (`Complexity.LogProg.ncompileTM_stepWith_choose`).

This is infrastructure for [AB09, §4.1–4.3], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ncompileTM`, `Complexity.LogProg.ncompileFinNDTM` — the compiled
  nondeterministic machine.
* `Complexity.LogProg.NBox` — register heads in `[-1, W]`, decider heads in `[-B, B]`.

## Main results

* `Complexity.LogProg.ndtm_runWith_eq_runFrom` — a nondeterministic machine agreeing with a
  deterministic one off a set of states follows its runs that avoid the set.
* `Complexity.LogProg.ndet_live`, `Complexity.LogProg.ndet_halt` — the deterministic abstract
  steps, on every branch.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, §4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Nondeterministic machines following deterministic ones -/

section Generic

variable {K : ℕ} {Sym St : Type} {input : List Sym}

/-- **A nondeterministic machine follows a deterministic one off a set of states.** If both
transition functions of `N` agree with that of `M` at the states outside `X`, and the run of
`M` from `c` does not visit `X` before time `T`, then every choice word of length at most `T`
drives `N` along `M`'s run.

**Proof sketch.** Induction on the word: at a halted configuration both machines stay; at a
live one outside `X` the two steps apply the same action. -/
theorem ndtm_runWith_eq_runFrom (N : NDTM K Sym St) (M : MultiTapeTM K Sym St)
    (X : St → Prop) (hNM : ∀ b q, ¬ X q → N.tr b q = M.tr q) (c : Cfg K Sym St input) (T : ℕ)
    (hX : ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q)
    (w : List Bool) (hw : w.length ≤ T) : N.runWith w c = M.runFrom c w.length := by
  induction w generalizing c T with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨T, rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by simp at hw; omega⟩
    have hstep : N.stepWith b c = M.step c := by
      cases hc : c.state with
      | none => rw [NDTM.stepWith_of_halt hc, MultiTapeTM.step_of_halt hc]
      | some q =>
        have hq := hX 0 (by omega) q (by simpa using hc)
        simp only [NDTM.stepWith, MultiTapeTM.step, hc, hNM b q hq]
    rw [NDTM.runWith_cons, hstep, List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    exact ih _ T (fun t ht q hq => hX (t + 1) (by omega) q
      (by rwa [MultiTapeTM.runFrom_succ_eq_step])) (by simp at hw; omega)

/-- If `M` halts at once at the states of `X`, a run of `M` ending live does not visit `X`
before its end. -/
lemma avoid_of_live (M : MultiTapeTM K Sym St) (X : St → Prop)
    (hX : ∀ (c : Cfg K Sym St input) q, c.state = some q → X q → (M.step c).state = none)
    (c : Cfg K Sym St input) (T : ℕ) (hT : (M.runFrom c T).state ≠ none) :
    ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q := by
  intro t ht q hq hx
  have h1 : (M.runFrom c (t + 1)).state = none := by
    rw [MultiTapeTM.runFrom_succ_eq_step']; exact hX _ q hq hx
  apply hT
  rw [show T = (t + 1) + (T - (t + 1)) by omega, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_of_halt _ h1]
  exact h1

/-- The output of a run extends the starting output. -/
lemma runFrom_output_extends (M : MultiTapeTM K Sym St) (c : Cfg K Sym St input) (t : ℕ) :
    ∃ u, (M.runFrom c t).output = c.output ++ u := by
  induction t with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u ++ (M.outputSymbol (M.runFrom c t)).toList, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, hu, List.append_assoc]

/-- If `M` halts at once at the states of `X`, writing `β`, a run of `M` ending with exactly
one more symbol `b ≠ β` does not visit `X` before its end.

**Proof sketch.** A visit at time `t < T` halts the run at `t + 1` with output `o ++ [β]`,
where `o` extends the starting output `o₀` (`runFrom_output_extends`); this is the final
output `o₀ ++ [b]`, so `o = o₀` and `β = b`. -/
lemma avoid_of_halt (M : MultiTapeTM K Sym St) (X : St → Prop) (β : Sym)
    (hX : ∀ (c : Cfg K Sym St input) q, c.state = some q → X q →
      (M.step c).state = none ∧ (M.step c).output = c.output ++ [β])
    (c : Cfg K Sym St input) (T : ℕ) (b : Sym) (hT : (M.runFrom c T).output = c.output ++ [b])
    (hb : b ≠ β) : ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q := by
  intro t ht q hq hx
  obtain ⟨h1, h2⟩ := hX _ q hq hx
  rw [← MultiTapeTM.runFrom_succ_eq_step'] at h1 h2
  have e : M.runFrom c T = M.runFrom c (t + 1) := by
    rw [show T = (t + 1) + (T - (t + 1)) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ h1]
  obtain ⟨u, hu⟩ := runFrom_output_extends M c t
  rw [e, h2, hu, List.append_assoc] at hT
  have hu' := List.append_cancel_left hT
  rcases u with _ | ⟨y, u⟩
  · simp only [List.nil_append, List.cons.injEq, and_true] at hu'
    exact hb hu'.symm
  · simp at hu'

/-- The space of a branch is bounded by the sizes of ranges containing every head after every
prefix of the choice word. -/
lemma spaceUsedWith_le_of_ranges (N : NDTM K Sym St) (w : List Bool) (c : Cfg K Sym St input)
    (lo hi : Fin K → ℤ)
    (h : ∀ u : List Bool, u.length ≤ w.length → ∀ i, lo i ≤ (N.runWith u c).workTapePos i ∧
      (N.runWith u c).workTapePos i ≤ hi i) :
    N.spaceUsedWith w c ≤ ∑ i, (hi i - lo i + 1).toNat := by
  unfold NDTM.spaceUsedWith
  refine Finset.sum_le_sum fun i _ => ?_
  have hsub : N.visitedWith w c i ⊆ Finset.Icc (lo i) (hi i) := by
    intro z hz
    simp only [NDTM.visitedWith, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact h _ (by simp) i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Int.card_Icc]
  congr 1
  ring

end Generic

/-! ## The compiled nondeterministic machine -/

section Construction

variable {m d kD : ℕ} {Λ SD : Type}

/-- The targets of the `choose` whose fragment starts at a compiled state (`none` elsewhere). -/
def nchoice (A : NARM m d Λ) : CSt (Λ × Ph) SD m → Option (Λ × Λ)
  | .prog (l, ph) => if ph = .start then (A l).targets else none
  | _ => none

/-- A compiled state with `choose` targets is the start state of a `choose` fragment. -/
lemma nchoice_spec {A : NARM m d Λ} {q : CSt (Λ × Ph) SD m} {l₁ l₀ : Λ}
    (h : nchoice A q = some (l₁, l₀)) : ∃ l, q = .prog (l, .start) ∧ A l = .choose l₁ l₀ := by
  match q, h with
  | .prog (l, ph), h =>
    simp only [nchoice] at h
    split_ifs at h with hph
    · subst hph
      refine ⟨l, rfl, ?_⟩
      cases hA : A l with
      | det i => rw [hA] at h; simp [NIns.targets] at h
      | choose a b => rw [hA] at h; simp only [NIns.targets, Option.some.injEq,
          Prod.mk.injEq] at h; rw [h.1, h.2]

/-- **The compiled nondeterministic machine** of a nondeterministic abstract register machine
`A` with start label `l₀`, calling the deciders `D` from the start states `q0 j`: at the start
state of a `choose l₁ l₀'` fragment, choice bit `b` moves to the start of `l₁` (if `b`) or
`l₀'`; everywhere else both choices make the step of the compiled deterministic part. -/
def ncompileTM (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    NDTM (m + kD) Bool (CSt (Λ × Ph) SD m) where
  q₀ := .prog (l₀, .start)
  tr b q a w :=
    match nchoice A q with
    | some (l₁, l₀') => goAct (.prog ((if b then l₁ else l₀'), .start))
    | none => ctr (armProg (A.detPart false) l₀) D q0 q a w

/-- The compiled nondeterministic machine as a bundled finite nondeterministic machine. -/
def ncompileFinNDTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinNDTM Bool where
  k := m + kD
  State := CSt (Λ × Ph) SD m
  tm := ncompileTM A l₀ D q0

/-- The transition table of a compiled program depends on the program only through its call
nodes, and its transitions at the program states visited. -/
lemma ctr_congr {Λ' : Type} {P P' : RProg m d Λ'} (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (q : CSt Λ' SD m) (hcall : P.call = P'.call)
    (htr : ∀ s, q = .prog s → P.tm.tr s = P'.tm.tr s) : ctr P D q0 q = ctr P' D q0 q := by
  funext a w
  cases q with
  | prog s => simp only [ctr, hcall, htr s rfl]
  | sim l q s par dir res => simp only [ctr, hcall]
  | ret1 l s dir res => rfl
  | ret2 l s dir res => simp only [ctr, hcall]
  | retR l s dir res a' scan => simp only [ctr, hcall]

/-- The call nodes of the compiled deterministic parts do not depend on the answer at the
`choose` labels. -/
lemma armProg_detPart_call (A : NARM m d Λ) (l₀ : Λ) (β β' : Bool) :
    (armProg (A.detPart β) l₀).call = (armProg (A.detPart β') l₀).call := by
  funext q
  obtain ⟨l, ph⟩ := q
  show insCall (A.detPart β l) ph = insCall (A.detPart β' l) ph
  cases hA : A l with
  | det i => rw [NARM.detPart_det hA, NARM.detPart_det hA]
  | choose l₁ l₀' => rw [NARM.detPart_choose hA, NARM.detPart_choose hA]; rfl

/-- **Away from the `choose` start states, both choices of the compiled nondeterministic
machine make the step of the compiled deterministic part `A.detPart β`**, for either `β`. -/
lemma ncompileTM_tr (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    {q : CSt (Λ × Ph) SD m} (hq : nchoice A q = none) (b β : Bool) :
    (ncompileTM A l₀ D q0).tr b q =
      (compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).tr q := by
  funext a w
  simp only [ncompileTM, compileTM, hq]
  rw [ctr_congr D q0 q (armProg_detPart_call A l₀ false β) ?_]
  rintro ⟨l, ph⟩ rfl
  funext a' w'
  show insTr (A.detPart false l) l ph a' w' = insTr (A.detPart β l) l ph a' w'
  cases hA : A l with
  | det i => rw [NARM.detPart_det hA, NARM.detPart_det hA]
  | choose l₁ l₀' =>
    have hph : ph ≠ .start := by
      rintro rfl; simp [nchoice, hA, NIns.targets] at hq
    rw [NARM.detPart_choose hA, NARM.detPart_choose hA]
    cases ph <;> first | exact absurd rfl hph | rfl

/-- **At a `choose` start state the compiled deterministic part halts at once, writing `β`.** -/
lemma detPart_step_choose (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (β : Bool) {x : List Bool} (c : Cfg (m + kD) Bool (CSt (Λ × Ph) SD m) x)
    (q : CSt (Λ × Ph) SD m) (hc : c.state = some q) (hq : nchoice A q ≠ none) :
    ((compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).step c).state = none ∧
      ((compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).step c).output =
        c.output ++ [β] := by
  obtain ⟨⟨l₁, l₀'⟩, hq'⟩ := Option.ne_none_iff_exists'.mp hq
  obtain ⟨l, rfl, hA⟩ := nchoice_spec hq'
  have hcall : (armProg (A.detPart β) l₀).call (l, .start) = none := by
    show insCall (A.detPart β l) .start = none
    rw [NARM.detPart_choose hA]; rfl
  have htr : ∀ a w, (armProg (A.detPart β) l₀).tm.tr (l, .start) a w = retAct β := by
    intro a w
    show insTr (A.detPart β l) l .start a w = retAct β
    rw [NARM.detPart_choose hA]; rfl
  unfold MultiTapeTM.step
  rw [hc]
  simp only [compileTM, ctr, hcall, htr, retAct, Action.apply]
  exact ⟨rfl, by simp⟩

/-- **A `choose` is one control step** of the compiled nondeterministic machine: from the
compiled program configuration at `l` the choice bit `b` moves to that at `l₁` or `l₀'`. -/
lemma ncompileTM_stepWith_choose (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) {x : List Bool} {l l₁ l₀' : Λ} (hA : A l = .choose l₁ l₀') (b : Bool)
    (v : Fin m → ℕ) (out : List Bool) :
    (ncompileTM A l₀ D q0).stepWith b (seam (kD := kD) (SD := SD) (aseam x l v out)) =
      seam (aseam x (if b then l₁ else l₀') v out) := by
  have hs : (seam (kD := kD) (SD := SD) (aseam x l v out)).state = some (.prog (l, .start)) :=
    rfl
  have hn : nchoice (SD := SD) A (.prog (l, .start)) = some (l₁, l₀') := by
    simp [nchoice, hA, NIns.targets]
  unfold NDTM.stepWith
  rw [hs]
  simp only [ncompileTM, hn]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [goAct, Action.apply, seam, aseam]
  · simp [goAct, Action.apply, seam, aseam]
  · funext i; simp [goAct, Action.apply, seam, aseam]
  · funext i; simp [goAct, Action.apply, seam, aseam]
  · simp [goAct, Action.apply, seam, aseam]

/-- The initial configuration of the compiled nondeterministic machine is the compiled program
configuration of the start label with all registers `0`. -/
lemma ncompileTM_init (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (ncompileTM A l₀ D q0).initCfg x = seam (aseam x l₀ (fun _ => 0) []) := by
  rw [← init_eq_aseam]
  exact seam_init (armProg (A.detPart false) l₀) (l₀, .start) D q0 x

end Construction

/-! ## Deterministic steps on every branch -/

section Steps

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- A compiled configuration with register heads in `[-1, W]` and decider heads in `[-B, B]`. -/
def NBox {St : Type} (W B : ℕ) (C : Cfg (m + kD) Bool St x) : Prop :=
  (∀ r : Fin m, (-1 : ℤ) ≤ C.workTapePos (Fin.castAdd kD r) ∧
    C.workTapePos (Fin.castAdd kD r) ≤ W) ∧
  ∀ i : Fin kD, |C.workTapePos (Fin.natAdd m i)| ≤ B

/-- The compiled program configuration of an abstract configuration is in the box. -/
lemma nbox_seam {St : Type} (W B : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) :
    NBox (kD := kD) (St := CSt (Λ × Ph) St m) W B (seam (aseam x l v out)) :=
  ⟨fun r => by simp [seam, aseam], fun i => by simp [seam]⟩

/-- **A live deterministic step on every branch.** If, at a deterministic label, the abstract
machine steps from `(l, v)` to the live `(l', v')`, with the preconditions and register widths
of `arm_step`, then there is `S` such that every choice word of length `S` drives the compiled
nondeterministic machine from the compiled configuration of `(l, v)` to that of `(l', v')`,
every word of length at most `S` staying in the box.

**Proof sketch.** `arm_step` for `A.detPart false` and `compile_correct_from` give a run of
the compiled deterministic part `M` reaching the seam of `(l', v')`, in the box. It ends live,
so it avoids the `choose` start states (`avoid_of_live`, `detPart_step_choose`), and every
branch follows it (`ndtm_runWith_eq_runFrom`, `ncompileTM_tr`). -/
theorem ndet_live (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l l' : Λ) (v v' : Fin m → ℕ)
    (out : List Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (some l', v', none))
    (hp : NPre A oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    ∃ S, (∀ u : List Bool, u.length ≤ S →
        NBox W B ((ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)))) ∧
      ∀ u : List Bool, u.length = S →
        (ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)) = seam (aseam x l' v' out) := by
  obtain ⟨T, e, hinv⟩ := arm_step (A.detPart false) l₀ oracle D q0 B W l l' v v' out hs hp hw
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart false) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        rw [e]; simp [aseam])
    (fun t ht => (hinv t ht).2)
  set M := compileTM (armProg (A.detPart false) l₀) (l₀, .start) D q0
  have hX := avoid_of_live M (fun q => nchoice A q ≠ none)
    (fun c q hc hq => (detPart_step_choose A l₀ D q0 false c q hc hq).1)
    (seam (aseam x l v out)) S (by rw [hS, e]; simp [seam, aseam])
  have hag := ndtm_runWith_eq_runFrom (ncompileTM A l₀ D q0) M (fun q => nchoice A q ≠ none)
    (fun b q hq => ncompileTM_tr A l₀ D q0 (not_not.mp hq) b false) _ S hX
  refine ⟨S, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hag u hu]; exact hb u.length hu
  · rw [hag u hu.le, hu, hS, e]

/-- **A halting deterministic step on every branch.** If, at a deterministic label, the
abstract machine halts from `(l, v)` with answer `b₀`, with the preconditions and register
widths of `arm_run`, then there are `S` and a halted configuration with output `out ++ [b₀]`
reached by every choice word of length `S` from the compiled configuration of `(l, v)`, every
word of length at most `S` staying in the box.

**Proof sketch.** As `ndet_live`, with `arm_run` (one step) for the deterministic part
`A.detPart (!b₀)`: its run ends with answer `b₀ ≠ !b₀`, so it avoids the `choose` start states,
where it would answer `!b₀` (`avoid_of_halt`). -/
theorem ndet_halt (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l : Λ) {i : Ins m d Λ}
    (hA : A l = .det i) (v : Fin m → ℕ) (out : List Bool) (b₀ : Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (none, v, some b₀))
    (hp : NPre A oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    ∃ S Cf, (∀ u : List Bool, u.length ≤ S →
        NBox W B ((ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)))) ∧
      (∀ u : List Bool, u.length = S →
        (ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)) = Cf) ∧
      Cf.state = none ∧ Cf.output = out ++ [b₀] := by
  have hs' : astep (A.detPart (!b₀)) oracle x (some l, v, none) = (none, v, some b₀) := by
    rw [← nastep_det hA (!b₀) false, nastep_det hA false false]; exact hs
  obtain ⟨T, e1, e2, e3, hinv⟩ := arm_run (x := x) (A.detPart (!b₀)) l₀ oracle D q0 B W 1 l v out b₀
    (by simp [arun, hs']) (by simp [arun, hs'])
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      exact ⟨(pre_detPart D q0 B (!b₀) _).2 hp, hw⟩)
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart (!b₀)) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        exact e3 r)
    (fun t ht => (hinv t ht).2)
  set M := compileTM (armProg (A.detPart (!b₀)) l₀) (l₀, .start) D q0
  have hX := avoid_of_halt M (fun q => nchoice A q ≠ none) (!b₀)
    (fun c q hc hq => detPart_step_choose A l₀ D q0 (!b₀) c q hc hq)
    (seam (aseam x l v out)) S b₀ (by rw [hS]; exact e2) (by cases b₀ <;> simp)
  have hag := ndtm_runWith_eq_runFrom (ncompileTM A l₀ D q0) M (fun q => nchoice A q ≠ none)
    (fun b q hq => ncompileTM_tr A l₀ D q0 (not_not.mp hq) b (!b₀)) _ S hX
  refine ⟨S, seam (rrun (armProg (A.detPart (!b₀)) l₀) oracle (aseam x l v out) T),
    fun u hu => ?_, fun u hu => ?_, seam_state_none _ e1, e2⟩
  · rw [hag u hu]; exact hb u.length hu
  · rw [hag u hu.le, hu, hS]

end Steps

end Complexity.LogProg
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
