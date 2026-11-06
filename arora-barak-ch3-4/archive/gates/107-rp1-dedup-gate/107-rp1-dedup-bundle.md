## ===== campaign/gates/107-rp1-dedup/pack.md =====

# External audit pack: dedup RP-1, definitional reads re-pointed to #196's equations (PR #216, a dedup gate)

## Why this PR

The dedup window (12.2c) started on 2026-11-06 (the user). It retires the ledger's families one PR
at a time. **RP-1** (`campaign/duplication-ledger.md`) is rule 10 debt rather than duplication.
#196 published `Iff.rfl` characterizations for seven definitions:

| Definition | Home | Equation(s) |
|---|---|---|
| `Complexity.WalkLe` | `Logspace/PathWalk` | `walkLe_zero_iff`, `walkLe_succ_iff_head` |
| `Complexity.Codec.StepRel` | `Codec/Bridge` | `stepRel_iff_mem` |
| `Complexity.ExpBFS.RCode` | `ExpBFS/Radius` | `rcode_iff_reflTransGen` |
| `Complexity.ExpBFS.WinRun` | `ExpBFS/Radius` | `winRun_iff` |
| `Complexity.LogProg.SavitchARM.Rel` | `SavitchARM/Recursion` | `rel_iff_orc` |
| `Complexity.LogProg.SavitchARM.InitO` | `SavitchARM/Search` | `initO_iff_orc` |
| `Complexity.LogProg.SavitchARM.AccO` | `SavitchARM/Search` | `accO_iff_orc` |

Proofs in other files, mostly Hydroxyi's (mechanical edits allowed with an FYI, the user,
2026-11-06), still read these definitions by unfolding them (`simp [WalkLe]`, `rw [RCode]`) or
through their definitional equality: `exact h` across the definition, anonymous constructors,
`rintro` patterns. The ledger recorded 10 sites. A scoping pass, and then an exhaustive
irreducibility probe, widened the family to **23 public proof bodies in 14 files**. All of them
now go through the equations.

**The PR:** #216 on `lean/dedup-rp1`, head `485cfbab` (full hash in the bundle header). The
commits are:
- the change `f200144b`;
- `cl_iff`'s proof sketch, `3d0f6ceb` (after the re-point it is a 21-line proof, which policy
  requires to have a sketch);
- merges of the campaign, the last at `485cfbab`, after #208, #212 and #213 merged.

The change touches 14 files, with 75 lines added and 57 removed at the merged head against the
campaign's Lean `a28b8c42` (`evidence/landing/rp1-merged.diff`).

## What changed (verify)

Every changed declaration keeps its statement. Only proof bodies change, plus `cl_iff`'s docstring
sketch (`evidence/freeze/`, 14 files):

| File | Public bodies changed |
|---|---|
| `ClassPSPACE/TQBFHardMachine` | `TQBFHard.reflTransGen_stepRel` |
| `Randomized/BPLInP` | `BPLInP.entryW_eq` |
| `Randomized/BPLInPCount` | `BPLInP.stepRel_iff` |
| `SpaceComplexity/ExpBFS/Main` | `ExpBFS.cl_iff` (and its sketch), `ExpBFS.stp_orcN` |
| `SpaceComplexity/ExpBFS/Radius` | `ExpBFS.rcode_iff` |
| `Logspace/ISCountGenRadius` | `ISGen.mem_ball_iff_rcode`, `ISGen.mem_of_exists_acc`, `ISGen.one_le_card_rset` |
| `Logspace/ISCountGenStage` | `ISGen.guloop`, `ISGen.gvloop` |
| `Logspace/ISCountGenWalk` | `ISGen.gwalk_loop`, `ISGen.gwalk_spec` |
| `Logspace/ISCountMath` | `ISCount.card_ball_zero`, `ISCount.walkLe_lt`, `ISCount.walkLe_succ_iff` |
| `Logspace/PathHard` | `PathHard.red_mem_iff` |
| `Logspace/PathHardRegs` | `PathHard.orc_step` |
| `Logspace/PathWalkMachine` | `LogProg.ps_walk` |
| `SavitchARM/Correct` | `SavitchARM.accO_orcN`, `initO_orcN`, `rel_orcN` |
| `SavitchARM/Reach` | `SavitchARM.mem_iff_reach` |

There are no new declarations, no removed declarations, no import changes and no private
changes. Public counts are equal before and after in every file.

`SavitchARM/Reach`'s `mem_iff_reach` is the one site found only by the probe. It passed a
`stepLang` membership where `StepRel` was expected, and is now
`fun j hj => stepRel_iff_mem.mpr (hstep j hj)`.

`ISCountMath`'s `walkLe_succ_iff` is itself a copy of `PathWalk`'s step equation, a separate
family (**WL-1**). The user ruled that it moves into `PathWalk` as `Complexity.walkLe_succ_iff`
after this PR merges. Here only its body is re-pointed.

## Brief for the auditor

1. **Completeness:** does any proof outside the seven home files still read one of the seven
   definitions other than through its equation? This covers `simp`/`rw`/`unfold` with the
   definition's name, `show`/`change` through it, `exact` across it, anonymous constructors and
   `rintro`/`cases` patterns on it.
2. **Scope:** does the change touch anything beyond those reads? In particular, is each new body
   the old argument with the read replaced, and is `cl_iff`'s sketch accurate?

## Repository-side attestations (verify or challenge)

- **Rule 10, exhaustively** (`evidence/rule10/README.md`). Each of the 52 modules that can see a
  home file was copied with `attribute [local irreducible]` on every one of the seven definitions it
  imports, then elaborated at `f200144b`. Explicit `simp [Def]`/`rw [Def]` unfolds still work under
  `irreducible`; they were found by grep, and none remains.
  - Result: **52 modules, 0 errors**. The only failure ever seen was `Reach` before its fix.
  - Since `f200144b`, two things changed:
    - `cl_iff`'s docstring;
    - the campaign merge, which brought #208's IL-1 re-points into `ExpBFS/Main`,
      `SavitchARM/Correct`, `PathHardRegs` and `PathWalkMachine`. These are other declarations,
      citing `indicator_inputLenLang`/`indicator_inputBitLang`, and none reads the seven
      definitions.

    The probes were not re-run on the merged head; the merged-tree replay below elaborates it.
- **Freeze** (`evidence/freeze/`, merged head against `a28b8c42`): 14 files, 23 authorized public
  body changes (the table above), 0 statement changes, 0 unauthorized, 0 private changes.
- **Lint** (`evidence/lint/`, `git archive`s of both trees):
  - The campaign lint is identical at base and head:
    - `SpaceComplexity` 0 FAIL, 81 WARN over 112 files;
    - `Randomized` 0 FAIL, 51 WARN over 65 files;
    - `ClassPSPACE` 0 FAIL, 10 WARN over 14 files.
  - The policy linter over the 14 files gives the same single pre-existing finding at both. The
    round-1 `cl_iff` finding is gone.
- **Replay** (`evidence/merged-tree/`): `replay-lrp3` at `485cfbab`, the downstream closure of the
  14 files (53 modules), chained from the campaign's new snapshot `oleans-lcamp2` (the combined
  replay after #208, #212 and #213; `campaign/status/2026-11-06-campaign-replay-2/`).
  **53 modules, 0 failed.** The static check finds 0 mismatches. Its 21 `sorry` warnings are all in
  `ClassPSPACE/TQBF`, the campaign's existing ones.
- **Screen:** not run. The change replaces reads with citations and adds no proof text that could
  pair.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/107-rp1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `rp1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/107-rp1-dedup/STATUS.md =====

# Gate 107 (#216, the dedup window's RP-1, widened)

- 2026-11-06: the change `f200144b` (a sub-agent; 14 files, 24 bodies), #216 opened. The exhaustive
  rule-10 check (52 sealed probes) in `evidence/rule10/`. `replay-lrp1` running. The policy linter
  finds one new item, `cl_iff` at 21 lines without a sketch: to fix after the replay.
- 2026-11-06: `cl_iff`'s sketch (`3d0f6ceb`); the campaign merged at `485cfbab` (after #208, #212, #213). `replay-lrp3` from `oleans-lcamp2`: 53 modules, 0 failed. Freeze and lint regenerated at the merged head; pack written; staged.

## ===== campaign/standards/TEMPLATE.md =====

# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

   **Accounting inside an acknowledged family is a minor.** Once the human
   maintainer has acknowledged a debt family and named its resolution, a later
   correction to that family's *accounting* is reported at **minor**, not major.
   Examples are a missed member, a miscounted span, or an imprecise description of
   the screen. Such a correction does not change what was approved. It is a
   **major** again only if it changes the approval itself: the correction pushes a
   further file past the one-fifth threshold, reveals copies outside the
   acknowledged family's named scope, or shows the named resolution cannot work.

**Seals and reducible abbreviations.** A rule-10 seal (`attribute [local irreducible]` on
other-file definitions, each with an `rfl` control that closes unsealed and fails sealed) cannot
include a reducible `abbrev`: Lean's default reducibility validation refuses the attribute (the
unsafe override `allowUnsafeReducibility` is not used in seals). `policy.md` (*Definitions
land with their lemmas*) allows reading an abbreviation through its body, so that is not a finding.
Do report an `abbrev` passed to `simp`, `rw` or `unfold` where a published lemma exists, and a new
public `abbrev` without its lemma.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment (accounting corrections inside an already-acknowledged family are
minors; see failure mode 5); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

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

## ===== campaign/duplication-ledger.md =====

# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` and `_anchor_return` near-copies are counted as source-side members since round 7 — Catalog twins reproduce them cross-file) | **98** after RB4 (merged, PR #13 `b2833d46`; was 117 — generated, pass 4): 88 historical + 10 from pairs. RB4 deleted 12 H3 copies, the 4 relocation originals and `emLoopHost_init`; `emLoopHost_anchor_return` and `emLoopHost_start` no longer reproduce a Catalog proof after the agreement-transfer rewrite | **49.2%** (98/199) | **2,647** (was 3,153; both totals from the script's span routine, which reproduces the audited 3,153) |
| `Build/Primitives.lean` | 259 (272 before RB5) | 146 →Catalog (of the historical 150; strict 143) + **6 public originals** reproduced in Catalog (round-5 screen: `computesFunInTime_stripLast` → the adaptation `f2_strip_linear`; `_prepend`, `_pairEncodeFixed`, `_pairFst`, `_pairSnd`, `_pairConcat` → their strengthened `_spaceUsed` counterparts) | **none** — RB5 (PR #14, merged 2026-10-10) deleted the 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run`, formerly byte-identical to Loop's) | **168** after RB5 (was 173) — generated (pass 4): 145 historical (the 4 relocation members and the `splitEmbed_run` twin are deleted) + the same 23 sources of like-kind MEMBER pairs (the 6 round-5 publics, round-6 `emitterP2_control`, and 16 found by the complete round-7 pass: `emitterAppend_run`, `emitterP2EraseTM`, `emitterP2StateDecidableEq`, `emitterP2_erase_scan`, `emitterP2_prepare_rewind_candidate`/`_suffix`, `emitterSplit_find`/`_loop_bound`/`_of_body`/`_result`, `emitterTokenTM`, `emitterToken_double`/`_separator`, `emitter_first_entry`, `mapCfg`, `mapStart`) | **64.9%** (was 63.6%) | **3,790** before RB5 (3,415 + 375 round 7); not re-measured after it |
| `CookLevin/Hardness.lean` | 545 (549 before RB5) | 0 | **none** — RB5 deleted the 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run`) and `clMap_run`. Not copy debt, but recorded: its replacement certified-layout layer `clPlacement` is a private generic adapter, scheduled for dissolution as 12.2c item 13 | **0** (was 4) | **0%** | 0 (was 73) |
| `Build/Catalog.lean` | 428 (423 at the R1 close, plus the five §12.6 framed contracts) | 2 in-file originals (`f2_finSumEquiv`, `f2_sum_add` — their `a2_` copies are normalized-identical, round-3 verified) | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` copies + **3 Composition-sourced** (`f2_idTM`, `f2_idTM_run`, `f2_constTM` — maintainer-reconciled normalized-identical to `Composition.lean`'s originals) + **20 counter-block members** (`f2_counterInc` … `f2_counter_computes` — maintainer reconciliation, declaration by declaration: **19 normalized-identical** to `ClassP/TimeConstructible.lean`'s originals, and `f2_counter_computes` a **near-copy adaptation** of the proof body of the public `timeConstructible_id`) + **7 strengthened public counterparts** whose time conjuncts reproduce a public source proof (`computesFunInTime_id_spaceUsed`/`_const_spaceUsed` ← `Composition.lean`, round 4; `_prepend`/`_pairEncodeFixed`/`_pairFst`/`_pairSnd`/`_pairConcat_spaceUsed` ← `Build/Primitives.lean`, round 5 — 89-100% of each source proof reproduced) + **2 F2A adaptations** of public proofs (`f2_strip_linear` ← `computesFunInTime_stripLast`, 86% of the source reproduced — round-5 finding R5-1; `f2_counter_heads` ← `timeConstructible_id`, 64% — round-5 screen) + **20 round-6 members** from the exhaustive screen: R6-1's `f2_counter_count_space` (80.3% of the private `counter_count`) and 19 further cross-file adaptations — 4 F2A (`f2_exists_loopFind_space` 97.8% of `exists_loopFindTM`, `f2_cond_time` 92.0% of Wrappers' `computesFunInTime_cond`, `f2_rewind_heads` 90.8% of `catalogRewind`, `f2_cond_ledger` 70.3% of `timed_start`), 13 A2 (`a2_map_block`/`_suffix`/`_backA`/`_backB`/`_parse`/`_setup`, `a2_mapVirtual_run`, `a2_mapSetup_stationary`/`_run`/`_heads`, `a2_call_run`, `a2_loop_prepare` 86.8% of `loopHost_prepare`, `a2_loop_round`), and 2 public rows (`computesFunInTime_pairLenCheck_spaceUsed` 71.4% of `computesFunInTime_pairFst`; `exists_loopTM_spaceUsed` 85.5% of `exists_loopCfgTM`, 81.0% of `exists_loopTM`) | **318** | **74.3%** (75.2% of 423 at the R1 close; strict — excluding the 34 strengthened counterparts/adaptations and the 1 near-copy: **283, 66.1%**) | **7,539** (6,267 round-4 measured + 224 round 5 + 52 R6-1 + 996 for the 19) |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 + 1 round-6 source (the public `computesFunInTime_cond`) | 0 | **19** — generated (pass 4): 17 historical + `computesFunInTime_cond` (round 6) + `captureCfg` (round 7) | **65.5%** | **355** (297 + 40 + 18) |
| `ClassP/TimeConstructible.lean` | 21 | 20 (the 19 identical counter originals + `timeConstructible_id`, the source of both the near-copy `f2_counter_computes` and the adaptation `f2_counter_heads`; the private `counter_count` is likewise the source of R6-1's `f2_counter_count_space`) | 0 | **20** | **95.2%** (strict: 19, 90.5%) | 355 (round-4 measured) |
| `TuringMachine/Composition.lean` | 19 | 5 (`idTM`, `idTM_run`, `constTM` + the public `computesFunInTime_id`, `computesFunInTime_const` whose proofs the Catalog rows reproduce) | 0 | **6** — generated (pass 4): + `controlCfg_run` (R7-1) | **31.6%** (strict: 3, 15.8%) | **109** (97 + 12) |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean` | — | 0 | 0 | 0 | 0% | 0 |
| `Codes2Tape.lean` (ZF-B/B2/B3, integrated 2026-10-10) | 49 (9 pub + 40 priv; B3 added 16 new, non-copy privates) | 0 | **23 format-specific adaptations** of `CodeParser.lean`'s / `MathlibBridge.lean`'s one-tape top layer (20 retargeted + `zfBParse_full`/`zfBCanonical`/`zfBCanonical_eq`; agent-measured 60–100% body share) — the 46 format-independent copies were deleted after the promotion (f171767f) | **23** | **46.9%** (strict 3, 6.1%) | 290 code lines (agent-measured) — over one fifth: `backlog.md` §1 CH34-D2, **ACKNOWLEDGED (user, 2026-10-10) → 12.2c tasklist item 8** |
| `Robustness/SingleTape.lean` (ZF-C2) | 100 | 0 | 0 — **3 in-file near-duplicates noted, uncounted** per the in-file convention (maintainer screen: `dgPos_move` 93.1% of `sweepPos_move`, `dgStart` 72.9% of `sweepStart`, `dgInput_read` 64.3% of `sweepInput_read`; the agent disclosed the first and third as borderline) | 0 | 0% | 0 |

**Reconciliation notes (rounds 3-4 repairs)**: the F2A report's 306
inventory entries decompose as **150 Primitives + 94 Loop + 10 Wrappers +
3 Composition copies + 20 counter members + 2 in-file originals + 7
adaptations (`f2_strip_linear`, `f2_counter_heads`, round 5;
`f2_counter_count_space`, `f2_exists_loopFind_space`, `f2_cond_time`,
`f2_rewind_heads`, `f2_cond_ledger`, round 6) + 20 nonmembers** (the
round-4 correction: the old "29 outside" wrongly included the two counted
in-file originals); the 20 share no member-level material with any
declaration of the five source files (round-6 exhaustive screen below) (the `f2_polyHeads`/`f2_space_of_time`/
`f2_segment_heads`-class engines and strengthenings — round-4 sampled and
accepted). The A2 report's 45 declarations contribute 2 in-file copies +
`a2_loop_halted_run` (in the Loop 95) + **13 cross-file adaptations**
(round-6 screen) + 29 new constructions. Catalog's union:
`318 = 286 F2A + 16 A2 + 7 earlier redirect + 9 public counterparts`.

**The public-proof screen (round-5 repair of R4-1; R5-1/R5-2/R5-3).**
Published as `audits/evidence/retrofit/r1-public-proof-screen.py` with its
output `r1-public-proof-screen.out`. *Erratum:* the round-4 run tested
whether a source proof was contained **whole** in its counterpart, but the
round-4 text described "segments ≥ 60 characters". The round-5 auditor ran
the method as described and found six fragment hits that the containment
test could not see. The method below is the one actually run.

- **Method.** Strip comments and all whitespace. Rename each source
  identifier `h` to `f2_h` wherever Catalog declares `f2_h` (dotted names
  split). Report two measures:
  - the **longest common contiguous segment** (LCS), with the literal ≥ 60
    candidate threshold;
  - the **shared length**: greedy string tiling with blocks of at least 25
    characters, as a fraction of the **source** proof.
- **Rule.** A pair is a **member** when at least half of the source proof
  reappears in the target, with an absolute floor of 60 shared characters
  so that a one-line citation of a public lemma counts as reuse. Any other
  shared tiling of at least 60 characters is a recorded **fragment**, not
  counted. The rest are citations or no match.
- **Population (R5-3).** 17 eligible pairs: 2 from Composition (`id`,
  `const`) and **15** from Primitives, not the 16 stated in round 4. Five
  source theorems have no `_spaceUsed` counterpart: `ifEq`, `comp`,
  `splitSolveWith`, `unaryToken`, `appendBit`.
- **Pass 1, direct pairs.**
  - Members (7): `id` 96.5%, `const` 97.1%, `prepend` 93.9%,
    `pairEncodeFixed` 100%, `pairFst`/`pairSnd` 88.8%, `pairConcat`
    88.7%.
  - Fragments, recorded and not counted (3): `polyUnary` (119 characters
    shared, 46.7%); `pairLenCheck` (305, 21.9%; its LCS is the 91-character
    `Nat.pow_one` bound); `stripLast` (221, 11.7%; its LCS is the
    121-character `have hn` weakening).
  - Citations or no match (7): `lengthBits`, `polyBits`, `pairValid`,
    `pairDup`, `pairMapSnd`, `splitSolve` (the auditor's 27-character
    citation), `incFixed`.
  - The literal ≥ 60 LCS screen reproduces the auditor's hit set exactly
    (`id` 776, `const` 273, and 62/75/75/75/91/121 for the six Primitives
    pairs). One member falls below the 60-character LCS threshold:
    `pairEncodeFixed`, whose longest block is 53 characters but whose whole
    91-character source proof reappears. This is why the rule measures
    coverage, not contiguity alone.
- **Pass 2, residual helpers.** Each of the 27 nonmembers recorded in
  round 4 is screened against every public proof of Composition,
  Primitives and TimeConstructible, taking the best match by shared length.
  - Members (2): `f2_strip_linear` (86.0% of `computesFunInTime_stripLast`;
    R5-1) and `f2_counter_heads` (64.1% of `timeConstructible_id`; the
    auditor's 215-character partial-reuse candidate, which crosses the
    member bar once measured by tiling).
  - Fragments, recorded (6): `f2_counter_count_space` 6.5%,
    `f2_unary_sharp` 35.7%, `f2_cond_time` 30.0% (vs
    `bufferedCompTM_computesInTime`, a candidate the auditor did not list),
    `f2_rewind_scan_heads` 7.4%, `f2_rewind_heads` 6.0%,
    `f2_cond_ledger` 11.7%.
  - The remaining 19 share under 60 characters with any public proof.
- **Round-6 repair (R6-1, R6-5): pass 3, exhaustive.** Round 6 found
  R6-1, which the public-only residual pass could not see. Pass 3 replaces
  that scope limit. **Every one of Catalog's 124 non-members** (all of
  Catalog minus the post-R6-1 299-member union, computed by name in the
  script) is screened against **every declaration, public and private, of
  Composition, Primitives, TimeConstructible, Loop and Wrappers** (553
  declarations, of which 542 have an extracted body of at least 25
  characters; the other 11 cannot reach the 60-character floor). An exact 25-character prefilter is used; it loses nothing,
  because every tile is at least 25 characters. Verdicts compare like with
  like, proof with proof and term with term, so a proof that spells out a
  definition's term is reported as a restatement and not counted. **Every**
  qualifying pair is printed, not just each target's best match (R6-5).
  - Result: **19 cross-file members**, all counted in the Catalog row
    above. *Round-7 correction:* the round-6 text derived the source side
    from each target's best match only, giving "6 new source-side members"
    (R7-1). Pass 4 below replaces that hand step.
  - Five A2 members reproduce just over half of one 129-character Loop
    proof, `emLoop_run_prefix`. They are counted, as the rule requires,
    and flagged as low-coverage.
- **Round-7 repair (R7-1, R7-2): pass 4 generates the census.** No
  per-file member count is assembled by hand any more. **Pass 4** runs the
  like-kind rule over **all 423 Catalog declarations**, not only the
  non-members, against all five source files: 537 like-kind MEMBER pairs.
  **Every** pair's source joins its file's member set, together with the
  historical rules, stated by name in the script: f2_-twins, the
  `a2_loop_halted_run` twin, the relocation family, the 13 H3 copies, the
  counter block and `catalog_` twins. The script prints each file's count
  and every member beyond the historical rules, with spans. The rows above
  quote it.
  - Pass 4 reproduces the auditor's R7-1 additions (`controlCfg_run`,
    `emCall_right_run`, `exists_emitLoopTM`).
  - It also finds **24 further source-side members** (Primitives 16, Loop
    7, Wrappers 1). These are source declarations that a Catalog twin of a
    *sibling* declaration reproduces by more than half, so their material
    is duplicated in Catalog. Two of them are Loop's H3 near-copies
    `emLoopHost_init` and `emLoopHost_anchor_return`, previously
    "noted, uncounted"; they are now counted through the cross-file path.
  - Catalog is unchanged at 318.
  - **R7-2:** the body extractor now handles equation-style definitions and
    inductives (text from the first depth-0 `|` or `where`). The population
    labels are exact: 553 source declarations, 542 with an extracted body
    of at least 25 characters; the other 11 are genuinely shorter. Pass 3b
    carries the kind guard: **107 like-kind in-file pairs over 62 targets
    (12 at 90% or more), plus 2 restatements** (`f2_cond_ledger` ~
    `f2_timedReadyCfg`, `a2_loop_prepare` ~ `f2_loopReady`).
- **The membership rule in one sentence.** A declaration is a member when
  it is a historical twin or copy, or when it is either side of a
  like-kind cross-file pair in which at least half of the source's
  extracted body, and at least 60 characters, reappears in the target. The
  **exception** is in-file near-duplicates, which are recorded (pass 3b)
  and not counted; in-file exact copies are counted.
- **Standing in-file convention, stated explicitly.** Pass 3b lists
  in-file near-duplicates among the non-members: **109 raw printed
  pairs, of which 107 are like-kind, over 62 targets**. Twelve like-kind
  pairs reach 90%, and the other 2 are kind-mismatched restatements. They
  are led by the §12 sibling
  machine rows (`transferTM` against `copyTM` 99.8%, and the
  clear/compare/increment rows), which are public constructions audited at
  the §12 and F1 gates. Per the ledger's standing convention, which counts
  in-file **exact** copies (the H3 thirteen, the `a2_mapSumEquiv`/
  `a2_map_sum` pair) and **notes in-file near-duplicates without counting
  them**, they are recorded, not counted. None is an exact copy. Their
  disposition is the 12.2c per-theme split, which factors these families.
  An in-file near-match alone never adds a member. A declaration can still
  be a member independently through a cross-file pair: Loop's
  `emLoopHost_init` and `emLoopHost_anchor_return` count because their
  Catalog twins reproduce them.
- **Coverage qualification.** The screen covers the five source files of
  Catalog's copy families, in full, at the stated thresholds. Copies from
  files outside those families, or adaptations restructured below the
  25-character tile size, are outside it.

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`) are noted,
uncounted. The H3 `_init` pair, once in this list, counts since round 7
through its cross-file Catalog correspondence.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Epoch 2, B1 (PR #26): the oracle layer and FH-1

Added at the B1 fill-gate close (`audits/b1-fill-findings.md`, finding 2).
The primary rule applies: each member is counted once per file it
inhabits, and fractions are over the file's total declarations at
`integrate/b1-oracle`. None of these files had a ledger row before.

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Disposition |
|---|---:|---|---|---:|---:|---|
| `TuringMachine/Oracle.lean` | 42 | 0 | 2: `OracleTM.runFrom_comm_of_step` (63/63 both ways against Deterministic's) and `OracleTM.ComputesInTime.output_unique` (72/87 = 83% of Finite's) | **2** | **4.8%** | Approved forced mirrors (B1 decision 6; gate note 16) |
| `TuringMachine/Deterministic.lean` | 34 | 1: `MultiTapeTM.runFrom_comm_of_step` | 0 | **1** | **2.9%** | Mirror source |
| `TuringMachine/Finite.lean` | 18 | 2: `FinTM.ComputesInTime.output_unique` (mirror source) and `MultiTapeTM.exists_first_halt` (FH-1's public form) | 0 | **2** | **11.1%** | Sources |
| `ClassNP/EXP.lean` | 153 | 0 | 1 (FH-1): `enumCont_first_halt` | **1** | **0.7%** | FH-1, to retire (`backlog.md`) |
| `ClassNP/SAT.lean` | 282 | 0 | 2 (FH-1): `sat_first_halt`, `sat_call_first_halt` | **2** | **0.7%** | FH-1 |
| `CookLevin/Hardness.lean` | 545 | 0 | 1 (FH-1): `clA5_call_first_halt` | **1** (was 0) | **0.2%** | FH-1 |
| `Build/Catalog.lean`, `Build/Loop.lean` | 428, 194 | — | FH-1: `f2_loop_first_halt`, `f2_splitCount_firstHalt` (Catalog); `loop_first_halt` (Loop) | unchanged | — | `loop_first_halt` and `f2_loop_first_halt` are a 341/341 twin pair, already counted in the Loop→Catalog family. `f2_splitCount_firstHalt` is in the F2A-22 inventory; whether it is one of Catalog's 318 members or one of the 20 F2A nonmembers is settled by the FH-1 retirement census |

The FH-1 copies predate the public form. B1 adds no copies, so no file
gains a copy in this epoch and none crosses one fifth.

**Exclusions** (screen hits that are not members, with their dispositions
in `audits/b1-integration.md`, accepted by gate note 17):

- `uw_tail` (Relativization) → E3 `OracleNDTM.stepWith_eq_of_ne_qQuery`
  (OracleNondeterministic), 57%. Glue: shared citations of the
  fixed-choice step bridge.
- `uw_scan_step` → `uw_false_step` (Relativization, in-file), 71%. Glue:
  the shared `uw_step_scan` call line. It is also uncounted under the
  in-file convention.
- `Catalog.f2_loopBody_step` → `queryTM_init` (Classes), 54%. The
  configuration-equality idiom; no machine argument is shared.
- `runFrom_ofMultiTapeTM` → `runFrom_plainEmptyOracle` (Oracle, in-file),
  53%. A screen artifact: both declarations are unchanged (gate note 18).

So Relativization, Classes and OracleNondeterministic have no members.
`OracleNondeterministic`'s private blank-cell bound moved to `Oracle.lean`
as the public `queryString_length_le_of_blank` (C1-P1). Both consumers cite
it, so no copy remains (gate note 8).

## §12.8 statement layer (PR #28)

Added at the §12.8 statement gate, round 1 (`audits/s12-8-statements-findings.md`,
finding 8 and note 38).

- **Catalog's denominator** (2026-10-11). Part 3 adds 31 public declarations,
  none of them members, bringing Catalog to 459 declarations (75 public,
  384 private). The members are unchanged, so the fraction is now
  **318/459 = 69.3%**; strict, 283/459 = 61.7%. The R1-close figure of
  318/428 is the historical snapshot. The scheduled resolution is still the
  12.2c per-theme split.
- **Same-file similarities, not members.** The screen found twelve new pairs,
  all within a file. They are uncounted under the in-file convention:
  - the four seek tables among themselves, including `seekEndTM` ←
    `skipTM` at 100%;
  - `writeConstTM` ← `writeAdvTM` at 58%.

  These are distinct small transition tables over shared phase types, with
  different stop and return behaviour; no proof is copied (gate note 38). The
  fills must use the one shared trace that the sketches promise.
- **The new files** (`SymbolLift`, `Build/Scan`, `Build/InputCall`,
  `Build/CfgRecord`) have no members.

## Wave-1 statements (PR #43): §12.8b, §12.10, §12.11

Added at the wave-1 statement gate, round 2 (`audits/wave1-statements-findings.md`, finding 2;
`audits/wave1-statements-resolutions.md`).

**Round 1's copy-side member is gone.** `CertShell.certificateShell_proj` reproduced
`Nondeterminism`'s private `certificate_split_strictMono` (82/99). By user decision
(2026-10-11) it and both disclosed re-derivations were factored, not acknowledged:

| Mirror (round 1) | Shared home now | Re-derived from it |
|---|---|---|
| certificate split uniqueness and certificate-length monotonicity (`CertShell` against `Nondeterminism`) | `TuringMachine/ChoiceWords.lean`: `append_split_unique`, `certificateLength_strictMono`, `expCertificateLength_strictMono` | `CertShell.certificateShell_proj`, `Nondeterminism`'s split proofs (five privates removed) |
| W2-0, the query-length invariant (`OracleSim` against `Oracle`/`OracleNondeterministic` privates) | `Oracle.lean`: `OracleTM.step_radius`, `OracleTM.runFrom_radius` | W2-0, `Oracle.lean`'s initialized invariant, `runWith_headBlank` |
| the choice-word certificate law (`OracleSim.mem_iff_exists_choiceOut` against `Nondeterminism.choice_certificate_iff`) | `ChoiceWords.lean`: `choiceBudget_le`, `run_take_of_halted` | both laws (`acceptsWithin_iff_of_halts`, `mem_iff_exists_choiceOut`) |

**Members after round 2.** The five statement modules and `ChoiceWords` have no members.
`Nondeterminism`'s count does not grow.

**Exclusions** (screen hits that are not members; for the gate to rule on):
- `Nondeterminism.a3n_unpad_EXP` → `ChoiceWords.expCertificateLength_strictMono`, 82/130
  (63%). A pre-existing in-file pair: the base screen shows it against the former
  `e3_split_strictMono`, also at 63%. It became cross-file when the exponential monotonicity
  moved beside its polynomial sibling. The shared text is one monotone-power inequality
  (`Nat.mul_le_mul_left C (Nat.pow_le_pow_right … (Nat.pow_le_pow_left … c))`) inside an
  unrelated padding proof. No argument is copied.
- `ChoiceWords.certificateLength_strictMono` ↔ `expCertificateLength_strictMono`, 84% / 64%:
  an in-file pair, uncounted under the in-file convention. These are two monotonicity facts
  for two different length functions, NP and NEXP; the pair was in-file in `Nondeterminism`
  before.
- `CodeSimulator.tableBitsK` reproduced by the frozen serializers: `CodeFormat.oneTapeFormat`
  (85%), `CodeFormat.codeTable2Bits` (67%), `Codes2Tape.Code2TM.serialize` (56%),
  `UniversalInterpreter.universalRecords` (56%). This is the **item-8 residual family** (the
  generic writer against the frozen writers, which cannot be redefined), with the bridges
  `tableBitsK_two` and `oneTape_serialize_eq` proving the equalities; gate round 1, note 47.
  The `universalRecords` hit is the same family, visible once round 2 screened the
  `Universal*` files.

## Watch items (design-parallel, no byte-copies)

| Item | Status |
|---|---|
| **ch7 EmitIter layer vs the §12 layer** (merged with PR #11, 2026-10-10): `Build/EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer (`padAction`/`embedCfg`/`embed_step`/`embed_run`/`SafeRun` — 18 public declarations, none private; *corrected 2026-10-10: the first version of this row called them private*), written against main (which lacks `Build/Embed.lean`) and structurally parallel to the §12 bank-embedding transformers; the emit-iteration host (`Build/EmitIterBody.lean`, 20 declarations: 1 public, 19 private — corrected at ch7 fill gate round 2, R2-3) parallels the §12/Loop host family. **Body-level screen** (`audits/evidence/ch7/ch7-fill-duplication-screen.md`; the first version of this row rested on a name screen alone): **no copies of pre-existing repository material** — none of the §12 or loop-library material matches; the ch7 modules consume main's public `exists_emitLoopTM`/`exists_emitCallTM`/`exists_installCallTM` rows by citation. This row is design duplication; the stack's own copy family is ledgered below. | **12.2c docket** (user, 2026-10-10): harmonize to one embedding layer and one host family at the per-theme split; the naming of the shared block primitive is settled there too. The ch7 fill gate (`audits/ch7-fill-pack.md`, run on the merged tree; question 7) compares the two layers as facts. Consumption embargo until that gate closes. |
| **Pre-issue shared lemmas for epoch C1** (maintainer, 2026-10-10): `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`Finite.lean`) is the bound inside Catalog's private `f2_space_of_time`; `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff` (`ClassNP/NTIME.lean`) is `DTIME_subset_NTIME`'s per-input content, which now cites it; `Complexity.SPACE.mono_const` and `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` (`SpaceComplexity/Basic.lean`). They were landed so that C1a/C1b cite instead of copying. **Residual:** `f2_space_of_time` should become a citation of the public bound in 12.2c T3 (Catalog core). Also recorded for later tranches (item 11 dossier): private live-prefix copies of `runFrom_state_ne_none_of_le` in Catalog, Hardness and SAT, and Loop's `loop_input_run_le`, which equals the public `timed_input_bound` (removed in 11A) | Watch; T3 / T2 |

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 318 expanded members (↔ Primitives/Loop/Wrappers/Composition/TimeConstructible + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| **The §12 sibling rows' in-file repetition** (`transferTM`/`copyTM`/`clearTM`/`compareTM`/`incrementTM`, their traces, framed contracts, canonical rows and space rows; pass 3b and the copy-text screen). **Grown by the §12.6 fill:** 16 new directed pairs (5,520 matched characters), against 20 gone and a net −330 characters (`audits/evidence/s12-framed-fill/copytext-diff.txt`). Examples: transfer-framed → copy-framed 97%, and increment success → overflow 90% | **12.2c item 5** on the user-consolidated tasklist (2026-10-10). The §12.6 fill gate ruled the growth inside this acknowledged family, so a minor (`audits/s12-framed-fill-findings.md` F1/F2) | the user's **12.2c**, item 5: a common scanner. Its scope now explicitly includes the generalized traces, the framed consequence proofs, the canonical specializations and the space wrappers |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **ACKNOWLEDGED (user, 2026-10-09): retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes — **RB4 merged (PR #13, 2026-10-10): 12 of 13 H3 copies deleted by Z5 transfer; `emLoopHost_prepare` survives with a rewritten proof, still counted.** The inlined residue is the row "RB4's inlined residue in Loop" below |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **the user, 2026-10-09** (the round-2 audit's R2-2 disposition) | **ACKNOWLEDGED (user, 2026-10-09): the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it — **RB4 (2026-10-10): Loop's 4 originals DELETED** (R1 embedding + injective state transport + Z5). **Primitives' and Hardness's 4 + 4 copies REMAIN.** Their generic interfaces are stronger than R1 (aliased host slots, non-injective state maps), so a literal replacement would weaken surviving statements. Continuation: **RB5 (revision 2, 2026-10-10)** promotes `runFrom_mapState_of_agreeOn` into `Build/Embed.lean` (it needs both `StateRenaming` and Z5, and only Embed already imports both), then specializes per concrete layout, Primitives before Hardness. **DISCHARGED (RB5, PR #14, merged by the user 2026-10-10):** all 12 family members are gone. Primitives' and Hardness's copies are deleted, and every relocation pair is gone from the copy-text screen (739 → 692 pairs over the four files, with no new pair). The census twin `f2_splitEmbed_run` in Catalog survives; it is now a special case of the public lemma, and 12.2c item 2 can replace it by a citation |
| **RB4's inlined residue in Loop** (post-merge copy-text finding, 2026-10-10): the forwarding host's consumers reproduce the original loop host's phase proofs. `emLoopHost_round` reproduces 100% of `loopHost_reject`; `emLoopHost_prepare` 99% of `loopHost_prepare` and 100% of `loopHost_input_rewind`; `emLoopHost_anchor_return` 95%; `emLoopHost_start` 92%. The frame pairs `emCall_bank_*` (94%) and `emCall_finish_*` (79%) grew more alike. In all, 11,476 characters of the forwarding host reproduce the original (`audits/evidence/retrofit/copy-text-screen.py`) | **ACKNOWLEDGED (user, 2026-10-10)**: RB4 accepted as merged, and RB5's Loop task withdrawn. The residue is not removable phase by phase: the `loopHost_*` lemmas state endpoints only, and the anchor-return phase runs in body control from `t = 0`, exactly where the two hosts differ (RB5's first dispatch kernel-checked the counterexample) | the user's **12.2c**, tasklist item 11: unify the two hosts structurally |
| **ch7 block stack's per-loop lemma family** (PR #11, 2026-10-10): the OR/XOR/majority loops re-prove one orbit/length/init/emit lemma set under renaming. **Census corrected at ch7 fill gate round 2 (R2-2) to the standing source-inclusive rule, as lower bounds:** `PolyTimeBlockTests` **≥ 12/25 (48%)**, `PolyTimeBlockMajority` **≥ 8/14 (57%)**, `PolyTimeBlockLoop` ≥ 1/32. The first record (4/14 and 2/25) counted copy sides only, and the round-2 auditor found four more cross-file adaptations, `anyStep`/`majStep`, `anyEmit`/`majEmit`, the orbit lemmas and the loop outputs (81–93%), plus two length correspondences (`audits/ch7-fill-r2-findings.md`). The pre-screen is `audits/evidence/ch7/ch7-fill-duplication-screen.md`, whose method description is corrected | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D1**, opened under the one-fifth rule and answered. **Extension ACKNOWLEDGED (user, 2026-10-10, round 2)**: the enlarged family and the `PolyTimeBlockTests` threshold crossing | the **12.2c** per-theme refactor (the user's own window; colleagues spared deduplication work): one generic lemma set in `PolyTimeBlockLoop`, statements unchanged, coordinated with the ch7 owner, after the ch7 fill gate closes **DISCHARGED 2026-10-11** (12.2c T1 item 7, PR #18; gate CLOSED round 1, 0/0/3 minors swept): the generic layer `Complexity.BlockLoop`; census Tests 22/25 → 0/8, Majority 12/14 → 0/6, Loop 6/32 → 0/50; six-file screen 125 / 47,734 → 41 / 10,045. Residual: the excluded `length_xorPairStep_le`/`length_sliceDropAt_le` near-copy (watch). |
| **ch7 `EmitIterEmbed` run-infrastructure re-proofs** (ch7 fill gate round 2, R2-1): five facts are re-proved rather than cited, so **≥ 5/18 = 27.8%, over one fifth**. They are `step_output_prefix` and `runFrom_output_prefix` (Loop's private `emLoop_step_prefix`/`emLoop_run_prefix`), `runFrom_output_extends` (a specialization of `Finite`'s public `MultiTapeTM.output_prefix`), `runFrom_of_halted` (`Deterministic`'s public `runFrom_of_halt`), and `state_isSome_of_runFrom` (Loop's private `loop_live_prefix`). The screen missed all five because the proofs were restructured | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D2** | the user's **12.2c**, item 6: one shared home for the run facts (output-prefix commutation and extension, halting absorption, live prefix) in `Deterministic.lean`/`Finite.lean`, beside `runFrom_of_halt`. `EmitIterEmbed`'s five become citations or re-exports, statements unchanged, and Loop's three private copies are deleted. Coordinated with the ch7 owner |
| **`Codes2Tape.lean`'s format-specific parse layer** (ZF-B/B2, 2026-10-10): 23/33 two-tape instances of `CodeParser.lean`'s one-tape top layer (69.7%; 3 strict) | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH34-D2** | the **12.2c** tasklist item 8: a format-parameterized parse layer (one-tape, two-tape, ND), statements unchanged. **DISCHARGED 2026-10-11** (PR #19, gate CLOSED round 1, 0/0/0): adaptations 23 → 1 (`zfBFallback`, approved residual); screen 117 / 29,824 → 77 / 12,563; all 44 CodeParser/Codes2Tape and 7 Codes2Tape/MathlibBridge pairs gone. Brief `briefs/ch34-t1-item8.md` (tranche T1); the generic layer's resemblance to the frozen one-tape definitions it bridges (`actionBitsK`↔`actionBits`, `codeSkipActionK`↔`codeSkipAction`, the table writer against the three frozen `serialize` bodies) is pre-named in the brief and stays as a residual watch item |

**R8.0b E1, the mandated `counterLoopTMVia`/`counterLoopTM` definition pair** (§12.8 stream D,
PR #38): `CounterLoop.counterLoopTMVia` reproduces 261/287 = 91% of the frozen
`counterLoopTM`, and 84% the other way. It is a definition pair that the R8.0b brief itself
mandated; there is no copied proof. **ACKNOWLEDGED (user, 2026-10-11)**, as a one-off exception
for exactly this pair (R8.0b gate finding F1). **Cleanup owner and window:** the maintainer, in
**12.2c**, through backlog §1 R80B-E1: redefine `counterLoopTM` as the identity-embedding
instance and re-check consumers. `CounterLoop`'s other new pair, `counterLoopTM_run_done`
↔ `_run_escape` at 83%/72%, is two Z5 re-derivations sharing transport setup. It is not a
member (gate note F8).

**RW-1, the rewind row's copies of Catalog's seek frame and skip-back table** (PR #138,
`Build/Rewind`, 2026-10-18). Two like-kind cross-file pairs, both against `Build/Catalog`:
- the private `rw_cfg` reproduces Catalog's private `catalogSeekCfg` at 79/79 = 100%, both ways:
  one record update over a different phase type; no proof is copied;
- `rewindTM` and `skipBackTM` share one contiguous 140-character block, 80% of `rewindTM`'s
  175-character body and 69% of `skipBackTM`'s 202: `rewindTM`'s table is `skipBackTM`'s
  without its first row, with `start` in the role of `gap`. Inside the same 140 characters,
  `rewindTM` also pairs with the seek tables `seekStartTM` (98 characters, 56% of `rewindTM`),
  `skipTM` (71, 55% of `skipTM`) and `seekEndTM` (92, 53% of `rewindTM`): the seek family's
  table pattern.

**Census** (the primary rule, each member counted once per file it inhabits; corrected at gate
55, finding 1: the first version counted `rw_cfg` alone, 1 of 5, and called the table pairs
design-parallel, an exception the rule does not make for cross-file pairs; the seek tables'
resemblance among themselves, §12.8 statement layer above, is uncounted only because it is
in-file):
- `Build/Rewind`, the copy side: **2 of 5 declarations (40%)** (3 public, 2 private), **20**
  lines in member blocks (`rewindTM` 14, `rw_cfg` 6), 219 characters reproduced. `RewindPhase`
  (a 48-character body, below the floor) and `rw_step` (no pair at half) are not members.
- `Build/Catalog`, the original side: **5 more members**, `catalogSeekCfg` (6 lines),
  `skipBackTM` (16), `skipTM` (13), `seekEndTM` (18) and `seekStartTM` (19), 72 lines; 5 of its
  505 declarations. The file's row is re-totalled at its next census.
- The v3 screen of the module, `Build/Catalog` and the exhaustive replay at #136's head (563
  declarations, 416 pairs) regenerates byte-identical at gate 55; screened against the whole
  library, `rewindTM` and `rw_cfg` pair with nothing else.

**Exclusion** (a screen hit that is not a member; an exception to the rule, approved by the user
on 2026-10-21): `rewindTM_run_ofCfg` → Catalog's private `a2_mapSetup_run`, 84/163 = 52%. The shared
text is two tiles, 50 and 34 characters, of the run-by-induction idiom
(`| succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih (` and
`, MultiTapeTM.runFrom_succ_eq_step'`); no setup argument is shared. Screened against the whole
library, the same idiom reaches half of 12 short run proofs in 10 files: `a2_mapSetup_run`,
`Universal`'s `timedFrame_run`, `Robustness/ObliviousSchedule`'s `maskedClock_lockstep`,
`decorateTM_run` and `parallelTM_run`, `Nondeterminism`'s `b2_unary_run`, `CircuitEvalRun`'s
`step_rej`, `Build/Seam`'s `seamCompTM_runFrom_left`, `TimeHierarchy/ClockMachine`'s
`kCfg_run`, `SymbolLift`'s `MultiTapeTM.liftSymbols_runFrom`, `Composition`'s
`controlCfg_run`, and `Build/NDHost`'s `wr_cfg_scan` (there the frame-read idiom). As with the
B1 exclusion of the configuration-equality idiom (above), it is recorded, not counted. Counted,
`Build/Rewind` would be 3/5 = 60%.

**The one-fifth rule** (`workflow.md` §4): `Build/Rewind` is past one fifth. Its §1 item is
`backlog.md` RW-1, opened and acknowledged on 2026-10-18, before gate 55's pack shipped, for the
frame alone; gate 55 widens it to the table. `Build/Catalog` was past one fifth already (D-R2).

**Acknowledgment.** The frame: **ACKNOWLEDGED (user, 2026-10-18)**, before gate 55. The table
and the exclusion: **ACKNOWLEDGED (user, 2026-10-21)** (gate 55, finding 1: the census at 40%,
the idiom hit excluded), with the retirement by unification below chosen over a frame-only one. **Cleanup owner
and window:** the user's dedup window, through backlog §1 RW-1, with Catalog's next edit: one
public frame over any state type, cited from both files; and one left-pass table, the rewind
being skip back entered at `gap`, with both framed runs derived from one public back-pass run.
After the retirement, neither file has a member from this family.

**BW-1, the buffer-word identities** (PR #140, `TuringMachine/BufferWords`, 2026-10-18): four of the
module's six public lemmas restate `Build/StepBlock`'s privates (`bufferTape_append_shift` ↔
`bufferTape_suffix`, `bufferTape_append_mid` ↔ `bufferTape_reads`, `bufferTape_eq_none_of_not_mem`
↔ `bufferTape_outside`, `bufferTape_unary` ↔ `bufferTape_unary`): the same statements, with
different proofs (the new ones read `bufferTape` only through its published equations). The
copy-text screen pairs none of them, so this is a restated-fact family, not a text copy.
**ACKNOWLEDGED (user, 2026-10-18)**, in the ruling that chose the public module. **Cleanup owner
and window:** the user's dedup window: `StepBlock` imports the module and its four privates are
deleted, their uses re-pointed. **Census** (the primary rule, each member counted once per file it
inhabits; corrected at gate 57, finding 1: the first version counted `StepBlock`'s side only,
without fractions or spans):
- `TuringMachine/BufferWords`, the original side: **4 of 6 declarations (66.7%)** (6 public,
  0 private; `_drop` and `_take` have no counterpart), **45** lines in member blocks
  (`_append_shift` 10, `_append_mid` 9, `_eq_none_of_not_mem` 10, `_unary` 16).
- `Build/StepBlock`, the copy side: **4 of 135 declarations (3.0%)** (64 public, 71 private),
  **42** lines (`bufferTape_unary` 11, `_outside` 7, `_reads` 16, `_suffix` 8).
- No copied characters: the v3 screen of the module, `Simulation`, `Build/StepBlock` and
  `Build/SeamLayout` (140 declarations, 32 pairs) pairs none of the eight, before and after
  #140's merge of the campaign branch (`7c963897`).

**The one-fifth rule** (`workflow.md` §4): `BufferWords` is past one fifth, and its §1 item is
`backlog.md` BW-1, opened and acknowledged on 2026-10-18, before gate 57's pack shipped.
`StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
file has a member.

**IW-1, the window copier's interval patch** (PR #137, `Build/InputWindow`, 2026-10-21): the
private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`: token for token after
renaming its binders (`tape`, `head`, `v` for `ct`, `cp`, `u`), and equal by `rfl`
(`@iw_patch = @wordPatch Bool`). One definition; no proof is copied. The same definition is also
`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` (written
pointwise), both from 2026-10-10; `wordPatch` (2026-10-14) is the public one. These four are the
**interval-patch family**: the tree and the open branches hold no other. The B6 F1 record named
`counterPatch` for the dedup window; `catalogTape` was not recorded before. The worker reported
"new copies: none" (`StepClock` was outside its screen population and its import context). The
maintainer disclosed the copy in gate 54's pack (question 6), and gate 54's finding 1 made it a
debt major. **Not members:** `iw_patch_append` appends one cell (Catalog's public
`catalog_write_take` states the same fact in take form, with its own proof), and `iw_patch_true`
reads the patch at the all-true word (the `Bool` case of a step inside `CounterLoop`'s proof, not
a declaration). **ACKNOWLEDGED (user, 2026-10-21)**, at gate 54, for the whole family. **Cleanup
owner and window:** the user's dedup window, through backlog §1 IW-1: `wordPatch` moves below
`Build/Catalog` with Catalog's next edit, and the three private copies re-point to it
(`InputWindow`'s re-proofs are verified at gate 54's review). **Census** (the primary rule, each
member counted once per file it inhabits; declarations as the style lint counts them; lines by
the span rule):
- `Build/InputWindow`, a copy: **1 of 17 declarations (5.9%)** (1 public, 16 private), **5**
  lines (`iw_patch`).
- `Build/StepClock`, the public one: **1 of 41 (2.4%)** (8 public, 33 private), **4** lines
  (`wordPatch`). From #139 on, **1 of 42 (2.4%)** (9 public): #139 adds `wordPatch_append`, a
  member of WA-1 below.
- `Build/CounterLoop`: **1 of 79 (1.3%)** (59 public, 20 private), **4** lines (`counterPatch`).
- `Build/Catalog`: **1 of 505 (0.2%)** (113 public, 392 private), **5** lines (`catalogTape`). It
  is in none of the correspondences behind Catalog's row above, so it adds one member there.
- Copied characters: none by the v3 screen, which pairs none of the four. After renaming, each
  is the same definition of 175 to 199 characters.

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.
`InputWindow` had no earlier copies. `Catalog` had, but #137 adds no copy to it, since
`catalogTape` predates the delivery. The §1 item IW-1 is opened anyway, as for RW-1, and
answered. After the retirement only `wordPatch` remains, in its new home.

**WA-1, the adjacent-patch law** (PR #139, `Build/StepClock`, 2026-10-18; ledgered at gate 56,
finding 2): the public `wordPatch_append`,
`wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v)`, restates
`Build/RecordTable`'s private `rt_adjacentWrites` (2026-10-13). With `wordPatch` unfolded and
beta-reduced, the two elaborated statements are alpha-equivalent: they differ only in binder
names (`tape`, `o` for `ct`, `cp`), checked on the compiled declarations at #139's merged head
(gate 56's review). The proofs differ (the new one reads `wordPatch` and `FinTM.bufferTape` only
through their published equations; `rt_adjacentWrites` unfolds `FinTM.bufferTape`), and the v3
screen pairs neither, so this is a restated-fact family, not a text copy, as BW-1 is. The F3 review
that proposed the lemma disclosed the pair, and the ruling that chose it named it (backlog §2, F3
cont1: "E2 ruled (user, 2026-10-18): B"), but it was not ledgered until gate 56.
**Acknowledgment:** the ruling of 2026-10-18 that chose option B (F3's E2). The decision put to
the user named the re-point ("which also opens the `rt_adjacentWrites` re-point"), and the
ruling's record names `rt_adjacentWrites` as the lemma's private form, to re-point in the user's
dedup window. The record does not call the pair a copy family, as the same day's BW-1 ruling
does; gate 56's review (finding 2) reads the ruling as acknowledging it. **Confirmed (user,
2026-10-22):** the ruling acknowledges the pair. **Cleanup owner and window:**
the user's dedup window, through backlog §1 WA-1, with IW-1's move: once `wordPatch`, its cell
lemmas, `wordPatch_append` and the explicit-form lemma are below `Build/Catalog`, they are in
`RecordTable`'s closure; `rt_adjacentWrites` is deleted, and its one use (`rt_advanceCfg_append`)
cites `wordPatch_append`. **Census** (the primary rule, each member counted once per file it
inhabits; declarations as the style lint counts them at #139's merged head `1cd66f1b`; lines by
the span rule):
- `Build/StepClock`, the public one: **1 of 42 declarations (2.4%)** (9 public, 33 private),
  **25** lines (`wordPatch_append`). With IW-1's `wordPatch` (4 lines), the file has **2 members
  of 42 (4.8%)**, **29** lines.
- `Build/RecordTable`, the private one: **1 of 129 (0.8%)** (29 public, 100 private), **28** lines
  (`rt_adjacentWrites`). It had no member before.
- Copied characters: none. The v3 screen of `StepClock`, `RecordTable`, `WindowClock` and
  `WindowRun` (176 declarations, 19 pairs) pairs neither.

**The one-fifth rule** (`workflow.md` §4): neither file is past one fifth. #139 adds no copy to a
file that received copies before: `StepClock`'s earlier member is IW-1's `wordPatch`, the public
original, and #139 leaves `RecordTable` byte-unchanged. The §1 item WA-1 is opened anyway, as for
RW-1 and IW-1, and answered. After the retirement only `wordPatch_append` remains, in
`wordPatch`'s new home.

**C1-E cont1, the exhaustive replay** (PR #136, `ClassNP/ExhaustiveReplay`, 2026-10-21): **no
member.** The v3 screen's 122 new pairs are all in-file (0 cross-file, 0 gone; 297 → 428
declarations, 106 → 228 pairs). 26 are at or above the brief's 90% copy threshold, between 17 of
the module's 185 declarations (9.2%): the twenty `xr_*_ne_*` one-liners, two pairs of leaf tables,
two buffer-tape facts and the replay's two exits. They are disclosed in-file siblings, listed and
justified by family in the worker's report (§8) and qualified by its erratum
(`campaign/fills/c1/reports/exhaustive-2-ERRATUM.md`); gate 53 (minor 2, note 12) found no copied
material needing acknowledgment. Their consolidation, and the re-points to the public lemmas that
arrived after the fill's base, are `backlog.md` §1 C1E-1, in the user's dedup window.

**IR-1, the input rewind family** (megafill A, 2026-10-22). Four private input rewinds, each
with its own exact-time run proof:
- `ClassNP/ExhaustiveReplay`'s `xr_inRewindTM` (#136) and UN cont1's `un_inRewTM`
  (`Diagonalization/NTimeHierarchy`, 61% and 59% on the v3 screen): a cross-file pair, which the
  UN brief forbids;
- U2-S cont1's `ss_inputRewind` (`UniversalK`, #147);
- R cont2's `ic_rewind_scan` (`TuringMachine/NDCodeSimulator`), which re-proves the public
  `Turing.FinTM.rewind_scan` (51%; `Simulation` was outside that brief's screen population, so the
  worker's screen could not see it).

With them, UN's `un_mapState_comp` shares field-equation proof text with `ExhaustiveReplay`'s
`xr_E_initCfg` (54%; their statements differ: gate 65, minor 3).
**Acknowledgment and disposition (user, 2026-10-22):** UN's two pairs are resolved by **an API PR
first**: a public input rewind with an exact time and a first-visit cut, and a `mapState`
collapse lemma. UN's landing re-points to them. R's copy lands ledgered and re-points when that
API lands. U2-S's and `ExhaustiveReplay`'s are re-pointed in the user's dedup window.
**The API: #153** (2026-10-22): `Build/InputRewind`'s `Turing.inputRewindTM` and
`inputRewindTM_run`, and `Turing.Cfg.mapState_mapState`. Its v3 screen pairs the machine with
`xr_inRewindTM` (82% and 73%), and the lemma's proof text with `xr_E_initCfg`'s (54%; a shared
idiom, not a restatement: the composition lemma alone does not replace `xr_E_initCfg`); both are
in the dedup window, as above.
**Retirements (2026-10-23):** NDHost's `guessRun_mapState_mapState` with #153; R's
`ic_rewindLeafTM`, `ic_rewind_scan` and `ic_rewind_leaf_run` with #151; the canonizer's
`canonGramMapComp` with #152; UN's `un_inRewTM`, `un_inRew_run` and `un_mapState_comp` with #154
(its landing). Remaining in IR-1: `ExhaustiveReplay`'s `xr_inRewindTM` and `xr_E_initCfg` and U2-S's
`ss_inputRewind` (`UniversalK`), in the user's dedup window. A fifth copy found while building it, `Build/NDHost`'s private
`guessRun_mapState_mapState` (the lemma's exact statement), is removed in #153 (the user's ruling).
A sixth, found 2026-10-23 on #152's branch: the canonizer's private `canonGramMapComp`
(`TuringMachine/CodeSimulator`), the lemma's statement with the composite as `fun s => g (f s)`,
used at two `rw` sites; 99% each way on the v3 screen. **Disposition (user, 2026-10-23): re-pointed
at #152's landing** (prepared locally, `local/canon-mapcomp-repoint`), as for R's leaf.

**CC7-1, the canonizer cont7's in-file families** (megafill A item 3, `TuringMachine/CodeSimulator`,
2026-10-22). 59 new in-file pairs, none cross-file. Four are at or above 90%:
`canonGramCut_leg`/`canonStageCut_leg` (97% each way), `canonStageLeg4` → `canonStageLeg1` (94%)
and `canonStageLeg5` → `canonStageLeg1` (91%). Three families: the cut leg, the leg template and
the per-record bound. **Acknowledged (user, 2026-10-22): recorded as debt**, for the user's dedup
window, together with the retirement of the now-unused `canonCounterRepeat` link (the user,
2026-10-22).
**Census** (gate 67, minor 3; the primary rule, each member counted once per file it inhabits;
declarations as the style lint counts them; lines by the span rule, at #152's head `aed162fd`):
- the members, by family (11):
  - the cut leg (2): `canonGramCut_leg` (lines 7564–7585, 22), `canonStageCut_leg` (6332–6352,
    21);
  - the leg template (7): `canonStageLeg0`–`canonStageLeg6` (6354–7046: 90, 86, 91, 109, 106,
    98 and 107 lines);
  - the per-record bound (2): `canonStageBlock_consumes` (5669–5687, 19) and the base's frozen
    private `skipTable_consumes` (233–245, 13), whose local per-record bound it re-proves (61%);
- with IR-1's `canonGramMapComp` (7595–7607, 13), a cross-file member until #152's landing
  re-points it.

`TuringMachine/CodeSimulator`: **12 of 198 declarations (6.1%)** at the head (12 public, 186
private), **775** lines in member blocks; after the re-point, **11 of 197 (5.6%)**, **762** lines.
The file had no earlier ledger member: the item-8 entry's `tableBitsK` now lives in
`Build/StepBlock`. The review's other new in-file pairs, those not between two members of these
families, are screen matches, not members: all below 90%, between declarations with different
statements. **The one-fifth rule** (`workflow.md` §4): not reached.

**SD-1, the suffix drop** (PR #161, U2's API, 2026-10-24). One fact,
`(pairEncode u x).drop (2 * u.length + 2) = x`, in four files:
- `Turing.pairEncode_drop` (public, `Build/InputDevice`, line 198, new in #161), the one U2 cites;
- `NDCodeSimulator`'s private `ic_input_suffix` (line 340): the same statement and proof, 100% each
  way on the v3 screen (#161's evidence). **Retired** (2026-10-25): #162 moved it into
  `Build/InterpreterStartup` as the private `is_input_suffix`, and gate 74's round 2 deleted it
  there, the window call citing `Turing.pairEncode_drop` (the kit imports `Build/InputDevice`);
- `Complexity.Codec.pe_drop` (public, `SpaceComplexity/Codec/Parse`, line 69) and `PathWalk`'s
  private `drop_pairEncode` (line 225): the same statement through `pairEncode_eq_dbl`, different
  proofs (no screen pair).

*Historical (at #161's opening):* none of the four files could cite another's without a new import
(`InputDevice` was upstream of none of `NDCodeSimulator`, `Codec/Parse`, `PathWalk`). **Acknowledged
(user, 2026-10-24)**: the U2 review's F2 recommendation (publish `pairEncode_drop` with the API PR,
ledger the family) was the ruling's content. **Disposition:** the startup-kit re-point is **done**
(gate 74's round 2): the kit imports `Build/InputDevice`, so `NDCodeSimulator` sees it through the
kit, and the window call cites `Turing.pairEncode_drop`. Only the `Codec/Parse` and `PathWalk`
members remain, for the user's dedup window: one home beside `pairEncode_eq` in `Encoding` (a large
replay, hence the window). **Census** (one member per file): `InputDevice` 1 of 57 declarations
(1.8%), `Codec/Parse` 1 of 16 (6.3%), `PathWalk` 1 of 32 (3.1%); `NDCodeSimulator` and
`Build/InterpreterStartup` 0 since gate 74's round 2. The one-fifth rule is not reached.

**SK-1, U2-S's capture start** (PR #162, the startup-kit API PR, 2026-10-24). The kit's public
`Turing.embedSilentCfg_initCfg` (`Build/InterpreterStartup`) is U2-S's private
`ss_captureInitial` (`UniversalK`, line 329), harvested verbatim: 100% each way on the v3 screen.
`UniversalK` cannot cite the kit until `CodeSimulator` imports it (B5a's landing). U2-S's other
`ss_` startup pieces are the kit's constructions under other contracts (no screen pair). **By the
ruling (2026-10-24, the B5a review's recommendation)** they go to the user's dedup window, or to
U2's fill once `UniversalK` sees the kit. **Census** (gate 74, major 1, corrected at its round 2):
`Build/InterpreterStartup` 1 of 8 declarations (12.5%), the public `embedSilentCfg_initCfg`, 40
lines with its docstring; `UniversalK` 1 of 51 (2.0%), the private `ss_captureInitial`, 39 lines.
Round 1's kit had a second member, SD-1's suffix drop (2 of 9, 22.2%, past the one-fifth rule);
round 2 deleted it (SD-1 above), so the rule is not reached.

**RI-1, the round iteration along a sequence** (§13d G4 continuation 4, its review's F2,
2026-10-25). `Build/ZoneRebalance`'s private `zr_pinLoop` (line 8266, 71 lines with its docstring)
iterates pinned rounds by its own induction (`Round.segment`, then `Segment.trans`), which is the
proof of the published `Turing.Round.iterate` (`Build/Contract/Basic`, line 781), along the sequence
of pass indices `nxt^[m] j₀` instead of the configuration orbit `roundOrbit`. No published lemma
states the sequence form, so it re-derives `Round.iterate`'s argument, not its statement (the text
screen pairs nothing). All seven of the found path's passes go through it (`zr_passContract`). **The
ruling (user, 2026-10-25): land G4 with this entry; then an API PR adds the sequence form to
`Build/Contract/Basic`, with `Round.iterate` as its corollary, and re-points `zr_pinLoop` to it.**
Census (one member per file; the source side added at gate 75's minor 5): `Build/ZoneRebalance` 1 of
871 declarations (0.1%), the private `zr_pinLoop`, 71 lines with its docstring;
`Build/Contract/Basic` 1 of 85 (84 public, 1 private; 1.2%), the public `Turing.Round.iterate`, 18
lines with its docstring. The one-fifth rule is not reached. **The API PR is #167** (gate 78,
2026-10-25; stacked on #165): `Turing.Round.iterate_seq` beside `Round.iterate`, which becomes its
corollary, and `zr_pinLoop` re-pointed to it. On its landing RI-1 is retired. **Retired
(2026-10-26):** #167 merged as `4c8c2e7e`; `zr_pinLoop` cites `Round.iterate_seq`.

**SG-1, segment concatenation over a private segment predicate** (gate 98's finding 1,
2026-11-06). Two private predicates restate `Turing.Segment` (`Build/Contract/Basic`) at fixed
parameters, and each has its own concatenation lemma re-proving `Segment.trans`:
- `ClassNP/Tautology`'s `tautDualSegment c d t` is `Segment tautDualTM.tm {some .anchor}
  (fun _ => True) c d t`; `tautDual_segment_add` repeats `Segment.trans`'s endpoint and
  forbidden-prefix argument (the v3 screen pairs it with `Segment.trans`, 91/168, 54%);
- `Build/CounterLoop`'s `counterSpan` is a segment from `z` to its run endpoint over
  `{some .done, some .escape}`, whose head relation combines the counter head's interval and the
  body heads' `R`; `counter_span_append` repeats `Segment.trans`, then `Segment.mono` for the
  two relations.

Both predate #202 (the API PR whose gate found them); #202 adds no member. **ACKNOWLEDGED by kind
(the user, 2026-11-06):** every private predicate that restates `Turing.Segment` at fixed
parameters, with its concatenation lemma. **Cleanup owner and window:** the maintainer, in the
dedup window (12.2c): a bridge `tautDualSegment c d t ↔ Segment …` (and the same for
`counterSpan`), then `Segment.trans`/`Segment.mono` through it, deleting both concatenation
lemmas. **Census** (gate 98's, each member counted once per file; the source side included):
- `Build/Contract/Basic`, the public source: **1 of 93 (1.1%)**, `Segment.trans`, 20 lines;
- `ClassNP/Tautology`: **1 of 93 (1.1%)**, `tautDual_segment_add`, 12 lines. The file has no other
  recorded member;
- `Build/CounterLoop`: **1 of 79 (1.3%)**, `counter_span_append`, 28 lines. The file's
  recorded total, every acknowledged member counted once (corrected at gate 98's round-2 minor
  1): SG-1's `counter_span_append`, IW-1's `counterPatch` and R8.0b E1's pair `counterLoopTM`/
  `counterLoopTMVia`, **4 of 79 (5.1%)**, 68 lines (28 + 4 + 19 + 17).

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.

**The window (2026-11-06):** `CounterLoop`'s member is retired by #215 (`57939a97`: a private bridge
`counterSpan_iff_segment`; `counter_span_append` deleted; its three uses through `Segment.trans`
and `Segment.mono`). The scope search found a **third member**, `Robustness/SingleTape`'s private
`DGSpan` (`Segment tm ∅ (lo ≤ p 0 ≤ hi) c d t`) with `dgSpan_add` (7 uses). `Tautology`'s and
`SingleTape`'s members need a new import of `Build/Contract/Basic` (cycle-free; it adds that one
module to each closure): **parked for the user's ruling.** Also found, not counted: `Primitives`'
`splitSafe`/`splitSafe_add` and `Catalog`'s `f2_splitSafe`/`f2_splitSafe_add` restate
`Turing.SafeSegment` (a sibling `SafeSegment` family, for the user); `SAT`'s `sat_guard_add` and
`Hardness`' `clA5_guard_add` re-prove the cut half of `Segment.trans` with no predicate. If
`tautDual_segment_add` is deleted, `blueprint/src/chapter/Complexity/ClassNP/Tautology.tex:981`
changes with it.

**BL-2, the binary width of an incremented register value** (gate 101's finding 1,
2026-11-06). The bound `m ≤ 2 ^ e + 1 → |Nat.bits (m + 1)| ≤ e + 2`, through
`m + 1 < 4 · 2 ^ e = 2 ^ (e + 2)` and BL-1 (i)'s `length_bits_le`, was proved three times:
- `Logspace/ISCountGenCorrect`'s private `bits_succ_le` (BL-1 (i) lists it as a site that cites
  `length_bits_le`; its successor/exponential step is this family's);
- `Machines/ARMWidth`'s `arm_decides_pspace_val`, an inline `hlt` block at `N = C₀ (|x| + 1)^c₀`;
- `SavitchARM/Deepen`'s `deepen_contract` (new in #208), the same block at `W · W`.

Census (gate 101's, one member in each file): `Deepen` 1 of 45, `ARMWidth` 1 of 5,
`ISCountGenCorrect` 1 of 9. No file is past one fifth (`ARMWidth`'s 1 of 5 is at it).
**Ruled (the user, 2026-11-06): harvest in #208, all three.** `#208`'s commit `9db4f2ee`
publishes `Complexity.LogProg.length_bits_succ_le` in `Machines/Bin`, beside `length_bits_le`;
`bits_succ_le` is deleted, and the two inline blocks cite it. A library search for the
`4 · 2 ^ e` step (`2 ^ (… + 2) = 4 * 2 ^ …`) finds no other member: `ExpBFS/Main:535–539`
bounds a `Nat.log` width and a memory range, and `BinaryArith/AddSub:174` a sum of two words, both
other statements. **Retired on #208's merge.**

**IL-1, the input-length decider's answer** (gate 101's round-2 screen, 2026-11-06). The
public `Complexity.indicator_inputLenLang` (`Logspace/InputAccess`, since the ARM dedup `56716442`)
states that `inputLenLang` answers `decide (a < |y|)` on `pairEncode y (bits a)`. Six proofs
unfolded their decider table and repeated its two-line proof
(`inputLenLang`, `indicator_indexLang_pairEncode`, `decide_eq_decide.mpr Iff.rfl`):
- `Logspace/ISCountGenCorrect`'s `gen_start` (`hq`), which the v3 screen pairs with
  `indicator_inputLenLang` and with `ExpBFS/Main`'s `orcN_len` at 94%;
- `ExpBFS/Main`'s `orcN_len`, `SavitchARM/Correct`'s `hq`, `Machines/ARMWidthExample`'s `hq`,
  `Logspace/PathHardRegs`' `orc_len` and `Randomized/SpaceAmplifyPoly`'s input-length loop (each
  under the screen's cut-off or outside its population; found by `git grep` for the closing step).

All six predate #208; `Deepen` cites the lemma. Census: one member in each file. No file is past
one fifth. **Ruled (the user, 2026-11-06): re-point all six in #208.** #208's commit `6a289c50`
replaces each by the table's unfolding and `indicator_inputLenLang`; each file elaborates.

**Widened by kind (2026-11-06):** every proof that re-derives one of `InputAccess`'s two
published readings, `indicator_inputLenLang` or `indicator_inputBitLang`
(`y.getD a false` on `pairEncode y (bits a)`), by unfolding the language and
`indicator_indexLang_pairEncode`. The first search matched only the `decide_eq_decide` closing;
its simp-set variants are five more members: `PathWalkMachine`'s `pathOr_len` and `pathOr_bit`,
`PathHardRegs`' `orc_bit`, and both halves of `Mult`'s private `mult_queries`. **Ruled (the
user, 2026-11-06): re-point all five in #208**, done at `0140aee2`. A grep of every code line
naming `inputBitLang` or `inputLenLang` finds no other unfolding: `TQBFARM/Machine`'s and
`Codec/Run`'s `orc_bit`/`orc_len` and `QueryReshape`'s `drop_bit`/`drop_len` already cite the
lemmas. The other readers of `indicator_indexLang_pairEncode` (`QueryReshape`'s
`drop_lang_pair`, `comp_lang_pair` and `transport`; `PathHardDecide`'s `qLang` step) read other
languages, which have no published reading; they are not members. Census after widening (corrected
at gate 101's round-2 minor 1): **10 declarations across eight files, 11 proof sites**:
`PathHardRegs` (`orc_len`, `orc_bit`, 2 of 62) and `PathWalkMachine` (`pathOr_len`,
`pathOr_bit`) two declarations each, `Mult`'s `mult_queries` two sites in one declaration, every
other file one. No file is past one fifth. **Retired on #208's merge.**

**NZ-1, no machine halts in zero steps** (found 2026-11-06 in gate 102's round-1 search; widened
by kind in its round 2; **acknowledged, the user 2026-11-06: publish and re-point now**; PR #217,
`lean/dedup-nz1`, commits `5e77e558` and `2fdb84f7`). One fact in two readings: the initial
configuration is live, so no run halts within `0` steps.
- **Deterministic:** public as `Turing.FinTM.not_computesInTime_zero` (`TuringMachine/Finite`).
  Already cited by `ClassP/DTIME`, `ClassNP/TMSAT`, `CookLevin/Hardness` and
  `Diagonalization/EXPCOM`, and since #211 by `TwoTapes`' `tt_forward_run`. Re-derived (gate 102
  r2, finding 1) in `Build/Loop`'s private `emCall_prepared_eval_first` and `CircuitComplexity/Advice`'s
  `DTIMEAdvice_eq_empty_of_eq_zero`; #217 re-points both.
- **Nondeterministic:** no public lemma before #217, which publishes `Turing.NDTM.not_haltsWithin_zero`
  (`TuringMachine/Nondeterministic`). Its five copies, one per file: `ClassNP/ExhaustiveReplay`'s private
  `xr_not_haltsWithin_zero` (deleted), `ClassNP/NDNormalForm`'s `nf_forward` (`hpos`), `ClassNP/NTIME`'s
  `NTIME_eq_empty_of_exists_zero`, `Randomized/ExpectedTime`'s `AbortDecidesInTime.restart`,
  `Randomized/BPTIMEThreshold`'s `BPDecidesInTimeWith.one_le`; #217 re-points all five.

**The search** (by kind, at `1dd510aa`): `rw`/`simp`/`change … at` forms with `runFrom_zero`,
`runWith_nil`, `initCfg`, `Cfg.init` or `init_state`; zero-case scans (`by_contra`,
`Nat.pos_of_ne_zero`, `eq_zero_or_pos`, `| zero`) near initial-configuration terms; `[] rfl` and
`[] (by …)` instantiations of halting hypotheses; literal time-0 `runFrom`/`ComputesInTime`/`HaltsWithin`;
`show`/`change`. **Not members**, each a different fact: first-halt helpers from an arbitrary `cfg`
(`Loop:219`, `Catalog:6463`, `SAT:3797`, `Hardness:6176`); runs from non-initial configurations
ending in a state mismatch (`Hardness`, `NDCodeSimulator`, `NDNormalForm`, `StepBlockLoop`,
`Contract/Basic`, `Contract/Seam`, `NTimeDiagonalizer`); composite runs at positive times
(`UniversalK`, `NTimeHierarchy`, `Composition`, `Inclusions`); positive liveness facts
(`state = some q₀`); and other models (NARM's `narun`, `Yap`'s `badLang`, the oracle machines).
**Retired on #217's merge.**

**TC-1, the copying transducer state** (PR #164, A1, 2026-10-25; gate 76's note 7). One fact, a
transducer started in a state that copies every bit and is kept is the identity, in three files:
- `Complexity.transduce_of_copy` (public, `ClassNP/Transducer`, line 83, new in #164), the general
  form: from `∀ b, δ q b = q` and `∀ b, o q b = some b`, `transduce δ o q l = l`;
- `Complexity.KarpLipton.transduce_drop_true` (public, `CircuitComplexity/KarpLiptonPrefix`, line
  87) and `Complexity.Meyer.transduce_fT_copy` (public, `CircuitComplexity/MeyerVerifierGlue`,
  line 145): its instances at `q = true` and `q = none`, each the general lemma with `fun _ => rfl`
  twice (the megafill D review's `probe/A1ConsumerProbe`; gate 76 checked both specializations),
  each re-proved by its own induction.

Both instance files import `ClassNP/Transducer`, so each can cite the general form.
`spaceConstructible_poly`'s landing cites it (`Savitch`'s private `scp_transduce_copy` is the
one-line application), which avoids a third copy. **The ruling (user, 2026-10-25, Q-D2): include
the general form in A1; re-point the two instances in the user's dedup window (12.2c), since that
edits `CircuitComplexity/*`.** Census (one member per file, at A1's head): `ClassNP/Transducer` 1 of
10 declarations (10.0%), `KarpLiptonPrefix` 1 of 16 (6.3%), `MeyerVerifierGlue` 1 of 42 (2.4%). The
one-fifth rule is not reached.

**RS-1, the restart identity** (PR #170, B5a's landing, 2026-10-27; disclosed in gate 81's pack,
item 4; completed by gate 81's finding 1). One fact: a machine whose initial state is a relabelled
`q` starts in the relabelled blank configuration at `q`, i.e.
`B.q₀ = f A.q₀ → B.initCfg x = (A.initCfg x).mapState f`. It is proved at five sites in four
files, each by `Cfg.ext` with the `Cfg.init_*` and `Cfg.mapState_*` field equations:
- `Turing.UniversalK`'s `uk_init_mapState` (private, line 1816), the general form, used twice
  (`uk_loop_init`, the suffix startup);
- `Turing.UniversalK`'s `exists_selfStartupTMK` (public, line 1425): its local `hinit`
  (line 1584), `R.initCfg (pairEncode α w) = d₀.mapState Sum.inl` with
  `R := { W with q₀ := Sum.inl A.q₀ }` (gate 81's finding 1);
- `CodeSimulator`'s `us_start` (private, line 8984 at #170's head), its instance at
  `{ W with q₀ := Sum.inl entry }`, after `MultiTapeTM.initCfg_with_q₀`;
- `ExhaustiveReplay`'s `xr_E_initCfg` (private, line 3133), its instance at a doubled `Sum.inl`
  with the host's blank fields;
- `NTimeHierarchy`'s `un_setup` (private, line 604): its local `hstart` (line 1410), the instance
  at a seven-fold `Sum.inl` of the embedded blank start `c0`.

Census (one member per file; each count at the tree named): `CodeSimulator` 1 of 208 declarations at
#170's head (12 public, 196 private; 0.5%), `ExhaustiveReplay` 1 of 185 (0.5%), `UniversalK` 2 of 79
(2.5%), `NTimeHierarchy` 1 of 15 at the campaign tip before #172 (6.7%), 1 of 25 after it (4.0%;
cumulative with TR-1 below). The one-fifth rule is not reached. **Disposition** (gate 81's finding
1: publication need not precede #170 under D1(A)): a public row beside `MultiTapeTM.initCfg_with_q₀`
(`TuringMachine/Finite`) in the user's dedup window (12.2c), with the five sites re-pointed.

**PL-1, the linear-to-polynomial lift, and WT-1's residue** (PR #171, the word tests, 2026-10-27;
disclosed in gate 82's pack, item 5). Two copies outside the ruling's scope (E-DUP covered the
fixed-word and all-`true` tests only):
- `Nondeterminism`'s private `a3n_poly_linear` (line 3537 at #171's head `d17f63c8`; 13 uses) and
  `a3n_poly_const` (line 3544), equal in their proofs, up to the names, to the public
  `Complexity.polyTimeComputable_of_linear` and `Complexity.polyTimeComputable_const`
  (`ClassNP/PolyTimePairing`, lines 64 and 71). `Nondeterminism` does not import `PolyTimePairing`;
  the import is acyclic (`PolyTimePairing` imports only `ClassNP/PolyTime` and `Build/Primitives`).
- `Savitch`'s inline `hD'` (`SpaceComplexity/Savitch`, line 193 in `spaceConstructible_poly`'s
  proof): the conversion of `computesFunInTime_ifEq [] [true] [false]` to `[decide (x = [])]`,
  which is `Turing.FinTM.computesFunInTime_decideEq []` (#171). An inline step, not a declaration.
  **Re-pointed by #175's round-1 fix** (gate 86's finding 2, user, 2026-10-27): the proof, now in
  `Constructible`, takes its decider from `computesFunInTime_decideEq []`; no copy is left there.
- `SAT`'s private `sat_pt_eq` (line 2886) and `CookLevin/Hardness`'s private `clA5_pt_eq` (line
  6818), twins (found by gate 82's resolution of its finding 1): each lifts
  `computesFunInTime_ifEq w [true] [false]`, converts it to `[decide (x = w)]` and composes it with
  a polynomial field map. Each is `polyTimeComputable_of_linear (computesFunInTime_decideEq w)`
  composed with that map.

Census (one member per file, at #171's head): `Nondeterminism` 2 of 199 declarations (8 public, 191
private; 1.0%), `PolyTimePairing` 2 of 26 (7.7%; the public originals), `SAT` 1 of 270 (0.4%),
`CookLevin/Hardness` 1 of 545 (0.2%). **Corrected (gate 86's finding 2, 2026-10-27):** the census
omitted the fixed-word test's public original, `Build/WordTests`'s `computesFunInTime_decideEq`,
**1 of 4 declarations (25%)**, so the source-inclusive count crosses one fifth in `WordTests`.
**Human review (user, 2026-10-27): accepted** — a four-declaration module whose member is the
public row the copies should cite; the consumers' re-points retire the family. **Disposition:** the
user's dedup window (12.2c): re-point the two privates to the public rows (one import), and the
twins to `computesFunInTime_decideEq w` (each with the import of `Build/WordTests`); `hD'` is
re-pointed already (#175).

**TR-1, the truncation of an acceptance at an all-branch budget** (PR #172, H's landing,
2026-10-27; the H brief review's F1 and gate 84's pack, item 5). One fact: if every branch of `N`
on `x` halts within `T`, an acceptance at any length is an acceptance within `T` (and conversely
by `AcceptsWithin.mono`). It is stated privately in three files:
- `Nondeterminism`'s `acceptsWithin_iff_of_halts` (line 165), through the published
  `Turing.run_take_of_halted`;
- `ExhaustiveReplay`'s `xr_accepts_iff_of_halts` (line 134);
- `NTimeHierarchy`'s `nh_accepts_of_halts` (new in #172), through `run_take_of_halted`. The
  user's D1 (A) licensed this leaf; the v3 screen pairs it with the first at 61%.

`ClassNP/NTIME`'s `NTIME.mono` does the same truncation inline. Census (one member per file, at
#172's head `33d68537`, a tree before #171): `Nondeterminism` 1 of 201 (8 public, 193 private; 0.5%;
1 of 199 after #171), `ExhaustiveReplay` 1 of 185 (0.5%), `NTimeHierarchy` 1 of 25 (4.0%).
**Cumulative across families** (gate 84's finding 1): after #172, `NTimeHierarchy` carries RS-1's
`un_setup` and TR-1's `nh_accepts_of_halts`, **2 of 25 (8.0%)**. No file reaches one fifth.
**Disposition:** the user's dedup window (12.2c): publish the truncation beside
`FinNDTM.AcceptsWithin.mono` (`ClassNP/NTIME`, which would import `ChoiceWords`; no cycle), and
re-point the three.

**LS-1, the logarithmic bound below the linear one** (PR #175, the move of
`spaceConstructible_poly` to `Constructible`, 2026-10-27, pending its merge; gate 86's pack, item 3).
One fact, `logSpace n ≤ n + 1`, in three places:
- `Machines/ARMWidth`'s public `Complexity.logSpace_le_succ` (line 51), the lemma (a colleague's
  file, outside `Constructible`'s closure);
- `Constructible`'s `spaceConstructible_poly`, the dominance step, inline through `logSpace_eq` and
  `Nat.log_le_self` (before #175 it cited `logSpace_le_succ` from `Savitch`, whose closure has
  `ARMWidth`);
- `Constructible`'s `spaceConstructible_linear`, its dominance conjunct, inline as
  `Nat.succ_le_succ (Nat.log_le_self 2 n)` by reduction of `logSpace` (another file's definition;
  the proof predates rule 10).

Two inline steps and one declaration; the one-fifth rule is not in question. **Accepted (user,
2026-10-27; gate 86's finding 1)** as debt, the new inline step included. **Disposition:** the
user's dedup window (12.2c): move `logSpace_le_succ` into `SpaceComplexity/Basic` beside
`logSpace_eq` (a mechanical edit in `ARMWidth`, FYI to its author), and re-point the two inline
steps to it. **Brought forward (user, 2026-11-04): PR #181** (gate 89) does exactly that, and also
moves `logSpace_le_of_le_mul_two_pow` to `Basic` and `LOGSPACE_subset_PSPACE` and
`SPACE_succ_pow_subset_PSPACE` to `SpaceClasses`. **LS-1 is retired when #181 merges.**
**Scope corrected (gate 89, round 1, major 1).** Two further inline copies predated #181:
- `narm_decides` (`Machines/NARMProof`);
- `narm_logspace_ptm` (`Machines/NARMLogspace`).

Both are `have hLn : logSpace n ≤ n + 1` by `Nat.log_le_self` and `simp only [logSpace]`, in
Hydroxyi's files, and neither was in this entry. Round 2 of #181 (`1d1247a3`) re-points both to
`logSpace_le_succ`, a mechanical ARM dedup edit (FYI). A search of the round-2 head
(`campaign/gates/89-space-facts-api/evidence/round2/ls1-search/`) finds the fact stated only in
`Basic` and cited everywhere else.
**Scope corrected again (gate 89, round 2, major 1).** Two more inner steps derived the logarithm's
form of the fact, `Nat.log 2 m + 1 ≤ m + 1`:
- `ImplicitlyLogspaceComputable.computesInSpace` (`ImplicitPoly`, Hydroxyi's ARM-program file):
  `W ≤ F + 2` with `W = Nat.log 2 (F + 1) + 1`;
- `mem_LOGSPACE_preimage` (`Logspace/PreimageHost`, the campaign's).

Round 2's search had classed both as "polylogarithmic bounds": true of the enclosing bounds, not of
these steps. Round 3 of #181 (`8d41671c`) re-points both to `logSpace_le_succ` through
`logSpace_eq`. Its exhaustive classification of every `Nat.log_le_self` use and every
`logSpace`-by-successor statement
(`campaign/gates/89-space-facts-api/evidence/round3/ls1-search/classification.md`) finds the fact
proved once, in `Basic`, and cited at eight sites.
**Scope corrected a third time (gate 89, round 3, major 1).** Round 3's search had looked for
`Nat.log_le_self` only, so it missed one more inline copy: `arm_decides` (`Machines/ARMProof`,
Hydroxyi's) proved `hLn : Ls ≤ n + 1`, with `Ls := logSpace n`, by unfolding `logSpace` and citing
`Nat.log_lt_self`. Round 4 of #181 (`a7c2a655`) re-points it to `logSpace_le_succ` (a mechanical ARM
dedup edit, FYI). Round 4's search covers every line that touches `logSpace`'s definition and every
Mathlib upper bound of `Nat.log`
(`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/classification.md`). It finds the
fact proved once, in `Basic`, and cited at nine sites.

**LS-2, the logarithmic bound by the binary length** (gate 89, round 4's search; ruled with it, user,
2026-11-04: "Fix in #181 now"). The fact is `logSpace n ≤ Nat.size n + 1`, equivalently
`≤ |bits n| + 1`; its converse is `|bits n| ≤ Nat.log 2 n + 1`. Before round 4:
- the public `Complexity.LogProg.ISCount.logSpace_le_size_succ` (`Logspace/ISCountMath`);
- inline re-derivations in `Randomized/BPLInP`, twice (`two_pow_codes_le`, `BPL_subset_P`);
- the public `Randomized.PolyAmp.logSpace_le_ell` (`Randomized/SpaceAmplifyPoly`, its `ell n` is
  `|bits n| + 1`), re-proved through `Nat.log_lt_of_lt_pow`;
- the converse, published as `LogProg.length_bits_le_log` (`Machines/Bin`) and re-derived by the
  private `size_le_logSpace` (`Logspace/ISCountGenCorrect`).

All in Hydroxyi's files. `BPLInP` did not import `ISCountMath`. **Retired by #181, round 4**
(`fe4bdb67`, `227d92ee`): `logSpace_le_size_succ` moves verbatim to `SpaceComplexity/Basic` as
`Complexity.logSpace_le_size_succ`, and the four re-derivations cite it or `length_bits_le_log`
(copy deletions and re-points, FYI). Same round, same ruling: `ExpBFS/Run`'s `setup_run` cites its
own file's `lgv_le_succ` for `hv |x| ≤ |x|` instead of re-deriving it (`252bbcb8`).

**LS-3, the binary length as the logarithm** (gate 89, round 4's search). The fact is
`|bits n| = Nat.log 2 n + 1` for `n ≠ 0`. No public lemma states it. Private copies:
- `Constructible`'s `b3a_bits_length` (the campaign's);
- `Randomized/QuasiPolyHierarchy`'s `length_bits_eq` (Hydroxyi's);
- `Diagonalization/NTimeDiagonalizer`'s `qy_log_bits`, with `Nat.size n = Nat.log 2 n + 1` also
  inline in its `qy_two_pow_bits_le` (E-D's file, in flight).

**Census** (gate 89, round 4's minor 2; members over all declarations, private included):
- `Constructible` 1/28;
- `QuasiPolyHierarchy` 1/25;
- `NTimeDiagonalizer` 2/236 (`qy_log_bits` and `qy_two_pow_bits_le`'s inline equality).

None reaches one fifth. The halves of these equalities also prove LS-2's converse
(`QuasiPolyHierarchy:63`, `NTimeDiagonalizer:430`, `:446`); they stay within LS-3, and the one
public converse lemma is `LogProg.length_bits_le_log`. **Accepted (user, 2026-11-04)** as debt.
**Disposition:** the dedup window (12.2c): publish the equality beside `LogProg.length_bits_le_log`
and re-point all four occurrences (the three privates and the inline step) after E-D lands.

**BL-1, elementary bounds on the binary length** (gate 89, round 4's binary-length sweep,
`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/bitsweep.tsv`). One- and two-line
steps that carry a Mathlib `Nat.size` fact over to `|Nat.bits n|` through `Nat.size_eq_bits_len`,
where a lemma already states the bound:
- (i) `|bits n| ≤ m` from `n < 2 ^ m` (`LogProg.length_bits_le`, `Machines/Bin`): `Meyer:189`,
  `MeyerTableau:437`, `ISCountGenCorrect`'s private `bits_succ_le` (`:210`);
- (ii) monotonicity (`LogProg.length_bits_mono`): `NTimeDiagonalizer`'s private `qy_bits_len_mono`,
  `RecordTable:2762`, `InputLength:418`, `:420`, `Catalog:4125`;
- (iii) `|bits n| ≤ n` (`Turing.length_bits_le_self`, `TuringMachine/Encoding`):
  `CodeSimulator:1448`, `NTimeDiagonalizer:455`, `SpaceAmplifyPoly:287` (`ell_le`),
  `RecordTable:2764`, `:4256`;
- (iv) `n < 2 ^ |bits n|`: public as `Randomized.PolyAmp.lt_two_pow_bits` and, for `posWidth`,
  `Turing.record_pos_lt`; inline or private in `NTimeDiagonalizer`'s `qy_lt_two_pow_bits`,
  `Logspace/Mult:254`, `:255`, `WindowClock:119`;
- (v) `2 ^ |bits n| ≤ 2n` or `2n + 1`: public as `Complexity.Codec.two_pow_bits_le` (`Codec/Layout`)
  and `Randomized.PolyAmp.two_pow_bits_le`; inline or private in `Codec/Parse:90`,
  `NTimeDiagonalizer`'s `qy_two_pow_bits_le`, `BPLInP:399`.

The files are the campaign's, Hydroxyi's, E-D's in-flight `NTimeDiagonalizer` and the
colleague-owned `CircuitComplexity/Meyer*`. `Machines/Bin` sits above the `CircuitComplexity` and
`TuringMachine` layers, so several sites cannot import it. Each site is one step, so the one-fifth
rule is not in question. **Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window
(12.2c): one home for the five bounds below both layers (beside `Turing.length_bits_le_self`), then
re-points where the imports allow. `CircuitComplexity` needs its own authorization.
**Scope corrected (gate 89, round 4, major 1).** The list above missed:
- `Codec/Layout`'s `wP_le` (iii, through logarithms);
- `PathHard`'s `two_pow_ell_le` (v) and `ell_mono` (ii);
- `RandomWalkPad`'s `padDegree_le` (v);
- `PrimeFind:204`, `:318` and `TQBFHardParams`' `wP_le` (iii).

With `Layout`'s `wP_le`, `Layout` stood at 2 of 9 declarations. **Ruled (user, 2026-11-04): "Re-point
now in #181."** Round 5 of #181 (`d789d6db`, `98912ab2`) re-points every site whose file can reach
a canonical lemma:
- (v) `two_pow_bits_le` moves from `Codec/Layout` to `Machines/Bin`. `Parse:90`, `PathHard`'s
  `two_pow_ell_le`, `RandomWalkPad`'s `padDegree_le`, `BPLInP:399` and `PolyAmp.two_pow_bits_le`
  cite it;
- (iii) `Layout`'s `wP_le` cites `Turing.length_bits_le_self` through the new `Codec.wP_eq`, and
  `TQBFHardParams`' `wP_le`, a restatement of `Codec.wP_le`, is removed. `PrimeFind:204`, `:318`,
  `CodeSimulator:1448`, `RecordTable:2764`, `:4256` and `SpaceAmplifyPoly`'s `ell_le` cite
  `length_bits_le_self`;
- (i) `ISCountGenCorrect`'s `bits_succ_le` cites `length_bits_le`;
- (ii) `PathHard`'s `ell_mono` cites `length_bits_mono`;
- (iv) `WindowClock:119` cites `record_pos_lt`.

`Layout` now has no member. **The residual**, every member of the sweep's classification at
#181's round-5 head (`campaign/gates/89-space-facts-api/evidence/round5/ls1-search/bitsweep-classes.md`):
- (i) `Meyer:189` and `MeyerTableau:437`: colleague-owned `CircuitComplexity`;
- (ii) `RecordTable:2762`, `InputLength:418`, `:420` and `Catalog:4125`: `Machines/Bin` is above
  these files;
- (iv) `Mult:254`, `:255`: no (iv) lemma that this file can reach. `PolyAmp.lt_two_pow_bits` and
  `Turing.record_pos_lt` are two public statements of (iv) in different layers and forms;
- `NTimeDiagonalizer`, E-D's file in flight:
  - (ii) `qy_bits_len_mono`;
  - (iii) `qy_call_bound:455`, which E-D's landing already re-points;
  - (iv) `qy_lt_two_pow_bits`;
  - (v) `qy_two_pow_bits_le`;
  - (iv) **`qy_ones_ge:415–417`, new in round 5's sweep** (two inline `Nat.lt_size_self` steps); **acknowledged (user, 2026-11-04)**. The acknowledgment was asked on the
    premise that E-D's landing re-points it. That premise was wrong: the file does not reach `Machines/Bin`,
    so its disposition is the dedup window.

**Disposition of the residual:**
- E-D's landing PR re-points `qy_call_bound:455` (iii), since the file reaches `Encoding`;
- `NTimeDiagonalizer`'s other four members cannot reach `Machines/Bin`, like `RecordTable`'s, and go
  to the dedup window with the rest;
- `CircuitComplexity` comes under its own authorization.

**Scope by kind (gate 89, round 5, majors 1 and 2; ruled by the user, 2026-11-04: "Acknowledge,
scope by kind").** BL-1's acknowledged scope is every re-derivation of kinds (i)–(vi) anywhere in
TCSlib, whether or not a sweep lists it. A member found later is an accounting correction (a minor,
TEMPLATE failure mode 5), unless it pushes a file past one fifth. The kinds are:
- (i)–(v), above;
- **(vi)**, new: the word-value bound `bitsVal w < 2 ^ |w|` (`LogProg.bitsVal_lt_two_pow`,
  `Machines/Bin`).

Round 5's audit found five members outside the site lists, all predating #181 and all acknowledged:
- (v) `Logspace/QueryReshape`'s private `query_index_bound` (sweep group 90) and
  `Randomized/UniformSample`'s `le_two_pow_size_pred` (group 62), whose positive branches derive
  `2 ^ size n ≤ 2n` natively. Both files reach `Machines/Bin`. `UniformSample` is Hydroxyi's;
- (i) `CookLevin/Hardness`'s private `clCount_width`, by binary induction, and (iii) its
  `clElapsed_width`, through `clCount_width`. `Hardness` reaches `Encoding` but not `Bin`;
- (vi) `Codec/Word`'s `Complexity.Codec.bitsVal_lt_two_pow`, an exact copy of `Bin`'s, which
  `Word` imports. `Word` is Hydroxyi's. Its users would resolve to `Bin`'s through `open LogProg`.

**Census:**
- `QueryReshape` 1/120, `UniformSample` 1/19, `Hardness` 2/545, `Word` 1/47;
- `Bin`'s five members (`length_bits_le`, `length_bits_mono`, `two_pow_bits_le`,
  `length_bits_le_log`, `bitsVal_lt_two_pow`) are the canonical statements the copies re-point to,
  not copies. That makes 5/15, recorded as the one-fifth review item.

**Disposition:** the dedup window, with the rest. The one home below both layers re-points them
once.

**CL-1, the codec languages' sibling idiom** (gate 91, the edge-mode PR's screen; ruled with it,
user, 2026-11-04). Each code language of `SpaceComplexity/Codec` has its own definition, its own
membership lemma at an encoded input (`mem_validLang`, …), its own characterization through the
word-level check (`validLang_iff`, …) and its own decider proof (`validLang_mem`, …). The proofs
repeat two pieces: the decoding of `⟨x, ⟨bits c, bits s⟩⟩` (`pairEncode_inj` twice, then
`bits_injective`) and the decider wrapper (`arm_decides_poly` on `CA`, the `one_run` case split and
the reject branch). The four languages `validLang`, `initLang`, `acceptLang` and `stepLang`
(Hydroxyi's) already formed 31 copy pairs at the base. The edge-mode PR adds `edgeLang`,
`mem_edgeLang`, `edgeLang_iff` and `edgeLang_mem`, 25 more pairs. About 25 lines of shared text
are the decoding proofs and the wrapper's skeleton. The edge mode's own correctness proof
(`edge_round`, `edge_loop`, `edge_tail`) is in no pair. **Census** (gate 91, minor 3; members of the
family over all declarations, private included): `Langs` 8/9 → 10/12, `Checks` 4/26 → 5/31,
`Deciders` 3/16 → 4/22. `Langs` was already above one fifth at the base, from the four existing
languages; the acceptance above covers it. The edge member crosses no new file's threshold.
**Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window (12.2c): one membership
lemma for languages of encoded triples, and one decider wrapper parameterized by the mode's tail,
with the five languages re-proved through them. This reworks Hydroxyi's proved deciders, interface
design that waits for him. **Ruled (the user, 2026-11-06; Hydroxyi not active): the full refactor.**

**RO-1, the one-step identity `M.runFrom c 1 = M.step c`** (PR #176, E-Q cont1's landing,
2026-10-27; its review's F5; ruled with the landing, user, 2026-10-27). No public lemma states it
(`MultiTapeTM.runFrom` is in the vendored `Deterministic`). Private copies: `NTimeDiagonalizer`'s
`qy_run_one` (new), `ExhaustiveReplay`'s `xr_runFrom_one`, `SAT`'s `satRed_one`, `CfgRecord`'s
`recordStep_runFrom_one`; inline in 13 declarations (`SeamLayout` 3, `Catalog` 4, `Primitives` 4,
`Loop` 1, `Encoding` 1). Census (declaration members, at #176's head): `NTimeDiagonalizer` 1 of 236
(0.4%), `ExhaustiveReplay` 1 of 185 (0.5%), `SAT` 1 of 270 (0.4%), `CfgRecord` 1 of 138 (0.7%),
`SeamLayout` 3 of 36 (8.3%), `Catalog` 4 of 505, `Primitives` 4 of 285, `Loop` 1 of 205, `Encoding`
1 of 61. The one-fifth rule is not reached. **Disposition:** the dedup window (12.2c): a public
`MultiTapeTM.runFrom_one` in a non-vendored module, and the 17 sites re-pointed.
**+1 (G5's landing, #211; gate 102):** `Robustness/TwoTapes`' `tt_round` closes the one-step
identity inline (`runFrom_succ_eq_step.trans runFrom_zero`), 1 of 104 declarations; 18 sites for
the window.
**The window's first pass (2026-11-06; branch `lean/dedup-ro1` at `7c940a8a`, pushed, no PR):**
`Turing.MultiTapeTM.runFrom_one` in `TuringMachine/CfgFacts` (the user's ruling), the four
privates deleted and the 13 inline sites re-pointed; every changed file elaborates. **The scope is
far larger than recorded**, and the PR is parked for the user:
- a public Bool-only copy already exists: `Turing.runFrom_one` (`Build/EmitIterEmbed:261`,
  `simp [MultiTapeTM.runFrom]`), used four times by `EmitIterBody`;
- the rewrite chain `runFrom_succ_eq_step` + `runFrom_zero` (mostly induction base cases) appears
  in about 186 further declarations in 41 files, among them `Catalog` 26, `Primitives` 23,
  `CookLevin/Hardness` 14, `SAT` 12, `Universal` 12, `Nondeterminism` 10, `EXP` 7, and several
  colleague-owned `CircuitComplexity`/`Meyer` files;
- `have`/`show`/`change` forms: `EmitIterBody`'s `hone`/`honeG`, `NDNormalForm:1766`,
  `NDCodeSimulator:632`, `Primitives`' `splitSafe_one` and `hdepart`, `Catalog`'s
  `f2_splitSafe_one`, `hdepart`, `hfirst`, `Loop`'s `hfirst` and `hs`; and fixed-machine
  statements in `CodeSimulator`, `InputWindow` (`iw_one`), `UniversalK`, `WindowClock`,
  `Inclusions`, `CircuitSatReductionMachine`, `Universal` and `UniversalBlock`.
The ledger's census undercounts accordingly. **Questions for the user:** whether the general
lemma replaces `EmitIterEmbed`'s public `Turing.runFrom_one` (a public removal); and the scope of
the re-points (all non-colleague sites in one PR or several; `CircuitComplexity` needs its own
authorization).

**NB-1, the `Nat.bits` arithmetic family** (PR #176; the review's F2). `NTimeDiagonalizer`'s
`qy_two_pow_bits_le` (the statement of `SpaceAmplifyPoly`'s `two_pow_bits_le`, on `main`) and
`qy_log_bits` (whose `≤` half is `Machines/Bin`'s `length_bits_le_log`); before E3 also
`qy_bits_len_mono` (`Bin`'s `length_bits_mono`) and `qy_lt_two_pow_bits`, now through Mathlib's
`Nat.size` facts; and, inline, `qy_call_bound`'s `(Nat.bits (f a)).length ≤ f a`, the statement of
`Encoding`'s `Turing.length_bits_le_self` (gate 87's finding 2). Census, source-inclusive (gate 87's
finding 3; declaration members, inline steps counted as in RO-1): `NTimeDiagonalizer` 3 of 236
(1.3%), `Machines/Bin` 2 of 12 (16.7%), `SpaceAmplifyPoly` 1 of 20 (5%; `two_pow_bits_le`, on `main`
and on the campaign since its merge of `main`), `Encoding` 1 of 61 (1.6%; `length_bits_le_self`);
the last three are the public originals. Below one fifth. **Disposition:** `qy_call_bound`'s step
re-points to `length_bits_le_self` in E-D's landing (ruled, user, 2026-11-04); the rest in the dedup
window: a shared `Nat.bits` module.

**Cumulative per-file accounting for RO-1 and NB-1** (source-inclusive; gate 87's finding 3).
`NTimeDiagonalizer` 4 of 236 (1.7%: RO-1 1, NB-1 3; 3 after E-D's landing re-points
`qy_call_bound`); `Encoding` 2 of 61 (3.3%: RO-1 1, NB-1 1). Every other file is in one of the two
families only, its census above. No file approaches one fifth.

**RC-1, row candidates from E-Q cont1** (PR #176; the brief's and the report's, the review's F9).
Private leaves and lemmas with no published counterpart, each a candidate public row: the clocked
install call (`QyClockSpec`, `qy_clocked_call`, `qy_clockHost_*`); the framed length comparison
with verdict (`qyCmpTM`, `qy_cmp_run`); the repeating emitter (`qyEmitTM`, `qy_emit_run`,
`qy_emit_stop`); the phase host's segment forms (`qy_hosted*`, `qy_round_of_seg`); the
`Nat.unpair` successor rule (`qy_unpair_succ_*`). Not copies. **Disposition:** promotion when a
second consumer appears, or in the dedup window.

**QF-1, two in-file factorings** (PR #176; the review's F6). The `copyMapTM`/`transferMapTM`
endpoint conversion and the `clockCfg` field conversion recur in `NTimeDiagonalizer` (pairs at
90–94%, justified as readings of different rows). Optional. **Disposition:** the dedup window.

**RC-2, a framed take-one-cell row** (E-D's brief, 2026-11-04; its review's F1, ruled by the user).
No published row writes a blank at one cell, and every framed row needs blanks at its word's
relative positions `-1` and `|w|`, so a word inside a nonblank block cannot be split off by
published rows. E-D's own leaf `dzTakeTM` (read the cell, blank it, step right) fills the gap,
privately. Not a copy. **Disposition:** promotion to a public framed row when a second consumer
appears, or in the dedup window.

**AS-1, machine-specific step lemmas beside the general ones** (#182, gate 90, 2026-11-04). #182
publishes one step equation per instruction (`Complexity.LogProg.astep_inc` … `astep_jeqSnd`,
`Machines/ARM`). Three older lemmas state a step of one particular machine at one label:
`LogProg.astep_call₁` (`UnaryLogspace`: `astep_call` with `vword_unary₁`), and
`BoolCircuit.AdjScan.astep_hit` and `astep_jeqFst` (`CircuitComplexity/LogspaceUniformScan`). They
are specializations, not copies; the copy-text screen pairs none of them. The last shares its short
name with the general `astep_jeqFst`, and resolves by argument type in its own file, which opens
`Complexity.LogProg`. **Disposition:** in the dedup window (mechanical ARM edits, FYI), re-prove the
three through the general equations, and rename the circuit one if the shared name is unwanted.
**Extended (gate 90, minor 3):** three more specializations of `astep_call`:
- `BoolCircuit.AdjScan.astep_rd` (`LogspaceUniformScan:196`, with `vword_unary₁`);
- `BoolCircuit.AdjWalk.astep_call₁` and `astep_call₂` (`LogspaceUniformWalk:288, 298`, with
  `vword_unary₁` and `vword_unary₂`).

That makes six members. None is a copy: the screen with `LogspaceUniformWalk` added gives
170 → 179 declarations and 46 → 46 pairs, identical
(`campaign/gates/90-arm-embed-api/evidence/round1-fix/`). Same disposition, same window.

**NF-X1, an idiom exclusion** (NF's partial delivery, review F6; ruled by the user, 2026-11-04).
`NTimeHierarchy.lean::un_setup` reproduces 57% of `NDNormalForm.lean::nf_setup`. The shared text
is three invocations of the published initial-configuration field equations
(`MultiTapeTM.initCfg_eq`, `Cfg.init_state`, `Cfg.init_workTapes`): the idiom of reading the
initial configuration, not a re-derived composite. **Disposition:** excluded; not counted.

**E-D's delivery** (`exists_diagonalizer`, #188; review `campaign/fills/eq/reviews/ed-fill/`;
ruled by the user, 2026-11-04):
- **BL-1 (vi):** `dz_word_lt` (`Nat.ofDigits 2 (w.map Bool.toNat) < 2 ^ |w|`) is a new member,
  **acknowledged** for the dedup window's single home below both layers; `NTimeDiagonalizer`
  cannot reach `Machines/Bin`. Census `NTimeDiagonalizer` (vi) 1.
- **Removed at landing:** `dz_padded_value`'s inline re-derivation of Mathlib's
  `Nat.ofDigits_append_replicate_zero` (E3), and `dz_top_run`'s inline first halt, FH-1's
  `MultiTapeTM.exists_first_halt` (E4). Recorded so that the ledger shows them caught.
- **Promotion requests:** `dz_split_stream` restates `Build/NDHost`'s private `guessRun_split`
  (98%), to be promoted or given a public `List` form; `dz_word_lt` restates `ExhaustiveReplay`'s
  private `xr_val_lt` (65%), with BL-1 (vi)'s home.
- **QF-1, extended:** `dz_initCfg` and `qy_initCfg` state one fact for different machines ("a
  phase host's initial configuration is the blank seam in normal form"); one generic lemma over
  `phaseHostTM_q₀` and `initCfg_ofWords`.
- **RC-3, row candidates:** the clocked hosted run (`DzClockSpec`, `dz_clock_exists`); the
  silent-transport reconstruction (`dz_silentCfg_eq`), beside `embedEmitCfg_eq`; and the output
  length of a computed function (`dz_out_le`, `|F y| ≤ T |y|`), also inline in `SAT`,
  `Nondeterminism`, `TMSAT` and `Build/Loop`'s private `loop_fuel_width`. **Disposition:** the
  dedup window.
- **Census, landed (gate 93, finding 4):** 8 of `NTimeDiagonalizer`'s 342 declarations (2.3%),
  deduplicated: RO-1's one, the five distinct NB-1/BL-1/LS-3 members, `dz_word_lt` and
  `dz_split_stream`. E1 retires `qy_call_bound`'s BL-1 (iii) step. Row candidates (RC-3) and
  in-file factorings (QF-1) are not counted as debt.
- **ED-IN, inline re-derivations, scoped by kind (ruled by the user, 2026-11-04, gate 93 round
  2):** any inline step in `NTimeDiagonalizer` that re-derives a published run, buffer or segment
  lemma belongs to this family, for the dedup window; a later find is an accounting minor. The
  members found so far are all removed: `dz_first` (`Segment.time_eq`), `dz_split`'s separator
  (`bufferTape_append_mid`), `dz_split_tape`'s prefix (`bufferTape_take`), `dz_top_run`'s output
  (`runFrom_output_eq_of_halt`), and three natural cells (`bufferTape_nat`).
  **Further member (gate 93 round 3, finding 1):** `qy_patch_end`'s prefix branch re-derives
  `FinTM.bufferTape_take` (and so `_take` has a counterpart, against BW-1's note); re-pointed in the
  dedup window. Census 9 of 342.
- **Removed in round 2 (gate 93, findings 1–2):** `dz_first` re-proved `Segment.time_eq`, and
  `dz_split`'s separator cell re-proved `FinTM.bufferTape_append_mid`. Both now cite them (#188
  `a64f513d`).

**NF cont1's delivery, F2: four kinds re-stated** (review
`campaign/fills/c1/reviews/nf-cont1-fill/`; ruled by the user, 2026-11-04: **publish homes
first**). An API PR publishes each fact beside its definitions before NF lands, and NF's landing
cites them:
- (i) the input read depends on the input head only (`nf_inputSymbol_congr`; privates
  `ExhaustiveReplay.xr_inputSymbol_congr`, `ZoneRebalance.zr_inputSymbol_congr`);
- (ii) a live configuration redirected to `⟨i, q⟩` is phase `i`'s tagged configuration at `q`
  (`nf_retag`; `SeamLayout`'s private `sl_rewrap`, and inline in 15 declarations);
- (iii) a configuration tagged by phase `i` is at no state of another phase (`nf_tagged_ne_park`;
  privates `CfgRecord.record_tag_ne`, `SeamLayout.sl_tagged_ne_done`);
- (vi) the length of a list of equal-length chunks (`nf_stream_length`; public as
  `Complexity.CfgTableau.length_flatMap_const` in colleague-owned `CircuitComplexity`, which
  NF cannot import).

The existing private copies are re-pointed in the API PR where the files are the campaign's.
*Numbering (gate 95, note 9):* the kinds carry the review's labels, (i)–(iii) and (vi), as in the
decision put to the user. This entry first numbered the chunk length (iv), which collided with the
review's F8 (iv), the buffer end (RC-4 below). The review uses no (v).

**RN-1, renamed configurations converted field by field, scoped by kind** (ruled by the user,
2026-11-04, with gate 94). #190 publishes the general fact, `Turing.Cfg.mapState_eq_of_fields`: a
renamed configuration equals any configuration with its data fields and the renamed state.
- **The family:** every inline proof of that fact anywhere in TCSlib (the five-line
  `Cfg.ext`/`Cfg.mapState_*` block), with the retag (ii) as an instance. A later find is an
  accounting minor.
- **Re-pointed in #190:** `CfgRecord`'s `recordStep_mapState_eq` (removed), `SeamLayout`'s
  `sl_rewrap`, and `ExhaustiveReplay`'s `xr_phase_step` (two blocks) and `xr_halt_fixed` (two
  blocks).
- **Remaining, for the dedup window** (gate 94's minors 1–2, 2026-11-05; counted as conversions
  inside declarations, not copies of their statements). By file:
  - `CodeSimulator`: `canonStageLeg0`–`6`, `canonStageOuterSpec`, `canonStageInnerSpec`,
    `us_start` (10);
  - `ZoneRebalance`: 21 of about 870 (2.4%). These are `zr_short_fields`,
    `zr_rightSeekBack_post`, `zr_rightRuler_post`, `zr_adjustedWalk_post`,
    `zr_adjustedBack_post`, `zr_writeHalves_post`, `zr_rightPass_post`, `zr_test_post`,
    `zr_body_post`, `zr_return_post`, `zr_rightReturn_post`, `zr_rightLeft_post`,
    `zr_twoSteps_fields`, `zr_leftMove_fields`, `zr_leftWrite_fields`, `zr_leftPass_fields`,
    `zr_final_fields`, `zr_extend_fields`, `zr_scanBody_fields`, `zr_scan_fields` and
    `zr_countClear_fields`. RI-1's `zr_pinLoop` is retired and not counted;
  - `NDHost`: `gr_handoff`, `guessCtlRunTM_stop_of_halted`;
  - one each in `ExhaustiveReplay` (`xr_E_initCfg`), `NDCodeSimulator`
    (`exists_ndInterpreterCore`), `Seam` (`phaseHostTM_run`), `InputRewind`
    (`Cfg.mapState_mapState`), `NTimeHierarchy` (`un_setup`; NF-X1's pair too) and `SeamLayout`
    (`exists_seamLayoutTM`).

  The NF review's F2 list has 19 names, not 15; its `xr_phase_step` and `xr_halt_fixed` are
  re-pointed. No file crosses one fifth. NF's own copies (`nf_retag`, `nf_tag`, …) are checked at
  NF's landing (#191), where they cite `CfgFacts`.
The 15 inline (ii) steps and `CircuitComplexity`'s lemma go to the dedup window (the latter under
its own authorization). Also removed at NF's landing: `nf_all_cons`'s re-derivation of Mathlib's
`Nat.forall_lt_succ_left'` (E1).

**RN-1, an accounting minor at NF's landing** (gate 95, minor 3; 2026-11-05). `NDNormalForm`'s
`nf_pack` proved its local `hinit`, `(H.relabelState e).initCfg x = (H.initCfg x).mapState e`
(lines 62–69 at #191's head `e8994dc1`), by the five-line block: an RN-1 member that the list
above did not name. It is inside the family, so a minor. #191's repair commit `10c01517` cites
`(Cfg.mapState_eq_of_fields …).symm` there, as `nf_tag` does since `5732d5bd`. The file's other
eleven `Cfg.ext` blocks (`nf_sweep_run`, `nf_entry` and nine leaf-run endpoints) are
configuration-record equations, not renamings, so they are not members. Census: `NDNormalForm`
1 of 104 declarations at `e8994dc1`, none at `10c01517`.

**NF's landing, gate 95's major 1: repaired, no new family** (#191; ruled by the user,
2026-11-05: **repair**). At the landed head `NDNormalForm` imports `TuringMachine/BufferWords`,
but three inline steps still re-proved its identities, outside every acknowledged family (ED-IN
is scoped to `NTimeDiagonalizer`, BW-1 to `StepBlock`'s privates, RN-1 to renamings):
- `nf_bClear`'s `hw`, `bufferTape R (p + i) = bufferTape (R.drop i) p` for `0 ≤ p`, by
  `bufferTape_nat` twice and `List.getElem?_drop`: that is `FinTM.bufferTape_drop`;
- `nf_aReturn`'s `hw` (cell `|s|`) and `nf_region`'s cell `|R|`, blank at the buffer's end by
  `bufferTape_nat` and `List.getElem?_eq_none`: that is `FinTM.bufferTape_eq_none_of_not_mem`.

The steps came from the brief's own route probes, written when the fill could not import
`BufferWords`. #191's repair commit `10c01517` cites the two lemmas at the three sites, and no
member remains. Recorded so that the ledger shows them caught.

**Gate 95's round-2 major 1** (#191; repaired, the round-1 ruling's kind): `nf_split`'s local `h0`
rebuilt a list from its indexed entries by `List.ext_getElem`, re-proving Mathlib's
`List.ofFn_getElem` (with the index length moved by `List.ofFn_congr`). #191's commit `dfc3e990`
cites the two lemmas. No family; recorded so that the ledger shows it caught.

**The library sweep that followed** (gate 95, round 3; `evidence/round3/sweep/`). Every `have`,
`obtain` and private theorem of the file about core or Mathlib objects only, probed by `exact?`
in place, as a generalised `example` and as its normalised core with `apply?`. It found eight
further inline re-proofs, all of one published lemma each:
- `Nat.succ_mod_succ_eq_zero_iff` (`nf_ctl_position`), `Nat.pos_of_mul_pos_left`
  (`nf_display_firstStop`, `nf_firstStop_records`), `Nat.div_lt_of_lt_mul`
  (`nf_display_firstStop`), `Nat.mul_div_cancel'` (`nf_firstStop_records`);
- `List.ofFn_eq_nil_iff` (`nf_split`), `List.ne_nil_of_length_pos` (`nf_V_display`,
  `nf_forward`; the file already cited it twice).

It also found two rewrite chains that are each one lemma: `List.length_take` with
`Nat.min_eq_left` is `List.length_take_of_le` (eight sites), and `List.foldl_append`,
`foldl_cons`, `foldl_nil` on `l ++ [x]` is `List.foldl_concat` (seven sites). Separately,
`nf_prefix_last` and `nf_sweep_record` proved the same completion of the parser's prefix array;
it is now one private, `nf_update_last`. #191's commit `49c4d0f7` repairs all of them, with no
statement change. No family; no member remains.

**Gate 95's round-3 major 1**: one more member, which the sweep's candidate list missed because it
is an untyped `have`. `nf_display_firstStop`'s `he` (`Nat.mod_add_div`, then the zero remainder)
re-proved `Nat.mul_div_cancel'`; #191's commit `698dcdf5` cites it. The sweep now also takes every
untyped `have`/`obtain` on a core or Mathlib term with a later rewrite `at` it (gate 95,
`evidence/round4/sweep/`); the one other such site, `nf_display_flag`'s `hm`, has no library
statement. No family; no member remains.

**Gate 95's round-4 major 1**: one more fold-concatenation member, in `nf_ctl_position`'s
`simp only` set, which the round-3 sweep had wrongly exempted as a simp set. #191's commit
`b4af93b7` cites `List.foldl_concat`. The sweep now checks every member of both chain classes
anywhere in the file (gate 95, `evidence/round5/sweep/`). No family; no member found by that
check.

**RC-4, row candidates from NF cont1** (the cont1 review's F8, 2026-11-04; completed by gate 95's
note 9, 2026-11-05). The review's list "for the ledger" named F8's row candidates; they were not
carried here until now.
- **The first halting time of a choice word**, FH-1's kind for `NDTM.runWith`: `Nat.find` over
  the run's prefixes (`find_spec`, `find_min`, `find_min'`), then the output after the halt by
  `NDTM.runWith_append` and `NDTM.runWith_of_halt`. FH-1's public form,
  `MultiTapeTM.exists_first_halt`, is deterministic, and no `NDTM` form exists. It runs inline at
  two sites: `NDNormalForm`'s `nf_forward` (lines 3097–3127 at #191's head `e8994dc1`) and
  `ExhaustiveReplay`'s `xr_replay_host` (lines 2179–2189 at the campaign tip). Neither
  re-derives a lemma. **Disposition:** a public `NDTM` first-halt row in the dedup window
  (12.2c), cited at both sites.
- **(iv) a buffer is blank at and past its end** is not a row candidate after all: the review's
  "no public form" held only at the fill's frozen imports. `FinTM.bufferTape_eq_none_of_not_mem`
  (`TuringMachine/BufferWords`, public since PR #140; BW-1) states it. NF's three inline sites
  cite it: `nf_entry` since `4354cbeb`, `nf_aReturn` and `nf_region` since `10c01517` (major 1
  above). `CodeSimulator`'s private `canonStageBuffer_none` (lines 5040–5043 at the campaign
  tip; six invocations at five locations: lines 5203, 6422, 6566, 6778 and twice at 7022, corrected
  by gate 95's round-2 minor 3) restates it for cells at or past the end. **Disposition:** the dedup
  window (12.2c): re-point all six invocations to `FinTM.bufferTape_eq_none_of_not_mem` and delete
  it.
  `CodeSimulator` does not import `BufferWords` yet; the import is acyclic (`BufferWords`
  imports only `Simulation`).

Census (members over all declarations, as the style lint counts them, at the campaign tip):
`CodeSimulator` 1 of 208 (`canonStageBuffer_none`). With CC7-1's eleven and RN-1's three others
(`canonStageOuterSpec`, `canonStageInnerSpec`, `us_start`, the last also RS-1's), the file holds
15 of 208 (7.2%). The first-halt sites are row candidates and are not counted, as in RC-1–RC-3.
The one-fifth rule is not reached.

**WS-1, one step keeps a configuration in a window, and window monotonicity, scoped by kind**
(#196, the deepening's API; gate 96, major 2; acknowledged by the user, 2026-11-05, and widened by
kind the same day). #196's public `Turing.Cfg.InWindow.apply_of_lt` (`Build/CfgRecord`)
re-derived its own file's private `recordStep_window` (line 679 at #196's head `89f4ebbc`), and
one of its steps repeated `ExpBFS.inWin_mono`'s second component verbatim. The v3 screen paired
none of them (the proofs are restructured), and no family covered the kind, so it was a debt
major.
- **Ruled (user, 2026-11-05): harvest.** On #196's repaired head `b1b5199b`, `recordStep_window` is
  public as `Turing.Cfg.InWindow.apply_iff`, over any alphabet, beside the new
  `Turing.Cfg.InWindow.mono`; `apply_of_lt` is proved from the two; and the record step
  (`recordStep_observed_action`), the private lemma's one use, cites `apply_iff`.
- **The family, acknowledged by kind for 12.2c (user, 2026-11-05), widened by kind (user,
  2026-11-05):** every proof, anywhere in TCSlib, that one step keeps a configuration within a
  window of any shape (the radius window `Cfg.InWindow`, a per-tape radius, an interval, a
  visited interval), and every proof of window monotonicity. A later find is an accounting minor.
  The canonical statements:
  - `Turing.Cfg.InWindow.apply_iff`: for `c` in the radius-`s` window, `(a.apply c).InWindow s`
    holds iff no work head is at `-s` moving left or at `s` moving right;
  - `Turing.Cfg.InWindow.mono`: `c.InWindow s → s ≤ s' → c.InWindow s'`;
  - **the tape half**, to be published in the 12.2c window: an action changes a work cell only
    under that tape's old head (`z ≠ c.workTapePos i → (a.apply c).workTapes i z =
    c.workTapes i z`). It exists today as `TuringMachine/Oracle`'s private
    `apply_workTapes_eq_of_ne` (line 304 at the campaign tip), the natural one to harvest.
- **Members on `Cfg.InWindow`** (lines at the campaign tip):
  - `Complexity.ExpBFS.inWin_mono` and `inWin_stepWith` (`SpaceComplexity/ExpBFS/Radius`, lines
    63 and 70; Hydroxyi's): the monotonicity, and one choice step from radius `s` into `s + 1`;
  - the window half of `Complexity.Codec.boundary_iff` (`SpaceComplexity/Codec/Step`, line 195;
    Hydroxyi's): once the two boundary cells are read as head conditions, `apply_iff`;
  - `codec_step_blank` (private, `ClassPSPACE/TQBF`, line 1505; the campaign's): the tape half at
    the same radius for one deterministic step;
  - `xr_window_stepWith` (private, `ClassNP/ExhaustiveReplay`, line 67; the campaign's):
    `inWin_stepWith` for any machine, with `Cfg.InWindow`'s two clauses written out (its output
    bound is outside the kind).
- **Members over other window shapes** (the widening; all the campaign's):
  - `Turing.FinTM.source_bounds` (`TuringMachine/Sweep`, line 359): the interval `[-t, t]`, its
    one-step case inline;
  - `Turing.OracleTM.step_radius` (`TuringMachine/Oracle`, line 346): a per-tape radius, one
    oracle step, through the private tape half above;
  - `dgWindow_step` (private, `TuringMachine/Robustness/SingleTape`, line 1933): the window part of
    a grown interval (its visited, history and size fields are outside the kind);
  - `emCall_track_support` with `emCall_track_extent` (private, `TuringMachine/Build/Loop`, lines
    3316 and 3294): the visited interval of a source run, its step inline.
- **Disposition:** the dedup window (12.2c): publish the tape half, then re-prove the members from
  the canonical statements or re-point their uses; a member over another window shape keeps its
  own statement and cites the canonical ones for its step. Eight of the members re-prove the tape
  half.

Census (members over **all source declarations**, public and private, anonymous instances
included, as `devtools/seyoon/declfreeze.py` counts them at #196's repair `b1b5199b`; corrected
by gate 96's round-2 minor 1, which found the style lint's count, without the seven anonymous
private instances, used before): `Build/CfgRecord` 2 of 137 (1.5%; the canonical pair), 3 of 137
(2.2%) with RO-1's `recordStep_runFrom_one`; `ExpBFS/Radius` 2 of 27 (7.4%) for WS-1, and **3 of
27 (11.1%) cumulatively** with CE-1's `coreSum_eq_of_code_eq`; `Codec/Step` 1 of 30 (3.3%); one
member each in `TQBF`, `ExhaustiveReplay`, `Sweep`, `Oracle` (`step_radius`; its private
`apply_workTapes_eq_of_ne` is the tape half's harvest source, not a copy) and
`Robustness/SingleTape`, and two declarations in `Build/Loop`. The one-fifth rule is not
reached.

**WL-1, a `WalkLe` equation in a consumer file** (gate 96, minor 3's residue; recorded
2026-11-05). `Complexity.LogProg.ISCount.walkLe_succ_iff` (`Logspace/ISCountMath`, line 120),
the last-edge form
`WalkLe R K (j + 1) c t ↔ WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K`,
is a fact about `Complexity.WalkLe` (`Logspace/PathWalk`) that lives in a consumer file and
namespace, and its proof unfolds `WalkLe` by `simp only [WalkLe]`, a cross-file unfolding.
Since #196's repair (`b1b5199b`) `SavitchARM/Reach` no longer uses it: `chain_of_walkLe` reads
walks at the front through the new `Complexity.walkLe_succ_iff_head` (`PathWalk`, `Iff.rfl`),
and `Reach` imports `PathWalk` instead of `ISCountMath`. Its remaining uses are in
`ISCountMath`'s own `mem_succ_iff`. Not a copy. **Disposition:** the dedup window (12.2c): move
it beside `WalkLe` in `PathWalk`, or re-prove it there from `walkLe_succ_iff_head` without
unfolding, and cite it from `ISCountMath`. Both files are Hydroxyi's. **Ruled (the user, 2026-11-06): move it
to `PathWalk` as `Complexity.walkLe_succ_iff`, after #216 (which removes its unfolding) merges.**

**WC-1, a window-run closure lemma (optional)** (gate 96, note 10; recorded 2026-11-05).
`Complexity.ExpBFS.winRun_of_card_eq` (`ExpBFS/Radius`) and the induction inside
`Complexity.LogProg.SavitchARM.mem_iff_reach_of_noEdge` (`SavitchARM/Window`) share about ten
lines of one skeleton: extend a window run by `WinRun.snoc`, then finish with `rcode_iff` and
`mem_acceptLang`. The closing steps differ: a shared pattern, not a copy. The induction also
shows more than it states: under `NoEdge`, every word is a window run. **Disposition
(optional):** the dedup window (12.2c): one closure lemma, "if every one-step extension of a
window run stays in the window, every word is a window run", from which `winRun_of_card_eq` and
a public `winRun_of_noEdge` both follow.

**QL-X1, an idiom exclusion: the query layout** (gate 96, note 11; ruled by the user,
2026-11-05). `SavitchARM/Window`'s `NoEdge` reproduces 85% of `SavitchARM/Recursion`'s `Rel` on
the v3 screen. The shared text is the query layout
`pairEncode x (pairEncode (bits u) … (bits s))`, through which each predicate reads a code
language or an oracle answer; `NoEdge` restates none of `Rel`'s meaning. **Ruled (user,
2026-11-05): an idiom**, as with NF-X1's. **Disposition:** excluded; not counted.

**CQ-1, codec-level query predicates** (gate 96, note 11; opened by the user, 2026-11-05, as a
12.2c item). The queries "`⟨x, ⟨bits u, bits s⟩⟩` is in `initLang N`" (and likewise for
`acceptLang N` and `edgeLang N`) are spelled out wherever they are used: in
`Complexity.LogProg.SavitchARM`'s `mem_iff_reach` and `NoEdge`, and in the deepening's block-fit
lemmas (the design's `BlockFit` probe: `fit_initO`, `fit_edgeO`, `fit_accO`, `fit_edge_block`).
`Logspace/ISCountGenRadius` names two of them as public `abbrev`s in a consumer file,
`ISGen.InitM` and `ISGen.AccM`, with no `_iff` lemmas. **Disposition:** the dedup window
(12.2c): a `def` per query, each with its `_iff` lemma, beside `initLang`, `acceptLang` and
`edgeLang` (`SpaceComplexity/Codec/Langs`), replacing `ISGen`'s `InitM` and `AccM` and serving
`mem_iff_reach`, `NoEdge` and the fit lemmas alike. `Codec/Langs` and `ISCountGenRadius` are
Hydroxyi's: interface design in their files. **Ruled (the user, 2026-11-06): as disposed, with
`ISGen.InitM`/`AccM` deleted and their uses re-pointed.**

**RP-1, definitional reads that #196's equations can replace** (gate 96, the round-2 shape
search; recorded 2026-11-05; not duplication). #196 publishes `Iff.rfl` equations for `WalkLe`,
`StepRel`, `RCode`, `WinRun`, `Rel`, `InitO` and `AccO`. Colleagues' files read these definitions
by unfolding or by definitional equality: `WalkLe` in `Logspace/ISCountGenWalk` (83–105),
`PathWalkMachine` (429–439) and `ISCountMath` (124); `StepRel` in `ExpBFS/Radius` (167),
`Logspace/PathHard` (232) and `Randomized/BPLInPCount` (119); `RCode` in `ExpBFS/Main` (98–104)
and `ISCountGenRadius` (88–92); `Rel`, `InitO` and `AccO` in `SavitchARM/Correct` (55–71); lines
at the campaign tip. **Disposition:** the dedup window (12.2c): re-point them to the equations.
Not counted.
**Widened and in PR #216** (2026-11-06; gate 107): a scoping pass and an exhaustive irreducibility
probe (52 modules) found 23 public proof bodies in 14 files, including `SavitchARM/Reach`'s
`mem_iff_reach` (probe only); all re-pointed (`f200144b`, `3d0f6ceb`). **Retired on #216's merge.**

**CE-1, equal codes of window configurations, copied** (found 2026-11-05 by gate 96's round-2
screen; **acknowledged by the user for 12.2c, 2026-11-05**). `coreSum_eq_of_code_eq` (equal
radius-`s` codes of two configurations in the radius-`s` window give equal vertices) is public, with
the same statement and the same one-line proof through `coreSum_eq_of_cfgWord_eq`, in
`SpaceComplexity/ExpBFS/Radius` (`Complexity.ExpBFS`, line 126 at the campaign tip) and in
`Randomized/BPLInPCount` (`Randomized.BPLInP`, line 106). Both files are Hydroxyi's, and the copy
predates #196. **Disposition:** the dedup window (12.2c): keep `ExpBFS`'s and re-point
`BPLInPCount`'s uses. Census: one declaration in each file.

**ZP-1, the zone row's precondition under a change of state** (#197, G5's consumer API; gate 97,
minor 5; ruled by the user, 2026-11-05). `Turing.zoneRowPre` (`Build/ZoneRebalance`) reads only
the work tapes and work tape `0`'s head, so it holds of a configuration exactly when it holds
after the state is renamed or rebound. No public lemma said so. `Build/ZoneStep` re-derived it
privately (`zs_rowPre_mapState`); G5's controller needs it too (its phase host starts a phase at
`d.mapState (fun _ => s₀)` and returns `post.bindState (red p)`); and `ZoneRebalance` proves it
inline twelve times, unfolding `zoneRowPre` with `funext_iff`, `Cfg.mapState_workTapes` and
`Cfg.mapState_workTapePos`. That is legal in the definition's home, so there is no rule-10 issue.
- **Ruled (user, 2026-11-05): publish** `zoneRowPre_congr` (across state types: equal work tapes
  and equal tape-`0` heads give the same precondition, which covers `mapState` and `bindState`)
  and its corollary `zoneRowPre_mapState_iff`, beside `zoneRowPre`. Done on #197's head
  `20e7fc75`; `ZoneStep` cites them, and its private copy is gone.
- **The twelve inline sites are re-pointed in the 12.2c window** (the same ruling): lines 831,
  884, 906, 1239, 2275, 2301, 2362, 3330, 3354, 3432, 3512 and 3539 at #197's original head
  `0a1b64d5` (each 22 lines lower at `20e7fc75`), one in each of `zr_rightSeekBack_post`,
  `zr_rightSeekBack_ruler_pre`, `zr_rightRuler_pre`, `zr_rightPass_pre`, `zr_rightReturn_pre`,
  `zr_rightReturn_post`, `zr_rightReturn_bounds`, `zr_rightLeft_pre`, `zr_rightLeft_post`,
  `zr_rightLeft_fields`, `zr_extend_pre` and `zr_extend_fields`.
- **Not RN-1, by kind.** RN-1's fact is a configuration equation (`Cfg.mapState_eq_of_fields`: a
  renamed configuration equals any configuration with its data fields and the renamed state),
  and its family is the five-line `Cfg.ext`/`Cfg.mapState_*` block. These twelve prove one
  predicate's invariance under a change of state, with no `Cfg.ext` and no configuration
  equation, so they are this 12.2c item, with `zoneRowPre_congr` and `zoneRowPre_mapState_iff`
  as its canonical statements. (Gate 97's pre-dispatch sweep, `evidence/sweep/README.md`, called
  `zs_rowPre_mapState` "RN-1's kind"; by RN-1's scope it belongs here.)
- **G5 (#211, gate 102; the review's F4):** `TwoTapes` does not cite the pair. Each phase starts at
  a configuration built at the phase's own state type (`tt_cfg_rowPre`), and each endpoint is
  converted by `tt_mapState_eq_cfg` through `zoneRowPre_iff` and RN-1's `Cfg.mapState_eq_of_fields`;
  nothing re-derives the state-independence. Not a member; the maintainer accepts the route.

Census (inline steps inside declarations, counted as RN-1's are; members over all declarations,
as the style lint counts them, at `20e7fc75`): `ZoneRebalance` 14 of 875 (1.6%: the twelve sites
and the canonical pair). Four of the twelve declarations also hold an RN-1 block
(`zr_rightSeekBack_post`, `zr_rightReturn_post`, `zr_rightLeft_post`, `zr_extend_fields`), so with
RN-1's 21 the file holds 31 of 875 (3.5%). The one-fifth rule is not reached.

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-BPLInP.txt =====

public before/after: 32 32 private before/after: 0 0
public added: []
public removed: []
authorized body change: Randomized.BPLInP.entryW_eq
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-BPLInPCount.txt =====

public before/after: 11 11 private before/after: 0 0
public added: []
public removed: []
authorized body change: Randomized.BPLInP.stepRel_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-Correct.txt =====

public before/after: 8 8 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.SavitchARM.accO_orcN
authorized body change: Complexity.LogProg.SavitchARM.initO_orcN
authorized body change: Complexity.LogProg.SavitchARM.rel_orcN
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-ISCountGenRadius.txt =====

public before/after: 9 9 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.ISGen.mem_ball_iff_rcode
authorized body change: Complexity.LogProg.ISGen.mem_of_exists_acc
authorized body change: Complexity.LogProg.ISGen.one_le_card_rset
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-ISCountGenStage.txt =====

public before/after: 3 3 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.ISGen.guloop
authorized body change: Complexity.LogProg.ISGen.gvloop
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-ISCountGenWalk.txt =====

public before/after: 2 2 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.ISGen.gwalk_loop
authorized body change: Complexity.LogProg.ISGen.gwalk_spec
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-ISCountMath.txt =====

public before/after: 17 17 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.ISCount.card_ball_zero
authorized body change: Complexity.LogProg.ISCount.walkLe_lt
authorized body change: Complexity.LogProg.ISCount.walkLe_succ_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-Main.txt =====

public before/after: 23 23 private before/after: 1 1
public added: []
public removed: []
authorized body change: Complexity.LogProg.ExpBFS.cl_iff
authorized body change: Complexity.LogProg.ExpBFS.stp_orcN
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-PathHard.txt =====

public before/after: 20 20 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.PathHard.red_mem_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-PathHardRegs.txt =====

public before/after: 62 62 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.PathHard.orc_step
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-PathWalkMachine.txt =====

public before/after: 37 37 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.LogProg.ps_walk
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-Radius.txt =====

public before/after: 27 27 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.ExpBFS.rcode_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-Reach.txt =====

public before/after: 8 8 private before/after: 1 1
public added: []
public removed: []
authorized body change: Complexity.LogProg.SavitchARM.mem_iff_reach
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/freeze/declfreeze-TQBFHardMachine.txt =====

public before/after: 8 8 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.TQBFHard.reflTransGen_stepRel
private removed: []
private added: []
private changed: []

## ===== campaign/gates/107-rp1-dedup/evidence/landing/rp1-merged.diff =====

diff --git a/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean b/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
index bf14ec15..1ad78913 100644
--- a/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
+++ b/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
@@ -121,9 +121,7 @@ theorem reflTransGen_stepRel (x : List Bool) (s u : ℕ) {γ : List Bool}
     have hs := bits_injective h6
     subst hc₂ hs
     refine (ih c₁ h3).tail ?_
-    show pairEncode x (pairEncode (Nat.bits c₁) (pairEncode (Nat.bits c) (Nat.bits s))) ∈
-      stepLang N
-    rw [← h3]
+    rw [stepRel_iff_mem, ← h3]
     exact hst
 
 /-- **Acceptance as a block path** ([AB09, Claim 4.4(1)] in the form of the proof of
diff --git a/TCSlib/Complexity/Randomized/BPLInP.lean b/TCSlib/Complexity/Randomized/BPLInP.lean
index 689c48a1..55b06b3b 100644
--- a/TCSlib/Complexity/Randomized/BPLInP.lean
+++ b/TCSlib/Complexity/Randomized/BPLInP.lean
@@ -226,7 +226,7 @@ theorem entryW_eq (s a a' v : ℕ) :
       Nat.bits ((if StepRel (fixCoin N false) x s a a' then v else 0) +
         (if StepRel (fixCoin N true) x s a a' then v else 0)) := by
   simp only [entryW, stepTest, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator,
-    StepRel]
+    stepRel_iff_mem]
   split_ifs <;> simp_all [add, bitsVal_bits, LogProg.bitsVal]
 
 /-- The initial state is the context and the table after `0` rounds. -/
diff --git a/TCSlib/Complexity/Randomized/BPLInPCount.lean b/TCSlib/Complexity/Randomized/BPLInPCount.lean
index f1170da3..18a9cf33 100644
--- a/TCSlib/Complexity/Randomized/BPLInPCount.lean
+++ b/TCSlib/Complexity/Randomized/BPLInPCount.lean
@@ -111,7 +111,8 @@ theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length 
     rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
   constructor
   · intro h
-    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ := (mem_stepLang (fixCoin N b) x _ _ s).mp h
+    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ :=
+      (mem_stepLang (fixCoin N b) x _ _ s).mp (stepRel_iff_mem.mp h)
     have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
       ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
     rw [← hcC', ← hb']
@@ -119,8 +120,8 @@ theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length 
     rw [stepWith_fixCoin, hstep]
     exact congrArg bitsVal (cfgWord_congr (NDTM.coreSum_stepWith N.tm b hcore))
   · rintro rfl
-    refine (mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v, inWin_run hN hs v, rfl,
-      run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩
+    refine stepRel_iff_mem.mpr ((mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v,
+      inWin_run hN hs v, rfl, run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩)
     change (fixCoin N b).tm.stepWith b (run v) = _
     rw [stepWith_fixCoin, hstep]
 
diff --git a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
index 044345da..0b9a4a83 100644
--- a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
+++ b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
@@ -77,7 +77,7 @@ lemma ini_orcN (r u : ℕ) :
 
 /-- Decider `2` answers the step relation. -/
 lemma stp_orcN (r u v : ℕ) : stp (orcN N) x r u v = true ↔ Codec.StepRel N x r u v := by
-  simp [stp, orcN, decs, indicator_eq_decide, Codec.StepRel]
+  simp [stp, orcN, decs, indicator_eq_decide, Codec.stepRel_iff_mem]
 
 /-- Decider `3` answers whether a code is accepting. -/
 lemma acc_orcN (r u : ℕ) :
@@ -85,25 +85,31 @@ lemma acc_orcN (r u : ℕ) :
       pairEncode x (pairEncode (Nat.bits u) (Nat.bits r)) ∈ Codec.acceptLang N := by
   simp [orcN, decs, indicator_eq_decide]
 
-/-- **The codes reachable below `K` are the reachable codes**, once `K` bounds the codes. -/
+/-- **The codes reachable below `K` are the reachable codes**, once `K` bounds the codes.
+
+**Proof sketch.** `→`: a search path from the initial code is a path of the step relation
+(`stp_orcN`), so its end is reachable (`ExpBFS.rcode_iff_reflTransGen`). `←`: induct on a
+reachability path; each code on it is reachable, so it is below `K` (`ExpBFS.rcode_lt` and `hK`),
+and each step is a search step (`stp_orcN`). -/
 lemma cl_iff {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1)) ≤ K) (v : ℕ) :
     Cl (orcN N) x r K v ↔ ExpBFS.RCode N x r v := by
   constructor
   · rintro ⟨u, -, hi, hpath⟩
     rw [ini_orcN] at hi
     subst hi
-    exact hpath.mono fun a b h => (stp_orcN r a b).mp h.1
+    exact ExpBFS.rcode_iff_reflTransGen.mpr (hpath.mono fun a b h => (stp_orcN r a b).mp h.1)
   · intro h
     refine ⟨_, (Codec.cfgCode_lt r _).trans_le hK, (ini_orcN r _).mpr rfl, ?_⟩
     have key : ∀ w, ExpBFS.RCode N x r w → Relation.ReflTransGen
         (fun a b => stp (orcN N) x r a b = true ∧ b < K)
         (Codec.cfgCode r (N.tm.initCfg x)) w := by
       intro w hw
+      rw [ExpBFS.rcode_iff_reflTransGen] at hw
       induction hw with
       | refl => exact Relation.ReflTransGen.refl
       | @tail b c hab hbc ih =>
         exact ih.tail ⟨(stp_orcN r b c).mpr hbc,
-          (ExpBFS.rcode_lt (hab.tail hbc)).trans_le hK⟩
+          (ExpBFS.rcode_lt (ExpBFS.rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK⟩
     exact key v h
 
 open Classical in
diff --git a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
index bbc05e6d..1cf0278d 100644
--- a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
+++ b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
@@ -162,7 +162,8 @@ theorem rcode_iff (s u : ℕ) :
     | refl => exact ⟨[], fun j _ => by simpa using inWin_init s, rfl⟩
     | tail _ hst ih =>
       obtain ⟨w, hw, hcode⟩ := ih
-      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
+      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ :=
+        (mem_stepLang N x _ _ s).mp (stepRel_iff_mem.mp hst)
       have hv : NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum C :=
         coreSum_eq_of_code_eq hw.last hC (hcode.trans hcC.symm)
       have hv' : NDTM.coreSum (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) = NDTM.coreSum C' := by
@@ -179,7 +180,7 @@ theorem rcode_iff (s u : ℕ) :
       | succ j ih =>
         intro hj
         refine (ih (by omega)).tail ?_
-        rw [StepRel, mem_stepLang]
+        rw [stepRel_iff_mem, mem_stepLang]
         refine ⟨_, hw j (by omega), rfl, _, ⟨w[j]'(by omega), ?_⟩, hw (j + 1) hj, rfl⟩
         rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
         rfl
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
index b58ac31f..dad3a220 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
@@ -83,15 +83,17 @@ theorem mem_ball_iff_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.leng
   · rintro ⟨u, hu, hinit, hw⟩
     rw [InitM, mem_initLang] at hinit
     subst hinit
-    exact (walkLe_reach hu hw).mono fun a b hab => hab.2.2
+    exact rcode_iff_reflTransGen.mpr ((walkLe_reach hu hw).mono fun a b hab => hab.2.2)
   · intro ht
     have hpath : ∀ t, RCode N x s t → Relation.ReflTransGen
         (fun u v => u < K ∧ v < K ∧ StepRel N x s u v) (cfgCode s (N.tm.initCfg x)) t := by
       intro t ht
+      rw [rcode_iff_reflTransGen] at ht
       induction ht with
       | refl => exact Relation.ReflTransGen.refl
       | @tail b c hab hbc ih =>
-        exact ih.tail ⟨(rcode_lt hab).trans_le hK, (rcode_lt (hab.tail hbc)).trans_le hK, hbc⟩
+        exact ih.tail ⟨(rcode_lt (rcode_iff_reflTransGen.mpr hab)).trans_le hK,
+          (rcode_lt (rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK, hbc⟩
     have h0 : cfgCode s (N.tm.initCfg x) < K := (cfgCode_lt s _).trans_le hK
     obtain ⟨j, hw⟩ := exists_walkLe (hpath t ht)
     exact ⟨_, h0, by rw [InitM, mem_initLang], walkLe_short ((rcode_lt ht).trans_le hK) h0 hw⟩
@@ -114,7 +116,7 @@ theorem card_ball_zero_code {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.len
 
 /-- There is a reachable code (the initial one). -/
 theorem one_le_card_rset (s : ℕ) : 1 ≤ (rset N x s).card :=
-  Finset.card_pos.mpr ⟨_, mem_rset.mpr Relation.ReflTransGen.refl⟩
+  Finset.card_pos.mpr ⟨_, mem_rset.mpr (rcode_iff_reflTransGen.mpr Relation.ReflTransGen.refl)⟩
 
 /-- **No accepting code in the balls** `C_1, …, C_K` iff no reachable code is accepting. -/
 theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
@@ -131,7 +133,7 @@ theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length
 theorem mem_of_exists_acc {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
     {s : ℕ} (h : ∃ t, RCode N x s t ∧ AccM N x s t) : x ∈ L := by
   obtain ⟨t, ht, hacc⟩ := h
-  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) ht hacc
+  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) (rcode_iff_reflTransGen.mp ht) hacc
 
 /-- **Equal counts at `s - 1` and `s` decide membership at radius `s`**: then `x ∈ L` iff some
 reachable code at radius `s` is accepting.
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
index 94662288..fab55360 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
@@ -130,10 +130,12 @@ theorem guloop (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hu :
         simp [he]
       refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he) ?_
       by_cases hr' : RelO orc x σ.s σ.u σ.v
-      · refine (nsem_call₃_pos rfl (St.greg hσ _ _) (by isr; exact hr')
+      · refine (nsem_call₃_pos rfl (St.greg hσ _ _)
+          (by isr; exact SavitchARM.rel_iff_orc.mp hr')
           (NSem.ret rfl (St.greg hσ _ _))).congr ?_
         simp [hr']
-      refine nsem_call₃_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.Rel] using hr') ?_
+      refine nsem_call₃_neg rfl (St.greg hσ _ _)
+        (by isr; simpa [SavitchARM.rel_iff_orc] using hr') ?_
       refine NSem.inc rfl (St.greg hσ _ _) ?_
       isr
       exact (hnext (σ.cnt + 1) (by omega)
@@ -229,10 +231,12 @@ theorem gvloop (Kont : ℕ → Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 
           Kont r (σ.v + 1) (σ.c + 1)) := by
       intro hmem
       by_cases ha : AccO orc x σ.s σ.v
-      · refine (nsem_call₂_pos rfl (St.greg hσ _ _) (by isr; exact ha)
+      · refine (nsem_call₂_pos rfl (St.greg hσ _ _)
+          (by isr; exact SavitchARM.accO_iff_orc.mp ha)
           (NSem.ret rfl (St.greg hσ _ _))).congr ?_
         simp [ha]
-      refine nsem_call₂_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.AccO] using ha) ?_
+      refine nsem_call₂_neg rfl (St.greg hσ _ _)
+        (by isr; simpa [SavitchARM.accO_iff_orc] using ha) ?_
       refine NSem.inc rfl (St.greg hσ _ _) ?_
       isr
       exact (hnext (σ.c + 1) (by omega)
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
index abe397e6..d82e8c65 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
@@ -83,13 +83,13 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
         isr
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
-        exact hQ he
-      · simp only [WalkLe, he, true_and]
+        exact hQ (walkLe_zero_iff.mpr he)
+      · simp only [walkLe_zero_iff, he, true_and]
     · have hL : σ.stp = σ.wb b := by omega
       refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he)
         (NSem.jeq_pos rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL)
           (NSem.ret rfl (St.greg hσ _ _)))).congr ?_
-      simp only [WalkLe, he, Bool.false_eq_true, false_and]
+      simp only [walkLe_zero_iff, he, Bool.false_eq_true, false_and]
   | succ dd ih =>
     intro σ hd hσ hK hcur hstp hQ
     by_cases he : σ.cur = σ.wt b
@@ -101,8 +101,8 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
         isr
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
-        exact hQ (Or.inl he)
-      · simp only [WalkLe, he, true_or, true_and]
+        exact hQ (walkLe_succ_iff_head.mpr (Or.inl he))
+      · simp only [walkLe_succ_iff_head, he, true_or, true_and]
     have hbd : σ.wb b ≤ B := by simp only [St.wb, St.Bd] at hσ ⊢; cases b <;> simp <;> omega
     refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he) ?_
     have hL : σ.stp ≠ σ.wb b := by omega
@@ -117,7 +117,8 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
     · simp only [St.toV_K] at hj2
       isr
       by_cases hr : RelO orc x σ.s σ.cur j
-      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _) (by isr; exact hr) ?_
+      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _)
+          (by isr; exact SavitchARM.rel_iff_orc.mp hr) ?_
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
         refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b true) (.wcb b true)
@@ -129,14 +130,15 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
           (by show St.wb b σ - (σ.stp + 1) = dd; omega)
           (by isb) hK (by simpa using hj2) (by show σ.stp + 1 ≤ St.wb b σ; omega)
           (fun hw => IG.of_eq (by ext <;> rfl)
-            (hQ (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩)))).congr ?_
+            (hQ (walkLe_succ_iff_head.mpr
+              (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩))))).congr ?_
         simp [St.wt, hr]
       · refine (nsem_call₃_neg rfl (St.greg (by isb) _ _)
-          (by isr; simpa [SavitchARM.Rel] using hr)
+          (by isr; simpa [SavitchARM.rel_iff_orc] using hr)
           (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
         simp only [Bool.false_eq_true, false_iff, not_and]
         exact fun h => absurd h hr
-    · simp only [St.toV_g, St.toV_K, WalkLe, he, false_or]
+    · simp only [St.toV_g, St.toV_K, walkLe_succ_iff_head, he, false_or]
       constructor
       · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
       · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩
@@ -164,7 +166,8 @@ theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
   · simp only [St.toV_K] at hj2
     isr
     by_cases hi : InitO orc x σ.s j
-    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _) (by isr; exact hi) ?_
+    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _)
+        (by isr; exact SavitchARM.initO_iff_orc.mp hi) ?_
       refine NSem.clr rfl (St.greg (by isb) _ _) ?_
       isr
       refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b false) (.wcb b false)
@@ -178,7 +181,7 @@ theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
           (hQ ⟨j, by simpa using hj2, hi, by simpa [St.wb, St.wt] using hw⟩))).congr ?_
       exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
     · refine (nsem_call₂_neg rfl (St.greg (by isb) _ _)
-        (by isr; simpa [SavitchARM.InitO] using hi)
+        (by isr; simpa [SavitchARM.initO_iff_orc] using hi)
         (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
       simp only [Bool.false_eq_true, false_iff, not_and]
       exact fun h => absurd h hi
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
index f25b356f..3066bf69 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
@@ -84,9 +84,9 @@ variable {K R Init Acc}
 /-- A walk from a vertex below `K` ends below `K`. -/
 lemma walkLe_lt {j c t : ℕ} (hc : c < K) (h : WalkLe R K j c t) : t < K := by
   induction j generalizing c with
-  | zero => cases h; exact hc
+  | zero => cases walkLe_zero_iff.mp h; exact hc
   | succ j ih =>
-    rcases h with rfl | ⟨v, hv, -, hw⟩
+    rcases walkLe_succ_iff_head.mp h with rfl | ⟨v, hv, -, hw⟩
     · exact hc
     · exact ih hv hw
 
@@ -121,7 +121,7 @@ lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
     WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K := by
   induction j generalizing c with
   | zero =>
-    simp only [WalkLe]
+    simp only [walkLe_succ_iff_head, walkLe_zero_iff]
     constructor
     · rintro (h | ⟨v, hv, he, rfl⟩)
       · exact Or.inl h
@@ -130,18 +130,21 @@ lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
       · exact Or.inl h
       · exact Or.inr ⟨t, ht, he, rfl⟩
   | succ j ih =>
+    rw [walkLe_succ_iff_head (j := j + 1)]
     constructor
     · rintro (h | ⟨v, hv, he, hw⟩)
-      · exact Or.inl (Or.inl h)
+      · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inl h))
       · rcases (ih v).mp hw with h | ⟨w, hw', hwt, ht⟩
-        · exact Or.inl (Or.inr ⟨v, hv, he, h⟩)
-        · exact Or.inr ⟨w, Or.inr ⟨v, hv, he, hw'⟩, hwt, ht⟩
-    · rintro ((h | ⟨v, hv, he, hw⟩) | ⟨w, hw | ⟨v, hv, he, hw⟩, hwt, ht⟩)
-      · exact Or.inl h
-      · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
-      · subst hw
-        exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
-      · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩
+        · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, h⟩))
+        · exact Or.inr ⟨w, walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, hw'⟩), hwt, ht⟩
+    · rintro (h | ⟨w, hw, hwt, ht⟩)
+      · rcases walkLe_succ_iff_head.mp h with h | ⟨v, hv, he, hw⟩
+        · exact Or.inl h
+        · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
+      · rcases walkLe_succ_iff_head.mp hw with hw | ⟨v, hv, he, hw⟩
+        · subst hw
+          exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
+        · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩
 
 /-- **The balls grow by one step**: `C_{L+1}` is `C_L` together with the successors below `K`
 of its members. -/
@@ -176,12 +179,12 @@ lemma card_ball_zero {u₀ : ℕ} (hu₀ : u₀ < K) (hI : ∀ u, Init u ↔ u =
   rw [mem_ball, Finset.mem_singleton]
   constructor
   · rintro ⟨u, -, hi, hw⟩
-    have e : u = t := hw
+    have e : u = t := walkLe_zero_iff.mp hw
     rw [← e]
     exact (hI u).mp hi
   · intro h
     rw [h]
-    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, rfl⟩
+    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, walkLe_zero_iff.mpr rfl⟩
 
 /-! ## Guessed enumerations -/
 
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
index a1f376ee..896e12da 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
@@ -229,7 +229,7 @@ theorem red_mem_iff {L : Language Bool} {c₀ : ℕ}
         intro hj
         refine (ih (by omega)).tail ((rawEdge_adjWordE N x s n _ _).mpr
           ⟨hW j (by omega), hW (j + 1) hj, Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)⟩)
-        simpa [StepRel] using hstep j (by omega)
+        simpa [stepRel_iff_mem] using hstep j (by omega)
     have first : rawEdge n (adjWordE N x s n) 0 (c 0 + 2) :=
       (rawEdge_adjWordE N x s n _ _).mpr ⟨by omega, hW 0 (by omega),
         Or.inl ⟨rfl, by omega, by simpa using hinit⟩⟩
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
index f48bd13d..a507cf09 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
@@ -350,6 +350,6 @@ lemma orc_step (N : FinNDTM Bool) (x β : List Bool) (u v s : ℕ) :
         (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) =
       @decide (Codec.StepRel N x s u v) (Classical.dec _) := by
   simp only [orc, As, indicator_eq_decide]
-  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.StepRel])
+  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.stepRel_iff_mem])
 
 end Complexity.PathHard
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
index 96172f8c..ed3857f7 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
@@ -428,17 +428,17 @@ theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs :
     by_cases he : σ.s = σ.t
     · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
-      simp only [WalkLe, he]
+      simp only [walkLe_zero_iff, he]
     · refine (NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simp; omega)
           (NSem.ret rfl (PReg.reg hσ _ _)))).congr ?_
-      simp only [WalkLe, he, Bool.false_eq_true]
+      simp only [walkLe_zero_iff, he, Bool.false_eq_true]
   | succ d ih =>
     intro σ hd hσ hs ht hst hm
     by_cases he : σ.s = σ.t
     · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
-      simp only [WalkLe, he, true_or]
+      simp only [walkLe_succ_iff_head, he, true_or]
     refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he) ?_
     refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simp; omega) ?_
     refine NSem.clr rfl (PReg.reg hσ _ _) ?_
@@ -472,7 +472,7 @@ theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs :
           (by simp only [PReg.v_0, pathOr_bit]; simpa [pathEdge] using hedge)
           (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
         simp only [hedge, false_and, Bool.false_eq_true]
-    · simp only [PReg.v_8, PReg.v_1, WalkLe, he, false_or]
+    · simp only [PReg.v_8, PReg.v_1, walkLe_succ_iff_head, he, false_or]
       exact ⟨fun ⟨j, _, h⟩ => ⟨j, h.1, h.2⟩, fun ⟨j, h1, h2⟩ => ⟨j, Nat.zero_le _, h1, h2⟩⟩
 
 end Complexity.LogProg
diff --git a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
index de68ce1e..78814e59 100644
--- a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
+++ b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
@@ -56,19 +56,19 @@ lemma rel_orcN (N : FinNDTM Bool) (x : List Bool) (s : ℕ) :
     Rel (orcN N) x s = Codec.StepRel N x s := by
   funext u v
   apply propext
-  simp [Rel, Codec.StepRel, orcN, decs, indicator_eq_decide]
+  simp [rel_iff_orc, Codec.stepRel_iff_mem, orcN, decs, indicator_eq_decide]
 
 /-- Decider `1` answers membership in the initial-code language. -/
 lemma initO_orcN (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) :
     InitO (orcN N) x s u ↔
       pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.initLang N := by
-  simp [InitO, orcN, decs, indicator_eq_decide]
+  simp [initO_iff_orc, orcN, decs, indicator_eq_decide]
 
 /-- Decider `2` answers membership in the accepting-code language. -/
 lemma accO_orcN (N : FinNDTM Bool) (x : List Bool) (s v : ℕ) :
     AccO (orcN N) x s v ↔
       pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.acceptLang N := by
-  simp [AccO, orcN, decs, indicator_eq_decide]
+  simp [accO_iff_orc, orcN, decs, indicator_eq_decide]
 
 /-- The constant of the Savitch machine for `N` deciding in space `c (n ^ k + 1)`: large
 enough for the radius (`radius_le`), the code width (`codeWidth_le`) and the configuration
diff --git a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
index f9071f83..8da4bc53 100644
--- a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
+++ b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
@@ -290,8 +290,8 @@ theorem mem_iff_reach {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
     obtain ⟨t, c, ht, hinit, hstep, hacc, hlt⟩ := (mem_iff_codeChain h x s hs).mp hx
     have hK : ∀ j ≤ t, c j < 2 ^ w := fun j hj =>
       (hlt j hj).trans_le (Nat.pow_le_pow_right (by norm_num) hw)
-    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t hstep hK w 0 t (by omega)
-      (ht.trans hcb)
+    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t
+      (fun j hj => stepRel_iff_mem.mpr (hstep j hj)) hK w 0 t (by omega) (ht.trans hcb)
     rw [zero_add] at hr
     exact ⟨c 0, hK 0 (Nat.zero_le _), hinit, c t, hK t le_rfl, hacc, hr⟩
   · rintro ⟨u, -, hinit, v, -, hacc, hr⟩

## ===== campaign/gates/107-rp1-dedup/evidence/landing/rp1.diff =====

diff --git a/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean b/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
index bf14ec15..1ad78913 100644
--- a/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
+++ b/TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean
@@ -121,9 +121,7 @@ theorem reflTransGen_stepRel (x : List Bool) (s u : ℕ) {γ : List Bool}
     have hs := bits_injective h6
     subst hc₂ hs
     refine (ih c₁ h3).tail ?_
-    show pairEncode x (pairEncode (Nat.bits c₁) (pairEncode (Nat.bits c) (Nat.bits s))) ∈
-      stepLang N
-    rw [← h3]
+    rw [stepRel_iff_mem, ← h3]
     exact hst
 
 /-- **Acceptance as a block path** ([AB09, Claim 4.4(1)] in the form of the proof of
diff --git a/TCSlib/Complexity/Randomized/BPLInP.lean b/TCSlib/Complexity/Randomized/BPLInP.lean
index 689c48a1..55b06b3b 100644
--- a/TCSlib/Complexity/Randomized/BPLInP.lean
+++ b/TCSlib/Complexity/Randomized/BPLInP.lean
@@ -226,7 +226,7 @@ theorem entryW_eq (s a a' v : ℕ) :
       Nat.bits ((if StepRel (fixCoin N false) x s a a' then v else 0) +
         (if StepRel (fixCoin N true) x s a a' then v else 0)) := by
   simp only [entryW, stepTest, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator,
-    StepRel]
+    stepRel_iff_mem]
   split_ifs <;> simp_all [add, bitsVal_bits, LogProg.bitsVal]
 
 /-- The initial state is the context and the table after `0` rounds. -/
diff --git a/TCSlib/Complexity/Randomized/BPLInPCount.lean b/TCSlib/Complexity/Randomized/BPLInPCount.lean
index ca4c3ffd..939142db 100644
--- a/TCSlib/Complexity/Randomized/BPLInPCount.lean
+++ b/TCSlib/Complexity/Randomized/BPLInPCount.lean
@@ -116,7 +116,8 @@ theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length 
     rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
   constructor
   · intro h
-    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ := (mem_stepLang (fixCoin N b) x _ _ s).mp h
+    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ :=
+      (mem_stepLang (fixCoin N b) x _ _ s).mp (stepRel_iff_mem.mp h)
     have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
       coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
     rw [← hcC', ← hb']
@@ -124,8 +125,8 @@ theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length 
     rw [stepWith_fixCoin, hstep]
     exact congrArg bitsVal (cfgWord_congr (NDTM.coreSum_stepWith N.tm b hcore))
   · rintro rfl
-    refine (mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v, inWin_run hN hs v, rfl,
-      run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩
+    refine stepRel_iff_mem.mpr ((mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v,
+      inWin_run hN hs v, rfl, run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩)
     change (fixCoin N b).tm.stepWith b (run v) = _
     rw [stepWith_fixCoin, hstep]
 
diff --git a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
index f928c71b..66f542c6 100644
--- a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
+++ b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean
@@ -77,7 +77,7 @@ lemma ini_orcN (r u : ℕ) :
 
 /-- Decider `2` answers the step relation. -/
 lemma stp_orcN (r u v : ℕ) : stp (orcN N) x r u v = true ↔ Codec.StepRel N x r u v := by
-  simp [stp, orcN, decs, indicator_eq_decide, Codec.StepRel]
+  simp [stp, orcN, decs, indicator_eq_decide, Codec.stepRel_iff_mem]
 
 /-- Decider `3` answers whether a code is accepting. -/
 lemma acc_orcN (r u : ℕ) :
@@ -92,18 +92,19 @@ lemma cl_iff {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1))
   · rintro ⟨u, -, hi, hpath⟩
     rw [ini_orcN] at hi
     subst hi
-    exact hpath.mono fun a b h => (stp_orcN r a b).mp h.1
+    exact ExpBFS.rcode_iff_reflTransGen.mpr (hpath.mono fun a b h => (stp_orcN r a b).mp h.1)
   · intro h
     refine ⟨_, (Codec.cfgCode_lt r _).trans_le hK, (ini_orcN r _).mpr rfl, ?_⟩
     have key : ∀ w, ExpBFS.RCode N x r w → Relation.ReflTransGen
         (fun a b => stp (orcN N) x r a b = true ∧ b < K)
         (Codec.cfgCode r (N.tm.initCfg x)) w := by
       intro w hw
+      rw [ExpBFS.rcode_iff_reflTransGen] at hw
       induction hw with
       | refl => exact Relation.ReflTransGen.refl
       | @tail b c hab hbc ih =>
         exact ih.tail ⟨(stp_orcN r b c).mpr hbc,
-          (ExpBFS.rcode_lt (hab.tail hbc)).trans_le hK⟩
+          (ExpBFS.rcode_lt (ExpBFS.rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK⟩
     exact key v h
 
 open Classical in
diff --git a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
index bbc05e6d..1cf0278d 100644
--- a/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
+++ b/TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean
@@ -162,7 +162,8 @@ theorem rcode_iff (s u : ℕ) :
     | refl => exact ⟨[], fun j _ => by simpa using inWin_init s, rfl⟩
     | tail _ hst ih =>
       obtain ⟨w, hw, hcode⟩ := ih
-      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
+      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ :=
+        (mem_stepLang N x _ _ s).mp (stepRel_iff_mem.mp hst)
       have hv : NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum C :=
         coreSum_eq_of_code_eq hw.last hC (hcode.trans hcC.symm)
       have hv' : NDTM.coreSum (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) = NDTM.coreSum C' := by
@@ -179,7 +180,7 @@ theorem rcode_iff (s u : ℕ) :
       | succ j ih =>
         intro hj
         refine (ih (by omega)).tail ?_
-        rw [StepRel, mem_stepLang]
+        rw [stepRel_iff_mem, mem_stepLang]
         refine ⟨_, hw j (by omega), rfl, _, ⟨w[j]'(by omega), ?_⟩, hw (j + 1) hj, rfl⟩
         rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
         rfl
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
index b58ac31f..dad3a220 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean
@@ -83,15 +83,17 @@ theorem mem_ball_iff_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.leng
   · rintro ⟨u, hu, hinit, hw⟩
     rw [InitM, mem_initLang] at hinit
     subst hinit
-    exact (walkLe_reach hu hw).mono fun a b hab => hab.2.2
+    exact rcode_iff_reflTransGen.mpr ((walkLe_reach hu hw).mono fun a b hab => hab.2.2)
   · intro ht
     have hpath : ∀ t, RCode N x s t → Relation.ReflTransGen
         (fun u v => u < K ∧ v < K ∧ StepRel N x s u v) (cfgCode s (N.tm.initCfg x)) t := by
       intro t ht
+      rw [rcode_iff_reflTransGen] at ht
       induction ht with
       | refl => exact Relation.ReflTransGen.refl
       | @tail b c hab hbc ih =>
-        exact ih.tail ⟨(rcode_lt hab).trans_le hK, (rcode_lt (hab.tail hbc)).trans_le hK, hbc⟩
+        exact ih.tail ⟨(rcode_lt (rcode_iff_reflTransGen.mpr hab)).trans_le hK,
+          (rcode_lt (rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK, hbc⟩
     have h0 : cfgCode s (N.tm.initCfg x) < K := (cfgCode_lt s _).trans_le hK
     obtain ⟨j, hw⟩ := exists_walkLe (hpath t ht)
     exact ⟨_, h0, by rw [InitM, mem_initLang], walkLe_short ((rcode_lt ht).trans_le hK) h0 hw⟩
@@ -114,7 +116,7 @@ theorem card_ball_zero_code {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.len
 
 /-- There is a reachable code (the initial one). -/
 theorem one_le_card_rset (s : ℕ) : 1 ≤ (rset N x s).card :=
-  Finset.card_pos.mpr ⟨_, mem_rset.mpr Relation.ReflTransGen.refl⟩
+  Finset.card_pos.mpr ⟨_, mem_rset.mpr (rcode_iff_reflTransGen.mpr Relation.ReflTransGen.refl)⟩
 
 /-- **No accepting code in the balls** `C_1, …, C_K` iff no reachable code is accepting. -/
 theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
@@ -131,7 +133,7 @@ theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length
 theorem mem_of_exists_acc {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
     {s : ℕ} (h : ∃ t, RCode N x s t ∧ AccM N x s t) : x ∈ L := by
   obtain ⟨t, ht, hacc⟩ := h
-  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) ht hacc
+  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) (rcode_iff_reflTransGen.mp ht) hacc
 
 /-- **Equal counts at `s - 1` and `s` decide membership at radius `s`**: then `x ∈ L` iff some
 reachable code at radius `s` is accepting.
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
index 94662288..fab55360 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean
@@ -130,10 +130,12 @@ theorem guloop (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hu :
         simp [he]
       refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he) ?_
       by_cases hr' : RelO orc x σ.s σ.u σ.v
-      · refine (nsem_call₃_pos rfl (St.greg hσ _ _) (by isr; exact hr')
+      · refine (nsem_call₃_pos rfl (St.greg hσ _ _)
+          (by isr; exact SavitchARM.rel_iff_orc.mp hr')
           (NSem.ret rfl (St.greg hσ _ _))).congr ?_
         simp [hr']
-      refine nsem_call₃_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.Rel] using hr') ?_
+      refine nsem_call₃_neg rfl (St.greg hσ _ _)
+        (by isr; simpa [SavitchARM.rel_iff_orc] using hr') ?_
       refine NSem.inc rfl (St.greg hσ _ _) ?_
       isr
       exact (hnext (σ.cnt + 1) (by omega)
@@ -229,10 +231,12 @@ theorem gvloop (Kont : ℕ → Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 
           Kont r (σ.v + 1) (σ.c + 1)) := by
       intro hmem
       by_cases ha : AccO orc x σ.s σ.v
-      · refine (nsem_call₂_pos rfl (St.greg hσ _ _) (by isr; exact ha)
+      · refine (nsem_call₂_pos rfl (St.greg hσ _ _)
+          (by isr; exact SavitchARM.accO_iff_orc.mp ha)
           (NSem.ret rfl (St.greg hσ _ _))).congr ?_
         simp [ha]
-      refine nsem_call₂_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.AccO] using ha) ?_
+      refine nsem_call₂_neg rfl (St.greg hσ _ _)
+        (by isr; simpa [SavitchARM.accO_iff_orc] using ha) ?_
       refine NSem.inc rfl (St.greg hσ _ _) ?_
       isr
       exact (hnext (σ.c + 1) (by omega)
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
index abe397e6..d82e8c65 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean
@@ -83,13 +83,13 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
         isr
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
-        exact hQ he
-      · simp only [WalkLe, he, true_and]
+        exact hQ (walkLe_zero_iff.mpr he)
+      · simp only [walkLe_zero_iff, he, true_and]
     · have hL : σ.stp = σ.wb b := by omega
       refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he)
         (NSem.jeq_pos rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL)
           (NSem.ret rfl (St.greg hσ _ _)))).congr ?_
-      simp only [WalkLe, he, Bool.false_eq_true, false_and]
+      simp only [walkLe_zero_iff, he, Bool.false_eq_true, false_and]
   | succ dd ih =>
     intro σ hd hσ hK hcur hstp hQ
     by_cases he : σ.cur = σ.wt b
@@ -101,8 +101,8 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
         isr
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
-        exact hQ (Or.inl he)
-      · simp only [WalkLe, he, true_or, true_and]
+        exact hQ (walkLe_succ_iff_head.mpr (Or.inl he))
+      · simp only [walkLe_succ_iff_head, he, true_or, true_and]
     have hbd : σ.wb b ≤ B := by simp only [St.wb, St.Bd] at hσ ⊢; cases b <;> simp <;> omega
     refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he) ?_
     have hL : σ.stp ≠ σ.wb b := by omega
@@ -117,7 +117,8 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
     · simp only [St.toV_K] at hj2
       isr
       by_cases hr : RelO orc x σ.s σ.cur j
-      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _) (by isr; exact hr) ?_
+      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _)
+          (by isr; exact SavitchARM.rel_iff_orc.mp hr) ?_
         refine NSem.clr rfl (St.greg (by isb) _ _) ?_
         isr
         refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b true) (.wcb b true)
@@ -129,14 +130,15 @@ theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
           (by show St.wb b σ - (σ.stp + 1) = dd; omega)
           (by isb) hK (by simpa using hj2) (by show σ.stp + 1 ≤ St.wb b σ; omega)
           (fun hw => IG.of_eq (by ext <;> rfl)
-            (hQ (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩)))).congr ?_
+            (hQ (walkLe_succ_iff_head.mpr
+              (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩))))).congr ?_
         simp [St.wt, hr]
       · refine (nsem_call₃_neg rfl (St.greg (by isb) _ _)
-          (by isr; simpa [SavitchARM.Rel] using hr)
+          (by isr; simpa [SavitchARM.rel_iff_orc] using hr)
           (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
         simp only [Bool.false_eq_true, false_iff, not_and]
         exact fun h => absurd h hr
-    · simp only [St.toV_g, St.toV_K, WalkLe, he, false_or]
+    · simp only [St.toV_g, St.toV_K, walkLe_succ_iff_head, he, false_or]
       constructor
       · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
       · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩
@@ -164,7 +166,8 @@ theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
   · simp only [St.toV_K] at hj2
     isr
     by_cases hi : InitO orc x σ.s j
-    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _) (by isr; exact hi) ?_
+    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _)
+        (by isr; exact SavitchARM.initO_iff_orc.mp hi) ?_
       refine NSem.clr rfl (St.greg (by isb) _ _) ?_
       isr
       refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b false) (.wcb b false)
@@ -178,7 +181,7 @@ theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K +
           (hQ ⟨j, by simpa using hj2, hi, by simpa [St.wb, St.wt] using hw⟩))).congr ?_
       exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
     · refine (nsem_call₂_neg rfl (St.greg (by isb) _ _)
-        (by isr; simpa [SavitchARM.InitO] using hi)
+        (by isr; simpa [SavitchARM.initO_iff_orc] using hi)
         (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
       simp only [Bool.false_eq_true, false_iff, not_and]
       exact fun h => absurd h hi
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
index f25b356f..3066bf69 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean
@@ -84,9 +84,9 @@ variable {K R Init Acc}
 /-- A walk from a vertex below `K` ends below `K`. -/
 lemma walkLe_lt {j c t : ℕ} (hc : c < K) (h : WalkLe R K j c t) : t < K := by
   induction j generalizing c with
-  | zero => cases h; exact hc
+  | zero => cases walkLe_zero_iff.mp h; exact hc
   | succ j ih =>
-    rcases h with rfl | ⟨v, hv, -, hw⟩
+    rcases walkLe_succ_iff_head.mp h with rfl | ⟨v, hv, -, hw⟩
     · exact hc
     · exact ih hv hw
 
@@ -121,7 +121,7 @@ lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
     WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K := by
   induction j generalizing c with
   | zero =>
-    simp only [WalkLe]
+    simp only [walkLe_succ_iff_head, walkLe_zero_iff]
     constructor
     · rintro (h | ⟨v, hv, he, rfl⟩)
       · exact Or.inl h
@@ -130,18 +130,21 @@ lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
       · exact Or.inl h
       · exact Or.inr ⟨t, ht, he, rfl⟩
   | succ j ih =>
+    rw [walkLe_succ_iff_head (j := j + 1)]
     constructor
     · rintro (h | ⟨v, hv, he, hw⟩)
-      · exact Or.inl (Or.inl h)
+      · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inl h))
       · rcases (ih v).mp hw with h | ⟨w, hw', hwt, ht⟩
-        · exact Or.inl (Or.inr ⟨v, hv, he, h⟩)
-        · exact Or.inr ⟨w, Or.inr ⟨v, hv, he, hw'⟩, hwt, ht⟩
-    · rintro ((h | ⟨v, hv, he, hw⟩) | ⟨w, hw | ⟨v, hv, he, hw⟩, hwt, ht⟩)
-      · exact Or.inl h
-      · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
-      · subst hw
-        exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
-      · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩
+        · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, h⟩))
+        · exact Or.inr ⟨w, walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, hw'⟩), hwt, ht⟩
+    · rintro (h | ⟨w, hw, hwt, ht⟩)
+      · rcases walkLe_succ_iff_head.mp h with h | ⟨v, hv, he, hw⟩
+        · exact Or.inl h
+        · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
+      · rcases walkLe_succ_iff_head.mp hw with hw | ⟨v, hv, he, hw⟩
+        · subst hw
+          exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
+        · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩
 
 /-- **The balls grow by one step**: `C_{L+1}` is `C_L` together with the successors below `K`
 of its members. -/
@@ -176,12 +179,12 @@ lemma card_ball_zero {u₀ : ℕ} (hu₀ : u₀ < K) (hI : ∀ u, Init u ↔ u =
   rw [mem_ball, Finset.mem_singleton]
   constructor
   · rintro ⟨u, -, hi, hw⟩
-    have e : u = t := hw
+    have e : u = t := walkLe_zero_iff.mp hw
     rw [← e]
     exact (hI u).mp hi
   · intro h
     rw [h]
-    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, rfl⟩
+    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, walkLe_zero_iff.mpr rfl⟩
 
 /-! ## Guessed enumerations -/
 
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
index a1f376ee..896e12da 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean
@@ -229,7 +229,7 @@ theorem red_mem_iff {L : Language Bool} {c₀ : ℕ}
         intro hj
         refine (ih (by omega)).tail ((rawEdge_adjWordE N x s n _ _).mpr
           ⟨hW j (by omega), hW (j + 1) hj, Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)⟩)
-        simpa [StepRel] using hstep j (by omega)
+        simpa [stepRel_iff_mem] using hstep j (by omega)
     have first : rawEdge n (adjWordE N x s n) 0 (c 0 + 2) :=
       (rawEdge_adjWordE N x s n _ _).mpr ⟨by omega, hW 0 (by omega),
         Or.inl ⟨rfl, by omega, by simpa using hinit⟩⟩
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
index 41188777..2e7f830b 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean
@@ -351,6 +351,6 @@ lemma orc_step (N : FinNDTM Bool) (x β : List Bool) (u v s : ℕ) :
         (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) =
       @decide (Codec.StepRel N x s u v) (Classical.dec _) := by
   simp only [orc, As, indicator_eq_decide]
-  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.StepRel])
+  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.stepRel_iff_mem])
 
 end Complexity.PathHard
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
index 26364e11..c0b58389 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean
@@ -426,17 +426,17 @@ theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs :
     by_cases he : σ.s = σ.t
     · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
-      simp only [WalkLe, he]
+      simp only [walkLe_zero_iff, he]
     · refine (NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simp; omega)
           (NSem.ret rfl (PReg.reg hσ _ _)))).congr ?_
-      simp only [WalkLe, he, Bool.false_eq_true]
+      simp only [walkLe_zero_iff, he, Bool.false_eq_true]
   | succ d ih =>
     intro σ hd hσ hs ht hst hm
     by_cases he : σ.s = σ.t
     · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
         (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
-      simp only [WalkLe, he, true_or]
+      simp only [walkLe_succ_iff_head, he, true_or]
     refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he) ?_
     refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simp; omega) ?_
     refine NSem.clr rfl (PReg.reg hσ _ _) ?_
@@ -470,7 +470,7 @@ theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs :
           (by simp only [PReg.v_0, pathOr_bit]; simpa [pathEdge] using hedge)
           (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
         simp only [hedge, false_and, Bool.false_eq_true]
-    · simp only [PReg.v_8, PReg.v_1, WalkLe, he, false_or]
+    · simp only [PReg.v_8, PReg.v_1, walkLe_succ_iff_head, he, false_or]
       exact ⟨fun ⟨j, _, h⟩ => ⟨j, h.1, h.2⟩, fun ⟨j, h1, h2⟩ => ⟨j, Nat.zero_le _, h1, h2⟩⟩
 
 end Complexity.LogProg
diff --git a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
index f13f1100..4b9fc515 100644
--- a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
+++ b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean
@@ -56,19 +56,19 @@ lemma rel_orcN (N : FinNDTM Bool) (x : List Bool) (s : ℕ) :
     Rel (orcN N) x s = Codec.StepRel N x s := by
   funext u v
   apply propext
-  simp [Rel, Codec.StepRel, orcN, decs, indicator_eq_decide]
+  simp [rel_iff_orc, Codec.stepRel_iff_mem, orcN, decs, indicator_eq_decide]
 
 /-- Decider `1` answers membership in the initial-code language. -/
 lemma initO_orcN (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) :
     InitO (orcN N) x s u ↔
       pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.initLang N := by
-  simp [InitO, orcN, decs, indicator_eq_decide]
+  simp [initO_iff_orc, orcN, decs, indicator_eq_decide]
 
 /-- Decider `2` answers membership in the accepting-code language. -/
 lemma accO_orcN (N : FinNDTM Bool) (x : List Bool) (s v : ℕ) :
     AccO (orcN N) x s v ↔
       pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.acceptLang N := by
-  simp [AccO, orcN, decs, indicator_eq_decide]
+  simp [accO_iff_orc, orcN, decs, indicator_eq_decide]
 
 /-- The constant of the Savitch machine for `N` deciding in space `c (n ^ k + 1)`: large
 enough for the radius (`radius_le`), the code width (`codeWidth_le`) and the configuration
diff --git a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
index f9071f83..8da4bc53 100644
--- a/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
+++ b/TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean
@@ -290,8 +290,8 @@ theorem mem_iff_reach {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
     obtain ⟨t, c, ht, hinit, hstep, hacc, hlt⟩ := (mem_iff_codeChain h x s hs).mp hx
     have hK : ∀ j ≤ t, c j < 2 ^ w := fun j hj =>
       (hlt j hj).trans_le (Nat.pow_le_pow_right (by norm_num) hw)
-    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t hstep hK w 0 t (by omega)
-      (ht.trans hcb)
+    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t
+      (fun j hj => stepRel_iff_mem.mpr (hstep j hj)) hK w 0 t (by omega) (ht.trans hcb)
     rw [zero_add] at hr
     exact ⟨c 0, hK 0 (Nat.zero_le _), hinit, c t, hK t le_rfl, hacc, hr⟩
   · rintro ⟨u, -, hinit, v, -, hacc, hr⟩

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-ClassPSPACE-base.txt =====

WARN  TCSlib/Complexity/ClassPSPACE/Games.lean              3 public def(s) without a lemma beside them (check 8): FirstWins, SecondWins, playOut
WARN  TCSlib/Complexity/ClassPSPACE/TQBF.lean               2522 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassPSPACE/TQBF.lean               28 public def(s) without a lemma beside them (check 8): PSPACEComplete, PSPACEHard, caseAction, caseList, expectBit, expectOf, guard, headOf, headVar, inputEquality, inputVar, kindPred, moveInput, portCount, portWire, readSummary, readSymbol, stateCount, stateIndex, stateOffset, summaryOffset, summaryVar, summaryWord, transition, transitionGate, workFlags, workOffset, workVar
WARN  TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean    18 public def(s) without a lemma beside them (check 8): A, Bd, cpDst, cpExit, cpI, cpSrc, dmI, hvI, mvI, rC, rK, rP, rS, rT, rV, rZ, sbI, zero
WARN  TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean       1 public def(s) without a lemma beside them (check 8): CallOK
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHard.lean           8 public def(s) without a lemma beside them (check 8): redCircuit, redK, redM, redMap, redQBF, redQuants, redT, redW
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean    4 public def(s) without a lemma beside them (check 8): blockAcc, blockInit, blockStep, codeLen
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean     4 public def(s) without a lemma beside them (check 8): lbChunk, lbStep, levelBits, wCoef
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean  5 public def(s) without a lemma beside them (check 8): Sel, levelQuants, uRec, vRec, zRec
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean   14 public def(s) without a lemma beside them (check 8): accB, baseB, blkAt, cpAt, initB, lvlQ, nxtW, orB, predB, selT, vlen, vrad, vwid, winBlk
INFO  TCSlib/Complexity/ClassPSPACE/Games.lean              175 lines; 4 public / 7 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBF.lean               2522 lines; 72 public / 118 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean    225 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean       331 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean    533 lines; 54 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean  246 lines; 17 public / 1 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean       267 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHard.lean           327 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardBridge.lean     152 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean    208 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean     241 lines; 10 public / 3 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean  513 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean    136 lines; 2 public / 2 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean   371 lines; 34 public / 0 private declarations

style_lint: 0 FAIL, 10 WARN over 14 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-ClassPSPACE-head.txt =====

WARN  TCSlib/Complexity/ClassPSPACE/Games.lean              3 public def(s) without a lemma beside them (check 8): FirstWins, SecondWins, playOut
WARN  TCSlib/Complexity/ClassPSPACE/TQBF.lean               2522 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassPSPACE/TQBF.lean               28 public def(s) without a lemma beside them (check 8): PSPACEComplete, PSPACEHard, caseAction, caseList, expectBit, expectOf, guard, headOf, headVar, inputEquality, inputVar, kindPred, moveInput, portCount, portWire, readSummary, readSymbol, stateCount, stateIndex, stateOffset, summaryOffset, summaryVar, summaryWord, transition, transitionGate, workFlags, workOffset, workVar
WARN  TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean    18 public def(s) without a lemma beside them (check 8): A, Bd, cpDst, cpExit, cpI, cpSrc, dmI, hvI, mvI, rC, rK, rP, rS, rT, rV, rZ, sbI, zero
WARN  TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean       1 public def(s) without a lemma beside them (check 8): CallOK
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHard.lean           8 public def(s) without a lemma beside them (check 8): redCircuit, redK, redM, redMap, redQBF, redQuants, redT, redW
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean    4 public def(s) without a lemma beside them (check 8): blockAcc, blockInit, blockStep, codeLen
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean     4 public def(s) without a lemma beside them (check 8): lbChunk, lbStep, levelBits, wCoef
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean  5 public def(s) without a lemma beside them (check 8): Sel, levelQuants, uRec, vRec, zRec
WARN  TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean   14 public def(s) without a lemma beside them (check 8): accB, baseB, blkAt, cpAt, initB, lvlQ, nxtW, orB, predB, selT, vlen, vrad, vwid, winBlk
INFO  TCSlib/Complexity/ClassPSPACE/Games.lean              175 lines; 4 public / 7 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBF.lean               2522 lines; 72 public / 118 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean    225 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean       331 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean    533 lines; 54 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean  246 lines; 17 public / 1 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean       267 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHard.lean           327 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardBridge.lean     152 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean    206 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean     241 lines; 10 public / 3 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean  513 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean    136 lines; 2 public / 2 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean   371 lines; 34 public / 0 private declarations

style_lint: 0 FAIL, 10 WARN over 14 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-Randomized-base.txt =====

WARN  TCSlib/Complexity/Randomized/Adleman.lean                  1 public def(s) without a lemma beside them (check 8): VerifierHasCircuits
WARN  TCSlib/Complexity/Randomized/AlgCircuit.lean               7 public def(s) without a lemma beside them (check 8): WellFormed, ZEROP, encodeGates, parseBin, refsBelow, shift, subCircuit
WARN  TCSlib/Complexity/Randomized/AlgCircuitExample.lean        4 public def(s) without a lemma beside them (check 8): isOp, prodOnePlus, prodOnePlusGates, varOrOne
WARN  TCSlib/Complexity/Randomized/BPLInP.lean                   8 public def(s) without a lemma beside them (check 8): accW, ctxOf, dpRun, initEntry, pickW, rowW, stepTest, vecW
WARN  TCSlib/Complexity/Randomized/BPLInPCount.lean              1 public def(s) without a lemma beside them (check 8): fixCoin
WARN  TCSlib/Complexity/Randomized/BPLInPWords.lean              4 public def(s) without a lemma beside them (check 8): codeStep, pow2W, radius, sumStep
WARN  TCSlib/Complexity/Randomized/BPPHard.lean                  2 public def(s) without a lemma beside them (check 8): BPPHard, CodePTM.toFinNDTM
WARN  TCSlib/Complexity/Randomized/BiasedCoin.lean               3 public def(s) without a lemma beside them (check 8): BiasedBPDecidesInTime, biasedBPTIME, biasedOutputProb
WARN  TCSlib/Complexity/Randomized/BiasedCoinHalting.lean        10 public def(s) without a lemma beside them (check 8): haltDigit, haltPrefix, hcCD, hcCD3, hcLin, hlDWord, hlJ, lenLeB, onesW, pow4Step
WARN  TCSlib/Complexity/Randomized/Classes.lean                  1328 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/Randomized/Classes.lean                  13 public def(s) without a lemma beside them (check 8): ClosedUnderAnswerIs, ClosedUnderAny, ClosedUnderMajority, ClosedUnderNot, ClosedUnderRace, InBPP, InBPPStrong, InCoRP, anyVerifier, boolVerifier, majorityVerifier, polyLen, raceVerifier
WARN  TCSlib/Complexity/Randomized/Coins.lean                    2 public def(s) without a lemma beside them (check 8): binDigit, vonNeumannRun
WARN  TCSlib/Complexity/Randomized/DirectedWalk.lean             1 public def(s) without a lemma beside them (check 8): outNbrs
WARN  TCSlib/Complexity/Randomized/ErrorReduction.lean           2 public def(s) without a lemma beside them (check 8): coordIndicator, successCount
WARN  TCSlib/Complexity/Randomized/ExpectedTime.lean             7 public def(s) without a lemma beside them (check 8): AbortDecidesInTime, IsPrefixStable, ZDecidesInTime, ZPPAbort_PTM, ZPP_PTM, ZTIME, bitOfOutput
WARN  TCSlib/Complexity/Randomized/Fingerprint.lean              6 public def(s) without a lemma beside them (check 8): ZeroTestCore, inputBits, modParam, numTrials, testModulus, testPoint
WARN  TCSlib/Complexity/Randomized/Inclusions.lean               1 public def(s) without a lemma beside them (check 8): InRPStrong
WARN  TCSlib/Complexity/Randomized/Matching.lean                 3 public def(s) without a lemma beside them (check 8): lovaszEntryW, lovaszRowW, lovaszRows
WARN  TCSlib/Complexity/Randomized/MatchingMath.lean             2 public def(s) without a lemma beside them (check 8): edmondsMatrix, lovaszMatrix
WARN  TCSlib/Complexity/Randomized/Median.lean                   1 public def(s) without a lemma beside them (check 8): IsMedian
WARN  TCSlib/Complexity/Randomized/NPPoly.lean                   1 public def(s) without a lemma beside them (check 8): wireVal
WARN  TCSlib/Complexity/Randomized/PTM.lean                      8 public def(s) without a lemma beside them (check 8): BPDecidesInTime, BPP_PTM, RDecidesInTime, RP_PTM, RunsInTime, coRP_PTM, flipCfg, outputWith
WARN  TCSlib/Complexity/Randomized/PTMEquiv.lean                 4 public def(s) without a lemma beside them (check 8): BPDecidesInTimeWith, BPP_PTMWith, InRPWith, RDecidesInTimeWith
WARN  TCSlib/Complexity/Randomized/PolyTimeModel.lean            4 public def(s) without a lemma beside them (check 8): dropPrefixByLen, sliceDrop, sliceTake, takePrefixByLen
WARN  TCSlib/Complexity/Randomized/Primality.lean                1 public def(s) without a lemma beside them (check 8): compositeVerifier
WARN  TCSlib/Complexity/Randomized/PrimalityMath.lean            1 public def(s) without a lemma beside them (check 8): PRIMES
WARN  TCSlib/Complexity/Randomized/RPExpected.lean               1 public def(s) without a lemma beside them (check 8): RDecidesInExpTime
WARN  TCSlib/Complexity/Randomized/RandomWalk.lean               3 public def(s) without a lemma beside them (check 8): avg, hits, mult
WARN  TCSlib/Complexity/Randomized/RandomWalkCover.lean          2 public def(s) without a lemma beside them (check 8): Connected, IsBipartite
WARN  TCSlib/Complexity/Randomized/RandomWalkMixing.lean         1 public def(s) without a lemma beside them (check 8): visits
WARN  TCSlib/Complexity/Randomized/Reductions.lean               2 public def(s) without a lemma beside them (check 8): BPNP, RandReducible
WARN  TCSlib/Complexity/Randomized/SipserGacs.lean               4 public def(s) without a lemma beside them (check 8): ClosedUnderShiftOr, InPi2, InSigma2, shiftOrVerifier
WARN  TCSlib/Complexity/Randomized/Space.lean                    4 public def(s) without a lemma beside them (check 8): BPDecidesInSpace, BPL, BPSPACE, RDecidesInSpace
WARN  TCSlib/Complexity/Randomized/SpaceAmplify.lean             7 public def(s) without a lemma beside them (check 8): Fresh, amp, bump, emb, finish, push, tr
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean         2 public def(s) without a lemma beside them (check 8): reg0, sreg
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean     1 public def(s) without a lemma beside them (check 8): codeBound
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean  5 public def(s) without a lemma beside them (check 8): cpDst, cpEx, cpSrc, sL0, sL1
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean      2 public def(s) without a lemma beside them (check 8): accBit, decRule
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean          1 public def(s) without a lemma beside them (check 8): acc
WARN  TCSlib/Complexity/Randomized/UPath.lean                    3 public def(s) without a lemma beside them (check 8): SymRest, UShape, inEdge
WARN  TCSlib/Complexity/Randomized/UPathMachine.lean             14 public def(s) without a lemma beside them (check 8): UReg.Le, adEx, adP, adY, cpDst, cpEx, cpSrc, ixCol, ixEx, ixRow, mulA, mulB, mulEx, mulR
WARN  TCSlib/Complexity/Randomized/UPathRL.lean                  1 public def(s) without a lemma beside them (check 8): UReg.zero
WARN  TCSlib/Complexity/Randomized/UPathWalk.lean                1 public def(s) without a lemma beside them (check 8): upGraph
WARN  TCSlib/Complexity/Randomized/UniformSample.lean            3 public def(s) without a lemma beside them (check 8): encSample, sampleCoins, sampleStep
WARN  TCSlib/Complexity/Randomized/Yap.lean                      7 public def(s) without a lemma beside them (check 8): Core, M, M, Match, SoundFail, nLen, nN
WARN  TCSlib/Complexity/Randomized/ZPPEquiv.lean                 1 public def(s) without a lemma beside them (check 8): BPDecidesInExpTime
WARN  TCSlib/Complexity/Randomized/ZPPHostsClasses.lean          1 public def(s) without a lemma beside them (check 8): keepAs
WARN  TCSlib/Complexity/Randomized/ZeroP.lean                    17 public def(s) without a lemma beside them (check 8): pG, pG, pI, pM, pN, pPts, pR, ptStep, pts, qG, qG, qL, qN, qP, rawj, trStep, trialTest
WARN  TCSlib/Complexity/Randomized/ZeroPEval.lean                30 public def(s) without a lemma beside them (check 8): arg1W, arg2W, bodyW, ctxOf, encState, evalVals, isAddW, isDone, isMulW, isOneW, isSubW, isVarW, midW, okW, ptVal, rawValW, rest2W, restW, sCtx, sI, sK, sL, sN, sPts, sRaw, sW, tagBit, valN, valW, xW
WARN  TCSlib/Complexity/Randomized/ZeroPReduce.lean              3 public def(s) without a lemma beside them (check 8): gatesBody, pitToZerop, shiftGateW
WARN  TCSlib/Complexity/Randomized/ZeroPRun.lean                 2 public def(s) without a lemma beside them (check 8): gateInit, scanRun
INFO  TCSlib/Complexity/Randomized/Adleman.lean                  220 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/AlgCircuit.lean               547 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/AlgCircuitExample.lean        237 lines; 14 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInP.lean                   472 lines; 32 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInPCount.lean              259 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInPWords.lean              251 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPOperator.lean               109 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPPAmplify.lean               138 lines; 8 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/BPPEqP.lean                   95 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPPHard.lean                  268 lines; 11 public / 6 private declarations
INFO  TCSlib/Complexity/Randomized/BPTIMEThreshold.lean          224 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BiasedCoin.lean               280 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BiasedCoinHalting.lean        587 lines; 44 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Classes.lean                  1328 lines; 50 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Coins.lean                    470 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/DirectedWalk.lean             197 lines; 10 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/ErrorReduction.lean           402 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ExpectedTime.lean             622 lines > target 600
INFO  TCSlib/Complexity/Randomized/ExpectedTime.lean             622 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Fingerprint.lean              460 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Inclusions.lean               444 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Matching.lean                 514 lines; 25 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/MatchingMath.lean             421 lines; 20 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/Median.lean                   515 lines; 15 public / 15 private declarations
INFO  TCSlib/Complexity/Randomized/NPPoly.lean                   482 lines; 8 public / 5 private declarations
INFO  TCSlib/Complexity/Randomized/PTM.lean                      324 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PTMEquiv.lean                 492 lines; 39 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PolyTimeModel.lean            561 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Primality.lean                276 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PrimalityMath.lean            536 lines; 28 public / 3 private declarations
INFO  TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean       325 lines; 12 public / 13 private declarations
INFO  TCSlib/Complexity/Randomized/RPExpected.lean               218 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomBits.lean               406 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalk.lean               307 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkCover.lean          202 lines; 5 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkHitting.lean        555 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkMixing.lean         555 lines; 35 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean      292 lines; 3 public / 11 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkPad.lean            186 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Reductions.lean               362 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SchwartzZippel.lean           116 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SipserGacs.lean               679 lines > target 600
INFO  TCSlib/Complexity/Randomized/SipserGacs.lean               679 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Space.lean                    465 lines; 36 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplify.lean             530 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean         467 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean     181 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean  332 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean      405 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean          447 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPath.lean                    195 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathLoops.lean               331 lines; 10 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/UPathMachine.lean             455 lines; 56 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathParse.lean               348 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathRL.lean                  217 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathSearch.lean              333 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathWalk.lean                357 lines; 5 public / 2 private declarations
INFO  TCSlib/Complexity/Randomized/UniformSample.lean            368 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Yap.lean                      596 lines; 31 public / 6 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPEquiv.lean                 307 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPHosts.lean                 398 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPHostsClasses.lean          380 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroP.lean                    513 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPEval.lean                470 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPPIT.lean                 298 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPReduce.lean              402 lines; 26 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPRun.lean                 495 lines; 36 public / 15 private declarations

style_lint: 0 FAIL, 51 WARN over 65 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-Randomized-head.txt =====

WARN  TCSlib/Complexity/Randomized/Adleman.lean                  1 public def(s) without a lemma beside them (check 8): VerifierHasCircuits
WARN  TCSlib/Complexity/Randomized/AlgCircuit.lean               7 public def(s) without a lemma beside them (check 8): WellFormed, ZEROP, encodeGates, parseBin, refsBelow, shift, subCircuit
WARN  TCSlib/Complexity/Randomized/AlgCircuitExample.lean        4 public def(s) without a lemma beside them (check 8): isOp, prodOnePlus, prodOnePlusGates, varOrOne
WARN  TCSlib/Complexity/Randomized/BPLInP.lean                   8 public def(s) without a lemma beside them (check 8): accW, ctxOf, dpRun, initEntry, pickW, rowW, stepTest, vecW
WARN  TCSlib/Complexity/Randomized/BPLInPCount.lean              1 public def(s) without a lemma beside them (check 8): fixCoin
WARN  TCSlib/Complexity/Randomized/BPLInPWords.lean              4 public def(s) without a lemma beside them (check 8): codeStep, pow2W, radius, sumStep
WARN  TCSlib/Complexity/Randomized/BPPHard.lean                  2 public def(s) without a lemma beside them (check 8): BPPHard, CodePTM.toFinNDTM
WARN  TCSlib/Complexity/Randomized/BiasedCoin.lean               3 public def(s) without a lemma beside them (check 8): BiasedBPDecidesInTime, biasedBPTIME, biasedOutputProb
WARN  TCSlib/Complexity/Randomized/BiasedCoinHalting.lean        10 public def(s) without a lemma beside them (check 8): haltDigit, haltPrefix, hcCD, hcCD3, hcLin, hlDWord, hlJ, lenLeB, onesW, pow4Step
WARN  TCSlib/Complexity/Randomized/Classes.lean                  1328 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/Randomized/Classes.lean                  13 public def(s) without a lemma beside them (check 8): ClosedUnderAnswerIs, ClosedUnderAny, ClosedUnderMajority, ClosedUnderNot, ClosedUnderRace, InBPP, InBPPStrong, InCoRP, anyVerifier, boolVerifier, majorityVerifier, polyLen, raceVerifier
WARN  TCSlib/Complexity/Randomized/Coins.lean                    2 public def(s) without a lemma beside them (check 8): binDigit, vonNeumannRun
WARN  TCSlib/Complexity/Randomized/DirectedWalk.lean             1 public def(s) without a lemma beside them (check 8): outNbrs
WARN  TCSlib/Complexity/Randomized/ErrorReduction.lean           2 public def(s) without a lemma beside them (check 8): coordIndicator, successCount
WARN  TCSlib/Complexity/Randomized/ExpectedTime.lean             7 public def(s) without a lemma beside them (check 8): AbortDecidesInTime, IsPrefixStable, ZDecidesInTime, ZPPAbort_PTM, ZPP_PTM, ZTIME, bitOfOutput
WARN  TCSlib/Complexity/Randomized/Fingerprint.lean              6 public def(s) without a lemma beside them (check 8): ZeroTestCore, inputBits, modParam, numTrials, testModulus, testPoint
WARN  TCSlib/Complexity/Randomized/Inclusions.lean               1 public def(s) without a lemma beside them (check 8): InRPStrong
WARN  TCSlib/Complexity/Randomized/Matching.lean                 3 public def(s) without a lemma beside them (check 8): lovaszEntryW, lovaszRowW, lovaszRows
WARN  TCSlib/Complexity/Randomized/MatchingMath.lean             2 public def(s) without a lemma beside them (check 8): edmondsMatrix, lovaszMatrix
WARN  TCSlib/Complexity/Randomized/Median.lean                   1 public def(s) without a lemma beside them (check 8): IsMedian
WARN  TCSlib/Complexity/Randomized/NPPoly.lean                   1 public def(s) without a lemma beside them (check 8): wireVal
WARN  TCSlib/Complexity/Randomized/PTM.lean                      8 public def(s) without a lemma beside them (check 8): BPDecidesInTime, BPP_PTM, RDecidesInTime, RP_PTM, RunsInTime, coRP_PTM, flipCfg, outputWith
WARN  TCSlib/Complexity/Randomized/PTMEquiv.lean                 4 public def(s) without a lemma beside them (check 8): BPDecidesInTimeWith, BPP_PTMWith, InRPWith, RDecidesInTimeWith
WARN  TCSlib/Complexity/Randomized/PolyTimeModel.lean            4 public def(s) without a lemma beside them (check 8): dropPrefixByLen, sliceDrop, sliceTake, takePrefixByLen
WARN  TCSlib/Complexity/Randomized/Primality.lean                1 public def(s) without a lemma beside them (check 8): compositeVerifier
WARN  TCSlib/Complexity/Randomized/PrimalityMath.lean            1 public def(s) without a lemma beside them (check 8): PRIMES
WARN  TCSlib/Complexity/Randomized/RPExpected.lean               1 public def(s) without a lemma beside them (check 8): RDecidesInExpTime
WARN  TCSlib/Complexity/Randomized/RandomWalk.lean               3 public def(s) without a lemma beside them (check 8): avg, hits, mult
WARN  TCSlib/Complexity/Randomized/RandomWalkCover.lean          2 public def(s) without a lemma beside them (check 8): Connected, IsBipartite
WARN  TCSlib/Complexity/Randomized/RandomWalkMixing.lean         1 public def(s) without a lemma beside them (check 8): visits
WARN  TCSlib/Complexity/Randomized/Reductions.lean               2 public def(s) without a lemma beside them (check 8): BPNP, RandReducible
WARN  TCSlib/Complexity/Randomized/SipserGacs.lean               4 public def(s) without a lemma beside them (check 8): ClosedUnderShiftOr, InPi2, InSigma2, shiftOrVerifier
WARN  TCSlib/Complexity/Randomized/Space.lean                    4 public def(s) without a lemma beside them (check 8): BPDecidesInSpace, BPL, BPSPACE, RDecidesInSpace
WARN  TCSlib/Complexity/Randomized/SpaceAmplify.lean             7 public def(s) without a lemma beside them (check 8): Fresh, amp, bump, emb, finish, push, tr
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean         2 public def(s) without a lemma beside them (check 8): reg0, sreg
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean     1 public def(s) without a lemma beside them (check 8): codeBound
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean  5 public def(s) without a lemma beside them (check 8): cpDst, cpEx, cpSrc, sL0, sL1
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean      2 public def(s) without a lemma beside them (check 8): accBit, decRule
WARN  TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean          1 public def(s) without a lemma beside them (check 8): acc
WARN  TCSlib/Complexity/Randomized/UPath.lean                    3 public def(s) without a lemma beside them (check 8): SymRest, UShape, inEdge
WARN  TCSlib/Complexity/Randomized/UPathMachine.lean             14 public def(s) without a lemma beside them (check 8): UReg.Le, adEx, adP, adY, cpDst, cpEx, cpSrc, ixCol, ixEx, ixRow, mulA, mulB, mulEx, mulR
WARN  TCSlib/Complexity/Randomized/UPathRL.lean                  1 public def(s) without a lemma beside them (check 8): UReg.zero
WARN  TCSlib/Complexity/Randomized/UPathWalk.lean                1 public def(s) without a lemma beside them (check 8): upGraph
WARN  TCSlib/Complexity/Randomized/UniformSample.lean            3 public def(s) without a lemma beside them (check 8): encSample, sampleCoins, sampleStep
WARN  TCSlib/Complexity/Randomized/Yap.lean                      7 public def(s) without a lemma beside them (check 8): Core, M, M, Match, SoundFail, nLen, nN
WARN  TCSlib/Complexity/Randomized/ZPPEquiv.lean                 1 public def(s) without a lemma beside them (check 8): BPDecidesInExpTime
WARN  TCSlib/Complexity/Randomized/ZPPHostsClasses.lean          1 public def(s) without a lemma beside them (check 8): keepAs
WARN  TCSlib/Complexity/Randomized/ZeroP.lean                    17 public def(s) without a lemma beside them (check 8): pG, pG, pI, pM, pN, pPts, pR, ptStep, pts, qG, qG, qL, qN, qP, rawj, trStep, trialTest
WARN  TCSlib/Complexity/Randomized/ZeroPEval.lean                30 public def(s) without a lemma beside them (check 8): arg1W, arg2W, bodyW, ctxOf, encState, evalVals, isAddW, isDone, isMulW, isOneW, isSubW, isVarW, midW, okW, ptVal, rawValW, rest2W, restW, sCtx, sI, sK, sL, sN, sPts, sRaw, sW, tagBit, valN, valW, xW
WARN  TCSlib/Complexity/Randomized/ZeroPReduce.lean              3 public def(s) without a lemma beside them (check 8): gatesBody, pitToZerop, shiftGateW
WARN  TCSlib/Complexity/Randomized/ZeroPRun.lean                 2 public def(s) without a lemma beside them (check 8): gateInit, scanRun
INFO  TCSlib/Complexity/Randomized/Adleman.lean                  220 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/AlgCircuit.lean               547 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/AlgCircuitExample.lean        237 lines; 14 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInP.lean                   472 lines; 32 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInPCount.lean              260 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPLInPWords.lean              251 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPOperator.lean               109 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPPAmplify.lean               138 lines; 8 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/BPPEqP.lean                   95 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BPPHard.lean                  268 lines; 11 public / 6 private declarations
INFO  TCSlib/Complexity/Randomized/BPTIMEThreshold.lean          224 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BiasedCoin.lean               280 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/BiasedCoinHalting.lean        587 lines; 44 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Classes.lean                  1328 lines; 50 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Coins.lean                    470 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/DirectedWalk.lean             197 lines; 10 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/ErrorReduction.lean           402 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ExpectedTime.lean             622 lines > target 600
INFO  TCSlib/Complexity/Randomized/ExpectedTime.lean             622 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Fingerprint.lean              460 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Inclusions.lean               444 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Matching.lean                 514 lines; 25 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/MatchingMath.lean             421 lines; 20 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/Median.lean                   515 lines; 15 public / 15 private declarations
INFO  TCSlib/Complexity/Randomized/NPPoly.lean                   482 lines; 8 public / 5 private declarations
INFO  TCSlib/Complexity/Randomized/PTM.lean                      324 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PTMEquiv.lean                 492 lines; 39 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PolyTimeModel.lean            561 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Primality.lean                276 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/PrimalityMath.lean            536 lines; 28 public / 3 private declarations
INFO  TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean       325 lines; 12 public / 13 private declarations
INFO  TCSlib/Complexity/Randomized/RPExpected.lean               218 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomBits.lean               406 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalk.lean               307 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkCover.lean          202 lines; 5 public / 7 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkHitting.lean        555 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkMixing.lean         555 lines; 35 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean      292 lines; 3 public / 11 private declarations
INFO  TCSlib/Complexity/Randomized/RandomWalkPad.lean            186 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Reductions.lean               362 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SchwartzZippel.lean           116 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SipserGacs.lean               679 lines > target 600
INFO  TCSlib/Complexity/Randomized/SipserGacs.lean               679 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Space.lean                    465 lines; 36 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplify.lean             530 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean         467 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean     181 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean  332 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean      405 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean          447 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPath.lean                    195 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathLoops.lean               331 lines; 10 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/UPathMachine.lean             455 lines; 56 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathParse.lean               348 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathRL.lean                  217 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathSearch.lean              333 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/UPathWalk.lean                357 lines; 5 public / 2 private declarations
INFO  TCSlib/Complexity/Randomized/UniformSample.lean            368 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/Yap.lean                      596 lines; 31 public / 6 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPEquiv.lean                 307 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPHosts.lean                 398 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZPPHostsClasses.lean          380 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroP.lean                    513 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPEval.lean                470 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPPIT.lean                 298 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPReduce.lean              402 lines; 26 public / 1 private declarations
INFO  TCSlib/Complexity/Randomized/ZeroPRun.lean                 495 lines; 36 public / 15 private declarations

style_lint: 0 FAIL, 51 WARN over 65 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-SpaceComplexity-base.txt =====

WARN  TCSlib/Complexity/SpaceComplexity/Basic.lean                          3 public def(s) without a lemma beside them (check 8): ImplicitlyLogspaceComputable, SPACE, indexLang
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean                   4 public def(s) without a lemma beside them (check 8): Gs, hdOfV, inpOf, movePos
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 2 public def(s) without a lemma beside them (check 8): InitScan, PreChk
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean                    5 public def(s) without a lemma beside them (check 8): acceptLang, edgeLang, initLang, stepLang, validLang
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean                   1 public def(s) without a lemma beside them (check 8): layR
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean                  2 public def(s) without a lemma beside them (check 8): lay2R, zcode
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean                  17 public def(s) without a lemma beside them (check 8): dcAcc, dcBase, dcDowns, dcIncs, dcNext, dcPtr, icL, pmNext, prAdvL, prCont, sA1, sA2, sAd0, scIncs, vA1, vA2, vAd0
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean                    3 public def(s) without a lemma beside them (check 8): Shape1, Shape2, bnd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean                     1 public def(s) without a lemma beside them (check 8): Regs.Bd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean                     2 public def(s) without a lemma beside them (check 8): adStep, slStep
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Step.lean                     13 public def(s) without a lemma beside them (check 8): cellE, effAct, hdOf, idleAct, nbL, nbR, newHd, pairChunk, sChunk, sInit, stepCell, stepG, sumUpd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    7 public def(s) without a lemma beside them (check 8): BlankTogether, VAcc, mkCfg, outOf, vChunk, vInit, vStep
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Word.lean                     3 public def(s) without a lemma beside them (check 8): codeK, hH, padBits
WARN  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    3 public def(s) without a lemma beside them (check 8): CfgStep, configBound, summaryWord
WARN  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 5 public def(s) without a lemma beside them (check 8): A, ans, rO, rP, rg
WARN  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              1 public def(s) without a lemma beside them (check 8): Bd
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 34 public def(s) without a lemma beside them (check 8): A, Bd, Site.idx, Site.set, acExit, acI, clrReg, cpDst, cpExit, cpI, cpSrc, mvI, rBs, rC, rK, rLg, rN, rT, rT2, rU, rV, rX, rZ, rad, rc, rc1, rch, rs, rs1, rw, shI, toPh, wkExit, zero
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    6 public def(s) without a lemma beside them (check 8): bigB, decs, st1, st2, st3, st5
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean                  2 public def(s) without a lemma beside them (check 8): RCode, rset
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean                   4 public def(s) without a lemma beside them (check 8): Cl, SBd, rr, stp
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     1 public def(s) without a lemma beside them (check 8): wkSt
WARN  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   3 public def(s) without a lemma beside them (check 8): Shape, prog, tm
WARN  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2860 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean        2 public def(s) without a lemma beside them (check 8): gKv, gev
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean     3 public def(s) without a lemma beside them (check 8): grdX, gwX, gwcX
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean           1 public def(s) without a lemma beside them (check 8): GS
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean           26 public def(s) without a lemma beside them (check 8): Bd, St.Clear, St.wb, St.wt, lgv, rK, rT, rY, rc, rcnt, rcp, rcur, re, rg, ri, ri1, rk, rlg, rn, rs, rstp, ru, rv, wB, wT, zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2156 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           1 public def(s) without a lemma beside them (check 8): readTr
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  2 public def(s) without a lemma beside them (check 8): GraphReach, encodePATH
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean              2 public def(s) without a lemma beside them (check 8): Edge, expo
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean        1 public def(s) without a lemma beside them (check 8): qLang
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean       24 public def(s) without a lemma beside them (check 8): A, advF, advT, cpDst, cpI, cpNext, cpSrc, dInc, eInc, hvI, leI, leNo, leReg, leYes, sEinc, sSinc, sbExit, sbI, sbReg, shExit, shI, shReg, tAdv, tailAns
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean          2 public def(s) without a lemma beside them (check 8): Bd, zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean           1 public def(s) without a lemma beside them (check 8): setSt
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean          2 public def(s) without a lemma beside them (check 8): tailVal, wAns
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean              4 public def(s) without a lemma beside them (check 8): pathEdge, pathRaw, pathRawLang, rawEdge
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean       3 public def(s) without a lemma beside them (check 8): PReg.Le, akEx, akY
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean         1 public def(s) without a lemma beside them (check 8): PReg.zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          8 public def(s) without a lemma beside them (check 8): call, hi, liftAct, lo, nextPh, prog, start, tr
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          2613 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            2 public def(s) without a lemma beside them (check 8): LogspaceReducible, NLComplete
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   10 public def(s) without a lemma beside them (check 8): armCall, armProg, armTr, aseam, goAct, insCall, insTr, junkAct, retAct, rw2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              3 public def(s) without a lemma beside them (check 8): AHalt, AReach, Ins.embed
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                1 public def(s) without a lemma beside them (check 8): Pre
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean       4 public def(s) without a lemma beside them (check 8): G, decs, orc, searchA
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  4 public def(s) without a lemma beside them (check 8): bankK, bankStart, padCfg, sigCfg
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   1 public def(s) without a lemma beside them (check 8): incW
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  1 public def(s) without a lemma beside them (check 8): CleanRun
WARN  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            3 public def(s) without a lemma beside them (check 8): RegBox, leftSide, retPos
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 5 public def(s) without a lemma beside them (check 8): markSet, simCfg, simSt, stSt, stg
WARN  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            5 public def(s) without a lemma beside them (check 8): clAct, clNext, eraseAbove, idleK, wr
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               4 public def(s) without a lemma beside them (check 8): CallOK, compileFinTM, regWords, rstep
WARN  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               6 public def(s) without a lemma beside them (check 8): K, Rch, nilTM, o, prog, tr
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  5 public def(s) without a lemma beside them (check 8): eqBAct, eqCAct, halfLAct, halfSt, mv2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               5 public def(s) without a lemma beside them (check 8): clrEAct, decDAct, decEAct, decLAct, toEndAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                5 public def(s) without a lemma beside them (check 8): TPos.Valid, render, vsym, vword, wlen
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   3 public def(s) without a lemma beside them (check 8): incBAct, incCAct, regAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean                  3 public def(s) without a lemma beside them (check 8): MHalt, MIns.isMem, MReach
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean           5 public def(s) without a lemma beside them (check 8): MBox, mcompileFinTM, memAct, memTape, mseam
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean              1 public def(s) without a lemma beside them (check 8): MGuard
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean                  5 public def(s) without a lemma beside them (check 8): NAns, NHalts, NIns.targets, NPre, NPreS
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean           2 public def(s) without a lemma beside them (check 8): NBox, ncompileFinNDTM
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean               3 public def(s) without a lemma beside them (check 8): NAcc, NSem, RegLe
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean              2 public def(s) without a lemma beside them (check 8): PSem, ansProb
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean               2 public def(s) without a lemma beside them (check 8): NGood, NGuard
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 4 public def(s) without a lemma beside them (check 8): backAct, cmpAct, rewAct, skipAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                3 public def(s) without a lemma beside them (check 8): valP1Act, valP2Act, wSt
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              5 public def(s) without a lemma beside them (check 8): ReachesB, dcmp1Act, dcmp2Act, pskip1Act, pskip2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            7 public def(s) without a lemma beside them (check 8): FragOK, ValidPair, rejAct, valSAct, valUAct, valWAct, xAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               13 public def(s) without a lemma beside them (check 8): Mode.seg0, argSegs, compileTM, ctr, dIdle, gstep, isCharRead, nextRet, regMove, segDbl, segReg, toFin, virtSym
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   4 public def(s) without a lemma beside them (check 8): Consistent, HaltRel, SimRel, TPos.isCell
WARN  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         2 public def(s) without a lemma beside them (check 8): DecidesInSpace, NSPACE
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean             3 public def(s) without a lemma beside them (check 8): bigE, decs, orcN
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              1 public def(s) without a lemma beside them (check 8): DeepenContract
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             34 public def(s) without a lemma beside them (check 8): Bd, cpDst, cpExit, cpI, cpSrc, dmI, hvI, mvDst, mvExit, mvI, mvSrc, rC, rE, rI, rK, rM, rP, rQ, rSE, rSP, rT, rU, rV, rX, rZ, ra, rn, rs, rw, sbI, shExit, shI, shReg, zero
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean           1 public def(s) without a lemma beside them (check 8): CallOK
WARN  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   3 public def(s) without a lemma beside them (check 8): NL, NPSPACE, coNL
WARN  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  4 public def(s) without a lemma beside them (check 8): A, G, uBit, uLen
WARN  TCSlib/Complexity/SpaceComplexity/WindowClock.lean                    1676 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          265 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean                   211 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean                   524 lines; 31 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 790 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 790 lines; 19 public / 2 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean                   347 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean                    185 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean                   335 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean                  306 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean                  524 lines; 81 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean                    466 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean                     334 lines; 67 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Run.lean                      281 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean                     336 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Step.lean                     509 lines; 29 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean              425 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    601 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    601 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Word.lean                     511 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    590 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    646 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    646 lines; 31 public / 3 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  703 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  703 lines; 5 public / 23 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       147 lines; 4 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 608 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 608 lines; 77 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    618 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    618 lines; 23 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean                  356 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean                   475 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     630 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     630 lines; 40 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean                  280 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpTime.lean                        142 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      317 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   418 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2860 lines; 4 public / 64 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean     297 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean        315 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean     363 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean      158 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean       358 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean        192 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean           320 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean           311 lines; 69 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  120 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2156 lines; 27 public / 57 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1460 lines; 2 public / 62 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  210 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean              353 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean        243 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean       577 lines; 45 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean          355 lines; 62 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean           303 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean          422 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean              504 lines; 33 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean       478 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean         577 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          825 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          825 lines; 13 public / 16 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          2613 lines; 9 public / 111 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            184 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   408 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean                93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean              427 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              505 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean              231 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean                551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean              299 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean       319 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   222 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               296 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean                  295 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean           477 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean              556 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean                  448 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean           403 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean           103 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean               473 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace.lean          195 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean              471 lines; 29 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean              314 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean             360 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean               270 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               353 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean                 116 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Savitch.lean                        143 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean             140 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              844 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              844 lines; 2 public / 43 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             635 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             635 lines; 80 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean               302 lines; 8 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean           506 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean                 337 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean              305 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean               197 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Window.lean              182 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   109 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/WindowClock.lean                    1676 lines; 4 public / 66 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean                      264 lines; 11 public / 2 private declarations

style_lint: 0 FAIL, 81 WARN over 112 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/campaign-SpaceComplexity-head.txt =====

WARN  TCSlib/Complexity/SpaceComplexity/Basic.lean                          3 public def(s) without a lemma beside them (check 8): ImplicitlyLogspaceComputable, SPACE, indexLang
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean                   4 public def(s) without a lemma beside them (check 8): Gs, hdOfV, inpOf, movePos
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 2 public def(s) without a lemma beside them (check 8): InitScan, PreChk
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean                    5 public def(s) without a lemma beside them (check 8): acceptLang, edgeLang, initLang, stepLang, validLang
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean                   1 public def(s) without a lemma beside them (check 8): layR
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean                  2 public def(s) without a lemma beside them (check 8): lay2R, zcode
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean                  17 public def(s) without a lemma beside them (check 8): dcAcc, dcBase, dcDowns, dcIncs, dcNext, dcPtr, icL, pmNext, prAdvL, prCont, sA1, sA2, sAd0, scIncs, vA1, vA2, vAd0
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean                    3 public def(s) without a lemma beside them (check 8): Shape1, Shape2, bnd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean                     1 public def(s) without a lemma beside them (check 8): Regs.Bd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean                     2 public def(s) without a lemma beside them (check 8): adStep, slStep
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Step.lean                     13 public def(s) without a lemma beside them (check 8): cellE, effAct, hdOf, idleAct, nbL, nbR, newHd, pairChunk, sChunk, sInit, stepCell, stepG, sumUpd
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    7 public def(s) without a lemma beside them (check 8): BlankTogether, VAcc, mkCfg, outOf, vChunk, vInit, vStep
WARN  TCSlib/Complexity/SpaceComplexity/Codec/Word.lean                     3 public def(s) without a lemma beside them (check 8): codeK, hH, padBits
WARN  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    3 public def(s) without a lemma beside them (check 8): CfgStep, configBound, summaryWord
WARN  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 5 public def(s) without a lemma beside them (check 8): A, ans, rO, rP, rg
WARN  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              1 public def(s) without a lemma beside them (check 8): Bd
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 34 public def(s) without a lemma beside them (check 8): A, Bd, Site.idx, Site.set, acExit, acI, clrReg, cpDst, cpExit, cpI, cpSrc, mvI, rBs, rC, rK, rLg, rN, rT, rT2, rU, rV, rX, rZ, rad, rc, rc1, rch, rs, rs1, rw, shI, toPh, wkExit, zero
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    6 public def(s) without a lemma beside them (check 8): bigB, decs, st1, st2, st3, st5
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean                  2 public def(s) without a lemma beside them (check 8): RCode, rset
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean                   4 public def(s) without a lemma beside them (check 8): Cl, SBd, rr, stp
WARN  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     1 public def(s) without a lemma beside them (check 8): wkSt
WARN  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   3 public def(s) without a lemma beside them (check 8): Shape, prog, tm
WARN  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2860 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean        2 public def(s) without a lemma beside them (check 8): gKv, gev
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean     3 public def(s) without a lemma beside them (check 8): grdX, gwX, gwcX
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean           1 public def(s) without a lemma beside them (check 8): GS
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean           26 public def(s) without a lemma beside them (check 8): Bd, St.Clear, St.wb, St.wt, lgv, rK, rT, rY, rc, rcnt, rcp, rcur, re, rg, ri, ri1, rk, rlg, rn, rs, rstp, ru, rv, wB, wT, zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2156 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           1 public def(s) without a lemma beside them (check 8): readTr
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  2 public def(s) without a lemma beside them (check 8): GraphReach, encodePATH
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean              2 public def(s) without a lemma beside them (check 8): Edge, expo
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean        1 public def(s) without a lemma beside them (check 8): qLang
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean       24 public def(s) without a lemma beside them (check 8): A, advF, advT, cpDst, cpI, cpNext, cpSrc, dInc, eInc, hvI, leI, leNo, leReg, leYes, sEinc, sSinc, sbExit, sbI, sbReg, shExit, shI, shReg, tAdv, tailAns
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean          2 public def(s) without a lemma beside them (check 8): Bd, zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean           1 public def(s) without a lemma beside them (check 8): setSt
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean          2 public def(s) without a lemma beside them (check 8): tailVal, wAns
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean              4 public def(s) without a lemma beside them (check 8): pathEdge, pathRaw, pathRawLang, rawEdge
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean       3 public def(s) without a lemma beside them (check 8): PReg.Le, akEx, akY
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean         1 public def(s) without a lemma beside them (check 8): PReg.zero
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          8 public def(s) without a lemma beside them (check 8): call, hi, liftAct, lo, nextPh, prog, start, tr
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          2613 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            2 public def(s) without a lemma beside them (check 8): LogspaceReducible, NLComplete
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   10 public def(s) without a lemma beside them (check 8): armCall, armProg, armTr, aseam, goAct, insCall, insTr, junkAct, retAct, rw2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              3 public def(s) without a lemma beside them (check 8): AHalt, AReach, Ins.embed
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                1 public def(s) without a lemma beside them (check 8): Pre
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean       4 public def(s) without a lemma beside them (check 8): G, decs, orc, searchA
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  4 public def(s) without a lemma beside them (check 8): bankK, bankStart, padCfg, sigCfg
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   1 public def(s) without a lemma beside them (check 8): incW
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  1 public def(s) without a lemma beside them (check 8): CleanRun
WARN  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            3 public def(s) without a lemma beside them (check 8): RegBox, leftSide, retPos
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 5 public def(s) without a lemma beside them (check 8): markSet, simCfg, simSt, stSt, stg
WARN  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            5 public def(s) without a lemma beside them (check 8): clAct, clNext, eraseAbove, idleK, wr
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               4 public def(s) without a lemma beside them (check 8): CallOK, compileFinTM, regWords, rstep
WARN  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               6 public def(s) without a lemma beside them (check 8): K, Rch, nilTM, o, prog, tr
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  5 public def(s) without a lemma beside them (check 8): eqBAct, eqCAct, halfLAct, halfSt, mv2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               5 public def(s) without a lemma beside them (check 8): clrEAct, decDAct, decEAct, decLAct, toEndAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                5 public def(s) without a lemma beside them (check 8): TPos.Valid, render, vsym, vword, wlen
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   3 public def(s) without a lemma beside them (check 8): incBAct, incCAct, regAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean                  3 public def(s) without a lemma beside them (check 8): MHalt, MIns.isMem, MReach
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean           5 public def(s) without a lemma beside them (check 8): MBox, mcompileFinTM, memAct, memTape, mseam
WARN  TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean              1 public def(s) without a lemma beside them (check 8): MGuard
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean                  5 public def(s) without a lemma beside them (check 8): NAns, NHalts, NIns.targets, NPre, NPreS
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean           2 public def(s) without a lemma beside them (check 8): NBox, ncompileFinNDTM
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean               3 public def(s) without a lemma beside them (check 8): NAcc, NSem, RegLe
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean              2 public def(s) without a lemma beside them (check 8): PSem, ansProb
WARN  TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean               2 public def(s) without a lemma beside them (check 8): NGood, NGuard
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 4 public def(s) without a lemma beside them (check 8): backAct, cmpAct, rewAct, skipAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                3 public def(s) without a lemma beside them (check 8): valP1Act, valP2Act, wSt
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              5 public def(s) without a lemma beside them (check 8): ReachesB, dcmp1Act, dcmp2Act, pskip1Act, pskip2Act
WARN  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            7 public def(s) without a lemma beside them (check 8): FragOK, ValidPair, rejAct, valSAct, valUAct, valWAct, xAct
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               13 public def(s) without a lemma beside them (check 8): Mode.seg0, argSegs, compileTM, ctr, dIdle, gstep, isCharRead, nextRet, regMove, segDbl, segReg, toFin, virtSym
WARN  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   4 public def(s) without a lemma beside them (check 8): Consistent, HaltRel, SimRel, TPos.isCell
WARN  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         2 public def(s) without a lemma beside them (check 8): DecidesInSpace, NSPACE
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean             3 public def(s) without a lemma beside them (check 8): bigE, decs, orcN
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              1 public def(s) without a lemma beside them (check 8): DeepenContract
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             34 public def(s) without a lemma beside them (check 8): Bd, cpDst, cpExit, cpI, cpSrc, dmI, hvI, mvDst, mvExit, mvI, mvSrc, rC, rE, rI, rK, rM, rP, rQ, rSE, rSP, rT, rU, rV, rX, rZ, ra, rn, rs, rw, sbI, shExit, shI, shReg, zero
WARN  TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean           1 public def(s) without a lemma beside them (check 8): CallOK
WARN  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   3 public def(s) without a lemma beside them (check 8): NL, NPSPACE, coNL
WARN  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  4 public def(s) without a lemma beside them (check 8): A, G, uBit, uLen
WARN  TCSlib/Complexity/SpaceComplexity/WindowClock.lean                    1676 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          265 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean                   211 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean                   524 lines; 31 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 790 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 790 lines; 19 public / 2 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean                   347 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean                    185 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean                   335 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean                  306 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean                  524 lines; 81 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean                    466 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean                     334 lines; 67 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Run.lean                      281 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean                     336 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Step.lean                     509 lines; 29 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean              425 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    601 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean                    601 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Word.lean                     511 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    590 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    646 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    646 lines; 31 public / 3 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  703 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  703 lines; 5 public / 23 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       147 lines; 4 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 608 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean                 608 lines; 77 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    624 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean                    624 lines; 23 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean                  357 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean                   475 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     630 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean                     630 lines; 40 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean                  280 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ExpTime.lean                        142 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      317 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   418 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2860 lines; 4 public / 64 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean     297 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean        315 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean     363 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean      160 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean       362 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean        195 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean           323 lines; 17 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean           311 lines; 69 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  120 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2156 lines; 27 public / 57 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1460 lines; 2 public / 62 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  210 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean              353 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean        243 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean       577 lines; 45 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean          355 lines; 62 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean           303 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean          422 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean              504 lines; 33 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean       478 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean         577 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          825 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          825 lines; 13 public / 16 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          2613 lines; 9 public / 111 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            184 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   408 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean                93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean              427 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              505 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean              231 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean                551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean              299 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean       319 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   222 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               296 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean                  295 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean           477 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean              556 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean                  448 lines; 37 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean           403 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean           103 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean               473 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace.lean          195 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean              471 lines; 29 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean              314 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean             360 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean               270 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               353 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean                 116 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Savitch.lean                        143 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean             140 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              844 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean              844 lines; 2 public / 43 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             635 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean             635 lines; 80 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean               302 lines; 8 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean           506 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean                 337 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean              305 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean               197 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SavitchARM/Window.lean              182 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   109 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/WindowClock.lean                    1676 lines; 4 public / 66 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean                      264 lines; 11 public / 2 private declarations

style_lint: 0 FAIL, 81 WARN over 112 files

## ===== campaign/gates/107-rp1-dedup/evidence/lint/policy-base.txt =====


1 findings in 14 files




TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean:72: `inWin_stepWith` proof is 21 lines, no **Proof sketch.**










## ===== campaign/gates/107-rp1-dedup/evidence/lint/policy-head.txt =====


1 findings in 14 files




TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean:72: `inWin_stepWith` proof is 21 lines, no **Proof sketch.**










## ===== campaign/gates/107-rp1-dedup/evidence/merged-tree/down-lrp3.txt =====

TCSlib/Complexity/ClassPSPACE/TQBFHardMachine
TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier
TCSlib/Complexity/ClassPSPACE/TQBFHardBridge
TCSlib/Complexity/ClassPSPACE/TQBFHardParams
TCSlib/Complexity/ClassPSPACE/TQBFHard
TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main
TCSlib/Complexity/SpaceComplexity/ExpTime
TCSlib/Complexity/Randomized/Space
TCSlib/Complexity/Randomized/BPLInPCount
TCSlib/Complexity/Randomized/BPLInP
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace
TCSlib/Complexity/Randomized/SpaceAmplifyPoly
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof
TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/Randomized/UPath
TCSlib/Complexity/Randomized/UPathMachine
TCSlib/Complexity/Randomized/UPathLoops
TCSlib/Complexity/Randomized/UPathParse
TCSlib/Complexity/Randomized/UPathSearch
TCSlib/Complexity/Randomized/UPathWalk
TCSlib/Complexity/Randomized/UPathRL
TCSlib/Complexity/Randomized
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach
TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion
TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup
TCSlib/Complexity/SpaceComplexity/SavitchARM/Search
TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/SavitchARM/Window
TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen
TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/SpaceComplexity

## ===== campaign/gates/107-rp1-dedup/evidence/merged-tree/replay-lrp3-static.txt =====

modules 53, mismatches 0, static total 21

## ===== campaign/gates/107-rp1-dedup/evidence/merged-tree/replay-lrp3.log =====

# replay-lrp3 at 485cfbab: #216, RP-1, merged with the campaign after #208/#212/#213 (53 modules), fresh .oleans into oleans-lrp3
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardBridge exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardParams exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF exit=0 errors=0 sorry=21
TCSlib/Complexity/ClassPSPACE exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpTime exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Space exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInPCount exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/Path exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPath exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathLoops exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathParse exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathSearch exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathRL exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Search exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Window exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Savitch exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
# modules=53 failed=0

## ===== campaign/gates/107-rp1-dedup/evidence/merged-tree/replay-lrp3.sh =====

#!/usr/bin/env bash
# Replay lrp3 (#216, RP-1, merged with the campaign after #208/#212/#213; branch lean/dedup-rp1, stacked on the campaign after #208, #212, #213 (oleans-lcamp2)): its downstream closure (53 modules),
# fresh .oleans into oleans-lrp3, a copy of oleans-lcamp2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-rp1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lrp3.txt"
LOG="$S/fills/replay/replay-lrp3.log"
PINS="TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean:1ad7891373f537d35ae897a763480ba150284258
TCSlib/Complexity/Randomized/BPLInP.lean:55b06b3b5fdfdb4f129912aad004e97d60e71b7b
TCSlib/Complexity/Randomized/BPLInPCount.lean:18a9cf33245ef2959816eeffeb7372a8d2f6df54
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean:0b9a4a831d1fb87a49ab6c8faedc37db9f99e6a9
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean:1cf0278d862100ff0cd0d999d469f40996172e92
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean:dad3a22033c61ef2669953329f94b4ebe5e5ac6b
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean:fab553600356b779249af104adb90b7eb25fcd95
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean:d82e8c6548309fbe90eae665732d7250ad661a45
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean:3066bf69ca7c0942b95f3fb2821cea222425a479
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean:896e12dac231e0ed4fa0aceb3fdc6dc52a231700
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean:a507cf09b43132d3ece206d5a1c4be15cac84607
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean:ed3857f7b55b665df0d26dc4738ae6a8adfe77a4
TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean:78814e59e44912a0d59ce3a9cd92e25349f39f74
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean:8da4bc53b70397c0640942064cec52de987fc9d5"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-rp1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3a1c8740d7baf9eb3584f2ae3ecaed5cfe40e994 HEAD || { echo "precheck: the head must contain the campaign after #208, #212, #213 (oleans-lcamp2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3a1c8740d7baf9eb3584f2ae3ecaed5cfe40e994 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #208, #212, #213 (oleans-lcamp2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "53" ] || { echo "precheck: the replay list must have 53 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lrp3" ] && { echo "precheck: $S/oleans-lrp3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp2" ] || { echo "precheck: oleans-lcamp2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp2" "$S/oleans-lrp3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lrp3 at $(git rev-parse --short HEAD): #216, RP-1, merged with the campaign after #208/#212/#213 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lrp3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lrp3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"; sst=$?
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
# the exit status: nonzero unless every listed module passed and the static check found no mismatch
tail -1 "$LOG" | grep -qx "# modules=53 failed=0" || { echo "replay: a module failed, or the count is not 53" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/README.md =====

# RP-1: exhaustive rule-10 check (gate evidence)

Branch `lean/dedup-rp1`, worktree `/home/user/tcslib-scratch/wt-rp1`, base `4c7dffce`, commit
`f200144b`. The probes were run on 2026-11-06 with
`devtools/seyoon/leanelab.sh <wt-hk> /home/user/tcslib-scratch/oleans-lnth <probe>`. They ran one
at a time, and no `lake` command was used.

## Method

Rule 10: no proof outside a definition's home file reads it by unfolding or by definitional
equality. The check makes each sealed definition `irreducible` in a copy of every module that can
see it, then elaborates the copy. Any proof that still reads the body fails to elaborate. That
covers `exact h` across the definition, `cases`/`rcases`/`rintro` on it, anonymous constructors and
`Or.inl`/`Or.inr` built against it, and `show`/`change` through it. Explicit `simp [Def]` or
`rw [Def]` unfolds use equation lemmas and still work under `irreducible`, so those were found by
grep and re-pointed separately; the commit has none left. The published `Iff.rfl` equations live in
the home files, which are already compiled, so a proof that goes through them passes.

## The seven sealed definitions

| Definition | Home file | Equation(s) |
|---|---|---|
| `Complexity.WalkLe` | `Logspace/PathWalk` | `walkLe_zero_iff`, `walkLe_succ_iff_head` |
| `Complexity.Codec.StepRel` | `Codec/Bridge` | `stepRel_iff_mem` |
| `Complexity.ExpBFS.RCode` | `ExpBFS/Radius` | `rcode_iff_reflTransGen` |
| `Complexity.ExpBFS.WinRun` | `ExpBFS/Radius` | `winRun_iff` |
| `Complexity.LogProg.SavitchARM.Rel` | `SavitchARM/Recursion` | `rel_iff_orc` |
| `Complexity.LogProg.SavitchARM.InitO` | `SavitchARM/Search` | `initO_iff_orc` |
| `Complexity.LogProg.SavitchARM.AccO` | `SavitchARM/Search` | `accO_iff_orc` |

## How the 52 probe copies were generated

The generator is `mkprobes.py.txt`.

1. **Choosing the modules.** I built the import graph of `TCSlib/` from each file's `import`
   lines. The copies cover every module that imports at least one of the five home files, directly
   or through other modules. That is 49 modules. Three home files are probed as well, because each
   also uses definitions homed elsewhere:
   - `ExpBFS/Radius`, with `StepRel` sealed;
   - `SavitchARM/Search`, with `WalkLe`, `StepRel` and `Rel` sealed;
   - `SavitchARM/Recursion`, with `WalkLe` and `StepRel` sealed.

   Total: 52 copies.
2. **Choosing what to seal.** Each copy seals only the definitions whose home file it imports.
   A definition homed in the module itself is never sealed in that module's copy.
3. **Building each copy.**
   - The copy is the module's source as committed. The exception is `SavitchARM/Reach`, which was
     first probed before its fix and then regenerated and probed again after it.
   - Every `set_option maxHeartbeats` value that is `0` or above 400000 is set to `400000`.
   - After the last `import` line, the generator inserts `set_option maxHeartbeats 400000` and one
     `attribute [local irreducible] <name>` line per sealed definition. `example-header.lean.txt`
     shows this block for `ISCountGenWalk`.
   - Copies are written to `/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/`.

**Excluded home files.** Two home files are not probed: `Logspace/PathWalk` and `Codec/Bridge`.
Neither imports any other home file, directly or indirectly (checked against the same import
graph), so there is nothing to seal in them. This is two files, not three. The other three home
files are probed as described in step 1.

**State of the tree when probed.** The probes ran on the working tree after all re-points except
`SavitchARM/Reach`'s. That tree is identical to commit `f200144b` apart from `Reach`. `Reach` was
then fixed, regenerated and probed again: the "after fix" row below. `probes.out` holds each probe's
full output, under a header line `== <module> exit=N`.

## Results

53 runs: 52 modules, plus `Reach` a second time after its fix. In the final state all 52 modules
exit 0 with no errors. Only one probe ever failed: `Reach` before its fix, with one error at
`mem_iff_reach` (line 293 of the real file, line 296 of the copy). There, `hstep`, a `stepLang`
membership, was passed where `∀ j < t, StepRel N x s (c j) (c (j + 1))` is expected. The fix wraps
it as `fun j hj => stepRel_iff_mem.mpr (hstep j hj)`. Error counts are lines matching `: error`. The
only non-error output is the existing `sorry` warnings in `ClassPSPACE.TQBF`.

| Module | Sealed definitions | Exit code | Errors |
|---|---|---|---|
| `TCSlib.Complexity.ClassPSPACE` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBF` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHard` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardBridge` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardMachine` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardParams` | 1 | 0 | 0 |
| `TCSlib.Complexity.ClassPSPACE.TQBFHardVerifier` | 1 | 0 | 0 |
| `TCSlib.Complexity.Randomized` | 4 | 0 | 0 |
| `TCSlib.Complexity.Randomized.BPLInP` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.BPLInPCount` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.Space` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPoly` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun` | 3 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPath` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathLoops` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathMachine` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathParse` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathRL` | 4 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathSearch` | 2 | 0 | 0 |
| `TCSlib.Complexity.Randomized.UPathWalk` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpBFS.Main` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.ExpTime` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius` | 4 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi` | 7 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.Path` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHard` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof` | 1 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.Savitch` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct` | 5 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (before fix)` | 2 | 1 | 1 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (after fix)` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion` | 2 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Search` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup` | 3 | 0 | 0 |
| `TCSlib.Complexity.SpaceComplexity.SavitchARM.Window` | 4 | 0 | 0 |

## Sanity probe (`zz_sanity.lean.txt`, output `zz_sanity.out`)

The sanity probe checks that sealing actually catches reads. It imports `Logspace.PathWalk` and
`SavitchARM.Search` and seals `WalkLe`, `StepRel` and `Rel`. It then states four `example`s: three
are planted definitional reads and one goes through an equation. **Result: exit 1 with exactly
three errors, one on each planted read; the equation example passes.**

| Line | Planted read | Result |
|---|---|---|
| 9 | `exact h` from `WalkLe E n 0 c t` to `c = t` | error: Type mismatch |
| 11 | `rcases h` on `WalkLe E n 1 c t` | error: `rcases` failed, "is not an inductive datatype" |
| 17 | `exact h` from `Rel orc x s u v` to `orc 3 (…) = true` | error: Type mismatch |
| 19–20 | `walkLe_zero_iff.mp h` (control) | no error |

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/example-header.lean.txt =====

import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine
set_option maxHeartbeats 400000
attribute [local irreducible] Complexity.WalkLe
attribute [local irreducible] Complexity.Codec.StepRel
attribute [local irreducible] Complexity.LogProg.SavitchARM.Rel
attribute [local irreducible] Complexity.LogProg.SavitchARM.InitO
attribute [local irreducible] Complexity.LogProg.SavitchARM.AccO

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/mkprobes.py.txt =====

import os,re,sys
root='/home/user/tcslib-scratch/wt-rp1'
out='/home/user/tcslib-scratch/wt-hk/rvprobe/rp1'
H='TCSlib.Complexity.SpaceComplexity.'
homes={H+'Logspace.PathWalk':['Complexity.WalkLe'],
       H+'Codec.Bridge':['Complexity.Codec.StepRel'],
       H+'ExpBFS.Radius':['Complexity.ExpBFS.RCode','Complexity.ExpBFS.WinRun'],
       H+'SavitchARM.Recursion':['Complexity.LogProg.SavitchARM.Rel'],
       H+'SavitchARM.Search':['Complexity.LogProg.SavitchARM.InitO','Complexity.LogProg.SavitchARM.AccO']}
mods={}
for dp,dn,fn in os.walk(os.path.join(root,'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p=os.path.join(dp,f)
            m=os.path.relpath(p,root)[:-5].replace('/','.')
            mods[m]=re.findall(r'^import\s+(\S+)',open(p,encoding='utf-8').read(),re.M)
memo={}
def closure(m):
    if m in memo: return memo[m]
    memo[m]=set()
    s=set()
    for i in mods.get(m,[]):
        s.add(i); s|=closure(i)
    memo[m]=s; return s
targets=sys.argv[1:]
for m in targets:
    cl=closure(m)
    names=[n for h,ns in homes.items() if h in cl for n in ns]
    if not names: print('SKIP',m); continue
    src=open(os.path.join(root,m.replace('.','/')+'.lean'),encoding='utf-8').read()
    src=re.sub(r'(set_option maxHeartbeats) (\d+)',lambda mo: mo.group(1)+' '+('400000' if int(mo.group(2))==0 or int(mo.group(2))>400000 else mo.group(2)),src)
    lines=src.split('\n')
    last=max(i for i,l in enumerate(lines) if l.startswith('import '))
    ins=['set_option maxHeartbeats 400000']+['attribute [local irreducible] '+n for n in names]
    lines[last+1:last+1]=ins
    fn=os.path.join(out,m.split('.',1)[1].replace('.','_')+'.lean')
    open(fn,'w',encoding='utf-8').write('\n'.join(lines))
    print(fn, len(names))

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/probes.out =====

== TCSlib.Complexity.ClassPSPACE exit=0
== TCSlib.Complexity.ClassPSPACE.TQBF exit=0
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2167:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2213:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2221:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2228:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2237:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2247:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2256:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2269:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2285:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2299:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2319:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2332:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2344:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2353:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2359:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2368:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2380:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2405:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2422:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2435:8: warning: declaration uses 'sorry'
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_ClassPSPACE_TQBF.lean:2452:8: warning: declaration uses 'sorry'
== TCSlib.Complexity.ClassPSPACE.TQBFHard exit=0
== TCSlib.Complexity.ClassPSPACE.TQBFHardBridge exit=0
== TCSlib.Complexity.ClassPSPACE.TQBFHardMachine exit=0
== TCSlib.Complexity.ClassPSPACE.TQBFHardParams exit=0
== TCSlib.Complexity.ClassPSPACE.TQBFHardVerifier exit=0
== TCSlib.Complexity.Randomized exit=0
== TCSlib.Complexity.Randomized.BPLInP exit=0
== TCSlib.Complexity.Randomized.BPLInPCount exit=0
== TCSlib.Complexity.Randomized.Space exit=0
== TCSlib.Complexity.Randomized.SpaceAmplifyPoly exit=0
== TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode exit=0
== TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine exit=0
== TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun exit=0
== TCSlib.Complexity.Randomized.UPath exit=0
== TCSlib.Complexity.Randomized.UPathLoops exit=0
== TCSlib.Complexity.Randomized.UPathMachine exit=0
== TCSlib.Complexity.Randomized.UPathParse exit=0
== TCSlib.Complexity.Randomized.UPathRL exit=0
== TCSlib.Complexity.Randomized.UPathSearch exit=0
== TCSlib.Complexity.Randomized.UPathWalk exit=0
== TCSlib.Complexity.SpaceComplexity exit=0
== TCSlib.Complexity.SpaceComplexity.ExpBFS.Main exit=0
== TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius exit=0
== TCSlib.Complexity.SpaceComplexity.ExpTime exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.Path exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHard exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine exit=0
== TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof exit=0
== TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace exit=0
== TCSlib.Complexity.SpaceComplexity.Savitch exit=0
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_SpaceComplexity_Savitch.lean:99:8: warning: declaration uses 'sorry'
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct exit=0
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (before fix) exit=1
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/Complexity_SpaceComplexity_SavitchARM_Reach.lean:296:58: error: Application type mismatch: The argument
  hstep
has type
  ∀ i < t, pairEncode x (pairEncode (c i).bits (pairEncode (c (i + 1)).bits s.bits)) ∈ stepLang N
but is expected to have type
  ∀ j < t, StepRel N x s (c j) (c (j + 1))
in the application
  reach_of_chain (2 ^ w) (StepRel N x s) c t hstep
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach (after fix) exit=0
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion exit=0
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Search exit=0
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup exit=0
== TCSlib.Complexity.SpaceComplexity.SavitchARM.Window exit=0

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/zz_sanity.lean.txt =====

import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Search
set_option maxHeartbeats 400000
open Turing
attribute [local irreducible] Complexity.WalkLe Complexity.Codec.StepRel
attribute [local irreducible] Complexity.LogProg.SavitchARM.Rel

-- each of these must FAIL (a definitional read through an irreducible definition)
example (E : ℕ → ℕ → Prop) (n c t : ℕ) (h : Complexity.WalkLe E n 0 c t) : c = t := h
example (E : ℕ → ℕ → Prop) (n c t : ℕ) (h : Complexity.WalkLe E n 1 c t) : c = t ∨ True := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr trivial
example (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s u v : ℕ)
    (h : Complexity.LogProg.SavitchARM.Rel orc x s u v) :
    orc 3 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) = true :=
  h
-- this must succeed
example (E : ℕ → ℕ → Prop) (n c t : ℕ) (h : Complexity.WalkLe E n 0 c t) : c = t :=
  Complexity.walkLe_zero_iff.mp h

## ===== campaign/gates/107-rp1-dedup/evidence/rule10/zz_sanity.out =====

== zz_sanity exit=1
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/zz_sanity.lean:9:84: error: Type mismatch
  h
has type
  Complexity.WalkLe E n 0 c t
but is expected to have type
  c = t
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/zz_sanity.lean:11:16: error: Tactic `rcases` failed: `h : Complexity.WalkLe E n 1 c t` is not an inductive datatype
/home/user/tcslib-scratch/wt-hk/rvprobe/rp1/zz_sanity.lean:17:2: error: Type mismatch
  h
has type
  Complexity.LogProg.SavitchARM.Rel orc x s u v
but is expected to have type
  orc 3 (pairEncode x (pairEncode u.bits (pairEncode v.bits s.bits))) = true

## ===== TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardSemantics
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance as a short path of blocks

[AB09, Claim 4.4 and the proof of Theorem 4.13]: a space-bounded machine accepts `x` iff its
configuration graph has a path from the initial to an accepting configuration of length at
most the number of configurations. This file restates the bridge lemma of the configuration
codec (`Complexity.Codec.mem_iff_codeChain`, `Complexity.Codec.mem_of_codePath`) in the
form the `TQBF` reduction quantifies over: **blocks** of `w ≥ codeLen` bits whose first
`codeLen` bits are a code word, a one-step relation `blockStep` that is reflexive (so that
paths of length at most `2^w` are paths of length exactly `2^w`), and the midpoint recursion
`Complexity.TQBFHard.Mid` of `TQBFHardSemantics`.

Infrastructure for `Complexity.TQBF_PSPACEHard`; not itself a book result.

## Main definitions

* `Complexity.TQBFHard.codeLen` — the length of a code word.
* `Complexity.TQBFHard.blockInit`, `blockAcc`, `blockStep` — the three code-language tests on
  the code-word prefixes of blocks.

## Main results

* `Complexity.TQBFHard.mem_iff_mid` — membership is "some initial block reaches some
  accepting block in the midpoint recursion of depth `w`". [AB09, Claim 4.4(1), proof of
  Theorem 4.13]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4; §4.2, Theorem 4.13.)
-/

namespace Complexity

namespace TQBFHard

open Turing Codec LogProg

variable (N : FinNDTM Bool)

/-- The length `W(2s + 1) + wP n + 1` of a code word at input length `n` and radius `s`
(`Complexity.Codec.length_cfgWord`). -/
def codeLen (n s : ℕ) : ℕ := W N * (2 * s + 1) + wP n + 1

/-- The initial-code test on the first `L` bits of a block. -/
def blockInit (x : List Bool) (s L : ℕ) (β : List Bool) : Prop :=
  pairEncode x (pairEncode (β.take L) (Nat.bits s)) ∈ initLang N

/-- The accepting-code test on the first `L` bits of a block. -/
def blockAcc (x : List Bool) (s L : ℕ) (β : List Bool) : Prop :=
  pairEncode x (pairEncode (β.take L) (Nat.bits s)) ∈ acceptLang N

/-- **The one-step relation on blocks**: equal blocks, or blocks whose first `L` bits are a
step pair of the code (`Complexity.Codec.stepLang`). Reflexive by its first disjunct. -/
def blockStep (x : List Bool) (s L : ℕ) (β β' : List Bool) : Prop :=
  β = β' ∨ pairEncode x (pairEncode (β.take L) (pairEncode (β'.take L) (Nat.bits s))) ∈
    stepLang N

/-- With a reflexive one-step relation, a path can be lengthened. (Proved, by induction on
the excess, padding at the end.) -/
theorem steps_mono {w : ℕ} {E : List Bool → List Bool → Prop} (hE : ∀ B, E B B)
    {k k' : ℕ} (hk : k ≤ k') {A B : List Bool} (hB : B.length = w) (h : Steps w E k A B) :
    Steps w E k' A B := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  clear hk
  induction d with
  | zero => simpa using h
  | succ d ih => exact ⟨B, hB, ih, hE B⟩

/-- A block path is a path of code-word prefixes along step pairs. (Proved, by induction on
the path length.) -/
theorem steps_reflTransGen (x : List Bool) (s L w : ℕ) :
    ∀ (k : ℕ) (A B : List Bool), Steps w (blockStep N x s L) k A B →
      Relation.ReflTransGen (fun γ γ' : List Bool =>
        pairEncode x (pairEncode γ (pairEncode γ' (Nat.bits s))) ∈ stepLang N)
        (A.take L) (B.take L) := by
  intro k
  induction k with
  | zero => rintro A B rfl; exact Relation.ReflTransGen.refl
  | succ k ih =>
    rintro A B ⟨z, -, h1, h2 | h2⟩
    · subst h2; exact ih A z h1
    · exact (ih A z h1).tail h2

/-- A path of words along step pairs from the word of a code `u` reaches only words of codes,
along the code-level step relation `Complexity.Codec.StepRel`.

**Proof sketch.** Induction along the path. The empty path stays at the word of `u`, and
binary words are injective (`bits_injective`). A last step into the word of `c` is a step
pair `⟨x, ⟨γ, ⟨bits c, bits s⟩⟩⟩` of the step language; its nested pairs decode
(`pairEncode_inj`) to `γ = bits c₁` for a code `c₁` reached by induction, so the last step
is `StepRel N x s c₁ c`. -/
theorem reflTransGen_stepRel (x : List Bool) (s u : ℕ) {γ : List Bool}
    (h : Relation.ReflTransGen (fun γ γ' : List Bool =>
      pairEncode x (pairEncode γ (pairEncode γ' (Nat.bits s))) ∈ stepLang N) (Nat.bits u) γ) :
    ∀ c, γ = Nat.bits c → Relation.ReflTransGen (StepRel N x s) u c := by
  induction h with
  | refl =>
    intro c hc
    rw [bits_injective hc]
  | tail _ hst ih =>
    intro c hc
    subst hc
    obtain ⟨x', c₁, c₂, s', heq, -⟩ := id hst
    obtain ⟨rfl, h2⟩ := pairEncode_inj heq
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    obtain ⟨h5, h6⟩ := pairEncode_inj h4
    have hc₂ := bits_injective h5
    have hs := bits_injective h6
    subst hc₂ hs
    refine (ih c₁ h3).tail ?_
    rw [stepRel_iff_mem, ← h3]
    exact hst

/-- **Acceptance as a block path** ([AB09, Claim 4.4(1)] in the form of the proof of
Theorem 4.13): let `N` decide `L` in space `sp`, `s ≥ sp |x|`, blocks of width
`w ≥ codeLen |x| s`, and `configBound |x| s ≤ 2^w`. Then `x ∈ L` iff there are blocks `A`,
`B` of width `w`, `A` initial and `B` accepting (on their code-word prefixes), with
`Mid w (blockStep …) w A B`.

**Proof sketch.** `Complexity.TQBFHard.mid_iff_steps` turns `Mid` into a path of exactly `2^w`
steps. (⇒) The chain of codes of `Complexity.Codec.mem_iff_codeChain`, each padded to width
`w` (code words have length `codeLen`, `Complexity.Codec.length_cfgWord`), is a block path of
length `t ≤ configBound ≤ 2^w`, lengthened by reflexive steps (`steps_mono`). (⇐) The block
path is a path of code-word prefixes (`steps_reflTransGen`) from the initial code's word, and
every word along it is a code's word (`reflTransGen_stepRel`), ending at an accepting code;
conclude with `Complexity.Codec.mem_of_codePath`. -/
theorem mem_iff_mid {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s w : ℕ) (hs : sp x.length ≤ s) (hw : codeLen N x.length s ≤ w)
    (hR : N.configBound x.length s ≤ 2 ^ w) :
    x ∈ L ↔ ∃ A B : List Bool, A.length = w ∧ B.length = w ∧
      blockInit N x s (codeLen N x.length s) A ∧ blockAcc N x s (codeLen N x.length s) B ∧
      Mid w (blockStep N x s (codeLen N x.length s)) w A B := by
  set Lc := codeLen N x.length s with hLc
  have hrefl : ∀ B : List Bool, blockStep N x s Lc B B := fun B => Or.inl rfl
  constructor
  · intro hx
    obtain ⟨t, c, ht, hinit, hstep, hacc, -⟩ := (mem_iff_codeChain h x s hs).mp hx
    -- every code of the chain has a code word of length `Lc`
    have hlen : ∀ i ≤ t, (Nat.bits (c i)).length = Lc := by
      intro i hi
      rcases i with _ | i
      · rw [mem_initLang] at hinit
        rw [← hinit, bits_cfgCode, length_cfgWord, hLc, codeLen]
      · obtain ⟨-, -, -, C', -, -, hC'⟩ := (mem_stepLang N x _ _ s).mp (hstep i (by omega))
        rw [← hC', bits_cfgCode, length_cfgWord, hLc, codeLen]
    let β : ℕ → List Bool := fun i => Nat.bits (c i) ++ List.replicate (w - Lc) false
    have hβlen : ∀ i ≤ t, (β i).length = w := by
      intro i hi
      simp only [β, List.length_append, List.length_replicate, hlen i hi]
      omega
    have hβtake : ∀ i ≤ t, (β i).take Lc = Nat.bits (c i) := by
      intro i hi
      simp only [β]
      rw [List.take_append_of_le_length (by rw [hlen i hi]), List.take_of_length_le
        (by rw [hlen i hi])]
    have hpath : ∀ k ≤ t, Steps w (blockStep N x s Lc) k (β 0) (β k) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        refine ⟨β k, hβlen k (by omega), ih (by omega), Or.inr ?_⟩
        rw [hβtake k (by omega), hβtake (k + 1) hk]
        exact hstep k (by omega)
    refine ⟨β 0, β t, hβlen 0 (by omega), hβlen t le_rfl, ?_, ?_, ?_⟩
    · simp only [blockInit]
      rw [hβtake 0 (by omega)]
      exact hinit
    · simp only [blockAcc]
      rw [hβtake t le_rfl]
      exact hacc
    · rw [mid_iff_steps _ _ _ _ _ (hβlen 0 (by omega)) (hβlen t le_rfl)]
      exact steps_mono hrefl (ht.trans hR) (hβlen t le_rfl) (hpath t le_rfl)
  · rintro ⟨A, B, hA, hB, hinit, hacc, hmid⟩
    rw [mid_iff_steps _ _ _ _ _ hA hB] at hmid
    have hwords := steps_reflTransGen N x s Lc w _ A B hmid
    obtain ⟨x₁, u, s₁, h₁, hu⟩ := hinit
    obtain ⟨rfl, h₁'⟩ := pairEncode_inj h₁
    obtain ⟨hAu, hs₁⟩ := pairEncode_inj h₁'
    obtain rfl := bits_injective hs₁
    obtain ⟨x₂, v, s₂, h₂, hv⟩ := hacc
    obtain ⟨hx₂, h₂'⟩ := pairEncode_inj h₂
    obtain ⟨hBv, hs₂⟩ := pairEncode_inj h₂'
    obtain rfl := bits_injective hs₂
    subst hx₂
    rw [hAu] at hwords
    have hpath := reflTransGen_stepRel N x s u hwords v hBv
    refine mem_of_codePath h x s u v ((mem_initLang N x u s).mpr hu) hpath ?_
    exact (mem_acceptLang N x v s).mpr hv

end TQBFHard

end Complexity
```

## ===== TCSlib/Complexity/Randomized/BPLInP.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.BPLInPCount
import TCSlib.Complexity.Randomized.BPLInPWords
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `BPL ⊆ P`

[AB09, Exercise 7.9]: every language of `BPL` is decided in polynomial time. A log-space PTM
`N` has polynomially many configuration codes, and the table `Randomized.BPLInP.dpVal`
(`TCSlib.Complexity.Randomized.BPLInPCount`) computes `2^V · Pr[N(x) = 1]` exactly, in `V`
rounds over `V` codes, each entry a sum of entries of the previous round selected by the
step tests of the code languages. This file writes the table as a polynomial-time word
function — the rounds by `Complexity.BinArith.polyTimeComputable_iterate`, a round by the map
and zip loops of `Complexity.BinArith`, the step and accepting-code tests by `L ⊆ P` — and
accepts iff `2^V < 2 · dpVal`.

## Main definitions

* `Randomized.BPLInP.dpStep`, `Randomized.BPLInP.dpInit`, `Randomized.BPLInP.dpRun` — the
  rounds of the table on the state `⟨⟨x, ⟨bits s, codes⟩⟩, table⟩`.
* `Randomized.BPLInP.bplTest` — the polynomial-time test.

## Main results

* `Randomized.BPLInP.polyTimeComputable_bplTest` — the test is polynomial-time.
* `Randomized.BPLInP.bplTest_eq` — it compares `2^V` with `2 · dpVal` at the initial code.
* `Randomized.BPL_subset_P` — `BPL ⊆ P`. [AB09, Exercise 7.9]

## Divergences

* The window radius is `s = c · (|bits |x|| + 1)` rather than the space bound `c · logSpace |x|`
  itself (it is at least that, and computable in binary by a length count), and the table has
  `V = 8^e (|x| + 1)^e` rows, `e = codeK N · (c + 1)`, a polynomial bound on the number of codes
  `2 ^ (codeK N · (s + logSpace |x| + 1))`; rows beyond the codes stay unused.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.BPLInP

open Complexity Complexity.Codec Complexity.BinArith Turing
open Complexity.LogProg (bitsVal bitsVal_bits)

variable (N : FinNDTM Bool) (c B e : ℕ)

/-! ### The word functions -/

/-- The context `⟨x, ⟨bits s, codes⟩⟩` of the dynamic program. -/
def ctxW (x : List Bool) : List Bool := pairEncode x (pairEncode (radius c x) (codesW B e x))

/-- The coin-`b` step test on `⟨⟨x, ⟨r, a⟩⟩, ⟨a', _⟩⟩`: is `⟨x, ⟨a, ⟨a', r⟩⟩⟩` a step pair of
`fixCoin N b`? -/
noncomputable def stepTest (b : Bool) (z : List Bool) : Bool :=
  MultiTapeTM.indicator (stepLang (fixCoin N b) : Set (List Bool))
    (pairEncode (pairFstD (pairFstD z)) (pairEncode (pairSndD (pairSndD (pairFstD z)))
      (pairEncode (pairFstD (pairSndD z)) (pairFstD (pairSndD (pairFstD z))))))

/-- A summand of a table entry on `⟨⟨x, ⟨r, a⟩⟩, ⟨a', v⟩⟩`: `v` once per coin stepping `a` to
`a'`. -/
noncomputable def entryW (z : List Bool) : List Bool :=
  add (pairEncode (if stepTest N false z then pairSndD (pairSndD z) else [])
    (if stepTest N true z then pairSndD (pairSndD z) else []))

/-- The new table entry on `⟨⟨Q, table⟩, a⟩`, `Q = ⟨x, ⟨r, codes⟩⟩`: the sum of the summands
over the codes. -/
noncomputable def rowW (y : List Bool) : List Bool :=
  sumW (zipWithW (entryW N) (pairEncode
    (pairEncode (pairFstD (pairFstD (pairFstD y)))
      (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD y)))) (pairSndD y)))
    (pairEncode (pairSndD (pairSndD (pairFstD (pairFstD y)))) (pairSndD (pairFstD y)))))

/-- One round of the table on `⟨Q, table⟩`. -/
noncomputable def dpStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S) (mapW (rowW N) (pairEncode S (pairSndD (pairSndD (pairFstD S)))))

/-- The initial entry on `⟨Q, a⟩`: `1` iff `a` is an accepting code. -/
noncomputable def initEntry (y : List Bool) : List Bool :=
  if MultiTapeTM.indicator (acceptLang N : Set (List Bool)) (pairEncode (pairFstD (pairFstD y))
    (pairEncode (pairSndD y) (pairFstD (pairSndD (pairFstD y))))) then [true] else []

/-- The initial state `⟨Q, table₀⟩`. -/
noncomputable def dpInit (x : List Bool) : List Bool :=
  pairEncode (ctxW c B e x) (mapW (initEntry N) (pairEncode (ctxW c B e x) (codesW B e x)))

/-- The state after `V = B (|x| + 1)^e` rounds. -/
noncomputable def dpRun (x : List Bool) : List Bool :=
  (dpStep N)^[B * (x.length + 1) ^ e] (dpInit N c B e x)

/-- The entry on `⟨Q, ⟨a, v⟩⟩` kept by the final read: `v` iff `a` is the initial code. -/
noncomputable def pickW (z : List Bool) : List Bool :=
  if MultiTapeTM.indicator (initLang N : Set (List Bool)) (pairEncode (pairFstD (pairFstD z))
    (pairEncode (pairFstD (pairSndD z)) (pairFstD (pairSndD (pairFstD z))))) then
    pairSndD (pairSndD z) else []

/-- The final table entry at the initial code. -/
noncomputable def accW (x : List Bool) : List Bool :=
  sumW (zipWithW (pickW N) (pairEncode (pairFstD (dpRun N c B e x))
    (pairEncode (pairSndD (pairSndD (pairFstD (dpRun N c B e x)))) (pairSndD (dpRun N c B e x)))))

/-- **The test**: is `2^V < 2 · (the final entry at the initial code)`? -/
noncomputable def bplTest (x : List Bool) : Bool :=
  BinArith.lt (pairEncode (pow2W B e x) (false :: accW N c B e x))

/-! ### Polynomial time -/

/-- Composition in applied form (`Complexity.BinArith.polyTimeComputable_app`). -/
local notation "ptA" => Complexity.BinArith.polyTimeComputable_app

/-- A one-bit test of a function (`Complexity.BinArith.polyTimeComputable_test_app`). -/
local notation "ptT" => Complexity.BinArith.polyTimeComputable_test_app

/-- The step test is polynomial-time. -/
theorem polyTimeComputable_stepTest (b : Bool) :
    PolyTimeComputable (fun z => [stepTest N b z]) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hA := polyTimeComputable_indicator_of_LOGSPACE (stepLang_mem (N := fixCoin N b))
  unfold stepTest
  exact ptT hA
    ((ptA h1 h1).pairEncode ((ptA h2 (ptA h2 h1)).pairEncode
      ((ptA h1 h2).pairEncode (ptA h1 (ptA h2 h1)))))

/-- The round is polynomial-time. -/
theorem polyTimeComputable_dpStep : PolyTimeComputable (dpStep N) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hv : PolyTimeComputable (fun z : List Bool => pairSndD (pairSndD z)) := ptA h2 h2
  have hentry : PolyTimeComputable (entryW N) := by
    unfold entryW; exact ptA polyTimeComputable_add
      ((polyTimeComputable_ite (polyTimeComputable_stepTest N false) hv
        (polyTimeComputable_const [])).pairEncode
      (polyTimeComputable_ite (polyTimeComputable_stepTest N true) hv
        (polyTimeComputable_const [])))
  have hrow : PolyTimeComputable (rowW N) := by
    unfold rowW; exact ptA polyTimeComputable_sumW (ptA (polyTimeComputable_zipWithW hentry)
      (((ptA h1 (ptA h1 h1)).pairEncode ((ptA h1 (ptA h2 (ptA h1 h1))).pairEncode
        h2)).pairEncode ((ptA h2 (ptA h2 (ptA h1 h1))).pairEncode (ptA h2 h1))))
  unfold dpStep
  exact h1.pairEncode (ptA (polyTimeComputable_mapW hrow)
    (polyTimeComputable_id.pairEncode (ptA h2 (ptA h2 h1))))

/-- The initial state is polynomial-time. -/
theorem polyTimeComputable_dpInit : PolyTimeComputable (dpInit N c B e) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hctx : PolyTimeComputable (ctxW c B e) := by
    unfold ctxW; exact
    polyTimeComputable_id.pairEncode
      ((polyTimeComputable_radius c).pairEncode (polyTimeComputable_codesW B e))
  have hi : PolyTimeComputable (initEntry N) := by
    have hA := polyTimeComputable_indicator_of_LOGSPACE (acceptLang_mem (N := N))
    unfold initEntry; exact polyTimeComputable_ite (ptT hA
      ((ptA h1 h1).pairEncode (h2.pairEncode (ptA h1 (ptA h2 h1)))))
      (polyTimeComputable_const [true]) (polyTimeComputable_const [])
  unfold dpInit
  exact hctx.pairEncode (ptA (polyTimeComputable_mapW hi)
    (hctx.pairEncode (polyTimeComputable_codesW B e)))

/-- The final entry is polynomial-time, given the rounds. -/
theorem polyTimeComputable_bplTest_of_run (hrun : PolyTimeComputable (dpRun N c B e)) :
    PolyTimeComputable (fun x => [bplTest N c B e x]) := by
  have h1 := polyTimeComputable_pairFstD
  have h2 := polyTimeComputable_pairSndD
  have hpick : PolyTimeComputable (pickW N) := by
    have hA := polyTimeComputable_indicator_of_LOGSPACE (initLang_mem (N := N))
    unfold pickW; exact polyTimeComputable_ite (ptT hA
      ((ptA h1 h1).pairEncode ((ptA h1 h2).pairEncode (ptA h1 (ptA h2 h1)))))
      (ptA h2 h2) (polyTimeComputable_const [])
  have hacc : PolyTimeComputable (accW N c B e) := by
    unfold accW; exact ptA polyTimeComputable_sumW (ptA (polyTimeComputable_zipWithW hpick)
      ((ptA h1 hrun).pairEncode ((ptA h2 (ptA h2 (ptA h1 hrun))).pairEncode
        (ptA h2 hrun))))
  unfold bplTest
  exact ptT polyTimeComputable_lt
    ((polyTimeComputable_pow2W B e).pairEncode (ptA (polyTimeComputable_prepend [false]) hacc))

/-! ### What the word functions compute -/

section Semantics

variable {N} (x : List Bool)

/-- A list sum over `range V` is the `Finset` sum. -/
theorem sum_map_range (f : ℕ → ℕ) (V : ℕ) :
    ((List.range V).map f).sum = ∑ i ∈ Finset.range V, f i := by
  induction V with
  | zero => rfl
  | succ V ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- Mapping into binary words factors through the map of values. -/
theorem map_bits (f : ℕ → ℕ) (l : List ℕ) :
    l.map (fun a => Nat.bits (f a)) = (l.map f).map Nat.bits := by simp

/-- The context with radius `s` and `V` codes. -/
def ctxOf (s V : ℕ) : List Bool :=
  pairEncode x (pairEncode (Nat.bits s) (encWords ((List.range V).map Nat.bits)))

variable (N) in
/-- The table after `t` rounds, encoded. -/
noncomputable def vecW (s V t : ℕ) : List Bool :=
  encWords ((List.range V).map fun a => Nat.bits (dpVal N x s V t a))

/-- `ctxW` is the context of radius `c (|bits |x|| + 1)` and `B (|x| + 1)^e` codes. -/
theorem ctxW_eq : ctxW c B e x =
    ctxOf x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) := by
  rw [ctxW, codesW_eq, radius, ctxOf]

open Classical in
/-- A summand of an entry. -/
theorem entryW_eq (s a a' v : ℕ) :
    entryW N (pairEncode (pairEncode x (pairEncode (Nat.bits s) (Nat.bits a)))
      (pairEncode (Nat.bits a') (Nat.bits v))) =
      Nat.bits ((if StepRel (fixCoin N false) x s a a' then v else 0) +
        (if StepRel (fixCoin N true) x s a a' then v else 0)) := by
  simp only [entryW, stepTest, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator,
    stepRel_iff_mem]
  split_ifs <;> simp_all [add, bitsVal_bits, LogProg.bitsVal]

/-- The initial state is the context and the table after `0` rounds. -/
theorem dpInit_eq : dpInit N c B e x = pairEncode (ctxW c B e x)
    (vecW N x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) 0) := by
  classical
  rw [dpInit, codesW_eq, mapW_pairEncode, decWords_encWords, List.map_map, vecW]
  refine congrArg (pairEncode _) (congrArg encWords ?_)
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, initEntry, pairFstD_pairEncode, pairSndD_pairEncode, ctxW, radius,
    MultiTapeTM.indicator, dpVal]
  split_ifs <;> simp_all [Nat.one_bits]

/-- **A round computes the next table.** -/
theorem dpStep_eq (s V t : ℕ) :
    dpStep N (pairEncode (ctxOf x s V) (vecW N x s V t)) =
      pairEncode (ctxOf x s V) (vecW N x s V (t + 1)) := by
  classical
  simp only [dpStep, pairFstD_pairEncode, pairSndD_pairEncode, ctxOf]
  rw [mapW_pairEncode, decWords_encWords, List.map_map, vecW]
  refine congrArg (pairEncode _) (congrArg encWords ?_)
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, rowW, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [zipWithW_pairEncode, decWords_encWords, decWords_encWords, List.zipWith_map,
    List.zipWith_self]
  simp only [entryW_eq]
  rw [map_bits, sumW_encWords, sum_map_range, dpVal]

/-- The rounds of the table. -/
theorem iterate_dpStep (s V t : ℕ) :
    (dpStep N)^[t] (pairEncode (ctxOf x s V) (vecW N x s V 0)) =
      pairEncode (ctxOf x s V) (vecW N x s V t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, dpStep_eq]

/-- The state after `i` rounds. -/
theorem iterate_dpInit (i : ℕ) : (dpStep N)^[i] (dpInit N c B e x) = pairEncode (ctxW c B e x)
    (vecW N x (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e) i) := by
  rw [dpInit_eq, ctxW_eq, iterate_dpStep]

/-- **The test compares `2^V` with twice the table at the initial code.**

**Proof sketch.** After `V` rounds the state holds the table after `V` rounds
(`iterate_dpInit`); the final read keeps the entry whose code passes the initial-code test,
which is exactly the code of the initial configuration (`mem_initLang`, below `V` by
`cfgCode_lt`), and sums (`sumW_encWords`); `pow2W` has value `2^V` and prepending `0` doubles. -/
theorem bplTest_eq (hV : 2 ^ (codeK N * (c * ((Nat.bits x.length).length + 1) +
      logSpace x.length + 1)) ≤ B * (x.length + 1) ^ e) :
    bplTest N c B e x = decide (2 ^ (B * (x.length + 1) ^ e) < 2 * dpVal N x
      (c * ((Nat.bits x.length).length + 1)) (B * (x.length + 1) ^ e)
      (B * (x.length + 1) ^ e) (cfgCode (c * ((Nat.bits x.length).length + 1))
        (N.tm.initCfg x))) := by
  classical
  set s := c * ((Nat.bits x.length).length + 1) with hs_def
  set V := B * (x.length + 1) ^ e with hV_def
  have hacc : accW N c B e x = Nat.bits (dpVal N x s V V (cfgCode s (N.tm.initCfg x))) := by
    rw [accW, dpRun, iterate_dpInit, ctxW_eq, ← hs_def, ← hV_def]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, ctxOf, vecW]
    rw [zipWithW_pairEncode, decWords_encWords, decWords_encWords, List.zipWith_map,
      List.zipWith_self]
    have hpick : ∀ a, pickW N (pairEncode (pairEncode x (pairEncode (Nat.bits s)
        (encWords ((List.range V).map Nat.bits)))) (pairEncode (Nat.bits a)
          (Nat.bits (dpVal N x s V V a)))) = Nat.bits
          (if cfgCode s (N.tm.initCfg x) = a then dpVal N x s V V a else 0) := by
      intro a
      have hm := mem_initLang N x a s
      simp only [pickW, pairFstD_pairEncode, pairSndD_pairEncode, MultiTapeTM.indicator]
      by_cases h : cfgCode s (N.tm.initCfg x) = a
      · simp only [hm, h, ↓reduceIte]
      · simp only [hm, h, ↓reduceIte, Bool.false_eq_true, Nat.zero_bits]
    simp only [hpick]
    rw [map_bits, sumW_encWords, sum_map_range, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.mpr ((cfgCode_lt s _).trans_le hV))]
  rw [bplTest, BinArith.lt, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_pow2W, hacc]
  simp [LogProg.bitsVal, bitsVal_bits, s, V]

/-! ### Length bounds -/

/-- The encoded table after `t` rounds has length at most `V (2 (2Vt + 1) + 2)`. -/
theorem length_vecW_le (s V t : ℕ) :
    (vecW N x s V t).length ≤ V * (2 * (2 * V * t + 1) + 2) := by
  have := length_encWords_le ((List.range V).map fun a => Nat.bits (dpVal N x s V t a))
    (2 * V * t + 1) (by
      intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
      apply LogProg.length_bits_le
      calc dpVal N x s V t a ≤ (2 * V) ^ t := dpVal_le N x s V t a
        _ ≤ (2 ^ (2 * V)) ^ t := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le t
        _ = 2 ^ (2 * V * t) := by rw [← pow_mul]
        _ < 2 ^ (2 * V * t + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega))
  simpa [vecW] using this

/-- The context has length at most `2|x| + 2s + 4 + V (2V + 2)`. -/
theorem length_ctxOf_le (s V : ℕ) :
    (ctxOf x s V).length ≤ 2 * x.length + 2 * s + 4 + V * (2 * V + 2) := by
  have h1 := Turing.length_bits_le_self s
  have h2 := length_encWords_range_le V
  simp only [ctxOf, length_pairEncode]
  omega

end Semantics

/-- **The rounds run in polynomial time.**

**Proof sketch.** `Complexity.BinArith.polyTimeComputable_iterate` of the round from the
initial state. After `i ≤ V` rounds the state is the context and the table after `i` rounds
(`iterate_dpInit`); its entries are below `(2V)^i` (`dpVal_le`), so the state has length
`O((|x| + 1)(V + 1)^3)`, a polynomial since `V = B (|x| + 1)^e`. -/
theorem polyTimeComputable_dpRun : PolyTimeComputable (dpRun N c B e) := by
  refine polyTimeComputable_iterate (polyTimeComputable_dpStep N)
    (polyTimeComputable_dpInit N c B e) B e ((22 + 4 * c) * (B + 1) ^ 3) (3 * e + 1)
    fun x i hi => ?_
  rw [iterate_dpInit, ctxW_eq, length_pairEncode]
  set n := x.length
  set V := B * (n + 1) ^ e
  set s := c * ((Nat.bits n).length + 1)
  have h1 := length_ctxOf_le x s V
  have h2 := length_vecW_le (N := N) x s V i
  have hs : s ≤ c * (n + 1) :=
    Nat.mul_le_mul_left _ (by have := Turing.length_bits_le_self n; omega)
  set P := n + 1
  set W := V + 1
  have hP1 : 1 ≤ P := by omega
  have hW1 : 1 ≤ W := by omega
  have hW3 : 1 ≤ W ^ 3 := Nat.one_le_pow _ _ hW1
  have hPW : P ≤ P * W ^ 3 := Nat.le_mul_of_pos_right _ hW3
  have hWW : W ^ 3 ≤ P * W ^ 3 := Nat.le_mul_of_pos_left _ hP1
  have hW2 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hcP : c * P ≤ c * (P * W ^ 3) := Nat.mul_le_mul_left _ hPW
  have hvi : V * (2 * (2 * V * i + 1) + 2) ≤ 4 * W ^ 3 := by
    have : 2 * V * i ≤ 2 * V * V := Nat.mul_le_mul_left _ hi
    calc V * (2 * (2 * V * i + 1) + 2) ≤ V * (2 * (2 * V * V + 1) + 2) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 4 * W ^ 3 := by simp only [W]; ring_nf; nlinarith
  have hcod : V * (2 * V + 2) ≤ 2 * W ^ 2 := by simp only [W]; ring_nf; nlinarith
  have htot : 2 * (2 * n + 2 * s + 4 + V * (2 * V + 2)) + 2 + V * (2 * (2 * V * i + 1) + 2) ≤
      (22 + 4 * c) * (P * W ^ 3) := by
    have : n ≤ P := by omega
    nlinarith
  have hWB : W ≤ (B + 1) * P ^ e := by
    have : 1 ≤ P ^ e := Nat.one_le_pow _ _ hP1
    have hPe : P ^ e = (n + 1) ^ e := rfl
    simp only [W, V]; rw [hPe, add_mul, one_mul]; omega
  have hfin : P * W ^ 3 ≤ (B + 1) ^ 3 * P ^ (3 * e + 1) := by
    calc P * W ^ 3 ≤ P * ((B + 1) * P ^ e) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWB 3)
      _ = (B + 1) ^ 3 * P ^ (3 * e + 1) := by ring
  calc 2 * (ctxOf x s V).length + 2 + (vecW N x s V i).length
      ≤ (22 + 4 * c) * (P * W ^ 3) := by omega
    _ ≤ (22 + 4 * c) * ((B + 1) ^ 3 * P ^ (3 * e + 1)) := Nat.mul_le_mul_left _ hfin
    _ = (22 + 4 * c) * (B + 1) ^ 3 * (x.length + 1) ^ (3 * e + 1) := by ring

/-- **The test is polynomial-time.** -/
theorem polyTimeComputable_bplTest : PolyTimeComputable (fun x => [bplTest N c B e x]) :=
  polyTimeComputable_bplTest_of_run N c B e (polyTimeComputable_dpRun N c B e)

/-- The number of codes is polynomial: with `e = codeK N · (c + 1)`, the codes at radius
`c (|bits n| + 1)` are below `8^e (n + 1)^e`.

**Proof sketch.** With `m = |bits n|`: `logSpace n ≤ m + 1` (`Complexity.logSpace_le_size_succ`)
and `2^m ≤ 2(n + 1)` (`Complexity.LogProg.two_pow_bits_le`), so the exponent is at most
`e (m + 2)` and `2^{e(m+2)} = (4 · 2^m)^e ≤ (8(n + 1))^e`. -/
theorem two_pow_codes_le (n : ℕ) :
    2 ^ (codeK N * (c * ((Nat.bits n).length + 1) + logSpace n + 1)) ≤
      8 ^ (codeK N * (c + 1)) * (n + 1) ^ (codeK N * (c + 1)) := by
  set m := (Nat.bits n).length
  have hlog : logSpace n ≤ m + 1 := by
    have := logSpace_le_size_succ n
    rwa [← Nat.size_eq_bits_len] at this
  have hpow : 2 ^ m ≤ 2 * (n + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [m]
    · exact (Complexity.LogProg.two_pow_bits_le n hn).trans (by omega)
  set e := codeK N * (c + 1)
  calc 2 ^ (codeK N * (c * (m + 1) + logSpace n + 1)) ≤ 2 ^ (e * (m + 2)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        simp only [e, mul_assoc]
        refine Nat.mul_le_mul_left _ ?_
        nlinarith
    _ = (4 * 2 ^ m) ^ e := by rw [mul_comm, pow_mul]; ring
    _ ≤ (8 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
    _ = 8 ^ e * (n + 1) ^ e := mul_pow _ _ _

end Randomized.BPLInP

namespace Randomized

open Complexity Complexity.Codec Turing BPLInP

/-- **`BPL ⊆ P`.** [AB09, Exercise 7.9]

**Proof sketch.** Let `N` decide `L` with bounded error in space `c · logSpace`. At radius
`s = c (|bits |x|| + 1)` its configurations have codes below `V = 8^e (|x| + 1)^e`
(`two_pow_codes_le`), so it halts within `V` steps (`haltsWithin_of_codes`) and the table after
`V` rounds is `2^V · Pr[N(x) = 1]` at the initial code (`dpVal_init`). The test
`BPLInP.bplTest` computes exactly `2^V < 2 · dpVal` (`bplTest_eq`) in polynomial time
(`polyTimeComputable_bplTest`), and this holds iff `Pr[N(x) = 1] > 1/2`, i.e. iff `x ∈ L`: a
member is accepted with probability `≥ 2/3`, a non-member rejected with probability
`≥ 2/3`, so accepted with probability `≤ 1/3`. -/
theorem BPL_subset_P : BPL ⊆ P := by
  rintro L ⟨c, N, hUS, hdec⟩
  set e := codeK N * (c + 1)
  have key : ∀ x, bplTest N c (8 ^ e) e x = true ↔ x ∈ L := by
    intro x
    obtain ⟨T, hT, hp⟩ := hdec x
    set s := c * ((Nat.bits x.length).length + 1)
    set V := 8 ^ e * (x.length + 1) ^ e
    have hs : c * logSpace x.length ≤ s := by
      refine Nat.mul_le_mul_left _ ?_
      have := logSpace_le_size_succ x.length
      rwa [← Nat.size_eq_bits_len] at this
    have hV := two_pow_codes_le N c x.length
    have hHV : N.tm.HaltsWithin x V := haltsWithin_of_codes hUS hs hV hT
    have hdp := dpVal_init hUS hs hV hT
    have heq : N.outputProb x V [true] = N.outputProb x T [true] := by
      rw [← FinNDTM.outputProb_eq_of_haltsWithin hHV (le_max_left V T),
        FinNDTM.outputProb_eq_of_haltsWithin hT (le_max_right V T)]
    rw [heq] at hdp
    rw [bplTest_eq c (8 ^ e) e x hV, decide_eq_true_iff]
    set d := dpVal N x s V V (cfgCode s (N.tm.initCfg x))
    have h2V : (0 : ℚ) < 2 ^ V := by positivity
    have hiff : 2 ^ V < 2 * d ↔ (2 : ℚ) ^ V < 2 * ((2 : ℚ) ^ V * N.outputProb x T [true]) := by
      rw [← hdp]; exact_mod_cast Iff.rfl
    rw [hiff]
    classical
    by_cases hx : x ∈ L
    · simp only [MultiTapeTM.indicator, hx, if_true] at hp
      simp only [hx, iff_true]
      nlinarith
    · simp only [MultiTapeTM.indicator, hx, if_false] at hp
      simp only [hx, iff_false, not_lt]
      have hsum : N.outputProb x T [true] + N.outputProb x T [false] ≤ 1 := by
        unfold FinNDTM.outputProb
        rw [← randProb_or_disjoint _ _ fun r h => by
          have := h.1.symm.trans h.2
          simp at this]
        exact randProb_le_one
      nlinarith
  have hL : L = {x | bplTest N c (8 ^ e) e x = true} := Set.ext fun x => (key x).symm
  rw [hL]
  exact mem_P_of_test (polyTimeComputable_bplTest N c (8 ^ e) e)

end Randomized
```

## ===== TCSlib/Complexity/Randomized/BPLInPCount.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.Randomized.RandomBits
import Mathlib.Data.Fintype.Pigeonhole

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance probabilities of log-space PTMs by dynamic programming

The counting half of [AB09, Exercise 7.9] (`BPL ⊆ P`). Fix a PTM `N` using space `sp`, an
input `x` and a window radius `s ≥ sp(|x|)`, so that every configuration on every branch has a
code (`Complexity.Codec.cfgCode`) below `V ≥ 2 ^ (codeK N · (s + logSpace |x| + 1))`. The table
`dpVal t c` is computed from the code languages alone: `dpVal 0 c` is `1` on accepting codes
and `0` elsewhere, and `dpVal (t + 1) c` sums `dpVal t c'` over the codes `c' < V` that `c`
steps to under coin `0` and under coin `1`. On the code of a reachable configuration it is
`2^t` times the probability of acceptance within `t` further coins, and a halting log-space
PTM halts within `V` steps on every branch, so `dpVal V` at the initial code is `2^V` times the
acceptance probability.

## Main definitions

* `Randomized.BPLInP.fixCoin` — the PTM whose two transition functions are both `tr b`.
* `Randomized.BPLInP.dpVal` — the dynamic-programming table.

## Main results

* `Randomized.BPLInP.haltsWithin_of_codes` — a halting space-bounded PTM halts within the
  number of codes on every branch.
* `Randomized.BPLInP.dpVal_eq` — the table counts accepting coin words.
* `Randomized.BPLInP.dpVal_init` — at the initial code after `V` rounds it is
  `2^V · Pr[M(x) = 1]`.
* `Randomized.BPLInP.dpVal_le` — its entries are below `(2V)^t`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.BPLInP

open Complexity Complexity.Codec Turing
open Complexity.LogProg (bitsVal)

/-- The PTM `N` with the coin fixed to `b`: both transition functions are `N.tm.tr b`. Its
configuration-graph edges are the coin-`b` steps of `N`. It is definitionally
`(⟨N.k, N.State, N.tm.fixChoice b⟩ : FinTM Bool).toFinNDTM`. -/
def fixCoin (N : FinNDTM Bool) (b : Bool) : FinNDTM Bool where
  k := N.k
  State := N.State
  tm := ⟨N.tm.q₀, fun _ => N.tm.tr b⟩

/-- A step of `fixCoin N b` under any coin is a coin-`b` step of `N`. -/
theorem stepWith_fixCoin (N : FinNDTM Bool) (b b' : Bool) {x : List Bool}
    (C : Cfg (fixCoin N b).k Bool (fixCoin N b).State x) :
    (fixCoin N b).tm.stepWith b' C = N.tm.stepWith b C := by
  cases h : C.state <;> simp [NDTM.stepWith, h, fixCoin]

variable (N : FinNDTM Bool) (x : List Bool) (s V : ℕ)

open Classical in
/-- The dynamic-programming table over codes `c < V` at radius `s`: `dpVal 0 c` is `1` iff `c`
is an accepting code, and `dpVal (t + 1) c` sums `dpVal t c'` over the codes `c'` that `c` steps
to under coin `0` and under coin `1`. -/
noncomputable def dpVal : ℕ → ℕ → ℕ
  | 0, c => if pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N then 1 else 0
  | t + 1, c => ∑ c' ∈ Finset.range V,
      ((if StepRel (fixCoin N false) x s c c' then dpVal t c' else 0) +
        (if StepRel (fixCoin N true) x s c c' then dpVal t c' else 0))

open Classical in
/-- The entries of the table after `t` rounds are at most `(2V)^t`. -/
theorem dpVal_le (t c : ℕ) : dpVal N x s V t c ≤ (2 * V) ^ t := by
  induction t generalizing c with
  | zero => simp only [dpVal, pow_zero]; split_ifs <;> omega
  | succ t ih =>
    simp only [dpVal]
    calc ∑ c' ∈ Finset.range V, ((if StepRel (fixCoin N false) x s c c' then
            dpVal N x s V t c' else 0) + (if StepRel (fixCoin N true) x s c c' then
            dpVal N x s V t c' else 0))
        ≤ ∑ _c' ∈ Finset.range V, 2 * (2 * V) ^ t := by
          refine Finset.sum_le_sum fun c' _ => ?_
          have := ih c'
          split_ifs <;> omega
      _ = (2 * V) ^ (t + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

variable {N x s V}

/-- The configuration after the coin word `w`. -/
local notation "run" w => N.tm.runWith w (N.tm.initCfg x)

/-- Configurations reached on a branch of a space-`sp` PTM lie in the window of radius
`s ≥ sp(|x|)`. -/
theorem inWin_run {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s) (w : List Bool) :
    Cfg.InWindow s (run w) := by
  simpa using NDTM.runWith_take_inWindow N.tm w ((hN x w).trans hs) w.length

/-- From a reachable code, the coin-`b` step relation points exactly at the code of the
coin-`b` successor. -/
theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s) (v : List Bool)
    (b : Bool) (c' : ℕ) :
    StepRel (fixCoin N b) x s (cfgCode s (run v)) c' ↔ c' = cfgCode s (run (v ++ [b])) := by
  have hstep : (run (v ++ [b])) = N.tm.stepWith b (run v) := by
    rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
  constructor
  · intro h
    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ :=
      (mem_stepLang (fixCoin N b) x _ _ s).mp (stepRel_iff_mem.mp h)
    have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
      ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
    rw [← hcC', ← hb']
    change cfgCode s ((fixCoin N b).tm.stepWith b' C) = _
    rw [stepWith_fixCoin, hstep]
    exact congrArg bitsVal (cfgWord_congr (NDTM.coreSum_stepWith N.tm b hcore))
  · rintro rfl
    refine stepRel_iff_mem.mpr ((mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v,
      inWin_run hN hs v, rfl, run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩)
    change (fixCoin N b).tm.stepWith b (run v) = _
    rw [stepWith_fixCoin, hstep]

/-- A reachable code is accepting iff its configuration is halted with output `[true]`. -/
theorem acceptLang_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (v : List Bool) :
    pairEncode x (pairEncode (Nat.bits (cfgCode s (run v))) (Nat.bits s)) ∈ acceptLang N ↔
      (run v).state = none ∧ (run v).output = [true] := by
  rw [mem_acceptLang]
  constructor
  · rintro ⟨C, hC, hcC, hst, hout⟩
    have hcore := ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
    have h1 := congrArg (fun z => z.1.1) hcore
    have h2 := congrArg Prod.snd hcore
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at h1 h2
    rw [hout] at h2
    exact ⟨h1 ▸ hst, (outSummary_eq_accept_iff _).mp h2.symm⟩
  · rintro ⟨hst, hout⟩
    exact ⟨run v, inWin_run hN hs v, rfl, hst, hout⟩

/-- A probability over zero coins is the truth value of the event at the empty word. -/
theorem randProb_zero (A : List Bool → Prop) [DecidablePred A] :
    randProb 0 A = if A [] then 1 else 0 := by
  unfold randProb
  by_cases h : A [] <;> simp [h, Finset.filter_true_of_mem, Finset.filter_false_of_mem]

/-- **The table counts accepting coin words**: on the code of the configuration after `v`, the
table after `t` rounds is `2^t` times the probability that `t` further coins end halted with
output `[true]`.

**Proof sketch.** Induction on `t`. At `t = 0` the accepting-code test is the acceptance of the
configuration (`acceptLang_iff`). At `t + 1` the coin-`b` step relation from the code points
only at the code of the coin-`b` successor (`stepRel_iff`), which is below `V` (`cfgCode_lt`),
so the sum over `c' < V` collapses to the two successors; by induction and conditioning on
the first coin (`randProb_succ`) this is `2^{t+1}` times the probability. -/
theorem dpVal_eq {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) (t : ℕ) (v : List Bool) :
    (dpVal N x s V t (cfgCode s (run v)) : ℚ) = 2 ^ t * randProb t (fun u =>
      (run (v ++ u)).state = none ∧ (run (v ++ u)).output = [true]) := by
  classical
  induction t generalizing v with
  | zero =>
    rw [randProb_zero]
    simp only [List.append_nil, pow_zero, one_mul]
    by_cases h : (run v).state = none ∧ (run v).output = [true]
    · simp only [dpVal, if_pos h, if_pos ((acceptLang_iff hN hs v).mpr h), Nat.cast_one]
    · simp only [dpVal, if_neg h, if_neg (mt (acceptLang_iff hN hs v).mp h), Nat.cast_zero]
  | succ t ih =>
    have hcol : ∀ b : Bool, ∑ c' ∈ Finset.range V,
        (if StepRel (fixCoin N b) x s (cfgCode s (run v)) c' then dpVal N x s V t c' else 0) =
          dpVal N x s V t (cfgCode s (run (v ++ [b]))) := fun b => by
      rw [Finset.sum_eq_single (cfgCode s (run (v ++ [b])))]
      · rw [if_pos ((stepRel_iff hN hs v b _).mpr rfl)]
      · intro c' _ hne
        rw [if_neg fun h => hne ((stepRel_iff hN hs v b c').mp h)]
      · intro hnot
        exact absurd (Finset.mem_range.mpr ((cfgCode_lt s _).trans_le hV)) hnot
    simp only [dpVal]
    rw [Finset.sum_add_distrib, hcol, hcol, Nat.cast_add, ih, ih, randProb_succ]
    simp only [List.append_assoc, List.singleton_append]
    ring

/-- **A halting log-space PTM halts within the number of codes**: if every branch on `x` halts
within some `T`, every branch halts within `V` steps. [AB09, §4.1.1, Claim 4.4(1)]

**Proof sketch.** Suppose a branch `w` of length `V` has not halted. The `V + 1` configurations
after its prefixes have codes below `V`, so two prefixes `i < j` share a code, hence a vertex
(`Complexity.ExpBFS.coreSum_eq_of_code_eq`). Repeating the segment between them keeps the vertex
(`Turing.NDTM.coreSum_runWith`), so `w.take i` followed by `T` copies of the segment is a
branch of length at least `T` whose state is that of `w.take i`, not halted (else `w` would
have halted), contradicting halting within `T`. -/
theorem haltsWithin_of_codes {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) {T : ℕ}
    (hT : N.tm.HaltsWithin x T) : N.tm.HaltsWithin x V := by
  intro w hw
  by_contra hne
  let f : Fin (V + 1) → Fin V := fun j =>
    ⟨cfgCode s (run (w.take j)), (cfgCode_lt s _).trans_le hV⟩
  obtain ⟨i₀, j₀, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have key : ∀ i j : ℕ, i < j → j ≤ V →
      cfgCode s (run (w.take i)) = cfgCode s (run (w.take j)) → False := by
    intro i j hij hjV hcode
    set u := w.take i
    set v := (w.take j).drop i
    have huv : u ++ v = w.take j := by
      simp only [u, v]
      conv_rhs => rw [← List.take_append_drop i (w.take j)]
      rw [List.take_take, min_eq_left hij.le]
    have hvlen : v.length = j - i := by simp [v, hw]; omega
    have hcore : NDTM.coreSum (run (u ++ v)) = NDTM.coreSum (run u) := by
      rw [huv]
      exact (ExpBFS.coreSum_eq_of_code_eq (inWin_run hN hs _) (inWin_run hN hs _) hcode).symm
    have pump : ∀ m : ℕ, NDTM.coreSum (run (u ++ (List.replicate m v).flatten)) =
        NDTM.coreSum (run u) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.replicate_succ', List.flatten_append, List.flatten_singleton,
          ← List.append_assoc, NDTM.runWith_append, NDTM.coreSum_runWith N.tm v ih,
          ← NDTM.runWith_append, hcore]
    have hu : (run u).state ≠ none := by
      intro hu
      apply hne
      rw [← List.take_append_drop i w, NDTM.runWith_append, NDTM.runWith_of_halt _ hu]
      exact hu
    have hlen : T ≤ (u ++ (List.replicate T v).flatten).length := by
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul, hvlen]
      have : T ≤ T * (j - i) := Nat.le_mul_of_pos_right T (by omega)
      omega
    have hstate := congrArg (fun z => z.1.1) (pump T)
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at hstate
    exact hu (hstate ▸ (hT.mono hlen) _ rfl)
  have hval : cfgCode s (run (w.take i₀)) = cfgCode s (run (w.take j₀)) :=
    congrArg Fin.val hf
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i₀ j₀ h (Nat.lt_succ_iff.mp j₀.isLt) hval
  · exact key j₀ i₀ h (Nat.lt_succ_iff.mp i₀.isLt) hval.symm

/-- **The table computes the acceptance probability**: if every branch on `x` halts within some
`T`, then after `V` rounds the table at the initial code is `2^V · Pr[M(x) = 1]` over `V`
coins. -/
theorem dpVal_init {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) {T : ℕ}
    (hT : N.tm.HaltsWithin x T) :
    (dpVal N x s V V (cfgCode s (N.tm.initCfg x)) : ℚ) = 2 ^ V * N.outputProb x V [true] := by
  have h := dpVal_eq hN hs hV V []
  simp only [NDTM.runWith_nil, List.nil_append] at h
  rw [h, FinNDTM.outputProb]
  congr 1
  refine randProb_congr fun r => ?_
  have hhalt := haltsWithin_of_codes hN hs hV hT _ (List.length_ofFn (f := r))
  simp only [FinNDTM.outputWith, hhalt, true_and]

end Randomized.BPLInP
```

## ===== TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Search
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space in exponential time, by breadth-first search

The search machine `Complexity.LogProg.ExpBFS.A`, run with the deciders of the code languages
of a nondeterministic decider `N` (`TCSlib.Complexity.SpaceComplexity.Codec`), decides `N`'s
language: at each radius `s = 0, 1, …` it counts the reachable codes at radii `s` and `s + 1`
by breadth-first search, and at the first radius where the counts agree it answers whether a
reachable code at radius `s` is accepting (`Complexity.ExpBFS.mem_iff_of_card_eq`); this
happens by the space bound (`Complexity.ExpBFS.card_rset_succ_of_le`). Its registers hold
numbers below `2 ^ O(S)` and its memory head stays below `2 ^ O(S)`, so by
`Complexity.LogProg.marm_dtime` the language is decided in time `2 ^ O(S)`
[AB09, §4.1.1, Theorem 4.2, third inclusion]. The space bound need not be computed: only
`logSpace ≤ S` is used.

## Main definitions

* `Complexity.LogProg.ExpBFS.decs`, `Complexity.LogProg.ExpBFS.orcN` — the four deciders.

## Main results

* `Complexity.LogProg.ExpBFS.fscan_run` — the final scan.
* `Complexity.LogProg.ExpBFS.iter_run` — the iteration over the radii answers membership.
* `Complexity.NSPACE_subset_exp_dtime_of_le` — `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))`
  whenever `logSpace ≤ S`. [AB09, Theorem 4.2, third inclusion]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

namespace ExpBFS

open Turing

/-! ## The deciders -/

/-- The deciders of the search machine for `N`: `0` the input length, `1` the initial codes,
`2` the step pairs, `3` the accepting codes. -/
def decs (N : FinNDTM Bool) : Fin 4 → Language Bool :=
  ![inputLenLang, Codec.initLang N, Codec.stepLang N, Codec.acceptLang N]

/-- The answers of the deciders of the search machine for `N`. -/
noncomputable def orcN (N : FinNDTM Bool) : Fin 4 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs N j : Set (List Bool)) V

variable {N : FinNDTM Bool} {x : List Bool}

/-- Decider `0` answers the input length queries. -/
lemma orcN_len (N : FinNDTM Bool) (x : List Bool) :
    ∀ k ≤ x.length, orcN N 0 (pairEncode x (Nat.bits k)) = decide (k < x.length) := by
  intro k _
  simp only [orcN, decs, Matrix.cons_val_zero]
  exact indicator_inputLenLang x k

/-- Decider `1` answers whether a code is the initial code. -/
lemma ini_orcN (r u : ℕ) :
    ini (orcN N) x r u = true ↔ Codec.cfgCode r (N.tm.initCfg x) = u := by
  rw [← Codec.mem_initLang]
  simp [ini, orcN, decs, indicator_eq_decide]

/-- Decider `2` answers the step relation. -/
lemma stp_orcN (r u v : ℕ) : stp (orcN N) x r u v = true ↔ Codec.StepRel N x r u v := by
  simp [stp, orcN, decs, indicator_eq_decide, Codec.stepRel_iff_mem]

/-- Decider `3` answers whether a code is accepting. -/
lemma acc_orcN (r u : ℕ) :
    orcN N 3 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits r))) = true ↔
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits r)) ∈ Codec.acceptLang N := by
  simp [orcN, decs, indicator_eq_decide]

/-- **The codes reachable below `K` are the reachable codes**, once `K` bounds the codes.

**Proof sketch.** `→`: a search path from the initial code is a path of the step relation
(`stp_orcN`), so its end is reachable (`ExpBFS.rcode_iff_reflTransGen`). `←`: induct on a
reachability path; each code on it is reachable, so it is below `K` (`ExpBFS.rcode_lt` and `hK`),
and each step is a search step (`stp_orcN`). -/
lemma cl_iff {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1)) ≤ K) (v : ℕ) :
    Cl (orcN N) x r K v ↔ ExpBFS.RCode N x r v := by
  constructor
  · rintro ⟨u, -, hi, hpath⟩
    rw [ini_orcN] at hi
    subst hi
    exact ExpBFS.rcode_iff_reflTransGen.mpr (hpath.mono fun a b h => (stp_orcN r a b).mp h.1)
  · intro h
    refine ⟨_, (Codec.cfgCode_lt r _).trans_le hK, (ini_orcN r _).mpr rfl, ?_⟩
    have key : ∀ w, ExpBFS.RCode N x r w → Relation.ReflTransGen
        (fun a b => stp (orcN N) x r a b = true ∧ b < K)
        (Codec.cfgCode r (N.tm.initCfg x)) w := by
      intro w hw
      rw [ExpBFS.rcode_iff_reflTransGen] at hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
        exact ih.tail ⟨(stp_orcN r b c).mpr hbc,
          (ExpBFS.rcode_lt (ExpBFS.rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK⟩
    exact key v h

open Classical in
/-- The count of a search is the number of reachable codes. -/
lemma card_cl {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1)) ≤ K) :
    ((Finset.range K).filter (Cl (orcN N) x r K)).card = (ExpBFS.rset N x r).card := by
  classical
  rw [← ExpBFS.card_filter_rcode hK]
  exact congrArg Finset.card (Finset.filter_congr fun v _ => cl_iff hK v)

/-! ## The final scan -/

variable {K₀ : ℕ} {orc : Fin 4 → List Bool → Bool} {B P : ℕ}

open Classical in
/-- **The final scan**: from `fU` with `U = u₀`, the machine answers whether some marked code
`u₀ ≤ v < K` is accepting (decider `3` at radius `s`).

**Proof sketch.** Induction on `K - U`: read the mark of `U` (`ac_run`); if marked, ask the
accepting-code decider and accept on a yes; increment `U`; reject at `U = K`. -/
theorem fscan_run : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.U = j → S.U ≤ S.K →
    S.T = 0 → S.T2 = 0 → S.Z = 0 → SBd B P S →
    MHalt (A K₀) orc x (G x B P) (cf .fU S M 0)
      (decide (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true)) := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hUK hT hT2 hZ hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hU : S.U = S.K
  · have hno : ¬ ∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true := by
      rintro ⟨v, h1, h2, -⟩; omega
    rw [decide_eq_false hno]
    refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hU, ↓reduceIte]
    exact MHalt.ret rfl (g_of hbd ⟨le_rfl, by omega⟩ _)
  · have hlt : S.U < S.K := by omega
    have hsplit : (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) ↔
        (M (cell S.Bs S.U) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true) ∨
        ∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true := by
      constructor
      · rintro ⟨v, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact Or.inl ⟨h3, h4⟩
        · exact Or.inr ⟨v, e, h2, h3, h4⟩
      · rintro (⟨h3, h4⟩ | ⟨v, h1, h2, h3, h4⟩)
        · exact ⟨S.U, le_rfl, hlt, h3, h4⟩
        · exact ⟨v, by omega, h2, h3, h4⟩
    have hbd1 : St.Bd B { S with U := S.U + 1 } := by simp only [St.Bd] at hbd ⊢; omega
    have rest := ih (S.K - (S.U + 1)) (by omega) { S with U := S.U + 1 } M rfl
      (by simp only; omega) hT hT2 hZ ⟨hbd1, hB1, hP1, hK1⟩
    simp only at rest
    -- the next code
    have next : MHalt (A K₀) orc x (G x B P) (cf .fN S M 0)
        (decide (∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true)) := by
      refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs
      exact rest
    refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs; rw [if_neg hU]
    have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) .fU S M hbd hT
      hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
    simp only [Site.set, Site.idx, St.toV_U, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      acExit] at hac
    refine hac.halt ?_
    -- skipping the code `U`
    have hskip : ¬ (M (cell S.Bs S.U) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true) →
        decide (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) =
        decide (∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) := by
      intro hno
      exact decide_eq_decide.mpr (hsplit.trans (or_iff_right hno))
    by_cases hb : M (cell S.Bs S.U) = true
    · simp only [hb, ↓reduceIte]
      refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep, vword_whole₂]; regs
      by_cases ha : orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true
      · simp only [ha, ↓reduceIte]
        rw [decide_eq_true ⟨S.U, le_rfl, hlt, hb, ha⟩]
        exact MHalt.ret rfl (g_of hbd ⟨le_rfl, by omega⟩ _)
      · rw [hskip (fun h => ha h.2)]
        rw [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact next
    · rw [hskip (fun h => hb h.1)]
      rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact next

/-! ## The iteration over the radii -/

/-- The code bound at radius `s` on inputs of length `n`. -/
def kb (N : FinNDTM Bool) (n s : ℕ) : ℕ := 2 ^ (Codec.codeK N * (s + lgv n + 1))

/-- The code width factor is at least `2`. -/
lemma two_le_codeK (N : FinNDTM Bool) : 2 ≤ Codec.codeK N := by
  simp only [Codec.codeK]; omega

/-- The code bound at the next radius is at least four times larger. -/
lemma four_mul_kb_le (N : FinNDTM Bool) (n s : ℕ) : 4 * kb N n s ≤ kb N n (s + 1) := by
  have h2 := two_le_codeK N
  have e : Codec.codeK N * (s + 1 + lgv n + 1) =
      Codec.codeK N * (s + lgv n + 1) + Codec.codeK N := by ring
  simp only [kb, e, pow_add]
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Codec.codeK N := Nat.pow_le_pow_right (by norm_num) h2)

/-- The code bound grows with the radius. -/
lemma kb_mono (N : FinNDTM Bool) (n : ℕ) {s s' : ℕ} (h : s ≤ s') : kb N n s ≤ kb N n s' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))

/-- The code bound bounds the codes. -/
lemma code_bound_le (N : FinNDTM Bool) (n s : ℕ) :
    2 ^ (Codec.codeK N * (s + logSpace n + 1)) ≤ kb N n s :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by have := logSpace_le_lgv n; omega))

/-- The register bound of the machine on inputs of length `n` with space bound `t`. -/
def bigB (N : FinNDTM Bool) (n t : ℕ) : ℕ := 3 * kb N n (t + 1) + n + 3

/-- A count of codes below `K` is at most `K`. -/
lemma card_filter_range_le (K : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range K).filter p).card ≤ K :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The radius and the width are below the code bound. -/
lemma lt_kb (N : FinNDTM Bool) (n s : ℕ) :
    Codec.codeK N * (s + lgv n + 1) < kb N n s := Nat.lt_two_pow_self

/-- The register file at the start of an iteration at radius `s`. -/
def st1 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1 }

/-- The register file after copying the radius into `s1`. -/
def st2 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s }

/-- The register file at the start of the second search. -/
def st3 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s + 1 }

/-- The register file at the start of the final scan. -/
def st5 (n s c1 : ℕ) : St :=
  { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s + 1, c := c1 }

open Classical in
/-- **The iteration over the radii.** On input `x`, for a decider `N` of `L` in space `sp`,
from the first width computation at radius `s ≤ sp |x|`, with the memory marked only below
`2 K_s`, the machine answers `x ∈ L`.

**Proof sketch.** Strong induction on `sp |x| - s`. Two searches (`wk_run`, `search_run`)
count the reachable codes at radii `s` and `s + 1` (`card_cl`) in fresh regions
`[2K_s, 3K_s)` and `[K_{s+1}, 2K_{s+1})` (`four_mul_kb_le`). If the counts agree, the final
scan (`fscan_run`) over the first search's marks answers membership
(`Complexity.ExpBFS.mem_iff_of_card_eq`); otherwise `s < sp |x|`
(`Complexity.ExpBFS.card_rset_succ_of_le`) and the iteration continues at `s + 1`. -/
theorem iter_run {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp) :
    ∀ (d s : ℕ) (M : ℤ → Bool), sp x.length - s = d → s ≤ sp x.length →
      (∀ z, M z = true → z < ((2 * kb N x.length s : ℕ) : ℤ)) →
      MHalt (A (Codec.codeK N)) (orcN N) x
        (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
        (cf (.cp (.radX .fst) 0) { St.zero with Lg := lgv x.length, s := s } M 0)
        (MultiTapeTM.indicator (L : Set (List Bool)) x) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro s M hd hs hM
  have hK02 : 2 ≤ Codec.codeK N := two_le_codeK N
  have hK0 : 0 < Codec.codeK N := by omega
  have h4 : 4 * kb N x.length s ≤ kb N x.length (s + 1) := four_mul_kb_le N x.length s
  have hmax : kb N x.length (s + 1) ≤ kb N x.length (sp x.length + 1) :=
    kb_mono N x.length (by omega)
  have hlg : lgv x.length ≤ x.length + 1 := lgv_le_succ x.length
  have hwK : Codec.codeK N * (s + lgv x.length + 1) < kb N x.length s := lt_kb N x.length s
  have hw1K : Codec.codeK N * (s + 1 + lgv x.length + 1) < kb N x.length (s + 1) :=
    lt_kb N x.length (s + 1)
  have hsw : s + 1 ≤ Codec.codeK N * (s + 1 + lgv x.length + 1) := by nlinarith
  have hk0 : kb N x.length s = 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) := rfl
  have hk1 : kb N x.length (s + 1) = 2 ^ (Codec.codeK N * (s + 1 + lgv x.length + 1)) := rfl
  have hB : bigB N x.length (sp x.length) =
      3 * kb N x.length (sp x.length + 1) + x.length + 3 := rfl
  have hp0 : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ ((3 * kb N x.length (sp x.length + 1) : ℕ) : ℤ) :=
    ⟨le_rfl, Nat.cast_nonneg _⟩
  -- the first width computation, at radius `s`
  have hbd0 : St.Bd (bigB N x.length (sp x.length)) { St.zero with Lg := lgv x.length, s := s } :=
    by simp only [St.Bd, St.zero]; omega
  have hw1 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.cp (.radX .fst) 0) { St.zero with Lg := lgv x.length, s := s } M 0)
      (cf (.iU false) (wkSt (K₀ := Codec.codeK N) .fst
        { St.zero with Lg := lgv x.length, s := s } s) M 0) :=
    wk_run .fst _ M rfl rfl rfl rfl rfl rfl hK0 hbd0 (by
      show 3 * 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) ≤ _
      omega)
  set S1 := wkSt (K₀ := Codec.codeK N) .fst { St.zero with Lg := lgv x.length, s := s } s
    with hS1
  have hS1K : S1.K = kb N x.length s := rfl
  have hS1B : S1.Bs = 2 * kb N x.length s := by simp [hS1, wkSt, hk0]
  have hS1Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S1 :=
    ⟨by simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega, by omega, by omega, by omega⟩
  -- the first search
  obtain ⟨M1, hr1, hm1, ho1, hiff1⟩ := search_run (orc := orcN N) (x := x)
    (B := bigB N x.length (sp x.length)) (P := 3 * kb N x.length (sp x.length + 1))
    (K₀ := Codec.codeK N) false S1 M rfl rfl rfl rfl rfl rfl rfl hS1Bd (fun v hv => by
      cases h : M (cell S1.Bs v)
      · rfl
      · have := hM _ h
        rw [hS1B] at this
        simp only [cell] at this
        push_cast at this
        omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hr1
  have hrr1 : rr S1 false = s := rfl
  rw [hrr1] at hr1 hiff1
  set c1 := ((Finset.range S1.K).filter (Cl (orcN N) x s S1.K)).card with hc1
  have hc1le : c1 ≤ kb N x.length s := card_filter_range_le _ _
  have hc1eq : c1 = (ExpBFS.rset N x s).card := card_cl (code_bound_le N x.length s)
  -- clearing, `c1 := c`, `s1 := s + 1`
  have hbdA : St.Bd (bigB N x.length (sp x.length)) { S1 with U := S1.K, c := c1 } := by
    simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega
  have hd1 := d1_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M1 hbdA
  have hbdB : St.Bd (bigB N x.length (sp x.length))
      { { S1 with U := S1.K, c := c1 } with U := 0, V := 0, w := 0, K := 0, Bs := 0 } := by
    simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega
  have hmv := mv_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M1 0 hp0 hbdB
    (by simp [hS1, wkSt, St.zero]; omega)
  have hbdC : St.Bd (bigB N x.length (sp x.length)) (st1 x.length s c1) := by
    simp only [St.Bd, St.zero, st1]; omega
  have hcp := cp_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) .s1
    (st1 x.length s c1) M1 0 hp0 hbdC rfl
    (by simp only [cpDst, cpSrc]; regs; simp [St.zero, st1]; omega)
  simp only [cpDst, cpSrc, cpExit] at hcp
  regs at hcp
  have hbdD : St.Bd (bigB N x.length (sp x.length)) (st2 x.length s c1) := by
    simp only [St.Bd, St.zero, st2]; omega
  have hA2 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.d1 0) { S1 with U := S1.K, c := c1 } M1 0)
      (cf (.cp (.radX .snd) 0) (st3 x.length s c1) M1 0) := by
    refine hd1.trans ?_
    refine (reach_cf hmv (st' := st1 x.length s c1)
      (by ext <;> simp [hS1, wkSt, St.zero, st1]) rfl).trans ?_
    refine (reach_cf hcp (st' := st2 x.length s c1) (by ext <;> simp [St.zero, st1, st2])
      rfl).trans ?_
    refine inc_step (r := rs1) (l' := .cp (.radX .snd) 0) rfl hbdD hp0 ?_
    regs
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp [St.zero, st2, st3]
  -- the second width computation, at radius `s + 1`
  have hbd3 : St.Bd (bigB N x.length (sp x.length)) (st3 x.length s c1) := by
    simp only [St.Bd, St.zero, st3]; omega
  have hw2 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.cp (.radX .snd) 0) (st3 x.length s c1) M1 0)
      (cf (.iU true) (wkSt (K₀ := Codec.codeK N) .snd (st3 x.length s c1) (s + 1)) M1 0) :=
    wk_run .snd _ M1 rfl rfl rfl rfl rfl rfl hK0 hbd3 (by
      show 3 * 2 ^ (Codec.codeK N * (s + 1 + lgv x.length + 1)) ≤ _
      omega)
  set S4 := wkSt (K₀ := Codec.codeK N) .snd (st3 x.length s c1) (s + 1) with hS4
  have hS4K : S4.K = kb N x.length (s + 1) := rfl
  have hS4B : S4.Bs = kb N x.length (s + 1) := by simp [hS4, wkSt, hk1, st3]
  have hS4Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S4 :=
    ⟨by simp only [St.Bd, hS4, wkSt, St.zero, st3]; simp; omega, by omega, by omega, by omega⟩
  -- the marks after the first search lie below `3 K_s`
  have hM1 : ∀ z, M1 z = true → z < ((3 * kb N x.length s : ℕ) : ℤ) := by
    intro z hz
    by_cases hin : ∃ v, v < S1.K ∧ z = cell S1.Bs v
    · obtain ⟨v, hv, rfl⟩ := hin
      rw [hS1B]; rw [hS1K] at hv
      simp only [cell]; push_cast; omega
    · push_neg at hin
      rw [ho1 z (fun v hv e => hin v hv e)] at hz
      have := hM z hz
      push_cast at this ⊢; omega
  -- the second search
  obtain ⟨M2, hr2, hm2, ho2, hiff2⟩ := search_run (orc := orcN N) (x := x)
    (B := bigB N x.length (sp x.length)) (P := 3 * kb N x.length (sp x.length + 1))
    (K₀ := Codec.codeK N) true S4 M1 rfl rfl rfl rfl rfl rfl rfl hS4Bd (fun v hv => by
      cases h : M1 (cell S4.Bs v)
      · rfl
      · have := hM1 _ h
        rw [hS4B] at this
        simp only [cell] at this
        push_cast at this
        omega)
  simp only [↓reduceIte] at hr2
  have hrr2 : rr S4 true = s + 1 := rfl
  rw [hrr2] at hr2 hiff2
  set c2 := ((Finset.range S4.K).filter (Cl (orcN N) x (s + 1) S4.K)).card with hc2
  have hc2le : c2 ≤ kb N x.length (s + 1) := card_filter_range_le _ _
  have hc2eq : c2 = (ExpBFS.rset N x (s + 1)).card := card_cl (code_bound_le N x.length (s + 1))
  -- the comparison
  have hbdE : St.Bd (bigB N x.length (sp x.length)) { S4 with U := S4.K, c := c2 } := by
    simp only [St.Bd, hS4, wkSt, St.zero, st3]; simp; omega
  refine (((hw1.trans hr1).trans hA2).trans (hw2.trans hr2)).halt ?_
  refine stepH_of rfl hbdE hp0 ?_
  simp only [astep]; regs
  have hc1' : ({ S4 with U := S4.K, c := c2 } : St).c1 = c1 := rfl
  have hS4c1 : S4.c1 = c1 := rfl
  by_cases heq : c2 = c1
  · -- equal counts: the final scan
    simp only [hS4c1, heq, ↓reduceIte]
    have hcard : (ExpBFS.rset N x s).card = (ExpBFS.rset N x (s + 1)).card := by
      rw [← hc1eq, ← hc2eq, heq]
    have hfz := fz_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M2
      (by rw [heq] at hbdE; exact hbdE)
    have hbd5 : St.Bd (bigB N x.length (sp x.length)) (st5 x.length s c1) := by
      simp only [St.Bd, St.zero, st5]; omega
    have hw3 : MReach (A (Codec.codeK N)) (orcN N) x
        (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
        (cf (.cp (.radX .fin) 0) (st5 x.length s c1) M2 0)
        (cf .fU (wkSt (K₀ := Codec.codeK N) .fin (st5 x.length s c1) s) M2 0) :=
      wk_run .fin _ M2 rfl rfl rfl rfl rfl rfl hK0 hbd5 (by
        show 3 * 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) ≤ _
        omega)
    set S6 := wkSt (K₀ := Codec.codeK N) .fin (st5 x.length s c1) s with hS6
    have hS6B : S6.Bs = 2 * kb N x.length s := by simp [hS6, wkSt, hk0, st5]
    have hS6K : S6.K = kb N x.length s := rfl
    have hS6Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S6 :=
      ⟨by simp only [St.Bd, hS6, wkSt, St.zero, st5]; simp; omega, by omega, by omega, by omega⟩
    have hscan := fscan_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) (S6.K - S6.U) S6 M2 rfl
      (by simp [hS6, wkSt, St.zero, st5]) rfl rfl rfl hS6Bd
    refine (((reach_cf hfz (st' := st5 x.length s c1)
      (by ext <;> simp [hS4, wkSt, St.zero, st3, st5]) rfl).trans
      hw3).halt ?_)
    convert hscan using 1
    -- the answer
    rw [indicator_eq_decide]
    apply decide_eq_decide.mpr
    rw [ExpBFS.mem_iff_of_card_eq hN hcard]
    have hS6U : S6.U = 0 := rfl
    have hS6K : S6.K = kb N x.length s := rfl
    have hS6s : S6.s = s := rfl
    rw [hS6U, hS6K, hS6s, hS6B]
    constructor
    · rintro ⟨u, hu, hacc⟩
      have hlt : u < kb N x.length s :=
        (ExpBFS.rcode_lt hu).trans_le (code_bound_le N x.length s)
      refine ⟨u, Nat.zero_le _, hlt, ?_, (acc_orcN s u).mpr hacc⟩
      have hout : M2 (cell (2 * kb N x.length s) u) = M1 (cell (2 * kb N x.length s) u) := by
        apply ho2
        intro v hv e
        rw [hS4B] at e
        simp only [cell] at e
        rw [hS4K] at hv
        omega
      rw [hout, ← hS1B]
      exact (hiff1 u (by rw [hS1K]; exact hlt)).mpr ((cl_iff (code_bound_le N x.length s) u).mpr hu)
    · rintro ⟨u, -, hlt, hmark, hacc⟩
      have hout : M2 (cell (2 * kb N x.length s) u) = M1 (cell (2 * kb N x.length s) u) := by
        apply ho2
        intro v hv e
        rw [hS4B] at e
        simp only [cell] at e
        rw [hS4K] at hv
        omega
      rw [hout, ← hS1B] at hmark
      refine ⟨u, (cl_iff (code_bound_le N x.length s) u).mp
        ((hiff1 u (by rw [hS1K]; exact hlt)).mp hmark), (acc_orcN s u).mp hacc⟩
  · -- different counts: the next radius
    simp only [hS4c1, heq, ↓reduceIte]
    have hslt : s < sp x.length := by
      by_contra hge
      exact heq (by rw [hc1eq, hc2eq]; exact (ExpBFS.card_rset_succ_of_le hN (by omega)).symm)
    have hnz := nz_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M2 hbdE
      (by simp [hS4, wkSt, St.zero, st3]; omega)
    refine (reach_cf hnz (st' := { St.zero with Lg := lgv x.length, s := s + 1 })
      (by ext <;> simp [hS4, wkSt, St.zero, st3]) rfl).halt ?_
    refine ih (sp x.length - (s + 1)) (by omega) (s + 1) M2 rfl (by omega) ?_
    intro z hz
    by_cases hin : ∃ v, v < S4.K ∧ z = cell S4.Bs v
    · obtain ⟨v, hv, rfl⟩ := hin
      rw [hS4B]; rw [hS4K] at hv
      simp only [cell]; push_cast; omega
    · push_neg at hin
      rw [ho2 z (fun v hv e => hin v hv e)] at hz
      have := hM1 z hz
      push_cast at this ⊢; omega

end ExpBFS

end Complexity.LogProg

namespace Complexity

open Turing LogProg LogProg.ExpBFS

/-- The time bound of the search machine in exponential form: with
`E = codeK N (t + 1 + lgv n + 1)` the exponent of the largest code bound, the bound
`2 ^ (C (W + logSpace n + 1)) (P + 1)²` of `Complexity.LogProg.marm_dtime` at the register
width `W = log₂ (B + 1) + 1` and memory range `P = 3 · 2 ^ E` is at most `2 ^ (c (S n + 1))`
for `c = C (a + 4) + 2a + 4`, `a = codeK N (c₀ + 3)`, when `t = c₀ S n` and
`logSpace n ≤ S n`.

**Proof sketch.** `n + 4 ≤ 2 ^ (E + 1)`, so `B + 1 < 2 ^ (E + 3)` and `W ≤ E + 3`;
`P + 1 ≤ 2 ^ (E + 2)`; `E ≤ a (S n + 1)` as `lgv n ≤ logSpace n + 1 ≤ S n + 1`. -/
private lemma time_bound (N : FinNDTM Bool) (C c₀ n Sn : ℕ) (hdom : logSpace n ≤ Sn) :
    2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
        (3 * kb N n (c₀ * Sn + 1) + 1) ^ 2 ≤
      1 * 2 ^ ((C * (Codec.codeK N * (c₀ + 3) + 4) + 2 * (Codec.codeK N * (c₀ + 3)) + 4) *
        (Sn + 1)) := by
  set K₀ := Codec.codeK N with hK₀
  have hK0 : 2 ≤ K₀ := two_le_codeK N
  set E := K₀ * (c₀ * Sn + 1 + lgv n + 1) with hE
  have hkb : kb N n (c₀ * Sn + 1) = 2 ^ E := rfl
  have hlg := lgv_le n
  have hlg' := logSpace_le_lgv n
  have hn : n + 1 ≤ 2 ^ logSpace n := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hEl : logSpace n + 1 ≤ E := by
    have : lgv n + 1 ≤ E := by
      calc lgv n + 1 ≤ 1 * (c₀ * Sn + 1 + lgv n + 1) := by omega
        _ ≤ E := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpowE : 2 ^ (logSpace n + 2) ≤ 2 ^ (E + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hn4 : n + 4 ≤ 2 ^ (E + 1) := by
    have : 2 ^ (logSpace n + 2) = 4 * 2 ^ logSpace n := by rw [pow_add]; ring
    omega
  have hE2 : 2 ^ (E + 1) = 2 * 2 ^ E := by rw [pow_succ]; ring
  have hE3 : 2 ^ (E + 3) = 8 * 2 ^ E := by rw [pow_add]; ring
  have hE2' : 2 ^ (E + 2) = 4 * 2 ^ E := by rw [pow_add]; ring
  -- the register width
  have hW : Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1 ≤ E + 3 := by
    have hlt : bigB N n (c₀ * Sn) + 1 < 2 ^ (E + 3) := by
      simp only [bigB, hkb]; omega
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega
  -- the memory range
  have hP : 3 * kb N n (c₀ * Sn + 1) + 1 ≤ 2 ^ (E + 2) := by rw [hkb]; omega
  -- the exponent
  set a := K₀ * (c₀ + 3) with ha
  have hEa : E ≤ a * (Sn + 1) := by
    have : c₀ * Sn + 1 + lgv n + 1 ≤ (c₀ + 3) * (Sn + 1) := by
      have : (c₀ + 3) * (Sn + 1) = c₀ * Sn + c₀ + 3 * Sn + 3 := by ring
      omega
    calc E = K₀ * (c₀ * Sn + 1 + lgv n + 1) := rfl
      _ ≤ K₀ * ((c₀ + 3) * (Sn + 1)) := Nat.mul_le_mul_left _ this
      _ = a * (Sn + 1) := by rw [ha, mul_assoc]
  have hexp : C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) + 2 * (E + 2) ≤
      (C * (a + 4) + 2 * a + 4) * (Sn + 1) := by
    have h1 : (Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1 ≤ (a + 4) * (Sn + 1) := by
      have : (a + 4) * (Sn + 1) = a * (Sn + 1) + 4 * Sn + 4 := by ring
      omega
    have h2 : C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) ≤
        C * ((a + 4) * (Sn + 1)) := Nat.mul_le_mul_left _ h1
    have h3 : (C * (a + 4) + 2 * a + 4) * (Sn + 1) =
        C * ((a + 4) * (Sn + 1)) + 2 * (a * (Sn + 1)) + 4 * (Sn + 1) := by ring
    omega
  calc 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
        (3 * kb N n (c₀ * Sn + 1) + 1) ^ 2
      ≤ 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
          (2 ^ (E + 2)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2)
    _ = 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) + 2 * (E + 2)) := by
      rw [← pow_mul, ← pow_add, mul_comm (E + 2) 2]
    _ ≤ 2 ^ ((C * (a + 4) + 2 * a + 4) * (Sn + 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = 1 * 2 ^ ((C * (a + 4) + 2 * a + 4) * (Sn + 1)) := (one_mul _).symm

/-- **Nondeterministic space sits inside exponential time, for any space bound above the
logarithm** ([AB09, Theorem 4.2, third inclusion], without space-constructibility):
`NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))` whenever `logSpace ≤ S`.

**Proof sketch.** Let `N` decide `L` in space `c₀ S`. The search machine
(`Complexity.LogProg.ExpBFS.A`) with the deciders of the input length and of `N`'s code
languages (all in `L`) answers `x ∈ L` (`setup_run`, then `iter_run` from radius `0`), with
registers below `B = 3 · 2 ^ E + |x| + 3` and its memory head in `[0, 3 · 2 ^ E]`, where
`E = codeK N (c₀ S |x| + 1 + lgv |x| + 1)`. `Complexity.LogProg.marm_dtime` gives a machine
deciding `L` in time `2 ^ (C (W + logSpace n + 1)) (P + 1)²`, which `time_bound` bounds by
`2 ^ (c (S n + 1))`. -/
theorem NSPACE_subset_exp_dtime_of_le (S : ℕ → ℕ) (hdom : ∀ n, logSpace n ≤ S n) :
    NSPACE S ⊆ ⋃ c : ℕ, DTIME fun n => 2 ^ (c * (S n + 1)) := by
  classical
  rintro L ⟨c₀, N, hN⟩
  obtain ⟨M, C, hM⟩ := marm_dtime (L := L) (A (Codec.codeK N)) .scan (decs N)
    (fun j => by
      fin_cases j
      · exact inputLenLang_mem
      · exact Codec.initLang_mem
      · exact Codec.stepLang_mem
      · exact Codec.acceptLang_mem)
    (fun n => Nat.log 2 (bigB N n (c₀ * S n) + 1) + 1) (fun n => 3 * kb N n (c₀ * S n + 1))
    (fun x => by
      have h0 := setup_run (K₀ := Codec.codeK N) (orc := orcN N) (x := x)
        (B := bigB N x.length (c₀ * S x.length)) (P := 3 * kb N x.length (c₀ * S x.length + 1))
        (orcN_len N x) (fun _ => false) (by simp only [bigB]; omega)
      have h1 := iter_run (N := N) (x := x) hN (c₀ * S x.length - 0) 0 (fun _ => false) rfl
        (Nat.zero_le _) (fun z hz => by simp at hz)
      have h := (reach_cf h0 (st' := { St.zero with Lg := lgv x.length, s := 0 })
        (by ext <;> simp [St.zero]) rfl).halt h1
      rw [St.toV_zero]
      refine h.mono fun c ⟨⟨hps, hv⟩, hp0, hpP⟩ => ⟨hps, fun r => ?_, abs_le.mpr ⟨by omega, hpP⟩⟩
      have e1 := length_bits_le_log (c.1.2.1 r + 1)
      have e2 : Nat.log 2 (c.1.2.1 r + 1) ≤ Nat.log 2 (bigB N x.length (c₀ * S x.length) + 1) :=
        Nat.log_mono_right (by have := hv r; omega)
      dsimp only
      omega)
  refine Set.mem_iUnion.mpr ⟨C * (Codec.codeK N * (c₀ + 3) + 4) +
    2 * (Codec.codeK N * (c₀ + 3)) + 4, 1, M, fun x => (hM x).mono ?_⟩
  exact time_bound N C c₀ x.length (S x.length) (hdom x.length)

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reachable codes at growing radii

The exponential-time simulation of a space-bounded nondeterministic decider `N` does not know
the space bound: it searches the configuration graph at the radii `s = 0, 1, 2, …` and stops at
the first radius at which growing the window to `s + 1` does not add a reachable vertex. This
file proves that this works.

At radius `s`, the *reachable codes* (`Complexity.ExpBFS.RCode`) are the codes reachable from
the initial code along step pairs (`Complexity.Codec.StepRel`); they are exactly the codes of
the configurations reached by choice words all of whose prefixes stay in the window `[-s, s]`
(`Complexity.ExpBFS.rcode_iff`). Re-coding a configuration at radius `s + 1` maps the
reachable codes at `s` injectively into those at `s + 1`
(`Complexity.ExpBFS.card_rset_le_succ`). If the two sets have the same size, every one-step
successor of a window-`s` run is again in the window (it is in the window `s + 1`, hence the
re-coding of a window-`s` run, hence of the same vertex), so every run stays in the window and
acceptance is decided by the reachable codes at `s`
(`Complexity.ExpBFS.mem_iff_of_card_eq`). Once `s` is at least the space bound, every run is
in the window and the sizes agree (`Complexity.ExpBFS.card_rset_succ_of_le`).

Configuration-graph infrastructure for [AB09, §4.1.1, Theorem 4.2]; not itself a result of
the book (the book assumes `S` space-constructible and computes the radius instead).

## Main definitions

* `Complexity.ExpBFS.WinRun` — a choice word whose prefixes stay in the window.
* `Complexity.ExpBFS.RCode`, `Complexity.ExpBFS.rset` — reachable codes at a radius.

## Main results

* `Complexity.ExpBFS.rcode_iff` — reachable codes are the codes of window runs.
* `Complexity.ExpBFS.card_rset_le_succ` — the count does not drop when the radius grows.
* `Complexity.ExpBFS.mem_iff_of_card_eq` — equal counts decide membership.
* `Complexity.ExpBFS.card_rset_succ_of_le` — above the space bound the counts agree.
* `Complexity.ExpBFS.winRun_iff`, `Complexity.ExpBFS.rcode_iff_reflTransGen` — the two
  definitions as equations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4, Theorem 4.2.)
-/

namespace Complexity.ExpBFS

open Turing Codec LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## Windows -/

/-- The window grows with the radius. -/
lemma inWin_mono {s s' : ℕ} {C : Cfg N.k Bool N.State x} (h : Cfg.InWindow s C) (hs : s ≤ s') :
    Cfg.InWindow s' C :=
  ⟨fun i => (h.1 i).trans (by exact_mod_cast hs),
    fun i z hz => h.2 i z (lt_of_le_of_lt (by exact_mod_cast hs) hz)⟩

/-- One step from the window `[-s, s]` stays in the window `[-(s + 1), s + 1]`: heads move by
one cell and write under themselves. -/
lemma inWin_stepWith {s : ℕ} {C : Cfg N.k Bool N.State x} (h : Cfg.InWindow s C) (b : Bool) :
    Cfg.InWindow (s + 1) (N.tm.stepWith b C) := by
  unfold NDTM.stepWith
  cases hs : C.state with
  | none => exact inWin_mono h (by omega)
  | some q =>
    refine ⟨fun i => ?_, fun i z hz' => ?_⟩
    · have hp := h.1 i
      have hmove := workTapePos_apply_le (N.tm.tr b q C.inputSymbol C.workTapeSymbols) C i
      push_cast; rw [abs_le] at hp hmove ⊢; constructor <;> linarith [hp.1, hp.2,
        hmove.1, hmove.2]
    · have hp := h.1 i
      have hzs : (s : ℤ) < |z| := by push_cast at hz'; linarith
      rcases hwr : ((N.tm.tr b q C.inputSymbol C.workTapeSymbols).workTapes i).1 with _ | sym
      · simp only [Action.apply, hwr]
        exact h.2 i z hzs
      · simp only [Action.apply, hwr]
        have hzp : z ≠ C.workTapePos i := by
          rintro rfl; exact absurd hp (not_le.mpr hzs)
        rw [Function.update_of_ne hzp]
        exact h.2 i z hzs

/-- A choice word all of whose prefix configurations lie in the window `[-s, s]`. -/
def WinRun (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ∀ j ≤ w.length, Cfg.InWindow s (N.tm.runWith (w.take j) (N.tm.initCfg x))

/-- A choice word `w` is a window run at radius `s` exactly when, for every `j ≤ |w|`, the
configuration that `N` reaches on `x` after the first `j` choices of `w` lies in the window
`[-s, s]` (`Turing.Cfg.InWindow s`). -/
lemma winRun_iff {s : ℕ} {w : List Bool} :
    WinRun N x s w ↔ ∀ j ≤ w.length, Cfg.InWindow s (N.tm.runWith (w.take j) (N.tm.initCfg x)) :=
  Iff.rfl

/-- The initial configuration is in every window. -/
lemma inWin_init (s : ℕ) : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s

/-- Extending a window run by a step that stays in the window. -/
lemma WinRun.snoc {s : ℕ} {w : List Bool} (h : WinRun N x s w) (b : Bool)
    (hb : Cfg.InWindow s (N.tm.runWith (w ++ [b]) (N.tm.initCfg x))) : WinRun N x s (w ++ [b]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  rcases Nat.lt_or_ge j (w.length + 1) with h' | h'
  · rw [List.take_append_of_le_length (by omega)]; exact h j (by omega)
  · obtain rfl : j = w.length + 1 := by omega
    rw [List.take_of_length_le (by simp)]; exact hb

/-- A window run is a window run at every larger radius. -/
lemma WinRun.mono {s s' : ℕ} {w : List Bool} (h : WinRun N x s w) (hs : s ≤ s') :
    WinRun N x s' w := fun j hj => inWin_mono (h j hj) hs

/-- The whole run of a window run is in the window. -/
lemma WinRun.last {s : ℕ} {w : List Bool} (h : WinRun N x s w) :
    Cfg.InWindow s (N.tm.runWith w (N.tm.initCfg x)) := by
  simpa using h w.length le_rfl

/-! ## Reachable codes -/

/-- **The reachable codes at radius `s`**: codes reachable from the initial code along step
pairs at radius `s`. -/
def RCode (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) : Prop :=
  Relation.ReflTransGen (StepRel N x s) (cfgCode s (N.tm.initCfg x)) u

/-- `Complexity.ExpBFS.RCode`'s defining equation: a reachable code is a step-pair path's end
from the initial code. -/
lemma rcode_iff_reflTransGen {s u : ℕ} :
    RCode N x s u ↔ Relation.ReflTransGen (StepRel N x s) (cfgCode s (N.tm.initCfg x)) u :=
  Iff.rfl

/-- Equal codes of window configurations are equal vertices. -/
lemma coreSum_eq_of_code_eq {s : ℕ} {C D : Cfg N.k Bool N.State x} (hC : Cfg.InWindow s C)
    (hD : Cfg.InWindow s D) (h : cfgCode s C = cfgCode s D) : NDTM.coreSum C = NDTM.coreSum D :=
  coreSum_eq_of_cfgWord_eq hC hD (by rw [← bits_cfgCode, ← bits_cfgCode, h])

/-- Equal vertices have equal codes. -/
lemma code_eq_of_coreSum_eq {s : ℕ} {C D : Cfg N.k Bool N.State x}
    (h : NDTM.coreSum C = NDTM.coreSum D) : cfgCode s C = cfgCode s D := by
  simp only [cfgCode, cfgWord_congr (s := s) h]

/-- **Reachable codes are the codes of window runs.**

**Proof sketch.** (⇐) The codes of consecutive prefixes of a window run are step pairs.
(⇒) Induction along the path: a step pair from the code of a window run's end leads, by
the vertex's determination of its successors (`Turing.NDTM.coreSum_stepWith`), to the code of
the run extended by the pair's choice bit, still in the window
(`Turing.NDTM.inWindow_of_coreSum_eq`). -/
theorem rcode_iff (s u : ℕ) :
    RCode N x s u ↔ ∃ w, WinRun N x s w ∧ cfgCode s (N.tm.runWith w (N.tm.initCfg x)) = u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], fun j _ => by simpa using inWin_init s, rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, hw, hcode⟩ := ih
      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ :=
        (mem_stepLang N x _ _ s).mp (stepRel_iff_mem.mp hst)
      have hv : NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum C :=
        coreSum_eq_of_code_eq hw.last hC (hcode.trans hcC.symm)
      have hv' : NDTM.coreSum (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) = NDTM.coreSum C' := by
        rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil, ← hb]
        exact NDTM.coreSum_stepWith N.tm b hv
      refine ⟨w ++ [b], hw.snoc b (NDTM.inWindow_of_coreSum_eq hv' hC'), ?_⟩
      rw [code_eq_of_coreSum_eq hv', hcC']
  · rintro ⟨w, hw, rfl⟩
    have key : ∀ j ≤ w.length,
        RCode N x s (cfgCode s (N.tm.runWith (w.take j) (N.tm.initCfg x))) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih =>
        intro hj
        refine (ih (by omega)).tail ?_
        rw [stepRel_iff_mem, mem_stepLang]
        refine ⟨_, hw j (by omega), rfl, _, ⟨w[j]'(by omega), ?_⟩, hw (j + 1) hj, rfl⟩
        rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
        rfl
    simpa using key w.length le_rfl

/-- Reachable codes lie below the code bound. -/
lemma rcode_lt {s u : ℕ} (h : RCode N x s u) :
    u < 2 ^ (codeK N * (s + logSpace x.length + 1)) := by
  obtain ⟨w, -, rfl⟩ := (rcode_iff s u).mp h
  exact cfgCode_lt s _

/-- **The reachable codes at radius `s`**, as a finite set. -/
noncomputable def rset (N : FinNDTM Bool) (x : List Bool) (s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ (codeK N * (s + logSpace x.length + 1)))).filter (RCode N x s)

/-- Membership in the reachable codes. -/
lemma mem_rset {s u : ℕ} : u ∈ rset N x s ↔ RCode N x s u := by
  classical
  simp only [rset, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨rcode_lt h, h⟩⟩

open Classical in
/-- Counting the reachable codes below any bound above the code bound gives their number. -/
lemma card_filter_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    ((Finset.range K).filter (RCode N x s)).card = (rset N x s).card := by
  have e : (Finset.range K).filter (RCode N x s) = rset N x s := by
    apply Finset.ext
    intro u
    rw [mem_rset]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(rcode_lt h).trans_le hK, h⟩⟩
  rw [e]

/-! ## Growing the radius -/

open Classical in
/-- Re-coding at radius `s + 1`: a reachable code at radius `s` is the code of a window run,
re-coded at radius `s + 1` (well defined up to the vertex). -/
noncomputable def recode (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) : ℕ :=
  if h : RCode N x s u then
    cfgCode (s + 1) (N.tm.runWith (Classical.choose ((rcode_iff s u).mp h)) (N.tm.initCfg x))
  else 0

/-- The re-coding of the code of a window run is the code at radius `s + 1` of its end. -/
lemma recode_spec {s : ℕ} {w : List Bool} (hw : WinRun N x s w) :
    recode N x s (cfgCode s (N.tm.runWith w (N.tm.initCfg x))) =
      cfgCode (s + 1) (N.tm.runWith w (N.tm.initCfg x)) := by
  have h : RCode N x s (cfgCode s (N.tm.runWith w (N.tm.initCfg x))) :=
    (rcode_iff s _).mpr ⟨w, hw, rfl⟩
  rw [recode, dif_pos h]
  obtain ⟨hw', hcode⟩ := Classical.choose_spec ((rcode_iff s _).mp h)
  exact code_eq_of_coreSum_eq (coreSum_eq_of_code_eq hw'.last hw.last hcode)

/-- Re-coding is injective on the reachable codes. -/
lemma recode_injOn (s : ℕ) : Set.InjOn (recode N x s) (rset N x s : Set ℕ) := by
  intro u hu v hv huv
  obtain ⟨w, hw, rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
  obtain ⟨w', hw', rfl⟩ := (rcode_iff s v).mp (mem_rset.mp hv)
  rw [recode_spec hw, recode_spec hw'] at huv
  exact code_eq_of_coreSum_eq
    (coreSum_eq_of_code_eq ((hw.mono (by omega)).last) ((hw'.mono (by omega)).last) huv)

/-- Re-coding maps reachable codes to reachable codes. -/
lemma recode_mem {s u : ℕ} (hu : u ∈ rset N x s) : recode N x s u ∈ rset N x (s + 1) := by
  obtain ⟨w, hw, rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
  rw [recode_spec hw, mem_rset, rcode_iff]
  exact ⟨w, hw.mono (by omega), rfl⟩

/-- **The count of reachable codes does not drop when the radius grows.** -/
theorem card_rset_le_succ (s : ℕ) : (rset N x s).card ≤ (rset N x (s + 1)).card :=
  Finset.card_le_card_of_injOn _ (fun _ hu => recode_mem hu) (recode_injOn s)

/-- With equal counts, every reachable code at radius `s + 1` is a re-coding. -/
lemma image_recode_of_card_eq {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    (rset N x s).image (recode N x s) = rset N x (s + 1) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact recode_mem hu
  · rw [Finset.card_image_of_injOn (recode_injOn s), h]

/-- **Equal counts close the window**: if the counts at `s` and `s + 1` agree, every choice word
is a window run at radius `s`.

**Proof sketch.** Induction on the word. One more step from a window run is in the window
`s + 1` (`inWin_stepWith`), so its code at `s + 1` is reachable, hence (equal counts) the
re-coding of a window run at `s`; equal codes at `s + 1` are equal vertices, and the window
depends only on the vertex. -/
theorem winRun_of_card_eq {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    ∀ w : List Bool, WinRun N x s w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => exact fun j _ => by simpa using inWin_init s
  | append_singleton w b ih =>
    refine ih.snoc b ?_
    have hstep : Cfg.InWindow (s + 1) (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) := by
      rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
      exact inWin_stepWith ih.last b
    have hrun : WinRun N x (s + 1) (w ++ [b]) := (ih.mono (by omega)).snoc b hstep
    have hmem : cfgCode (s + 1) (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) ∈ rset N x (s + 1) :=
      mem_rset.mpr ((rcode_iff _ _).mpr ⟨_, hrun, rfl⟩)
    rw [← image_recode_of_card_eq h] at hmem
    obtain ⟨u, hu, hre⟩ := Finset.mem_image.mp hmem
    obtain ⟨w', hw', rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
    rw [recode_spec hw'] at hre
    exact NDTM.inWindow_of_coreSum_eq
      (coreSum_eq_of_code_eq ((hw'.mono (by omega)).last) hstep hre).symm hw'.last

/-- **Equal counts decide membership**: if `N` decides `L` (in any space) and the counts of
reachable codes at radii `s` and `s + 1` agree, then `x ∈ L` iff some reachable code at
radius `s` is an accepting code.

**Proof sketch.** (⇐) `Complexity.Codec.mem_of_codePath`. (⇒) An accepting branch is a
window run (`winRun_of_card_eq`), so the code of its halted end is reachable and accepting. -/
theorem mem_iff_of_card_eq {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    x ∈ L ↔ ∃ u, RCode N x s u ∧
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ acceptLang N := by
  constructor
  · intro hx
    obtain ⟨T, -, -, hiff⟩ := hN x
    obtain ⟨w, -, hhalt, hout⟩ := hiff.mp hx
    have hw := winRun_of_card_eq h w
    refine ⟨_, (rcode_iff s _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [mem_acceptLang]
    exact ⟨_, hw.last, rfl, hhalt, hout⟩
  · rintro ⟨u, hu, hacc⟩
    exact mem_of_codePath hN x s _ u (by rw [mem_initLang]) hu hacc

/-- Every configuration reached from initialization by a decider in space `sp` lies in the
window of radius `sp |x|`.

**Proof sketch.** Words of the halting budget's length use at most `sp |x|` cells, so their
prefixes are in the window (`Turing.NDTM.runWith_take_inWindow`); a shorter word is a prefix
of a padded one, a longer one has halted at the budget. -/
lemma inWin_runWith_of_decides {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    (w : List Bool) : Cfg.InWindow (sp x.length) (N.tm.runWith w (N.tm.initCfg x)) := by
  obtain ⟨T, hHalt, hSpace, -⟩ := hN x
  by_cases hw : w.length ≤ T
  · set w' := w ++ List.replicate (T - w.length) false
    have hw' : w'.length = T := by simp [w']; omega
    have := NDTM.runWith_take_inWindow N.tm w' (hSpace w' hw') w.length
    rwa [show w'.take w.length = w by simp [w']] at this
  · have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
    have frozen : N.tm.runWith w (N.tm.initCfg x) = N.tm.runWith (w.take T) (N.tm.initCfg x) := by
      conv_lhs => rw [← List.take_append_drop T w]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ (hHalt _ hlen)]
    rw [frozen]
    have := NDTM.runWith_take_inWindow N.tm (w.take T) (hSpace _ hlen) T
    rwa [show (w.take T).take T = w.take T by simp] at this

/-- **Above the space bound the counts agree.** If `N` decides `L` in space `sp` and
`sp |x| ≤ s`, the counts of reachable codes at radii `s` and `s + 1` agree.

**Proof sketch.** Every run is in the window `sp |x| ≤ s` (`inWin_runWith_of_decides`), so
every window run at `s + 1` is one at `s`, and its code at `s + 1` is the re-coding of its
code at `s`; with `card_rset_le_succ` the counts agree. -/
theorem card_rset_succ_of_le {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (hs : sp x.length ≤ s) : (rset N x s).card = (rset N x (s + 1)).card := by
  classical
  refine le_antisymm (card_rset_le_succ s) ?_
  calc (rset N x (s + 1)).card ≤ ((rset N x s).image (recode N x s)).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨w, -, rfl⟩ := (rcode_iff _ v).mp (mem_rset.mp hv)
        have hw : WinRun N x s w := fun j _ =>
          inWin_mono (inWin_runWith_of_decides hN (w.take j)) hs
        exact Finset.mem_image.mpr ⟨_, mem_rset.mpr ((rcode_iff s _).mpr ⟨w, hw, rfl⟩),
          recode_spec hw⟩
    _ ≤ (rset N x s).card := Finset.card_image_le

end Complexity.ExpBFS
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Balls of the configuration graph and reachable codes

The window-growing counting machine `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2] computes,
at the window radius `s`, the balls `C_j` (`Complexity.LogProg.ISCount.ball`) of the
configuration graph of a decider `N` over the codes below a bound `K` at least the code bound
`2 ^ (codeK N · (s + logSpace |x| + 1))`. This file identifies its largest ball `C_K` with
the reachable codes `Complexity.ExpBFS.rset N x s` of
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius` (`mem_ball_iff_rcode`,
`card_ball_eq_rset`), so that the radius-growing facts proved there apply to the counts the
machine computes, and records the two acceptance facts the radius loop uses
(`mem_of_exists_acc`, `mem_iff_exists_acc_of_card_eq`). The first is
`Complexity.Codec.mem_of_codePath`; the second is the radius-`s` form of
`Complexity.ExpBFS.mem_iff_of_card_eq` (which, from equal counts at `s - 1` and `s`,
concludes at radius `s - 1`; codes depend on the radius, so the form used by the loop is
re-derived from `Complexity.ExpBFS.winRun_of_card_eq`).

Configuration-graph infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISGen.InitM`, `Complexity.LogProg.ISGen.AccM` — the initial-code and
  accepting-code predicates at radius `s`, as memberships in the code languages.

## Main results

* `Complexity.LogProg.ISGen.mem_ball_iff_rcode`, `Complexity.LogProg.ISGen.card_ball_eq_rset`
  — the largest ball is the set of reachable codes.
* `Complexity.LogProg.ISGen.card_ball_zero_code` — the ball `C_0` is the initial code.
* `Complexity.LogProg.ISGen.noAcc_balls_iff` — no accepting code in the balls iff none is
  reachable.
* `Complexity.LogProg.ISGen.mem_of_exists_acc`,
  `Complexity.LogProg.ISGen.mem_iff_exists_acc_of_card_eq` — an accepting reachable code
  gives membership; once the counts at `s - 1` and `s` agree, membership is an accepting
  reachable code at radius `s`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.2.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing Codec ExpBFS ISCount

variable {N : FinNDTM Bool} {x : List Bool}

/-- The initial-code predicate at radius `s`, as a membership. -/
abbrev InitM (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (u : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N

/-- The accepting-code predicate at radius `s`, as a membership. -/
abbrev AccM (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (u : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ acceptLang N

/-- **The largest ball is the set of reachable codes**: for a code bound `K` at least
`2 ^ (codeK N · (s + logSpace |x| + 1))`, a code is in the ball `C_K` of the configuration
graph at radius `s` (codes below `K`) iff it is reachable from the initial code.

**Proof sketch.** (⇒) A walk is a path of step pairs (`walkLe_reach`). (⇐) Every code on a
path from the initial code is reachable, hence below the code bound (`rcode_lt`); the path is
then a walk through codes below `K` (`exists_walkLe`), shortened to at most `K` steps
(`walkLe_short`). -/
theorem mem_ball_iff_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K)
    (t : ℕ) : t ∈ ball K (StepRel N x s) (InitM N x s) K ↔ RCode N x s t := by
  rw [mem_ball]
  constructor
  · rintro ⟨u, hu, hinit, hw⟩
    rw [InitM, mem_initLang] at hinit
    subst hinit
    exact rcode_iff_reflTransGen.mpr ((walkLe_reach hu hw).mono fun a b hab => hab.2.2)
  · intro ht
    have hpath : ∀ t, RCode N x s t → Relation.ReflTransGen
        (fun u v => u < K ∧ v < K ∧ StepRel N x s u v) (cfgCode s (N.tm.initCfg x)) t := by
      intro t ht
      rw [rcode_iff_reflTransGen] at ht
      induction ht with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
        exact ih.tail ⟨(rcode_lt (rcode_iff_reflTransGen.mpr hab)).trans_le hK,
          (rcode_lt (rcode_iff_reflTransGen.mpr (hab.tail hbc))).trans_le hK, hbc⟩
    have h0 : cfgCode s (N.tm.initCfg x) < K := (cfgCode_lt s _).trans_le hK
    obtain ⟨j, hw⟩ := exists_walkLe (hpath t ht)
    exact ⟨_, h0, by rw [InitM, mem_initLang], walkLe_short ((rcode_lt ht).trans_le hK) h0 hw⟩

/-- **The size of the largest ball is the number of reachable codes.** -/
theorem card_ball_eq_rset {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (ball K (StepRel N x s) (InitM N x s) K).card = (rset N x s).card := by
  classical
  rw [← card_filter_rcode hK]
  congr 1
  ext t
  rw [mem_ball_iff_rcode hK, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨(rcode_lt h).trans_le hK, h⟩, fun h => h.2⟩

/-- **The ball `C_0` is the initial code**, so it has one element. -/
theorem card_ball_zero_code {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (ball K (StepRel N x s) (InitM N x s) 0).card = 1 :=
  card_ball_zero ((cfgCode_lt s (N.tm.initCfg x)).trans_le hK)
    fun u => by rw [InitM, mem_initLang]; exact eq_comm

/-- There is a reachable code (the initial one). -/
theorem one_le_card_rset (s : ℕ) : 1 ≤ (rset N x s).card :=
  Finset.card_pos.mpr ⟨_, mem_rset.mpr (rcode_iff_reflTransGen.mpr Relation.ReflTransGen.refl)⟩

/-- **No accepting code in the balls** `C_1, …, C_K` iff no reachable code is accepting. -/
theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (∀ j, 0 < j → j ≤ K → ∀ t ∈ ball K (StepRel N x s) (InitM N x s) j, ¬ AccM N x s t) ↔
      ∀ t, RCode N x s t → ¬ AccM N x s t := by
  have hK0 : 0 < K := lt_of_lt_of_le (Nat.two_pow_pos _) hK
  constructor
  · intro h t ht
    exact h K hK0 le_rfl t ((mem_ball_iff_rcode hK t).mpr ht)
  · intro h j _ hj t ht
    exact h t ((mem_ball_iff_rcode hK t).mp (ball_mono hj ht))

/-- **An accepting reachable code makes the input a member** (at any radius). -/
theorem mem_of_exists_acc {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (h : ∃ t, RCode N x s t ∧ AccM N x s t) : x ∈ L := by
  obtain ⟨t, ht, hacc⟩ := h
  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) (rcode_iff_reflTransGen.mp ht) hacc

/-- **Equal counts at `s - 1` and `s` decide membership at radius `s`**: then `x ∈ L` iff some
reachable code at radius `s` is accepting.

**Proof sketch.** (⇒) With equal counts every choice word is a window run at radius `s - 1`
(`winRun_of_card_eq`), hence at `s`; the code of an accepting branch's end is reachable and
accepting. (⇐) `mem_of_exists_acc`. -/
theorem mem_iff_exists_acc_of_card_eq {L : Language Bool} {sp : ℕ → ℕ}
    (hN : N.DecidesInSpace L sp) {s : ℕ} (hs : 1 ≤ s)
    (h : (rset N x (s - 1)).card = (rset N x s).card) :
    x ∈ L ↔ ∃ t, RCode N x s t ∧ AccM N x s t := by
  refine ⟨fun hx => ?_, mem_of_exists_acc hN⟩
  have h' : (rset N x (s - 1)).card = (rset N x (s - 1 + 1)).card := by
    rwa [Nat.sub_add_cancel hs]
  obtain ⟨T, -, -, hiff⟩ := hN x
  obtain ⟨w, -, hhalt, hout⟩ := hiff.mp hx
  have hw : WinRun N x s w := (winRun_of_card_eq h' w).mono (by omega)
  refine ⟨_, (rcode_iff s _).mpr ⟨w, hw, rfl⟩, ?_⟩
  rw [AccM, mem_acceptLang]
  exact ⟨_, hw.last, rfl, hhalt, hout⟩

end ISGen

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The stages of the window-growing counting machine

The counting part of `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2, proof of Theorem 4.20],
proved with **guarded continuations**:

* the inner enumeration (`guloop`) needs its continuation only when the guessed enumeration
  succeeded with the count `cp`;
* the outer enumeration (`gvloop`) needs its continuation only at counts `c'` reached by a
  successful guessed enumeration;
* the stages (`gstage`), started with the correct count `cp = |C_i|`, therefore reach their
  end (`cmp`) only with the correct final count `cp = |C_K|`, and some branch accepts iff no
  ball `C_{i+1}, …, C_K` contains an accepting code and the continuation at `cmp` accepts.

The last point is what the radius loop needs: its next radius is entered with the true count
of the reachable codes only, so it never has to terminate from a phantom count.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* none (run theorems for the stages of `Complexity.LogProg.ISGen.igA`).

## Main results

* `Complexity.LogProg.ISGen.guloop`, `Complexity.LogProg.ISGen.gvloop`,
  `Complexity.LogProg.ISGen.gstage`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount ISTac

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- **The inner enumeration** (guarded) [AB09, §4.3.2: certifying `v ∉ C_{i+1}` by
enumerating `C_i`]: at `uh`, some branch accepts iff the guessed enumeration of
`u, …, K - 1` (members of `C_i` that are neither `v` nor step to `v`, counted from `cnt`)
ends with the count `cp` and the continuation at `vn` accepts (with `u`, `cnt` cleared);
every branch terminates. The continuation is only needed when the enumeration succeeds.

**Proof sketch.** Induction on `K - u`. At `u = K` compare the count with `cp`. Otherwise
choose: certify `u ∈ C_i` by a walk (`gwalk_spec`), reject if `u = v` or `(u, v)` is a step
pair, count `u`; or skip `u`. The guard is carried along: a counted `u` is a certified
member that is not `v` and does not step to `v`, a skipped one is unconstrained, so success
of the rest of the enumeration implies success of the whole. -/
theorem guloop (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hu : σ.u ≤ σ.K)
    (hcnt : σ.cnt ≤ σ.u) (hz : σ.g = 0 ∧ σ.cur = 0 ∧ σ.stp = 0)
    (hQ : GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp)
        (σ.K - σ.u) σ.u σ.cnt →
      IG (E := E) orc x B .vn { σ with u := 0, cnt := 0 } Q) :
    IG (E := E) orc x B .uh σ
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q)
        (σ.K - σ.u) σ.u σ.cnt) := by
  suffices H : ∀ r (σ : St), σ.K - σ.u = r → σ.Bd B → σ.K + 1 ≤ B → σ.u ≤ σ.K →
      σ.cnt ≤ σ.u → (σ.g = 0 ∧ σ.cur = 0 ∧ σ.stp = 0) →
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) r σ.u σ.cnt →
        IG (E := E) orc x B .vn { σ with u := 0, cnt := 0 } Q) →
      IG (E := E) orc x B .uh σ
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r σ.u σ.cnt) by
    exact H _ σ rfl hσ hK hu hcnt hz hQ
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hu hcnt hz hQ
    refine NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; omega) ?_
    by_cases he : σ.cnt = σ.cp
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _) (by isr; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ he
      · simp only [GS, he, true_and]
    · refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he)
        (NSem.ret rfl (St.greg hσ _ _))).congr ?_
      simp only [GS, he, false_and, Bool.false_eq_true]
  | succ r ih =>
    intro σ hr hσ hK hu hcnt hz hQ
    obtain ⟨hg, hcur, hstp⟩ := hz
    -- the continuation at `un`: next `u`, with the guard pulled back
    have hnext : ∀ c', c' ≤ σ.u + 1 →
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) r (σ.u + 1) c' →
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) (r + 1) σ.u
            σ.cnt) →
        IG (E := E) orc x B .un { σ with cnt := c' }
          (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r (σ.u + 1)
            c') := by
      intro c' hc' hpull
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with cnt := c', u := σ.u + 1 } (by dsimp only; omega) (by isb) hK
        (by dsimp only; omega) (by dsimp only; omega) ⟨hg, hcur, hstp⟩
        (fun h => IG.of_eq (by ext <;> rfl) (hQ (hpull h)))
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; omega) ?_
    have hin : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i σ.u →
        IG (E := E) orc x B .uE σ (σ.u ≠ σ.v ∧ ¬ RelO orc x σ.s σ.u σ.v ∧
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r (σ.u + 1)
          (σ.cnt + 1)) := by
      intro hmem
      by_cases he : σ.u = σ.v
      · refine (NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he)
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [he]
      refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he) ?_
      by_cases hr' : RelO orc x σ.s σ.u σ.v
      · refine (nsem_call₃_pos rfl (St.greg hσ _ _)
          (by isr; exact SavitchARM.rel_iff_orc.mp hr')
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [hr']
      refine nsem_call₃_neg rfl (St.greg hσ _ _)
        (by isr; simpa [SavitchARM.rel_iff_orc] using hr') ?_
      refine NSem.inc rfl (St.greg hσ _ _) ?_
      isr
      exact (hnext (σ.cnt + 1) (by omega)
        (fun h => Or.inl ⟨⟨hmem, he, hr'⟩, h⟩)).congr (by simp [he, hr'])
    have hw := gwalk_spec true _ σ hσ hK
      (fun hm => IG.of_eq (by ext <;> simp [hg, hcur, hstp]) (hin (by simpa [St.wb, St.wt]
        using hm)))
    have hskip := hnext σ.cnt (by omega) (fun h => Or.inr ⟨trivial, h⟩)
    refine (NSem.choose (A := igA E) (l := .uch) rfl (St.greg hσ _ _) hw
      (IG.of_eq (by ext <;> rfl) hskip)).congr ?_
    simp only [GS, St.wb, St.wt, if_true, true_and, and_assoc]

/-- **The outer enumeration** (guarded) [AB09, §4.3.2: computing `|C_{i+1}|`]: at `vh`, some
branch accepts iff the guessed enumeration of `v, …, K - 1` (members of `C_{i1}` certified by
walks and not accepting; non-members certified by the inner enumeration with count `cp`),
counted from `c`, ends with a count accepted by the continuation at `se`; every branch
terminates. The continuation is only needed at counts `c'` that a successful enumeration
ends with.

**Proof sketch.** Induction on `K - v`. At `v = K` go to the stage end. Otherwise choose:
certify `v ∈ C_{i+1}` by a walk (`gwalk_spec`), reject if `v` is accepting, count `v`; or
certify `v ∉ C_{i+1}` by the inner enumeration (`guloop`). The guard is carried along: a
counted `v` is a certified non-accepting member, a skipped one a certified non-member, so
success of the rest of the enumeration implies success of the whole. -/
theorem gvloop (Kont : ℕ → Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hv : σ.v ≤ σ.K) (hc : σ.c ≤ σ.v) (hz : σ.Clear)
    (hKont : ∀ c', c' ≤ σ.K →
      GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
        (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
          ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
        (fun c => c = c') (σ.K - σ.v) σ.v σ.c →
      IG (E := E) orc x B .se { σ with v := σ.K, c := c' } (Kont c')) :
    IG (E := E) orc x B .vh σ
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
        (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
          ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
        Kont (σ.K - σ.v) σ.v σ.c) := by
  suffices H : ∀ r (σ : St), σ.K - σ.v = r → σ.Bd B → σ.K + 1 ≤ B → σ.v ≤ σ.K →
      σ.c ≤ σ.v → σ.Clear →
      (∀ c', c' ≤ σ.K →
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          (fun c => c = c') r σ.v σ.c →
        IG (E := E) orc x B .se { σ with v := σ.K, c := c' } (Kont c')) →
      IG (E := E) orc x B .vh σ
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          Kont r σ.v σ.c) by
    exact H _ σ rfl hσ hK hv hc hz hKont
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hv hc hz hKont
    have he : σ.v = σ.K := by omega
    refine NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he) ?_
    exact IG.of_eq (by ext <;> simp [he]) (hKont σ.c (by omega) rfl)
  | succ r ih =>
    intro σ hr hσ hK hv hc hz hKont
    obtain ⟨hg, hcur, hstp, hu, hcnt⟩ := hz
    -- the continuation at `vn`: next `v`, with the guard pulled back
    have hnext : ∀ c', c' ≤ σ.v + 1 →
        (∀ c'', GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            (fun c => c = c'') r (σ.v + 1) c' →
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            (fun c => c = c'') (r + 1) σ.v σ.c) →
        IG (E := E) orc x B .vn { σ with c := c' }
          (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            Kont r (σ.v + 1) c') := by
      intro c' hc' hpull
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with c := c', v := σ.v + 1 } (by dsimp only; omega) (by isb) hK
        (by dsimp only; omega) (by dsimp only; omega) ⟨hg, hcur, hstp, hu, hcnt⟩
        (fun c'' hc'' h => IG.of_eq (by ext <;> rfl) (hKont c'' hc'' (hpull c'' h)))
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; omega) ?_
    -- the member branch
    have hin : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 σ.v →
        IG (E := E) orc x B .vA σ (¬ AccO orc x σ.s σ.v ∧
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          Kont r (σ.v + 1) (σ.c + 1)) := by
      intro hmem
      by_cases ha : AccO orc x σ.s σ.v
      · refine (nsem_call₂_pos rfl (St.greg hσ _ _)
          (by isr; exact SavitchARM.accO_iff_orc.mp ha)
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [ha]
      refine nsem_call₂_neg rfl (St.greg hσ _ _)
        (by isr; simpa [SavitchARM.accO_iff_orc] using ha) ?_
      refine NSem.inc rfl (St.greg hσ _ _) ?_
      isr
      exact (hnext (σ.c + 1) (by omega)
        (fun c'' h => Or.inl ⟨⟨hmem, ha⟩, h⟩)).congr (by simp [ha])
    have hw := gwalk_spec false _ σ hσ hK
      (fun hm => IG.of_eq (by ext <;> simp [hg, hcur, hstp]) (hin (by simpa [St.wb, St.wt]
        using hm)))
    -- the non-member branch
    have hout : IG (E := E) orc x B .uI σ
        (GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ σ.v ∧
            ¬ RelO orc x σ.s u σ.v) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0 ∧
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            Kont r (σ.v + 1) σ.c) := by
      refine NSem.clr rfl (St.greg hσ _ _) ?_
      isr
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      have hU := guloop (E := E) (orc := orc) (x := x) _ { σ with u := 0, cnt := 0 }
        (by isb) hK (Nat.zero_le _) le_rfl ⟨hg, hcur, hstp⟩
        (fun hgs => IG.of_eq (by ext <;> simp [hu, hcnt])
          (hnext σ.c (by omega) (fun c'' h => Or.inr ⟨by simpa using hgs, h⟩)))
      refine hU.congr ?_
      simp only [Nat.sub_zero]
      exact gs_and _ _ _ _ _ _ _
    refine (NSem.choose (A := igA E) (l := .vch) rfl (St.greg hσ _ _) hw hout).congr ?_
    simp only [GS, St.wb, St.wt, Bool.false_eq_true, if_false, and_assoc]

/-- **The stages with the correct count** [AB09, §4.3.2]: at `sh` with stage `i ≤ K`,
`i1 = i + 1` and the correct previous count `cp = |C_i|`, some branch accepts iff none of the
balls `C_{i+1}, …, C_K` contains an accepting code and the continuation at `cmp` accepts,
where it is entered with `i = K`, `i1 = K + 1` and `cp = |C_K|` (and some values of `v`,
`c`); every branch terminates.

**Proof sketch.** Induction on `K - i`. At `i = K` go to `cmp`. Otherwise clear `v`, `c` and
run the outer enumeration (`gvloop`); a successful enumeration has count `|C_{i+1}|` and no
accepting member (`gs_outer`, with the inner enumeration certifying exactly non-membership,
`gs_inner`, `not_mem_succ_iff`), so the stage end copies the correct count into `cp`
(`nsem_copy`), increments `i`, `i1` and recurs. -/
theorem gstage (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hi : σ.i ≤ σ.K)
    (hi1 : σ.i1 = σ.i + 1)
    (hcp : σ.cp = (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i).card) (hz : σ.Clear)
    (hQ : ∀ v' c', v' ≤ B → c' ≤ B →
      IG (E := E) orc x B .cmp
        { σ with i := σ.K, i1 := σ.K + 1, v := v', c := c',
                 cp := (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.K).card } Q) :
    IG (E := E) orc x B .sh σ
      ((∀ j, σ.i < j → j ≤ σ.K →
        ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q) := by
  suffices H : ∀ r (σ : St), σ.K - σ.i = r → σ.Bd B → σ.K + 1 ≤ B → σ.i ≤ σ.K →
      σ.i1 = σ.i + 1 → σ.cp = (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i).card →
      σ.Clear →
      (∀ v' c', v' ≤ B → c' ≤ B →
        IG (E := E) orc x B .cmp
          { σ with i := σ.K, i1 := σ.K + 1, v := v', c := c',
                   cp := (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.K).card } Q) →
      IG (E := E) orc x B .sh σ
        ((∀ j, σ.i < j → j ≤ σ.K →
          ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q) by
    exact H _ σ rfl hσ hK hi hi1 hcp hz hQ
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hi hi1 hcp hz hQ
    have he : σ.i = σ.K := by omega
    refine (NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he)
      (IG.of_eq ?_ (hQ σ.v σ.c (by isb) (by isb)))).congr ?_
    · ext <;> simp [he, hi1, hcp]
    · constructor
      · intro h; exact ⟨fun j h1 h2 => by omega, h⟩
      · exact fun h => h.2
  | succ r ih =>
    intro σ hr hσ hK hi hi1 hcp hz hQ
    have hlt : σ.i ≠ σ.K := by omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact hlt) ?_
    refine NSem.clr rfl (St.greg hσ _ _) ?_
    isr
    refine NSem.clr rfl (St.greg (by isb) _ _) ?_
    isr
    obtain ⟨hg, hcur, hstp, hu, hcnt⟩ := hz
    -- the out-guesses certify exactly non-membership in `C_{i+1}`
    have hB : ∀ t < σ.K, GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧
        u ≠ t ∧ ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0 ↔
        ¬ Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t := by
      intro t ht
      rw [hcp, gs_inner, hi1, not_mem_succ_iff ht]
    refine (gvloop (fun c' => (∀ j, σ.i + 1 < j → j ≤ σ.K →
        ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q)
        { σ with v := 0, c := 0 } (by isb) hK (Nat.zero_le _) le_rfl
        ⟨hg, hcur, hstp, hu, hcnt⟩ (fun c' hc' hgs => ?_)).congr ?_
    · -- the stage end, entered with the correct count
      dsimp only at hc' hgs ⊢
      rw [Nat.sub_zero, gs_outer _ _ _ hB] at hgs
      obtain ⟨-, hcc⟩ := hgs
      rw [hi1] at hcc
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine nsem_copy (igA E) orc x B rcp rc (by decide) .sec .sinc .si rfl rfl _ _
        (St.greg (E := E) (by isb) none none) (by simp) ?_
      isr
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with v := σ.K, c := c', cp := c', i := σ.i + 1, i1 := σ.i1 + 1 }
        (by dsimp only; omega) (by isb) hK (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; exact hcc.symm) ⟨hg, hcur, hstp, hu, hcnt⟩
        (fun v' c'' hv' hc'' => IG.of_eq (by ext <;> rfl) (hQ v' c'' hv' hc''))
    · dsimp only
      rw [Nat.sub_zero, gs_outer _ _ _ hB, hi1]
      constructor
      · rintro ⟨h1, h2, hq⟩
        refine ⟨fun j hj1 hj2 => ?_, hq⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; exact h1
        · exact h2 j h hj2
      · rintro ⟨h, hq⟩
        exact ⟨h (σ.i + 1) (by omega) (by omega), fun j h1 h2 => h j (by omega) h2, hq⟩

end ISGen

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The walks of the window-growing counting machine

The walk subroutine of `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2: the membership
certificate is a guessed path]: from `w0 b` it guesses a start code `g < K`,
checks it is initial, and walks, guessing each next code below `K` and checking the step
pair, until it meets the target (`v` at the outer site, `u` at the inner one) or has made as
many steps as the bound; on success it clears `g`, `cur`, `stp` and continues at the exit.

The statements here are **guarded**: the semantics at the exit is only required when the
walk succeeded (the target is in the ball, `Complexity.LogProg.ISCount.Mem`). Exits reached
with an impossible register file need no semantics, which is what lets the radius loop of
`igA` require its continuation only at the correct counts.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* none (run theorems for the walk subroutine of `Complexity.LogProg.ISGen.igA`).

## Main results

* `Complexity.LogProg.ISGen.gwalk_loop` — the walk loop.
* `Complexity.LogProg.ISGen.gwalk_spec` — the walk subroutine.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount ISTac

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- **The walk loop** (guarded): at `wl b`, with the current code `cur < K` after `stp` steps
out of the bound `L`, some branch accepts iff the target is reachable from `cur` within
`L - stp` steps through codes below `K` and the continuation at the exit accepts (with the
scratch registers cleared); every branch terminates. The continuation is only needed when
the target is so reachable.

**Proof sketch.** Induction on `L - stp`: at the target exit (the walk of length `0`
witnesses reachability); out of steps reject; otherwise guess `g < K` (`nsem_guess`), reject
unless `(cur, g)` is a step pair, copy `g` into `cur` (`nsem_copy`), count the step, and
recur with the guard pulled back along the step. -/
theorem gwalk_loop (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hcur : σ.cur < σ.K) (hstp : σ.stp ≤ σ.wb b)
    (hQ : WalkLe (RelO orc x σ.s) σ.K (σ.wb b - σ.stp) σ.cur (σ.wt b) →
      IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) :
    IG (E := E) orc x B (.wl b) σ
      (WalkLe (RelO orc x σ.s) σ.K (σ.wb b - σ.stp) σ.cur (σ.wt b) ∧ Q) := by
  suffices H : ∀ dd (σ : St), σ.wb b - σ.stp = dd → σ.Bd B → σ.K + 1 ≤ B → σ.cur < σ.K →
      σ.stp ≤ σ.wb b →
      (WalkLe (RelO orc x σ.s) σ.K dd σ.cur (σ.wt b) →
        IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) →
      IG (E := E) orc x B (.wl b) σ (WalkLe (RelO orc x σ.s) σ.K dd σ.cur (σ.wt b) ∧ Q) by
    exact H _ σ rfl hσ hK hcur hstp hQ
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ hK hcur hstp hQ
    by_cases he : σ.cur = σ.wt b
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _)
        (by simp only [St.toV_cur, toV_wT]; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ (walkLe_zero_iff.mpr he)
      · simp only [walkLe_zero_iff, he, true_and]
    · have hL : σ.stp = σ.wb b := by omega
      refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he)
        (NSem.jeq_pos rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL)
          (NSem.ret rfl (St.greg hσ _ _)))).congr ?_
      simp only [walkLe_zero_iff, he, Bool.false_eq_true, false_and]
  | succ dd ih =>
    intro σ hd hσ hK hcur hstp hQ
    by_cases he : σ.cur = σ.wt b
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _)
        (by simp only [St.toV_cur, toV_wT]; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ (walkLe_succ_iff_head.mpr (Or.inl he))
      · simp only [walkLe_succ_iff_head, he, true_or, true_and]
    have hbd : σ.wb b ≤ B := by simp only [St.wb, St.Bd] at hσ ⊢; cases b <;> simp <;> omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_cur, toV_wT]; exact he) ?_
    have hL : σ.stp ≠ σ.wb b := by omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by simp only [St.toV_stp, toV_wB]; exact hL) ?_
    refine NSem.clr rfl (St.greg hσ _ _) ?_
    isr
    refine (nsem_guess (igA E) orc x B rg rK (by decide) (.gt b true) (.gc b true) (.gm b true)
      (.gxS b) .rej rfl rfl rfl rfl
      (fun j => RelO orc x σ.s σ.cur j ∧
        (WalkLe (RelO orc x σ.s) σ.K dd j (σ.wt b) ∧ Q)) _
      (St.greg (E := E) (by isb) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
    · simp only [St.toV_K] at hj2
      isr
      by_cases hr : RelO orc x σ.s σ.cur j
      · refine nsem_call₃_pos rfl (St.greg (by isb) _ _)
          (by isr; exact SavitchARM.rel_iff_orc.mp hr) ?_
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b true) (.wcb b true)
          (.wst b) rfl rfl _ _ (St.greg (E := E) (by isb) none none) (by simp) ?_
        isr
        refine NSem.inc rfl (St.greg (by isb) _ _) ?_
        isr
        refine (ih { σ with g := j, cur := j, stp := σ.stp + 1 }
          (by show St.wb b σ - (σ.stp + 1) = dd; omega)
          (by isb) hK (by simpa using hj2) (by show σ.stp + 1 ≤ St.wb b σ; omega)
          (fun hw => IG.of_eq (by ext <;> rfl)
            (hQ (walkLe_succ_iff_head.mpr
              (Or.inr ⟨j, by simpa using hj2, hr, by simpa [St.wt] using hw⟩))))).congr ?_
        simp [St.wt, hr]
      · refine (nsem_call₃_neg rfl (St.greg (by isb) _ _)
          (by isr; simpa [SavitchARM.rel_iff_orc] using hr)
          (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
        simp only [Bool.false_eq_true, false_iff, not_and]
        exact fun h => absurd h hr
    · simp only [St.toV_g, St.toV_K, walkLe_succ_iff_head, he, false_or]
      constructor
      · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
      · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩

/-- **The walk subroutine** (guarded) [AB09, §4.3.2: the membership certificate is a guessed
path]: from `w0 b`, some branch accepts iff the target is in the ball of radius the bound and
the continuation at the exit accepts with `g`, `cur`, `stp` cleared; every branch
terminates. The continuation is only needed when the target is in the ball.

**Proof sketch.** Guess the start code (`nsem_guess`), reject unless it is initial, copy it
into `cur` (`nsem_copy`), clear the step count, and run the walk loop (`gwalk_loop`); a
successful walk from an initial code witnesses membership in the ball, discharging the
guard. -/
theorem gwalk_spec (b : Bool) (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hQ : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) (σ.wb b) (σ.wt b) →
      IG (E := E) orc x B (gwX b) { σ with cur := 0, stp := 0, g := 0 } Q) :
    IG (E := E) orc x B (.w0 b) σ
      (Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) (σ.wb b) (σ.wt b) ∧ Q) := by
  refine NSem.clr rfl (St.greg hσ _ _) ?_
  isr
  refine (nsem_guess (igA E) orc x B rg rK (by decide) (.gt b false) (.gc b false)
    (.gm b false) (.gxI b) .rej rfl rfl rfl rfl
    (fun j => InitO orc x σ.s j ∧ (WalkLe (RelO orc x σ.s) σ.K (σ.wb b) j (σ.wt b) ∧ Q)) _
    (St.greg (E := E) (by isb) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
  · simp only [St.toV_K] at hj2
    isr
    by_cases hi : InitO orc x σ.s j
    · refine nsem_call₂_pos rfl (St.greg (by isb) _ _)
        (by isr; exact SavitchARM.initO_iff_orc.mp hi) ?_
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine nsem_copy (igA E) orc x B rcur rg (by decide) (.wc b false) (.wcb b false)
        (.w2 b) rfl rfl _ _ (St.greg (E := E) (by isb) none none) (by simp) ?_
      isr
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine (gwalk_loop b Q { σ with g := j, cur := j, stp := 0 } (by isb) hK
        (by simpa using hj2) (Nat.zero_le _)
        (fun hw => IG.of_eq (by ext <;> rfl)
          (hQ ⟨j, by simpa using hj2, hi, by simpa [St.wb, St.wt] using hw⟩))).congr ?_
      exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
    · refine (nsem_call₂_neg rfl (St.greg (by isb) _ _)
        (by isr; simpa [SavitchARM.initO_iff_orc] using hi)
        (NSem.ret rfl (St.greg (by isb) _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun h => absurd h hi
  · simp only [St.toV_g, St.toV_K, Mem]
    constructor
    · rintro ⟨j, -, hj, h1, h2, hq⟩; exact ⟨⟨j, hj, h1, h2⟩, hq⟩
    · rintro ⟨⟨j, hj, h1, h2⟩, hq⟩; exact ⟨j, Nat.zero_le _, hj, h1, h2, hq⟩

end ISGen

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The combinatorics of inductive counting

The predicates evaluated by the inductive-counting machine
`Complexity.LogProg.ISGen.igA` [AB09, §4.3.2, proof of Theorem 4.20], over a relation `R`
on vertices `< K` and a set `Init` of start vertices.

* `Complexity.LogProg.ISCount.Mem K R Init L t` — `t` is reachable from a start vertex by at
  most `L` steps; `Complexity.LogProg.ISCount.ball` — the set `C_L` of such `t < K`.
* `Complexity.LogProg.ISCount.GS A B Kont r t c` — the acceptance condition of a guessed
  enumeration of the vertices `t, …, t + r - 1` with count `c`: each vertex is guessed in
  (and then must satisfy `A`, counting one) or out (and then must satisfy `B`), and the
  continuation `Kont` receives the final count. Its closed form is `gs_iff`.

The counting argument [AB09, §4.3.2]: when the count `cp` of the previous ball is right, the
inner enumeration accepts exactly when no member of `C_i` is or steps to `v`
(`gs_inner`), which is `v ∉ C_{i+1}` (`not_mem_succ_iff`); then the outer enumeration must
guess exactly `C_{i+1}`, and passes on its size (`gs_outer`). So each stage started with the
right count ends with the right count (`Complexity.LogProg.ISGen.gstage`).

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISCount.Mem`, `Complexity.LogProg.ISCount.ball`,
  `Complexity.LogProg.ISCount.GS`.

## Main results

* `Complexity.LogProg.ISCount.gs_iff` — the closed form of a guessed enumeration.
* `Complexity.LogProg.ISCount.mem_succ_iff` — the balls grow by one step.
* `Complexity.LogProg.ISCount.gs_inner`, `Complexity.LogProg.ISCount.gs_outer` — the two
  enumerations with the right count. [AB09, §4.3.2]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISCount

/-! ## Halving counts -/

/-- Halving a positive number shortens its binary expansion by one digit. -/
lemma size_half {m : ℕ} (h : m ≠ 0) : Nat.size m = Nat.size (m / 2) + 1 := by
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, ← Nat.div2_val, Nat.div2_bits_eq_tail,
    List.length_tail]
  have : 0 < m.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (by omega)
  omega

/-- A number is below two to its binary length plus one. -/
lemma lt_two_pow_size_succ (n : ℕ) : n < 2 ^ (Nat.size n + 1) :=
  (Nat.lt_size_self n).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-! ## Balls -/

variable (K : ℕ) (R : ℕ → ℕ → Prop) (Init Acc : ℕ → Prop)

/-- **Reachability within `L` steps**: some start vertex `u < K` reaches `t` by at most `L`
steps of `R` through vertices `< K`. -/
def Mem (L t : ℕ) : Prop := ∃ u < K, Init u ∧ WalkLe R K L u t

open Classical in
/-- **The ball `C_L`**: the vertices `t < K` reachable within `L` steps. -/
noncomputable def ball (L : ℕ) : Finset ℕ := (Finset.range K).filter (Mem K R Init L)

variable {K R Init Acc}

/-- A walk from a vertex below `K` ends below `K`. -/
lemma walkLe_lt {j c t : ℕ} (hc : c < K) (h : WalkLe R K j c t) : t < K := by
  induction j generalizing c with
  | zero => cases walkLe_zero_iff.mp h; exact hc
  | succ j ih =>
    rcases walkLe_succ_iff_head.mp h with rfl | ⟨v, hv, -, hw⟩
    · exact hc
    · exact ih hv hw

/-- A reachable vertex is below `K`. -/
lemma Mem.lt {L t : ℕ} (h : Mem K R Init L t) : t < K := by
  obtain ⟨u, hu, -, hw⟩ := h
  exact walkLe_lt hu hw

/-- Membership in a ball. -/
lemma mem_ball {L t : ℕ} : t ∈ ball K R Init L ↔ Mem K R Init L t := by
  classical
  simp only [ball, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.lt, h⟩⟩

/-- The balls grow with the radius. -/
lemma ball_mono {L L' : ℕ} (h : L ≤ L') : ball K R Init L ⊆ ball K R Init L' := by
  intro t ht
  rw [mem_ball] at ht ⊢
  obtain ⟨u, hu, hi, hw⟩ := ht
  exact ⟨u, hu, hi, walkLe_mono h hw⟩

/-- **Walks extend at the end**: a walk of at most `j + 1` steps is a walk of at most `j`
steps, or one followed by a step into a vertex below `K`.

**Proof sketch.** `WalkLe` unfolds at the front (a walk is empty or a first step followed by
a shorter walk), so induct on `j` generalizing the start `c`. For `j = 0` both sides are the
empty walk or a single step. For `j + 1`, a walk that begins with a step `c → v` has its tail
split by the induction hypothesis at `v`; conversely, a last step appended to a walk is
pushed into the tail of that walk by the induction hypothesis (or, when the walk is empty, is
itself a one-step walk). -/
lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
    WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K := by
  induction j generalizing c with
  | zero =>
    simp only [walkLe_succ_iff_head, walkLe_zero_iff]
    constructor
    · rintro (h | ⟨v, hv, he, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, rfl, he, hv⟩
    · rintro (h | ⟨w, rfl, he, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, ht, he, rfl⟩
  | succ j ih =>
    rw [walkLe_succ_iff_head (j := j + 1)]
    constructor
    · rintro (h | ⟨v, hv, he, hw⟩)
      · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inl h))
      · rcases (ih v).mp hw with h | ⟨w, hw', hwt, ht⟩
        · exact Or.inl (walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, h⟩))
        · exact Or.inr ⟨w, walkLe_succ_iff_head.mpr (Or.inr ⟨v, hv, he, hw'⟩), hwt, ht⟩
    · rintro (h | ⟨w, hw, hwt, ht⟩)
      · rcases walkLe_succ_iff_head.mp h with h | ⟨v, hv, he, hw⟩
        · exact Or.inl h
        · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
      · rcases walkLe_succ_iff_head.mp hw with hw | ⟨v, hv, he, hw⟩
        · subst hw
          exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
        · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩

/-- **The balls grow by one step**: `C_{L+1}` is `C_L` together with the successors below `K`
of its members. -/
lemma mem_succ_iff (L t : ℕ) : Mem K R Init (L + 1) t ↔
    Mem K R Init L t ∨ ∃ w, Mem K R Init L w ∧ R w t ∧ t < K := by
  constructor
  · rintro ⟨u, hu, hi, hw⟩
    rcases (walkLe_succ_iff L u t).mp hw with h | ⟨w, hw', hwt, ht⟩
    · exact Or.inl ⟨u, hu, hi, h⟩
    · exact Or.inr ⟨w, ⟨u, hu, hi, hw'⟩, hwt, ht⟩
  · rintro (⟨u, hu, hi, hw⟩ | ⟨w, ⟨u, hu, hi, hw'⟩, hwt, ht⟩)
    · exact ⟨u, hu, hi, walkLe_succ hw⟩
    · exact ⟨u, hu, hi, (walkLe_succ_iff L u t).mpr (Or.inr ⟨w, hw', hwt, ht⟩)⟩

/-- **Non-membership in the next ball** (for `v < K`): no member of `C_L` is or steps to `v`. -/
lemma not_mem_succ_iff {L v : ℕ} (hv : v < K) : ¬ Mem K R Init (L + 1) v ↔
    ∀ u ∈ ball K R Init L, u ≠ v ∧ ¬ R u v := by
  rw [mem_succ_iff]
  constructor
  · intro h u hu
    rw [mem_ball] at hu
    refine ⟨fun e => h (Or.inl (e ▸ hu)), fun he => h (Or.inr ⟨u, hu, he, hv⟩)⟩
  · rintro h (hm | ⟨w, hw, hwv, -⟩)
    · exact (h v (mem_ball.mpr hm)).1 rfl
    · exact (h w (mem_ball.mpr hw)).2 hwv

/-- With a unique start vertex below `K`, the ball `C_0` has one element. -/
lemma card_ball_zero {u₀ : ℕ} (hu₀ : u₀ < K) (hI : ∀ u, Init u ↔ u = u₀) :
    (ball K R Init 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨u₀, Finset.ext fun t => ?_⟩
  rw [mem_ball, Finset.mem_singleton]
  constructor
  · rintro ⟨u, -, hi, hw⟩
    have e : u = t := walkLe_zero_iff.mp hw
    rw [← e]
    exact (hI u).mp hi
  · intro h
    rw [h]
    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, walkLe_zero_iff.mpr rfl⟩

/-! ## Guessed enumerations -/

/-- **A guessed enumeration** of the vertices `t, …, t + r - 1` with count `c`: each vertex
is guessed in (it must satisfy `A`, and the count grows) or out (it must satisfy `B`); at the
end the continuation `Kont` receives the count. -/
def GS (A B Kont : ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, _, c => Kont c
  | r + 1, t, c => (A t ∧ GS A B Kont r (t + 1) (c + 1)) ∨ (B t ∧ GS A B Kont r (t + 1) c)

/-- A continuation conjunct independent of the count factors out of an enumeration. -/
lemma gs_and (A B Kont : ℕ → Prop) (Q : Prop) (r t c : ℕ) :
    GS A B (fun c => Kont c ∧ Q) r t c ↔ GS A B Kont r t c ∧ Q := by
  induction r generalizing t c with
  | zero => rfl
  | succ r ih =>
    simp only [GS, ih]
    tauto

/-- **The closed form of a guessed enumeration**: some set `T` of the enumerated vertices has
`A` on its members and `B` on the other enumerated vertices, and the continuation accepts
the count `c + |T|`.

**Proof sketch.** Induction on `r`: the first vertex `t` is in `T` (then `T` is
`insert t T'`) or not. -/
lemma gs_iff (A B Kont : ℕ → Prop) (r t c : ℕ) :
    GS A B Kont r t c ↔ ∃ T : Finset ℕ, T ⊆ Finset.Ico t (t + r) ∧ (∀ y ∈ T, A y) ∧
      (∀ y ∈ Finset.Ico t (t + r), y ∉ T → B y) ∧ Kont (c + T.card) := by
  induction r generalizing t c with
  | zero =>
    simp only [GS, Nat.add_zero, Finset.Ico_self, Finset.subset_empty]
    constructor
    · intro h; exact ⟨∅, rfl, by simp, by simp, by simpa using h⟩
    · rintro ⟨T, rfl, -, -, h⟩; simpa using h
  | succ r ih =>
    simp only [GS, ih]
    constructor
    · rintro (⟨hA, T, hT, hTA, hTB, hK⟩ | ⟨hB, T, hT, hTA, hTB, hK⟩)
      · have htT : t ∉ T := fun h => by have := Finset.mem_Ico.mp (hT h); omega
        refine ⟨insert t T, fun y hy => ?_, fun y hy => ?_, fun y hy hyT => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
          · have := Finset.mem_Ico.mp (hT hy); exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hA
          · exact hTA y hy
        · have hne : y ≠ t := fun e => hyT (e ▸ Finset.mem_insert_self _ _)
          have := Finset.mem_Ico.mp hy
          exact hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            (fun h => hyT (Finset.mem_insert_of_mem h))
        · rw [Finset.card_insert_of_notMem htT]
          rwa [show c + (T.card + 1) = c + 1 + T.card by omega]
      · refine ⟨T, fun y hy => ?_, hTA, fun y hy hyT => ?_, hK⟩
        · have := Finset.mem_Ico.mp (hT hy); exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · rcases Nat.eq_or_lt_of_le (Finset.mem_Ico.mp hy).1 with h | h
          · subst h; exact hB
          · exact hTB y
              (Finset.mem_Ico.mpr ⟨by omega, by have := (Finset.mem_Ico.mp hy).2; omega⟩) hyT
    · rintro ⟨T, hT, hTA, hTB, hK⟩
      by_cases htT : t ∈ T
      · refine Or.inl ⟨hTA t htT, T.erase t, fun y hy => ?_, fun y hy => hTA y
          (Finset.mem_of_mem_erase hy), fun y hy hyT => ?_, ?_⟩
        · have hne := Finset.ne_of_mem_erase hy
          have := Finset.mem_Ico.mp (hT (Finset.mem_of_mem_erase hy))
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · have := Finset.mem_Ico.mp hy
          refine hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) fun h => hyT ?_
          exact Finset.mem_erase.mpr ⟨by omega, h⟩
        · have := Finset.card_erase_of_mem htT
          have hpos : 0 < T.card := Finset.card_pos.mpr ⟨t, htT⟩
          rwa [this, show c + 1 + (T.card - 1) = c + T.card by omega]
      · refine Or.inr ⟨hTB t (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) htT, T, fun y hy => ?_,
          hTA, fun y hy hyT => ?_, hK⟩
        · have := Finset.mem_Ico.mp (hT hy)
          have hne : y ≠ t := fun e => htT (e ▸ hy)
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · have := Finset.mem_Ico.mp hy
          exact hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hyT

/-- **The inner enumeration with the right count** [AB09, §4.3.2]: guessing members of `C_L`
none of which is or steps to `v`, and finding exactly `|C_L|` of them, is possible iff every
member of `C_L` is neither `v` nor steps to `v`.

**Proof sketch.** A guessed set of members of `C_L` of size `|C_L|` is `C_L` itself. -/
lemma gs_inner (L v : ℕ) :
    GS (fun u => Mem K R Init L u ∧ u ≠ v ∧ ¬ R u v) (fun _ => True)
        (fun c => c = (ball K R Init L).card) K 0 0 ↔
      ∀ u ∈ ball K R Init L, u ≠ v ∧ ¬ R u v := by
  rw [gs_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨T, -, hTA, -, hcard⟩
    have hsub : T ⊆ ball K R Init L := fun y hy => mem_ball.mpr (hTA y hy).1
    have heq : T = ball K R Init L := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro u hu
    rw [← heq] at hu
    exact (hTA u hu).2
  · intro h
    refine ⟨ball K R Init L, fun y hy => ?_, fun y hy => ⟨mem_ball.mp hy, h y hy⟩,
      fun _ _ _ => trivial, rfl⟩
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, (mem_ball.mp hy).lt⟩

/-- **The outer enumeration** [AB09, §4.3.2]: if the out-guesses certify exactly
non-membership in `C_L` (below `K`), then the enumeration guessing members of `C_L` that are
not accepting accepts iff no member of `C_L` is accepting and the continuation accepts
`|C_L|`.

**Proof sketch.** The guessed set must be `C_L`: its members are in `C_L`, and the other
vertices below `K` are not. -/
lemma gs_outer (L : ℕ) (B Kont : ℕ → Prop) (hB : ∀ t < K, B t ↔ ¬ Mem K R Init L t) :
    GS (fun t => Mem K R Init L t ∧ ¬ Acc t) B Kont K 0 0 ↔
      (∀ t ∈ ball K R Init L, ¬ Acc t) ∧ Kont (ball K R Init L).card := by
  rw [gs_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨T, hT, hTA, hTB, hK⟩
    have heq : T = ball K R Init L := by
      ext y
      rw [mem_ball]
      constructor
      · intro hy; exact (hTA y hy).1
      · intro hy
        by_contra hyT
        have hyK := Finset.mem_Ico.mpr ⟨Nat.zero_le y, hy.lt⟩
        exact (hB y hy.lt).mp (hTB y hyK hyT) hy
    subst heq
    exact ⟨fun t ht => (hTA t ht).2, hK⟩
  · rintro ⟨hA, hK⟩
    refine ⟨ball K R Init L, fun y hy => ?_, fun y hy => ⟨mem_ball.mp hy, hA y hy⟩,
      fun y hy hyT => ?_, hK⟩
    · exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, (mem_ball.mp hy).lt⟩
    · exact (hB y (Finset.mem_Ico.mp hy).2).mpr fun h => hyT (mem_ball.mpr h)

end ISCount

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The configuration-graph reduction to `PATH`

The reduction of [AB09, Theorem 4.18]: a language `L` decided by a nondeterministic machine
`N` in space `c₀ · logSpace` is mapped, input by input, to a raw `PATH` instance
(`Complexity.pathRaw`) whose vertices are configuration codes of `N` on `x`
(`TCSlib.Complexity.SpaceComplexity.Codec`). With `ℓ = |bits (|x| + 1)|` (at least
`logSpace |x|`), radius `s = c₀ ℓ` and exponent `E = K (c₀ + 1) ℓ + K + 2` (`K = codeK N`),
the graph has `n = 2 ^ E` vertices, polynomially many in `|x|`:

* vertex `0` is the source and vertex `1` the target;
* vertex `c + 2` stands for the code `c`;
* edges `0 → c + 2` for initial codes `c`, `c + 2 → 1` for accepting codes `c`, and
  `c + 2 → c' + 2` for step pairs `(c, c')` (all at radius `s`).

The codes of a space-bounded accepting branch are below `2 ^ (E - 2)`
(`Complexity.Codec.mem_iff_codeChain`), so they all are vertices; conversely any path from
`0` to `1` passes an initial code and ends with an accepting code, which gives membership
(`Complexity.Codec.mem_of_codePath`). The source and the target are the two vertices with the
shortest binary names, so the instance ends in the constant word `⟨bits 0, bits 1⟩`.

This file holds the reduction and its correctness; its implicit logspace computability is
`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide`.

## Main definitions

* `Complexity.PathHard.ell`, `expo`, `nV` — the size parameters.
* `Complexity.PathHard.Edge` — the edge relation of the configuration graph on codes.
* `Complexity.PathHard.adjWordE`, `Complexity.PathHard.red` — the adjacency word and the
  reduction.

## Main results

* `Complexity.PathHard.red_mem_iff` — `x ∈ L ↔ red x ∈ pathRawLang`. [AB09, Theorem 4.18,
  correctness of the reduction]
* `Complexity.PathHard.length_red`, `Complexity.PathHard.length_red_le` — the output length,
  and its polynomial bound.
* `Complexity.PathHard.red_getD` — the bits of the output by position.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg Codec

/-! ## Size parameters -/

/-- The logarithmic size parameter `ℓ = |bits (m + 1)|` of an input length `m`. -/
def ell (m : ℕ) : ℕ := (Nat.bits (m + 1)).length

/-- The vertex exponent `E = K (c₀ + 1) ℓ + K + 2`. -/
def expo (K c₀ m : ℕ) : ℕ := K * (c₀ + 1) * ell m + (K + 2)

/-- The vertex count `n = 2 ^ E`. -/
def nV (K c₀ m : ℕ) : ℕ := 2 ^ expo K c₀ m

/-- `ℓ` is the bit length of `m + 1`, a `Nat.size`. -/
lemma ell_eq_size (m : ℕ) : ell m = Nat.size (m + 1) := by
  rw [ell, Nat.size_eq_bits_len]

/-- `logSpace m ≤ ℓ`. -/
lemma logSpace_le_ell (m : ℕ) : logSpace m ≤ ell m := by
  rw [ell_eq_size, logSpace]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : m + 1 < 2 ^ Nat.size (m + 1) := Nat.lt_size_self _
    have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have : Nat.log 2 m < Nat.size (m + 1) :=
      (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    omega

/-- `2 ^ ℓ ≤ 2 (m + 1)`. -/
lemma two_pow_ell_le (m : ℕ) : 2 ^ ell m ≤ 2 * (m + 1) :=
  two_pow_bits_le (m + 1) (by omega)

/-- `ℓ` is monotone. -/
lemma ell_mono {m m' : ℕ} (h : m ≤ m') : ell m ≤ ell m' :=
  length_bits_mono (by omega)

/-- The vertex count is monotone in the input length. -/
lemma nV_mono (K c₀ : ℕ) {m m' : ℕ} (h : m ≤ m') : nV K c₀ m ≤ nV K c₀ m' := by
  unfold nV expo
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (ell_mono h)) _)

/-- There are at least four vertices. -/
lemma four_le_nV (K c₀ m : ℕ) : 4 ≤ nV K c₀ m := by
  unfold nV expo
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The vertex count is polynomial**: `n ≤ 2 ^ (K + 2) · 2 ^ e · (m + 1) ^ e` with
`e = K (c₀ + 1)`.

**Proof sketch.** `2 ^ (e ℓ) = (2 ^ ℓ) ^ e ≤ (2 (m + 1)) ^ e` (`two_pow_ell_le`). -/
lemma nV_le (K c₀ m : ℕ) :
    nV K c₀ m ≤ 2 ^ (K + 2) * 2 ^ (K * (c₀ + 1)) * (m + 1) ^ (K * (c₀ + 1)) := by
  unfold nV expo
  rw [pow_add, mul_comm (K * (c₀ + 1)) (ell m), pow_mul]
  have h := Nat.pow_le_pow_left (two_pow_ell_le m) (K * (c₀ + 1))
  rw [mul_pow] at h
  calc (2 ^ ell m) ^ (K * (c₀ + 1)) * 2 ^ (K + 2)
      ≤ 2 ^ (K * (c₀ + 1)) * (m + 1) ^ (K * (c₀ + 1)) * 2 ^ (K + 2) :=
        Nat.mul_le_mul_right _ h
    _ = _ := by ring

/-! ## The graph -/

variable (N : FinNDTM Bool)

/-- **The configuration-graph edge relation on vertex numbers** (radius `s`): `0 → c + 2`
for an initial code `c`, `c + 2 → 1` for an accepting code `c`, `c + 2 → c' + 2` for a step
pair `(c, c')`. [AB09, §4.3, proof of Theorem 4.18: the configuration graph `G_{N,x}`, with
the source and target vertices made explicit] -/
def Edge (x : List Bool) (s u v : ℕ) : Prop :=
  (u = 0 ∧ 2 ≤ v ∧ pairEncode x (pairEncode (Nat.bits (v - 2)) (Nat.bits s)) ∈ initLang N) ∨
  (2 ≤ u ∧ v = 1 ∧ pairEncode x (pairEncode (Nat.bits (u - 2)) (Nat.bits s)) ∈ acceptLang N) ∨
  (2 ≤ u ∧ 2 ≤ v ∧ StepRel N x s (u - 2) (v - 2))

/-- The row-major adjacency word of `Edge` on the vertices below `n`. -/
noncomputable def adjWordE (x : List Bool) (s n : ℕ) : List Bool :=
  (List.range (n * n)).map fun k => @decide (Edge N x s (k / n) (k % n)) (Classical.dec _)

/-- The adjacency word has `n²` letters. -/
lemma length_adjWordE (x : List Bool) (s n : ℕ) : (adjWordE N x s n).length = n * n := by
  simp [adjWordE]

/-- The letter of the adjacency word at `k < n²` is the edge bit of `(k / n, k % n)`. -/
lemma adjWordE_getD (x : List Bool) (s n k : ℕ) (hk : k < n * n) :
    (adjWordE N x s n).getD k false = @decide (Edge N x s (k / n) (k % n)) (Classical.dec _) := by
  simp [adjWordE, List.getD_eq_getElem?_getD, hk]

/-- The raw edge relation of the adjacency word is `Edge` below `n`.

**Proof sketch.** `rawEdge n w u v` reads letter `u n + v` of `w` for `u, v < n`; that index
is below `n²`, so the letter is the edge bit of `((u n + v) / n, (u n + v) % n) = (u, v)`
(`adjWordE_getD`), in both directions. -/
lemma rawEdge_adjWordE (x : List Bool) (s n u v : ℕ) :
    rawEdge n (adjWordE N x s n) u v ↔ u < n ∧ v < n ∧ Edge N x s u v := by
  unfold rawEdge
  constructor
  · rintro ⟨hu, hv, h⟩
    have hk : u * n + v < n * n := by nlinarith
    rw [adjWordE_getD N x s n _ hk] at h
    have e1 : (u * n + v) / n = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have e2 : (u * n + v) % n = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    rw [e1, e2] at h
    exact ⟨hu, hv, @of_decide_eq_true _ (Classical.dec _) h⟩
  · rintro ⟨hu, hv, h⟩
    have hk : u * n + v < n * n := by nlinarith
    refine ⟨hu, hv, ?_⟩
    rw [adjWordE_getD N x s n _ hk]
    have e1 : (u * n + v) / n = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have e2 : (u * n + v) % n = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    rw [e1, e2]
    exact @decide_eq_true _ (Classical.dec _) h

/-! ## The reduction -/

/-- **The reduction** [AB09, Theorem 4.18]: `x` maps to the raw `PATH` instance on
`n = nV (codeK N) c₀ |x|` vertices with adjacency word `adjWordE` at radius `c₀ ℓ`, source `0`
and target `1`. -/
noncomputable def red (c₀ : ℕ) (x : List Bool) : List Bool :=
  pathRaw (nV (codeK N) c₀ x.length)
    (adjWordE N x (c₀ * ell x.length) (nV (codeK N) c₀ x.length)) 0 1

/-- **Correctness of the reduction** [AB09, Theorem 4.18]: if `N` decides `L` in space
`c₀ · logSpace`, then `x ∈ L` iff the target `1` is reachable from the source `0` in the
graph of `red x`.

**Proof sketch.** (⇒) The bridge lemma at radius `s = c₀ ℓ ≥ c₀ logSpace |x|` gives a chain
of codes `c₀', …, c_t` from the initial code through step pairs to an accepting code, all
below `2 ^ (K (s + logSpace |x| + 1)) ≤ 2 ^ (E - 2)`; so `0, c₀' + 2, …, c_t + 2, 1` is a
path of vertices below `n = 2 ^ E`. (⇐) The output determines its graph (the pairing is
injective). By induction along a path to `1`: from a vertex `c + 2` there is a step path from
`c` to an accepting code, and from `0` a first edge to an initial code `c`; so there is a
step path from an initial to an accepting code, which gives membership
(`mem_of_codePath`). -/
theorem red_mem_iff {L : Language Bool} {c₀ : ℕ}
    (h : N.DecidesInSpace L fun n => c₀ * logSpace n) (x : List Bool) :
    x ∈ L ↔ red N c₀ x ∈ pathRawLang := by
  set n := nV (codeK N) c₀ x.length with hn
  set s := c₀ * ell x.length with hs
  have h4 := four_le_nV (codeK N) c₀ x.length
  constructor
  · intro hx
    obtain ⟨t, c, -, hinit, hstep, hacc, hlt⟩ :=
      (mem_iff_codeChain h x s (Nat.mul_le_mul_left _ (logSpace_le_ell _))).mp hx
    -- every code is a vertex
    have hW : ∀ i ≤ t, c i + 2 < n := by
      intro i hi
      have e1 := hlt i hi
      have e2 : codeK N * (s + logSpace x.length + 1) + 2 ≤ expo (codeK N) c₀ x.length := by
        have := logSpace_le_ell x.length
        simp only [expo, hs]
        nlinarith
      have e3 : 2 ^ (codeK N * (s + logSpace x.length + 1)) * 4 ≤ n := by
        rw [hn, nV, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) e2
      have e4 : 1 ≤ 2 ^ (codeK N * (s + logSpace x.length + 1)) := Nat.one_le_two_pow
      omega
    refine ⟨n, adjWordE N x s n, 0, 1, length_adjWordE N x s n, by omega, by omega, rfl, ?_⟩
    have hchain : ∀ j ≤ t, Relation.ReflTransGen (rawEdge n (adjWordE N x s n))
        (c 0 + 2) (c j + 2) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih =>
        intro hj
        refine (ih (by omega)).tail ((rawEdge_adjWordE N x s n _ _).mpr
          ⟨hW j (by omega), hW (j + 1) hj, Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)⟩)
        simpa [stepRel_iff_mem] using hstep j (by omega)
    have first : rawEdge n (adjWordE N x s n) 0 (c 0 + 2) :=
      (rawEdge_adjWordE N x s n _ _).mpr ⟨by omega, hW 0 (by omega),
        Or.inl ⟨rfl, by omega, by simpa using hinit⟩⟩
    have last : rawEdge n (adjWordE N x s n) (c t + 2) 1 :=
      (rawEdge_adjWordE N x s n _ _).mpr ⟨hW t le_rfl, by omega,
        Or.inr (Or.inl ⟨by omega, rfl, by simpa using hacc⟩)⟩
    exact (Relation.ReflTransGen.head first (hchain t le_rfl)).tail last
  · rintro ⟨n', M', s', t', -, -, -, he, hr⟩
    -- the output determines the graph
    have e := he
    simp only [red, pathRaw] at e
    obtain ⟨e1, e2⟩ := pairEncode_inj e
    obtain ⟨e3, e4⟩ := pairEncode_inj e2
    obtain ⟨e5, e6⟩ := pairEncode_inj e4
    have hn' : n' = n := by simpa using (congrArg List.length e1).symm
    subst hn'
    have hs' : s' = 0 := bits_injective e5.symm
    have ht' : t' = 1 := bits_injective e6.symm
    subst hs' ht'
    rw [← e3] at hr
    -- induction along the path
    have key : ∀ a, Relation.ReflTransGen (rawEdge (nV (codeK N) c₀ x.length)
        (adjWordE N x s (nV (codeK N) c₀ x.length))) a 1 →
        (a = 0 → x ∈ L) ∧ (2 ≤ a → ∃ v, Relation.ReflTransGen (StepRel N x s) (a - 2) v ∧
          pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N) := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨by omega, by omega⟩
      | @head a' b' hab _ ih =>
        obtain ⟨-, -, hE⟩ := (rawEdge_adjWordE N x s _ _ _).mp hab
        rcases hE with ⟨ha0, hb2, hinit⟩ | ⟨ha2, hb1, hacc⟩ | ⟨ha2, hb2, hst⟩
        · refine ⟨fun _ => ?_, by omega⟩
          obtain ⟨v, hp, hacc⟩ := ih.2 hb2
          exact mem_of_codePath h x s (b' - 2) v hinit hp hacc
        · exact ⟨by omega, fun _ => ⟨a' - 2, Relation.ReflTransGen.refl, hacc⟩⟩
        · refine ⟨by omega, fun _ => ?_⟩
          obtain ⟨v, hp, hacc⟩ := ih.2 hb2
          exact ⟨v, Relation.ReflTransGen.head hst hp, hacc⟩
    exact (key 0 hr).1 rfl

/-! ## The output by position -/

/-- **The output length**: `|red x| = 2n² + 2n + 7`. -/
lemma length_red (c₀ : ℕ) (x : List Bool) :
    (red N c₀ x).length = 2 * (nV (codeK N) c₀ x.length) ^ 2 +
      2 * nV (codeK N) c₀ x.length + 7 := by
  simp only [red, pathRaw, length_pairEncode, length_adjWordE, List.length_replicate,
    Nat.zero_bits, Nat.one_bits, List.length_nil, List.length_singleton]
  ring

/-- **The output length is polynomial** in the input length.

**Proof sketch.** `n ≤ D (m + 1) ^ e` (`nV_le`), so `2n² + 2n + 7 ≤ (2D² + 2D + 7)(m + 1)^{2e}`. -/
lemma length_red_le (c₀ : ℕ) :
    ∃ C c : ℕ, ∀ x : List Bool, (red N c₀ x).length ≤ C * (x.length + 1) ^ c := by
  set e := codeK N * (c₀ + 1)
  set D := 2 ^ (codeK N + 2) * 2 ^ e
  refine ⟨2 * D ^ 2 + 2 * D + 7, 2 * e, fun x => ?_⟩
  rw [length_red]
  have hn := nV_le (codeK N) c₀ x.length
  set q := (x.length + 1) ^ e
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by omega)
  have hq2 : (x.length + 1) ^ (2 * e) = q ^ 2 := by rw [pow_mul']
  rw [hq2]
  have h1 : nV (codeK N) c₀ x.length ^ 2 ≤ (D * q) ^ 2 := Nat.pow_le_pow_left hn 2
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : D * q ≤ D * q ^ 2 := Nat.mul_le_mul_left _ h2
  have h4 : (D * q) ^ 2 = D ^ 2 * q ^ 2 := by ring
  have h5 : 7 ≤ 7 * q ^ 2 := by nlinarith
  have hD : nV (codeK N) c₀ x.length ≤ D * q := hn
  nlinarith

/-- **The bits of the output** by position, with `n` the vertex count and `k = i - 2n - 2`:
the unary block `1²ⁿ`, the separator `01`, the doubled adjacency word (letter `k` is the edge
bit of `(k/2 / n, k/2 % n)`), and the tail `01 01 1`.

**Proof sketch.** `red x` is `pathRaw` of the unary block and the pair of the adjacency word
with the constant `⟨bits 0, bits 1⟩`, so `pairEncode_getD` splits position `i` into the
doubled unary block (`i < 2n`), the separator `01`, and the doubled pair at `i - (2n + 2)`;
applied once more, the latter splits into the doubled adjacency word (`length_adjWordE`,
letter `k / 2` by `adjWordE_getD`) and the tail past `2n²` (a separator and the constant
word), whose five letters are computed by cases. -/
lemma red_getD (c₀ : ℕ) (x : List Bool) (i : ℕ) :
    (red N c₀ x).getD i false =
      if i < 2 * nV (codeK N) c₀ x.length then true
      else if i = 2 * nV (codeK N) c₀ x.length then false
      else if i = 2 * nV (codeK N) c₀ x.length + 1 then true
      else if i - (2 * nV (codeK N) c₀ x.length + 2) < 2 * nV (codeK N) c₀ x.length ^ 2 then
        @decide (Edge N x (c₀ * ell x.length)
          ((i - (2 * nV (codeK N) c₀ x.length + 2)) / 2 / nV (codeK N) c₀ x.length)
          ((i - (2 * nV (codeK N) c₀ x.length + 2)) / 2 % nV (codeK N) c₀ x.length))
          (Classical.dec _)
      else [false, true, false, true, true].getD
        (i - (2 * nV (codeK N) c₀ x.length + 2) - 2 * nV (codeK N) c₀ x.length ^ 2) false := by
  simp only [red, pathRaw]
  set n := nV (codeK N) c₀ x.length
  rw [pairEncode_getD]
  simp only [List.length_replicate]
  split_ifs with h1 h2 h3 h4
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)]; rfl
  · rfl
  · rfl
  · rw [show i - 2 * n - 2 = i - (2 * n + 2) by omega, pairEncode_getD, length_adjWordE,
      if_pos (by nlinarith), adjWordE_getD N x _ n _ (by
        have : (i - (2 * n + 2)) / 2 < n * n := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith
        exact this)]
  · rw [show i - 2 * n - 2 = i - (2 * n + 2) by omega, pairEncode_getD, length_adjWordE,
      if_neg (by nlinarith)]
    simp only [Nat.zero_bits, Nat.one_bits]
    rw [sq] at h4 ⊢
    obtain ⟨r, hr⟩ : ∃ r, i - (2 * n + 2) = 2 * (n * n) + r := ⟨i - (2 * n + 2) - 2 * (n * n),
      by omega⟩
    rw [hr, show 2 * (n * n) + r - 2 * (n * n) = r by omega]
    rcases r with _ | _ | r
    · simp
    · simp
    · rw [show r + 1 + 1 - 2 = r by omega]
      rcases r with _ | _ | _ | r <;> simp [pairEncode, List.getD_eq_getElem?_getD]

end Complexity.PathHard
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHard
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The register file and the deciders of the `PATH`-reduction query machine

The interface of the query register machine `Complexity.PathHard.A`
(`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine`) of the reduction
`Complexity.PathHard.red` [AB09, Theorem 4.18]: its fifteen named registers, the register
file `Complexity.PathHard.St` with its read/write simp lemmas, bounds and partial-update
identities, the tactic macros `regs`, `sbd`, `stp` (scoped in `Complexity.PathHard`), and the
five deciders it calls — the input bits and length, and the initial-, accepting- and
step-code languages of the decider `N` read through `Complexity.dropIdx` — with their
logspace membership and their answers.

Infrastructure for [AB09, §4.3, Theorem 4.18]; not itself a result of the book.

## Main definitions

* `Complexity.PathHard.St` — the register file; `St.toV`, `St.Bd`.
* `Complexity.PathHard.As`, `Complexity.PathHard.orc` — the deciders and their answers.

## Main results

* `Complexity.PathHard.St.eq_qk`, `Complexity.PathHard.St.eq_yid` — partial updates.
* `Complexity.PathHard.As_mem` — the deciders are logspace.
* `Complexity.PathHard.orc_bit`, `orc_len`, `orc_init`, `orc_acc`, `orc_step` — the
  deciders' answers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg

/-! ## Registers -/

/-- Register `y`: the query length, then the decoding pointer. -/
abbrev rY : Fin 15 := 0
/-- Register `p`: the pair-scan pointer, then the start `2|x| + 2` of the index field. -/
abbrev rP : Fin 15 := 1
/-- Register `x`: the length `|x|`. -/
abbrev rX : Fin 15 := 2
/-- Register `t`: a scratch register. -/
abbrev rT : Fin 15 := 3
/-- Register `c`: the loop counter. -/
abbrev rC : Fin 15 := 4
/-- Register `s`: the radius. -/
abbrev rS : Fin 15 := 5
/-- Register `e`: the vertex exponent `E`. -/
abbrev rE : Fin 15 := 6
/-- Register `n`: `2n = 2 ^ (E + 1)`. -/
abbrev rN : Fin 15 := 7
/-- Register `m`: `2n² = 2 ^ (2E + 1)`. -/
abbrev rM : Fin 15 := 8
/-- Register `k`: the width cap `4n²`. -/
abbrev rK : Fin 15 := 9
/-- Register `q`: the pointer of the width check. -/
abbrev rQ : Fin 15 := 10
/-- Register `i`: the decoded index, then the remaining offset. -/
abbrev rI : Fin 15 := 11
/-- Register `d`: the scratch register of decoding and comparison. -/
abbrev rD : Fin 15 := 12
/-- Register `u`: the source vertex. -/
abbrev rU : Fin 15 := 13
/-- Register `z`: the scratch register of the shift loops. -/
abbrev rZ : Fin 15 := 14

/-- **The register file** of the query machine, by name. -/
@[ext] structure St where
  /-- the query length, then the decoding pointer -/
  y : ℕ
  /-- the pair-scan pointer -/
  p : ℕ
  /-- the length `|x|` -/
  x : ℕ
  /-- a scratch register -/
  t : ℕ
  /-- the loop counter -/
  c : ℕ
  /-- the radius -/
  s : ℕ
  /-- the vertex exponent -/
  e : ℕ
  /-- `2n` -/
  n : ℕ
  /-- `2n²` -/
  m : ℕ
  /-- the width cap -/
  k : ℕ
  /-- the pointer of the width check -/
  q : ℕ
  /-- the index, then the remaining offset -/
  i : ℕ
  /-- the decoding and comparison scratch -/
  d : ℕ
  /-- the source vertex -/
  u : ℕ
  /-- the shift scratch -/
  z : ℕ

namespace St

/-- The register values of a register file. -/
def toV (st : St) : Fin 15 → ℕ :=
  ![st.y, st.p, st.x, st.t, st.c, st.s, st.e, st.n, st.m, st.k, st.q, st.i, st.d, st.u, st.z]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero valuation. -/
lemma toV_zero : (fun _ => 0 : Fin 15 → ℕ) = toV zero := by
  funext r; fin_cases r <;> rfl

/-- Reading register `y`. -/
@[simp] lemma toV_y (st : St) : st.toV rY = st.y := rfl
/-- Reading register `p`. -/
@[simp] lemma toV_p (st : St) : st.toV rP = st.p := rfl
/-- Reading register `x`. -/
@[simp] lemma toV_x (st : St) : st.toV rX = st.x := rfl
/-- Reading register `t`. -/
@[simp] lemma toV_t (st : St) : st.toV rT = st.t := rfl
/-- Reading register `c`. -/
@[simp] lemma toV_c (st : St) : st.toV rC = st.c := rfl
/-- Reading register `s`. -/
@[simp] lemma toV_s (st : St) : st.toV rS = st.s := rfl
/-- Reading register `e`. -/
@[simp] lemma toV_e (st : St) : st.toV rE = st.e := rfl
/-- Reading register `n`. -/
@[simp] lemma toV_n (st : St) : st.toV rN = st.n := rfl
/-- Reading register `m`. -/
@[simp] lemma toV_m (st : St) : st.toV rM = st.m := rfl
/-- Reading register `k`. -/
@[simp] lemma toV_k (st : St) : st.toV rK = st.k := rfl
/-- Reading register `q`. -/
@[simp] lemma toV_q (st : St) : st.toV rQ = st.q := rfl
/-- Reading register `i`. -/
@[simp] lemma toV_i (st : St) : st.toV rI = st.i := rfl
/-- Reading register `d`. -/
@[simp] lemma toV_d (st : St) : st.toV rD = st.d := rfl
/-- Reading register `u`. -/
@[simp] lemma toV_u (st : St) : st.toV rU = st.u := rfl
/-- Reading register `z`. -/
@[simp] lemma toV_z (st : St) : st.toV rZ = st.z := rfl

/-- Writing register `y`. -/
@[simp] lemma upd_y (st : St) (v : ℕ) : Function.update st.toV rY v = toV { st with y := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `p`. -/
@[simp] lemma upd_p (st : St) (v : ℕ) : Function.update st.toV rP v = toV { st with p := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `x`. -/
@[simp] lemma upd_x (st : St) (v : ℕ) : Function.update st.toV rX v = toV { st with x := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `t`. -/
@[simp] lemma upd_t (st : St) (v : ℕ) : Function.update st.toV rT v = toV { st with t := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `c`. -/
@[simp] lemma upd_c (st : St) (v : ℕ) : Function.update st.toV rC v = toV { st with c := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `s`. -/
@[simp] lemma upd_s (st : St) (v : ℕ) : Function.update st.toV rS v = toV { st with s := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `e`. -/
@[simp] lemma upd_e (st : St) (v : ℕ) : Function.update st.toV rE v = toV { st with e := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `n`. -/
@[simp] lemma upd_n (st : St) (v : ℕ) : Function.update st.toV rN v = toV { st with n := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `m`. -/
@[simp] lemma upd_m (st : St) (v : ℕ) : Function.update st.toV rM v = toV { st with m := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `k`. -/
@[simp] lemma upd_k (st : St) (v : ℕ) : Function.update st.toV rK v = toV { st with k := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `q`. -/
@[simp] lemma upd_q (st : St) (v : ℕ) : Function.update st.toV rQ v = toV { st with q := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `i`. -/
@[simp] lemma upd_i (st : St) (v : ℕ) : Function.update st.toV rI v = toV { st with i := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `d`. -/
@[simp] lemma upd_d (st : St) (v : ℕ) : Function.update st.toV rD v = toV { st with d := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `u`. -/
@[simp] lemma upd_u (st : St) (v : ℕ) : Function.update st.toV rU v = toV { st with u := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `z`. -/
@[simp] lemma upd_z (st : St) (v : ℕ) : Function.update st.toV rZ v = toV { st with z := v } := by
  funext r; fin_cases r <;> rfl

/-- All registers of the file are at most `B`. -/
def Bd (B : ℕ) (st : St) : Prop :=
  st.y ≤ B ∧ st.p ≤ B ∧ st.x ≤ B ∧ st.t ≤ B ∧ st.c ≤ B ∧ st.s ≤ B ∧ st.e ≤ B ∧ st.n ≤ B ∧
    st.m ≤ B ∧ st.k ≤ B ∧ st.q ≤ B ∧ st.i ≤ B ∧ st.d ≤ B ∧ st.u ≤ B ∧ st.z ≤ B

/-- A bounded register file has bounded register values. -/
lemma Bd.toV {B : ℕ} {st : St} (h : st.Bd B) : ∀ r, st.toV r ≤ B := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  intro r; fin_cases r <;> assumption

/-- A register file whose values are bounded is bounded. -/
lemma Bd.of_toV {B : ℕ} {st : St} (h : ∀ r, st.toV r ≤ B) : st.Bd B :=
  ⟨h rY, h rP, h rX, h rT, h rC, h rS, h rE, h rN, h rM, h rK, h rQ, h rI, h rD, h rU, h rZ⟩

/-- A valuation agreeing with a register file outside `q` and `k` is that file with `q` and
`k` replaced. -/
lemma eq_qk (st : St) (v : Fin 15 → ℕ) (h : ∀ r, r ≠ rQ → r ≠ rK → v r = st.toV r) :
    v = toV { st with q := v rQ, k := v rK } := by
  funext r
  fin_cases r
  · show v rY = st.y; exact (h rY (by decide) (by decide)).trans (St.toV_y st)
  · show v rP = st.p; exact (h rP (by decide) (by decide)).trans (St.toV_p st)
  · show v rX = st.x; exact (h rX (by decide) (by decide)).trans (St.toV_x st)
  · show v rT = st.t; exact (h rT (by decide) (by decide)).trans (St.toV_t st)
  · show v rC = st.c; exact (h rC (by decide) (by decide)).trans (St.toV_c st)
  · show v rS = st.s; exact (h rS (by decide) (by decide)).trans (St.toV_s st)
  · show v rE = st.e; exact (h rE (by decide) (by decide)).trans (St.toV_e st)
  · show v rN = st.n; exact (h rN (by decide) (by decide)).trans (St.toV_n st)
  · show v rM = st.m; exact (h rM (by decide) (by decide)).trans (St.toV_m st)
  · show v rK = v rK; rfl
  · show v rQ = v rQ; rfl
  · show v rI = st.i; exact (h rI (by decide) (by decide)).trans (St.toV_i st)
  · show v rD = st.d; exact (h rD (by decide) (by decide)).trans (St.toV_d st)
  · show v rU = st.u; exact (h rU (by decide) (by decide)).trans (St.toV_u st)
  · show v rZ = st.z; exact (h rZ (by decide) (by decide)).trans (St.toV_z st)

/-- A valuation agreeing with a register file outside `y`, `i` and `d` is that file with
`y`, `i` and `d` replaced. -/
lemma eq_yid (st : St) (v : Fin 15 → ℕ) (h : ∀ r, r ≠ rY → r ≠ rI → r ≠ rD → v r = st.toV r) :
    v = toV { st with y := v rY, i := v rI, d := v rD } := by
  funext r
  fin_cases r
  · show v rY = v rY; rfl
  · show v rP = st.p; exact (h rP (by decide) (by decide) (by decide)).trans (St.toV_p st)
  · show v rX = st.x; exact (h rX (by decide) (by decide) (by decide)).trans (St.toV_x st)
  · show v rT = st.t; exact (h rT (by decide) (by decide) (by decide)).trans (St.toV_t st)
  · show v rC = st.c; exact (h rC (by decide) (by decide) (by decide)).trans (St.toV_c st)
  · show v rS = st.s; exact (h rS (by decide) (by decide) (by decide)).trans (St.toV_s st)
  · show v rE = st.e; exact (h rE (by decide) (by decide) (by decide)).trans (St.toV_e st)
  · show v rN = st.n; exact (h rN (by decide) (by decide) (by decide)).trans (St.toV_n st)
  · show v rM = st.m; exact (h rM (by decide) (by decide) (by decide)).trans (St.toV_m st)
  · show v rK = st.k; exact (h rK (by decide) (by decide) (by decide)).trans (St.toV_k st)
  · show v rQ = st.q; exact (h rQ (by decide) (by decide) (by decide)).trans (St.toV_q st)
  · show v rI = v rI; rfl
  · show v rD = v rD; rfl
  · show v rU = st.u; exact (h rU (by decide) (by decide) (by decide)).trans (St.toV_u st)
  · show v rZ = st.z; exact (h rZ (by decide) (by decide) (by decide)).trans (St.toV_z st)

end St

/-- Normalize register reads and writes of named register files. -/
scoped syntax "regs" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? :
  tactic
scoped macro_rules
  | `(tactic| regs $[$loc:location]?) =>
    `(tactic| simp only [St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s, St.toV_e,
      St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z] $[$loc]?)
  | `(tactic| regs [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s, St.toV_e,
      St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z, $args,*] $[$loc]?)

set_option hygiene false in
/-- Close a bound on a register file. -/
scoped macro "sbd" : tactic => `(tactic| (simp only [St.Bd] at hbd ⊢ <;> omega))

set_option hygiene false in
/-- Normalize one step of the query machine (after `step_of`/`stepH_of`). -/
scoped macro "stp" : tactic =>
  `(tactic| simp only [astep, A, St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s,
      St.toV_e, St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z, ↓reduceIte,
      Nat.add_one_ne_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, one_ne_zero,
      Nat.zero_add, Nat.add_zero, Bool.false_eq_true, ↓reduceDIte])

/-! ## The deciders -/

/-- **The deciders**: the input bits and length (`0`, `1`), and the initial-, accepting- and
step-code languages of `N` read through `dropIdx` (`2`, `3`, `4`). -/
def As (N : FinNDTM Bool) : Fin 5 → Language Bool :=
  ![inputBitLang, inputLenLang, {z | dropIdx z ∈ Codec.initLang N},
    {z | dropIdx z ∈ Codec.acceptLang N}, {z | dropIdx z ∈ Codec.stepLang N}]

/-- The deciders are logspace: the code languages are (`Complexity.Codec.initLang_mem`, …),
and `dropIdx` is implicitly logspace computable. -/
lemma As_mem (N : FinNDTM Bool) (j : Fin 5) : As N j ∈ LOGSPACE := by
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.initLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.acceptLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.stepLang_mem

/-- The oracle answering the machine's calls. -/
noncomputable def orc (N : FinNDTM Bool) : Fin 5 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (As N j : Set (List Bool)) V

/-- Decider `0` reads the query. -/
lemma orc_bit (N : FinNDTM Bool) (y : List Bool) (p : ℕ) :
    orc N 0 (pairEncode y (Nat.bits p)) = y.getD p false := by
  simp only [orc, As, Matrix.cons_val_zero]
  exact indicator_inputBitLang y p

/-- Decider `1` compares with the query length. -/
lemma orc_len (N : FinNDTM Bool) (y : List Bool) (p : ℕ) :
    orc N 1 (pairEncode y (Nat.bits p)) = decide (p < y.length) := by
  simp only [orc, As, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact indicator_inputLenLang y p

/-- Decider `2` answers the initial-code language on `⟨x, ⟨bits v, bits s⟩⟩`. -/
lemma orc_init (N : FinNDTM Bool) (x β : List Bool) (v s : ℕ) :
    orc N 2 (pairEncode (pairEncode x β) (pairEncode (Nat.bits v) (Nat.bits s))) =
      @decide (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.initLang N)
        (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode])

/-- Decider `3` answers the accepting-code language on `⟨x, ⟨bits u, bits s⟩⟩`. -/
lemma orc_acc (N : FinNDTM Bool) (x β : List Bool) (u s : ℕ) :
    orc N 3 (pairEncode (pairEncode x β) (pairEncode (Nat.bits u) (Nat.bits s))) =
      @decide (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.acceptLang N)
        (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode])

/-- Decider `4` answers the step relation. -/
lemma orc_step (N : FinNDTM Bool) (x β : List Bool) (u v s : ℕ) :
    orc N 4 (pairEncode (pairEncode x β)
        (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) =
      @decide (Codec.StepRel N x s u v) (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.stepRel_iff_mem])

end Complexity.PathHard
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic walk machine for `PATH`

[AB09, §4.1.2]: the machine `Complexity.LogProg.pathA`, a nondeterministic abstract register
machine with nine registers and the two input-access deciders
(`Complexity.inputBitLang`, `Complexity.inputLenLang`): it checks the unary prefix and the
matrix shape, guesses `s` and `t` and checks them against the input, then walks from `s`,
guessing each next vertex and reading its matrix bit, for at most `n` steps. This file
defines the machine and its register file and proves the walk loop correct
(`Complexity.LogProg.ps_walk`) in the continuation semantics of
`TCSlib.Complexity.SpaceComplexity.Machines.NARMKit`; the input checks and the assembly are in
`TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof`.

## Main definitions

* `Complexity.LogProg.PathLabel`, `Complexity.LogProg.pathA` — the machine.
* `Complexity.LogProg.pathAs`, `Complexity.LogProg.pathOr` — its deciders.
* `Complexity.LogProg.PReg` — its register file, by name; `Complexity.LogProg.PS` — the
  semantics at a label and register file.

## Main results

* `Complexity.LogProg.pathA_npreS` — the machine meets the syntactic preconditions.
* `Complexity.LogProg.ps_index` — the matrix position of an edge.
* `Complexity.LogProg.ps_walk` — the walk loop. [AB09, §4.1.2]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2.)
-/

namespace Complexity.LogProg

open Turing

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The labels of the walk machine: the unary scan (`u*`), the matrix scan (`m*`), the guess
and check of the source (`s*`) and of the target (`t*`), the walk (`w*`), the three
add-twice loops of the index computation (`ak k`, `ak₁ k`, `ak₂ k`, `ak₃ k`), and the two
answers. -/
inductive PathLabel
  | u0 | u1 | u2 | u3 | u4 | u5 | u6 | u7
  | m0 | mr | m1 | m2 | m3 | m4 | m5 | m7 | m8 | m9 | m10 | m11 | ms | m12
  | sg | sc | sm | scp | sbp | stt | sz1 | sz2 | sz3 | sz4 | sod | so1 | so2 | so3
  | se1 | se2 | se3 | sad | shf
  | tg | tc | tm | tcp | tbp | ttt | tend | tlen | tpar | tone | tzero | tad | thf
  | w0 | w1 | w2 | wg | wc | wm | wcp | wcb | wi1 | wi2 | wca | wrow | wrc | wrn | wcc
  | wrd | wcl | wcy | wby | wst
  | ak (k : Fin 3) | ak₁ (k : Fin 3) | ak₂ (k : Fin 3) | ak₃ (k : Fin 3)
  | acc | rej
  deriving DecidableEq, Fintype

open PathLabel

/-- The register added twice by add-twice loop `k`: `n`, `n`, the guessed vertex. -/
def akY : Fin 3 → Fin 9 := ![1, 1, 8]

/-- The exit of add-twice loop `k`. -/
def akEx : Fin 3 → PathLabel := ![wi1, wrn, wrd]

/-- **The walk machine** [AB09, §4.1.2]. Registers: `0` the input pointer `p`, `1` the vertex
count `n`, `2` and `3` counters `a`, `b`, `4` the source and then the current vertex, `5` the
target, `6` a scratch copy, `7` the step count, `8` the guessed next vertex. Deciders: `0`
reads an input bit, `1` compares with the input length.

* Unary scan: count the aligned `11` pairs into `n`, then expect `01`; `p = 2n + 2`.
* Matrix scan: aligned data pairs `00`/`11` counted by row `a` and column `b` (reset at `n`),
  inside the input; the separator `01` only after exactly `n²` pairs.
* Source and target: guess `s < n` (choose to stop or to increment), check the doubled field
  against the binary digits of `s` (parity and halving of a copy), then the separator;
  likewise `t < n` against the plain suffix, which must end the input.
* Walk: accept if the current vertex is `t`; reject after `n` steps; guess `v < n`, compute
  `p = 2n + 2 + 2(cur · n + v)` by add-twice loops, reject unless the input bit at `p` is `1`,
  move to `v`. -/
def pathA : NARM 9 2 PathLabel
  | u0 => .det (.call 0 .whole [0] u1 u2)
  | u1 => .det (.inc 0 u3)
  | u3 => .det (.call 0 .whole [0] u4 rej)
  | u4 => .det (.inc 0 u5)
  | u5 => .det (.inc 1 u0)
  | u2 => .det (.inc 0 u6)
  | u6 => .det (.call 0 .whole [0] u7 rej)
  | u7 => .det (.inc 0 m0)
  | m0 => .det (.call 1 .whole [0] mr rej)
  | mr => .det (.call 0 .whole [0] m1 m2)
  | m1 => .det (.inc 0 m3)
  | m3 => .det (.call 0 .whole [0] m5 rej)
  | m2 => .det (.inc 0 m4)
  | m4 => .det (.call 0 .whole [0] ms m5)
  | m5 => .det (.jeq 2 1 rej m7)
  | m7 => .det (.inc 0 m8)
  | m8 => .det (.inc 3 m9)
  | m9 => .det (.jeq 3 1 m10 m0)
  | m10 => .det (.clr 3 m11)
  | m11 => .det (.inc 2 m0)
  | ms => .det (.jeq 2 1 m12 rej)
  | m12 => .det (.inc 0 sg)
  | sg => .det (.jeq 4 1 rej sc)
  | sc => .choose scp sm
  | sm => .det (.inc 4 sg)
  | scp => .det (.jeq 6 4 stt sbp)
  | sbp => .det (.inc 6 scp)
  | stt => .det (.jz 6 sz1 sod)
  | sz1 => .det (.call 0 .whole [0] rej sz2)
  | sz2 => .det (.inc 0 sz3)
  | sz3 => .det (.call 0 .whole [0] sz4 rej)
  | sz4 => .det (.inc 0 tg)
  | sod => .det (.jodd 6 so1 se1)
  | so1 => .det (.call 0 .whole [0] so2 rej)
  | so2 => .det (.inc 0 so3)
  | so3 => .det (.call 0 .whole [0] sad rej)
  | se1 => .det (.call 0 .whole [0] rej se2)
  | se2 => .det (.inc 0 se3)
  | se3 => .det (.call 0 .whole [0] rej sad)
  | sad => .det (.inc 0 shf)
  | shf => .det (.half 6 stt)
  | tg => .det (.jeq 5 1 rej tc)
  | tc => .choose tcp tm
  | tm => .det (.inc 5 tg)
  | tcp => .det (.jeq 6 5 ttt tbp)
  | tbp => .det (.inc 6 tcp)
  | ttt => .det (.jz 6 tend tlen)
  | tend => .det (.call 1 .whole [0] rej w0)
  | tlen => .det (.call 1 .whole [0] tpar rej)
  | tpar => .det (.jodd 6 tone tzero)
  | tone => .det (.call 0 .whole [0] tad rej)
  | tzero => .det (.call 0 .whole [0] rej tad)
  | tad => .det (.inc 0 thf)
  | thf => .det (.half 6 ttt)
  | w0 => .det (.jeq 4 5 acc w1)
  | w1 => .det (.jeq 7 1 rej w2)
  | w2 => .det (.clr 8 wg)
  | wg => .det (.jeq 8 1 rej wc)
  | wc => .choose wcp wm
  | wm => .det (.inc 8 wg)
  | wcp => .det (.clr 0 wcb)
  | wcb => .det (.clr 3 (ak 0))
  | ak k => .det (.jeq 3 (akY k) (akEx k) (ak₁ k))
  | ak₁ k => .det (.inc 0 (ak₂ k))
  | ak₂ k => .det (.inc 0 (ak₃ k))
  | ak₃ k => .det (.inc 3 (ak k))
  | wi1 => .det (.inc 0 wi2)
  | wi2 => .det (.inc 0 wca)
  | wca => .det (.clr 2 wrow)
  | wrow => .det (.jeq 2 4 wcc wrc)
  | wrc => .det (.clr 3 (ak 1))
  | wrn => .det (.inc 2 wrow)
  | wcc => .det (.clr 3 (ak 2))
  | wrd => .det (.call 0 .whole [0] wcl rej)
  | wcl => .det (.clr 4 wcy)
  | wcy => .det (.jeq 4 8 wst wby)
  | wby => .det (.inc 4 wcy)
  | wst => .det (.inc 7 w0)
  | acc => .det (.ret true)
  | rej => .det (.ret false)

/-- **The machine meets the syntactic preconditions**: its comparisons are of distinct
registers and its calls have one argument. -/
lemma pathA_npreS (x : List Bool) (a : AConf 9 PathLabel) : NPreS pathA x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l <;> simp [NPreS, PreS, NARM.detPart, pathA]
    all_goals (rename_i k; fin_cases k <;> simp [akY])

/-- The deciders of the walk machine: the input bit and input length languages. -/
def pathAs : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- The deciders' answers. -/
noncomputable abbrev pathOr : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (pathAs j : Set (List Bool)) V

/-- Decider `0` reads an input bit. -/
lemma pathOr_bit (x : List Bool) (i : ℕ) :
    pathOr 0 (pairEncode x (Nat.bits i)) = x.getD i false := by
  show MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  exact indicator_inputBitLang x i

/-- Decider `1` compares with the input length. -/
lemma pathOr_len (x : List Bool) (i : ℕ) :
    pathOr 1 (pairEncode x (Nat.bits i)) = decide (i < x.length) := by
  show MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact indicator_inputLenLang x i

/-- The deciders are in `L`. -/
lemma pathAs_mem (j : Fin 2) : pathAs j ∈ LOGSPACE := by
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem

/-- The register file of the walk machine, by name. -/
@[ext] structure PReg where
  /-- the input pointer (register `0`) -/
  p : ℕ
  /-- the vertex count (register `1`) -/
  n : ℕ
  /-- the row counter (register `2`) -/
  a : ℕ
  /-- the column counter (register `3`) -/
  b : ℕ
  /-- the source, then the current vertex (register `4`) -/
  s : ℕ
  /-- the target (register `5`) -/
  t : ℕ
  /-- the scratch copy (register `6`) -/
  tmp : ℕ
  /-- the step count (register `7`) -/
  st : ℕ
  /-- the guessed next vertex (register `8`) -/
  nx : ℕ

/-- The register values of a register file. -/
def PReg.v (σ : PReg) : Fin 9 → ℕ := ![σ.p, σ.n, σ.a, σ.b, σ.s, σ.t, σ.tmp, σ.st, σ.nx]

/-- Every register of a register file is at most `B`. -/
def PReg.Le (σ : PReg) (B : ℕ) : Prop :=
  σ.p ≤ B ∧ σ.n ≤ B ∧ σ.a ≤ B ∧ σ.b ≤ B ∧ σ.s ≤ B ∧ σ.t ≤ B ∧ σ.tmp ≤ B ∧ σ.st ≤ B ∧ σ.nx ≤ B

/-- The register-bound guard from the named bounds. -/
lemma PReg.reg {σ : PReg} {B : ℕ} (h : σ.Le B) (l : Option PathLabel) (res : Option Bool) :
    RegLe 9 PathLabel B (l, σ.v, res) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  intro r
  fin_cases r <;> assumption

section PRegSimp

variable (σ : PReg) (z : ℕ)

/-- Register `0` is the input pointer. -/
@[simp] lemma PReg.v_0 : σ.v 0 = σ.p := rfl
/-- Register `1` is the vertex count. -/
@[simp] lemma PReg.v_1 : σ.v 1 = σ.n := rfl
/-- Register `2` is the row counter. -/
@[simp] lemma PReg.v_2 : σ.v 2 = σ.a := rfl
/-- Register `3` is the column counter. -/
@[simp] lemma PReg.v_3 : σ.v 3 = σ.b := rfl
/-- Register `4` is the current vertex. -/
@[simp] lemma PReg.v_4 : σ.v 4 = σ.s := rfl
/-- Register `5` is the target. -/
@[simp] lemma PReg.v_5 : σ.v 5 = σ.t := rfl
/-- Register `6` is the scratch copy. -/
@[simp] lemma PReg.v_6 : σ.v 6 = σ.tmp := rfl
/-- Register `7` is the step count. -/
@[simp] lemma PReg.v_7 : σ.v 7 = σ.st := rfl
/-- Register `8` is the guessed vertex. -/
@[simp] lemma PReg.v_8 : σ.v 8 = σ.nx := rfl

/-- Writing register `0` writes the input pointer. -/
@[simp] lemma PReg.u_0 : Function.update σ.v 0 z = { σ with p := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `1` writes the vertex count. -/
@[simp] lemma PReg.u_1 : Function.update σ.v 1 z = { σ with n := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `2` writes the row counter. -/
@[simp] lemma PReg.u_2 : Function.update σ.v 2 z = { σ with a := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `3` writes the column counter. -/
@[simp] lemma PReg.u_3 : Function.update σ.v 3 z = { σ with b := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `4` writes the current vertex. -/
@[simp] lemma PReg.u_4 : Function.update σ.v 4 z = { σ with s := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `5` writes the target. -/
@[simp] lemma PReg.u_5 : Function.update σ.v 5 z = { σ with t := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `6` writes the scratch copy. -/
@[simp] lemma PReg.u_6 : Function.update σ.v 6 z = { σ with tmp := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `7` writes the step count. -/
@[simp] lemma PReg.u_7 : Function.update σ.v 7 z = { σ with st := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `8` writes the guessed vertex. -/
@[simp] lemma PReg.u_8 : Function.update σ.v 8 z = { σ with nx := z }.v := by
  funext r; fin_cases r <;> rfl

end PRegSimp

open PathLabel

/-- The semantics of the walk machine at label `l` with register file `σ`, registers
bounded by `B`. -/
abbrev PS (x : List Bool) (B : ℕ) (l : PathLabel) (σ : PReg) (P : Prop) : Prop :=
  NSem pathA pathOr x (RegLe 9 PathLabel B) (some l, σ.v, none) P

variable {x : List Bool} {B : ℕ}

/-- Change the register file to an equal one. -/
lemma PS.of_eq {l : PathLabel} {σ σ' : PReg} {P : Prop} (h : σ = σ') (hp : PS x B l σ' P) :
    PS x B l σ P := h ▸ hp

namespace PathWalkTac

/-- Normalize reads and updates of a named register file of the walk machine. -/
scoped macro "pw_regs" : tactic => `(tactic| simp only [PReg.v_0, PReg.v_1, PReg.v_2, PReg.v_3,
  PReg.v_4, PReg.v_5, PReg.v_6, PReg.v_7, PReg.v_8, PReg.u_0, PReg.u_1, PReg.u_2, PReg.u_3,
  PReg.u_4, PReg.u_5, PReg.u_6, PReg.u_7, PReg.u_8])

/-- Prove a register bound of the walk machine by linear arithmetic. -/
scoped macro "pw_le" : tactic => `(tactic| (simp only [PReg.Le] at *; omega))

/-- Prove an equality of register files field by field. -/
scoped macro "pw_ext" : tactic => `(tactic| (ext <;> dsimp only <;> omega))

/-- Prove an equality of register files field by field, simplifying first. -/
scoped macro "pw_ext'" : tactic => `(tactic| (ext <;> (try simp) <;> (try omega)))

end PathWalkTac

open PathWalkTac

/-- **The row loop** of the index computation: from row `a ≤ s` with the pointer at the
start of row `a`, the machine reaches the start of row `s`.

**Proof sketch.** Induction on `s - a`: at `a = s` the loop exits; otherwise it clears the
column counter, adds `2n` to the pointer (`nsem_addTwice`) and increments the row. All
pointer values stay below the start of row `s`, inside the input. -/
lemma ps_row (hB : 2 * x.length + 2 ≤ B) (P : Prop) (σ : PReg) (hσ : σ.Le B)
    (hi : σ.a ≤ σ.s) (hs : σ.s < σ.n) (hp : σ.p = 2 * σ.n + 2 + 2 * (σ.a * σ.n))
    (hb : σ.b ≤ σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length)
    (hK : ∀ b', b' ≤ σ.n →
      PS x B wcc { σ with a := σ.s, p := 2 * σ.n + 2 + 2 * (σ.s * σ.n), b := b' } P) :
    PS x B wrow σ P := by
  suffices H : ∀ d (σ : PReg), σ.s - σ.a = d → σ.Le B → σ.a ≤ σ.s → σ.s < σ.n →
      σ.p = 2 * σ.n + 2 + 2 * (σ.a * σ.n) → σ.b ≤ σ.n →
      2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length →
      (∀ b', b' ≤ σ.n →
        PS x B wcc { σ with a := σ.s, p := 2 * σ.n + 2 + 2 * (σ.s * σ.n), b := b' } P) →
      PS x B wrow σ P from H _ σ rfl hσ hi hs hp hb hm hK
  intro d
  induction d with
  | zero =>
    intro σ hd hσ hi hs hp hb hm hK
    have he : σ.a = σ.s := by omega
    have he' : σ.a * σ.n = σ.s * σ.n := by rw [he]
    refine NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he) ?_
    exact PS.of_eq (by ext <;> simp <;> omega) (hK σ.b hb)
  | succ d ih =>
    intro σ hd hσ hi hs hp hb hm hK
    have hne : σ.a ≠ σ.s := by omega
    have h1 : (σ.a + 1) * σ.n ≤ σ.s * σ.n := Nat.mul_le_mul_right _ (by omega)
    have h2 : (σ.s + 1) * σ.n ≤ σ.n * σ.n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1 h2
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using hne) ?_
    refine NSem.clr rfl (PReg.reg hσ _ _) ?_
    pw_regs
    refine nsem_addTwice pathA pathOr x B 3 1 0 (by decide) (by decide) (by decide)
      (ak 1) (ak₁ 1) (ak₂ 1) (ak₃ 1) wrn rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
      (by simp) (by simp; omega) ?_
    pw_regs
    refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
    pw_regs
    refine PS.of_eq (σ' := { σ with a := σ.a + 1, p := σ.p + 2 * σ.n, b := σ.n })
      (by ext <;> simp) ?_
    exact ih _ (by dsimp only; omega) (by pw_le) (by dsimp only; omega) hs
      (by dsimp only; rw [Nat.add_mul, Nat.one_mul]; omega) le_rfl hm hK

/-- **The index computation**: the machine sets the pointer to the matrix position
`2n + 2 + 2(s · n + v)` of the edge from the current vertex `s` to the guessed vertex `v`.

**Proof sketch.** Clear the pointer, add `2n` (`nsem_addTwice`) and `2` to reach the
matrix, walk `s` rows (`ps_row`), then add `2v` (`nsem_addTwice`); the final position is
below `2n + 2 + 2n²`, inside the input (`rowMajor_lt`). -/
lemma ps_index (hB : 2 * x.length + 2 ≤ B) (P : Prop) (σ : PReg) (hσ : σ.Le B)
    (hs : σ.s < σ.n) (hj : σ.nx < σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length)
    (hK : PS x B wrd
      { σ with p := 2 * σ.n + 2 + 2 * (σ.s * σ.n + σ.nx), a := σ.s, b := σ.nx } P) :
    PS x B wcp σ P := by
  have hidx := rowMajor_lt hs hj
  have h0 : σ.s * σ.n ≤ σ.n * σ.n := by omega
  refine NSem.clr rfl (PReg.reg hσ _ _) ?_
  pw_regs
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine nsem_addTwice pathA pathOr x B 3 1 0 (by decide) (by decide) (by decide)
    (ak 0) (ak₁ 0) (ak₂ 0) (ak₃ 0) wi1 rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
    (by simp) (by simp; omega) ?_
  pw_regs
  refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine ps_row hB P _ (by pw_le) (by simp) (by simpa using hs) (by dsimp only; omega) (by simp)
    (by simpa using hm) fun b' hb' => ?_
  simp only at hb' ⊢
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine nsem_addTwice pathA pathOr x B 3 8 0 (by decide) (by decide) (by decide)
    (ak 2) (ak₁ 2) (ak₂ 2) (ak₃ 2) wrd rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
    (by simp) (by simp; omega) ?_
  pw_regs
  exact PS.of_eq (by pw_ext') hK

/-- **The walk loop** [AB09, §4.1.2]: from the current vertex `s` after `st ≤ n` steps,
some branch accepts iff `t` is reachable from `s` within `n - st` edges; every branch
terminates.

**Proof sketch.** Induction on `n - st`. At `s = t` the machine accepts; at `st = n` it
rejects; otherwise it guesses `v < n` (`nsem_guess`), computes the matrix position
(`ps_index`), rejects unless the edge bit is `1`, copies `v` into the current vertex
(`nsem_copy`) and counts the step. -/
theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs : σ.s < σ.n)
    (ht : σ.t < σ.n) (hst : σ.st ≤ σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length) :
    PS x B w0 σ (WalkLe (pathEdge x σ.n) σ.n (σ.n - σ.st) σ.s σ.t) := by
  suffices H : ∀ d (σ : PReg), σ.n - σ.st = d → σ.Le B → σ.s < σ.n → σ.t < σ.n →
      σ.st ≤ σ.n → 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length →
      PS x B w0 σ (WalkLe (pathEdge x σ.n) σ.n d σ.s σ.t) from H _ σ rfl hσ hs ht hst hm
  intro d
  induction d with
  | zero =>
    intro σ hd hσ hs ht hst hm
    by_cases he : σ.s = σ.t
    · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [walkLe_zero_iff, he]
    · refine (NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simp; omega)
          (NSem.ret rfl (PReg.reg hσ _ _)))).congr ?_
      simp only [walkLe_zero_iff, he, Bool.false_eq_true]
  | succ d ih =>
    intro σ hd hσ hs ht hst hm
    by_cases he : σ.s = σ.t
    · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [walkLe_succ_iff_head, he, true_or]
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he) ?_
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simp; omega) ?_
    refine NSem.clr rfl (PReg.reg hσ _ _) ?_
    pw_regs
    refine (nsem_guess pathA pathOr x B 8 1 (by decide) wg wc wm wcp rej rfl rfl rfl rfl
      (fun j => pathEdge x σ.n σ.s j ∧ WalkLe (pathEdge x σ.n) σ.n d j σ.t) _
      (PReg.reg (by pw_le) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
    · simp only [PReg.v_8, PReg.v_1] at hj1 hj2
      pw_regs
      have hidx := rowMajor_lt hs hj2
      refine ps_index hB _ _ (by pw_le) (by simpa using hs) (by simpa using hj2)
        (by simpa using hm) ?_
      simp only
      by_cases hedge : pathEdge x σ.n σ.s j
      · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit]; exact hedge) ?_
        refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        refine nsem_copy pathA pathOr x B 4 8 (by decide) wcy wby wst rfl rfl _ _
          (PReg.reg (by pw_le) none none) (by simp) ?_
        pw_regs
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        let σ' : PReg :=
          ⟨2 * σ.n + 2 + 2 * (σ.s * σ.n + j), σ.n, σ.s, j, j, σ.t, σ.tmp, σ.st + 1, j⟩
        refine PS.of_eq (σ' := σ') (by simp only [σ']) ((ih σ' (by dsimp only [σ']; omega)
          (by simp only [σ', PReg.Le] at hσ ⊢; omega) (by dsimp only [σ']; omega) ht
          (by dsimp only [σ']; omega) hm).congr ?_)
        simp only [σ', hedge, true_and]
      · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit]; simpa [pathEdge] using hedge)
          (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
        simp only [hedge, false_and, Bool.false_eq_true]
    · simp only [PReg.v_8, PReg.v_1, walkLe_succ_iff_head, he, false_or]
      exact ⟨fun ⟨j, _, h⟩ => ⟨j, h.1, h.2⟩, fun ⟨j, h1, h2⟩ => ⟨j, Nat.zero_le _, h1, h2⟩⟩

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Search
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's theorem at the polynomial level: `NPSPACE ⊆ PSPACE`

The Savitch register machine `Complexity.LogProg.SavitchARM.A`, run with the deciders of the
code languages of a nondeterministic polynomial-space decider `N`
(`TCSlib.Complexity.SpaceComplexity.Codec`), decides `N`'s language with registers of
polynomially many binary digits; `Complexity.LogProg.arm_decides_pspace_val` then places the
language in `PSPACE` [AB09, §4.2.1, Theorem 4.14 and its corollary `PSPACE = NPSPACE`].

## Main definitions

* `Complexity.LogProg.SavitchARM.decs`, `Complexity.LogProg.SavitchARM.orcN` — the four
  deciders of the Savitch machine for `N` and their answers.

## Main results

* `Complexity.NSPACE_poly_subset_PSPACE` — `NSPACE (n ^ k + 1) ⊆ PSPACE`.
* `Complexity.NPSPACE_subset_PSPACE` — `NPSPACE ⊆ PSPACE`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- The deciders of the Savitch machine for `N`: `0` the input length, `1` the initial codes,
`2` the accepting codes, `3` the step pairs. -/
def decs (N : FinNDTM Bool) : Fin 4 → Language Bool :=
  ![inputLenLang, Codec.initLang N, Codec.acceptLang N, Codec.stepLang N]

/-- The answers of the deciders of the Savitch machine for `N`. -/
noncomputable def orcN (N : FinNDTM Bool) : Fin 4 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs N j : Set (List Bool)) V

/-- The step relation answered by decider `3` is the code-level step relation of `N`. -/
lemma rel_orcN (N : FinNDTM Bool) (x : List Bool) (s : ℕ) :
    Rel (orcN N) x s = Codec.StepRel N x s := by
  funext u v
  apply propext
  simp [rel_iff_orc, Codec.stepRel_iff_mem, orcN, decs, indicator_eq_decide]

/-- Decider `1` answers membership in the initial-code language. -/
lemma initO_orcN (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) :
    InitO (orcN N) x s u ↔
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.initLang N := by
  simp [initO_iff_orc, orcN, decs, indicator_eq_decide]

/-- Decider `2` answers membership in the accepting-code language. -/
lemma accO_orcN (N : FinNDTM Bool) (x : List Bool) (s v : ℕ) :
    AccO (orcN N) x s v ↔
      pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.acceptLang N := by
  simp [accO_iff_orc, orcN, decs, indicator_eq_decide]

/-- The constant of the Savitch machine for `N` deciding in space `c (n ^ k + 1)`: large
enough for the radius (`radius_le`), the code width (`codeWidth_le`) and the configuration
count (`configBound_le`). -/
def bigE (N : FinNDTM Bool) (k c : ℕ) : ℕ :=
  k + c + 1 + 2 * Codec.codeK N + (Fintype.card N.State + 2 + 9 * N.k)

end SavitchARM

end Complexity.LogProg

namespace Complexity

open Turing LogProg LogProg.SavitchARM

/-- **Nondeterministic polynomial space is in `PSPACE`** [AB09, §4.2.1, Theorem 4.14 at
`S(n) = n ^ k + 1`]: `NSPACE (n ^ k + 1) ⊆ PSPACE`.

**Proof sketch.** Let `N` decide `L` in space `c (n ^ k + 1)`, and let `E = bigE N k c`. On
input `x`, with `s = (|x| + 2) ^ E ≥ c (|x| ^ k + 1)` and `w = (|x| + 2) ^ (2E)`, the codes at
radius `s` have width at most `w` and the configuration count is at most `2 ^ w`, so
`x ∈ L` iff some initial code reaches some accepting code by midpoint reachability at level
`w` (`mem_iff_reach`). The Savitch machine `A E` answers exactly this (`savitch_halts`),
with the deciders of `inputLenLang` and the code languages (all in `L ⊆ PSPACE`) and every
register value at most `2 ^ (w · w) ≤ 2 ^ (2 ^ (4E) (|x| + 1) ^ (4E))`; conclude with
`Complexity.LogProg.arm_decides_pspace_val`. -/
theorem NSPACE_poly_subset_PSPACE (k : ℕ) : NSPACE (fun n => n ^ k + 1) ⊆ PSPACE := by
  classical
  rintro L ⟨c, N, hN⟩
  set E := bigE N k c with hE
  have hE1 : 1 ≤ E := by simp only [hE, bigE]; omega
  refine arm_decides_pspace_val (A E) .scan (decs N) (fun j => ?_) (2 ^ (4 * E)) (4 * E)
    (fun x => ?_)
  · fin_cases j
    · exact LOGSPACE_subset_PSPACE inputLenLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.initLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.acceptLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.stepLang_mem
  set n := x.length with hn
  have hq : ∀ m ≤ x.length, orcN N 0 (pairEncode x (Nat.bits m)) = decide (m < x.length) := by
    intro m _
    simp only [orcN, decs, Matrix.cons_val_zero]
    exact indicator_inputLenLang x m
  have h := savitch_halts (E := E) (orc := orcN N) (x := x) hE1 hq
  have hmem := mem_iff_reach hN x ((n + 2) ^ E) ((n + 2) ^ (2 * E))
    (radius_le n k c E (by simp only [hE, bigE]; omega))
    (codeWidth_le N n E (by simp only [hE, bigE]; omega))
    (configBound_le N n E (by simp only [hE, bigE]; omega))
  rw [rel_orcN] at h
  simp only [initO_orcN, accO_orcN] at h
  rw [decide_eq_decide.mpr hmem.symm] at h
  rw [indicator_eq_decide]
  refine h.mono fun a ha => ⟨ha.1, fun r => (ha.2 r).trans ?_⟩
  -- `2 ^ (w · w) ≤ 2 ^ (2 ^ (4E) (n + 1) ^ (4E))`
  apply Nat.pow_le_pow_right (by norm_num)
  calc (n + 2) ^ (2 * E) * (n + 2) ^ (2 * E) = (n + 2) ^ (4 * E) := by rw [← pow_add]; ring_nf
    _ ≤ (2 * (n + 1)) ^ (4 * E) := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (4 * E) * (x.length + 1) ^ (4 * E) := by rw [mul_pow]

/-- **`NPSPACE ⊆ PSPACE`** [AB09, §4.2.1, the corollary of Theorem 4.14].

**Proof sketch.** A member of `NPSPACE` lies in some `NSPACE (n ^ k + 1)`
(`Complexity.NSPACE_poly_subset_PSPACE`). -/
theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
  exact NSPACE_poly_subset_PSPACE k hk

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Midpoint reachability over configuration codes

The predicate evaluated by Savitch's algorithm [AB09, §4.2.1, proof of Theorem 4.14]:
`Complexity.LogProg.SavitchARM.Reach K R i u v` holds when `v` is reachable from `u` in at
most `2 ^ i` steps of the relation `R`, witnessed by midpoints below `K` —
`Reach K R 0 u v` is `u = v ∨ R u v`, and `Reach K R (i + 1) u v` asks for some `m < K`
with `Reach K R i u m` and `Reach K R i m v`.

Over the code languages of a nondeterministic space-bounded decider `N`
(`TCSlib.Complexity.SpaceComplexity.Codec`), membership is midpoint reachability from an
initial code to an accepting code (`Complexity.LogProg.SavitchARM.mem_iff_reach`), once the
code width `w` is large enough that the codes lie below `2 ^ w` and the configuration count
is at most `2 ^ w`: chains of length at most `2 ^ w` are cut at midpoints
(`reach_of_chain`), and conversely every midpoint witness unfolds into a path of steps
(`reflTransGen_of_reach`), whose codes are realized by a branch of `N`
(`Complexity.Codec.mem_of_codePath`).

## Main definitions

* `Complexity.LogProg.SavitchARM.Reach` — midpoint reachability (over the code-level step
  relation `Complexity.Codec.StepRel` of a decider).

## Main results

* `Complexity.LogProg.SavitchARM.reach_of_chain`, `reflTransGen_of_reach` — the two
  directions of midpoint reachability.
* `Complexity.LogProg.SavitchARM.reach_of_reflTransGen` — a path through vertices below `K` is
  a midpoint witness at every level `i` with `K ≤ 2 ^ i` (path shortening).
* `Complexity.LogProg.SavitchARM.configBound_le` — the configuration count at radius
  `(n + 2) ^ E` is below `2 ^ ((n + 2) ^ (2 E))`.
* `Complexity.LogProg.SavitchARM.mem_iff_reach` — membership as midpoint reachability.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4; §4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing Codec

/-- **Midpoint reachability**: `Reach K R i u v` holds when `v` is reachable from `u` in at
most `2 ^ i` steps of `R`, with every midpoint of the recursion below `K`. [AB09, §4.2.1,
the predicate `REACH(C, C', i)` of the proof of Theorem 4.14] -/
def Reach (K : ℕ) (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v ∨ R u v
  | i + 1, u, v => ∃ m < K, Reach K R i u m ∧ Reach K R i m v

/-- **Chains are cut at midpoints**: a chain `c 0, …, c T` of `R`-steps with every member
below `K` gives `Reach K R i (c j) (c (j + t))` for every segment of length `t ≤ 2 ^ i`.

**Proof sketch.** Induction on `i`. A segment of length at most one is an equality or a
step. A segment of length `t ≤ 2 ^ (i + 1)` splits at `t₁ = min t (2 ^ i)` into two
segments of length at most `2 ^ i`, the split point `c (j + t₁)` serving as midpoint. -/
theorem reach_of_chain (K : ℕ) (R : ℕ → ℕ → Prop) (c : ℕ → ℕ) (T : ℕ)
    (hR : ∀ j < T, R (c j) (c (j + 1))) (hK : ∀ j ≤ T, c j < K) :
    ∀ i j t, j + t ≤ T → t ≤ 2 ^ i → Reach K R i (c j) (c (j + t)) := by
  intro i
  induction i with
  | zero =>
    intro j t hjt ht
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl rfl
    · obtain rfl : t = 1 := by simp at ht; omega
      exact Or.inr (hR j (by omega))
  | succ i ih =>
    intro j t hjt ht
    set t₁ := min t (2 ^ i) with ht₁
    have h1 : t₁ ≤ 2 ^ i := min_le_right _ _
    have h2 : t - t₁ ≤ 2 ^ i := by rw [pow_succ] at ht; omega
    refine ⟨c (j + t₁), hK _ (by omega), ih j t₁ (by omega) h1, ?_⟩
    have := ih (j + t₁) (t - t₁) (by omega) h2
    rwa [show j + t₁ + (t - t₁) = j + t by omega] at this

/-- **Midpoint witnesses unfold into paths**: `Reach K R i u v` gives an `R`-path from `u`
to `v`.

**Proof sketch.** Induction on `i`: an equality or a step is a path, and two paths through
a midpoint concatenate. -/
theorem reflTransGen_of_reach (K : ℕ) (R : ℕ → ℕ → Prop) :
    ∀ i u v, Reach K R i u v → Relation.ReflTransGen R u v := by
  intro i
  induction i with
  | zero =>
    rintro u v (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
  | succ i ih =>
    rintro u v ⟨m, -, h1, h2⟩
    exact (ih u m h1).trans (ih m v h2)

/-- A walk of at most `j` edges from `c < K` (`Complexity.WalkLe`) is a chain of at most `j`
steps with every member below `K`.

**Proof sketch.** Induction on `j`, generalizing the start, reading the walk through
`Complexity.walkLe_zero_iff` and the head form `Complexity.walkLe_succ_iff_head`: a walk of at
most `j + 1` edges is empty, or an edge from `c` to some `v < K` followed by a walk of at most `j`
edges from `v`, whose chain gains `c` in front. -/
private theorem chain_of_walkLe (K : ℕ) (R : ℕ → ℕ → Prop) (c : ℕ) (hc : c < K) :
    ∀ j t, WalkLe R K j c t → ∃ T ≤ j, ∃ f : ℕ → ℕ, f 0 = c ∧ f T = t ∧
      (∀ i < T, R (f i) (f (i + 1))) ∧ ∀ i ≤ T, f i < K := by
  intro j
  induction j generalizing c with
  | zero =>
    intro t h
    rw [walkLe_zero_iff] at h
    exact ⟨0, le_rfl, fun _ => c, rfl, h, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ => hc⟩
  | succ j ih =>
    intro t h
    rcases walkLe_succ_iff_head.mp h with rfl | ⟨v, hv, hcv, hvt⟩
    · exact ⟨0, Nat.zero_le _, fun _ => c, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun _ _ => hc⟩
    · obtain ⟨T, hT, f, h0, hTt, hstep, hlt⟩ := ih v hv t hvt
      refine ⟨T + 1, by omega, fun i => if i = 0 then c else f (i - 1), if_pos rfl, ?_, ?_, ?_⟩
      · show (if T + 1 = 0 then c else f (T + 1 - 1)) = t
        rw [if_neg (Nat.succ_ne_zero T), Nat.add_sub_cancel, hTt]
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · show R (if 0 = 0 then c else f (0 - 1)) (if 0 + 1 = 0 then c else f (0 + 1 - 1))
          rw [if_pos rfl, if_neg (Nat.succ_ne_zero 0), Nat.add_sub_cancel, h0]
          exact hcv
        · show R (if i = 0 then c else f (i - 1)) (if i + 1 = 0 then c else f (i + 1 - 1))
          rw [if_neg (Nat.pos_iff_ne_zero.mp hi0), if_neg (Nat.succ_ne_zero i),
            Nat.add_sub_cancel]
          have h := hstep (i - 1) (by omega)
          rwa [Nat.sub_add_cancel hi0] at h
      · intro i hi
        show (if i = 0 then c else f (i - 1)) < K
        split_ifs
        · exact hc
        · exact hlt (i - 1) (by omega)

/-- **Path shortening into a midpoint witness**: if every step of `R` joins vertices below
`K`, a path from `u < K` to `v` is a midpoint witness `Reach K R i u v` at every level `i` with
`K ≤ 2 ^ i`. This is the converse of `reflTransGen_of_reach` under a vertex bound. [AB09,
§4.2.1, proof of Theorem 4.14: a path in a graph of at most `2 ^ i` vertices has at most
`2 ^ i` steps]

**Proof sketch.** The path runs through vertices below `K`, so it is a walk of at most `K`
edges (`Complexity.reach_iff_walkLe`, from the shortening `Complexity.walkLe_short`), hence a
chain of at most `K ≤ 2 ^ i` steps, which `reach_of_chain` cuts at midpoints. -/
theorem reach_of_reflTransGen (K : ℕ) (R : ℕ → ℕ → Prop) (hR : ∀ a b, R a b → a < K ∧ b < K)
    {u v : ℕ} (hu : u < K) (h : Relation.ReflTransGen R u v) (i : ℕ) (hi : K ≤ 2 ^ i) :
    Reach K R i u v := by
  have hv : v < K := by
    rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, -, hb⟩
    · exact hu
    · exact (hR _ _ hb).2
  have h' : Relation.ReflTransGen (fun a b => a < K ∧ b < K ∧ R a b) u v :=
    Relation.ReflTransGen.mono (fun a b hab => ⟨(hR a b hab).1, (hR a b hab).2, hab⟩) h
  obtain ⟨T, hT, f, h0, hTv, hstep, hlt⟩ :=
    chain_of_walkLe K R u hu K v ((reach_iff_walkLe hu hv).mp h')
  have := reach_of_chain K R f T hstep hlt i 0 T (by omega) (hT.trans hi)
  rwa [h0, zero_add, hTv] at this

/-! ## The size bounds -/

/-- **The configuration count is doubly exponentially bounded**: at radius `(n + 2) ^ E`,
with `|Q| + 2 + 9k ≤ E`, the vertex count `configBound n ((n + 2) ^ E)` is at most
`2 ^ ((n + 2) ^ (2 E))`.

**Proof sketch.** Bound each factor of
`3 (|Q| + 1)(n + 2) 3 ^ (k (2s + 1)) (2s + 1) ^ k` by a power of two: the exponents add up
to at most `|Q| + n + 3 + 3k (2s + 1) ≤ (|Q| + 2 + 9k) s ≤ 2 ^ E s ≤ (n + 2) ^ E s`. -/
theorem configBound_le (N : FinNDTM Bool) (n E : ℕ)
    (hE : Fintype.card N.State + 2 + 9 * N.k ≤ E) :
    N.configBound n ((n + 2) ^ E) ≤ 2 ^ ((n + 2) ^ (2 * E)) := by
  set s := (n + 2) ^ E with hs
  set Q := Fintype.card N.State
  set k := N.k
  have hs1 : n + 2 ≤ s := by
    have : 1 ≤ E := by omega
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ s := Nat.pow_le_pow_right (by omega) this
  have f1 : 3 ≤ 2 ^ 2 := by decide
  have f2 : Q + 1 ≤ 2 ^ Q := Nat.lt_two_pow_self
  have f3 : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
  have f4 : 3 ^ (k * (2 * s + 1)) ≤ 2 ^ (2 * (k * (2 * s + 1))) := by
    rw [pow_mul 2 2]; exact Nat.pow_le_pow_left f1 _
  have f5 : (2 * s + 1) ^ k ≤ 2 ^ (k * (2 * s + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have hprod : N.configBound n s ≤
      2 ^ (2 + Q + (n + 1) + 2 * (k * (2 * s + 1)) + k * (2 * s + 1)) := by
    unfold FinNDTM.configBound
    rw [pow_add, pow_add, pow_add, pow_add]
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f2 f3) f4) f5) f1
    calc 3 * ((Q + 1) * (n + 2) * 3 ^ (k * (2 * s + 1)) * (2 * s + 1) ^ k)
        = (Q + 1) * (n + 2) * 3 ^ (k * (2 * s + 1)) * (2 * s + 1) ^ k * 3 := by ring
      _ ≤ 2 ^ Q * 2 ^ (n + 1) * 2 ^ (2 * (k * (2 * s + 1))) * 2 ^ (k * (2 * s + 1)) * 2 ^ 2 :=
        this
      _ = _ := by ring
  refine hprod.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  -- the exponent: `Q + n + 3 + 3k (2s + 1) ≤ (Q + 2 + 9k) s ≤ 2 ^ E s ≤ (n + 2) ^ E s`
  have hE2 : Q + 2 + 9 * k ≤ (n + 2) ^ E :=
    hE.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _))
  have e1 : (n + 2) ^ (2 * E) = s * s := by rw [hs, ← pow_add]; ring_nf
  rw [e1]
  have g1 : (Q + 2 + 9 * k) * s ≤ s * s := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hE2
  have g2 : Q ≤ Q * s := Nat.le_mul_of_pos_right _ (by omega)
  have g3 : k ≤ k * s := Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (Q + 2 + 9 * k) * s = Q * s + 2 * s + 9 * (k * s) := by ring
  have e3 : 2 + Q + (n + 1) + 2 * (k * (2 * s + 1)) + k * (2 * s + 1) =
      Q + n + 3 + 6 * (k * s) + 3 * k := by ring
  omega

/-- **The code width bound**: with `2 codeK N ≤ E`, the codes at radius `(n + 2) ^ E` on
inputs of length `n` have width at most `(n + 2) ^ (2 E)`.

**Proof sketch.** `logSpace n + 1 ≤ n + 2 ≤ (n + 2) ^ E`, so the width
`codeK N ((n + 2) ^ E + logSpace n + 1)` is at most `2 codeK N (n + 2) ^ E`, and
`2 codeK N ≤ E < 2 ^ E ≤ (n + 2) ^ E`. -/
theorem codeWidth_le (N : FinNDTM Bool) (n E : ℕ) (hE : 2 * codeK N ≤ E) :
    codeK N * ((n + 2) ^ E + logSpace n + 1) ≤ (n + 2) ^ (2 * E) := by
  set s := (n + 2) ^ E with hs
  have hlog := logSpace_le_succ n
  have hs1 : n + 2 ≤ s := by
    rcases Nat.eq_zero_or_pos E with h | h
    · have : codeK N = 0 := by omega
      simp [codeK, W] at this
    · calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
        _ ≤ s := Nat.pow_le_pow_right (by omega) h
  have hE2 : 2 * codeK N ≤ s :=
    hE.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _))
  have e1 : (n + 2) ^ (2 * E) = s * s := by rw [hs, ← pow_add]; ring_nf
  rw [e1]
  calc codeK N * (s + logSpace n + 1) ≤ codeK N * (2 * s) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * codeK N * s := by ring
    _ ≤ s * s := Nat.mul_le_mul_right _ hE2

/-- **The radius bound**: with `k + c + 1 ≤ E`, `c (n ^ k + 1) ≤ (n + 2) ^ E`.

**Proof sketch.** `n ^ k + 1 ≤ 2 (n + 2) ^ k` and `c < 2 ^ c ≤ (n + 2) ^ c`, so
`c (n ^ k + 1) ≤ 2 (n + 2) ^ (k + c) ≤ (n + 2) ^ (k + c + 1)`. -/
theorem radius_le (n k c E : ℕ) (hE : k + c + 1 ≤ E) :
    c * (n ^ k + 1) ≤ (n + 2) ^ E := by
  have h1 : n ^ k + 1 ≤ 2 * (n + 2) ^ k := by
    have : n ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) _
    have : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : 2 * c ≤ (n + 2) ^ c * 2 := by
    have : c < 2 ^ c := Nat.lt_two_pow_self
    have : 2 ^ c ≤ (n + 2) ^ c := Nat.pow_le_pow_left (by omega) _
    omega
  calc c * (n ^ k + 1) ≤ c * (2 * (n + 2) ^ k) := Nat.mul_le_mul_left _ h1
    _ = 2 * c * (n + 2) ^ k := by ring
    _ ≤ (n + 2) ^ c * 2 * (n + 2) ^ k := Nat.mul_le_mul_right _ h2
    _ = 2 * (n + 2) ^ (k + c) := by rw [pow_add]; ring
    _ ≤ (n + 2) ^ (k + c + 1) := by
        rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ (n + 2) ^ E := Nat.pow_le_pow_right (by omega) hE

/-- **Membership as midpoint reachability** [AB09, §4.2.1, proof of Theorem 4.14]: let `N`
decide `L` in space `sp`, and let the radius `s ≥ sp |x|` and the width `w` be such that the
codes have width at most `w` and the configuration count is at most `2 ^ w`. Then `x ∈ L` iff
some initial code `u < 2 ^ w` and some accepting code `v < 2 ^ w` have
`Reach (2 ^ w) (StepRel N x s) w u v`.

**Proof sketch.** (⇒) `Complexity.Codec.mem_iff_codeChain` gives a chain of codes below
`2 ^ w` of length at most the configuration count, hence at most `2 ^ w`; cut it at midpoints
(`reach_of_chain`). (⇐) Unfold the midpoint witness into a path (`reflTransGen_of_reach`) and
realize it by a branch (`Complexity.Codec.mem_of_codePath`). -/
theorem mem_iff_reach {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) (x : List Bool) (s w : ℕ) (hs : sp x.length ≤ s)
    (hw : codeK N * (s + logSpace x.length + 1) ≤ w)
    (hcb : N.configBound x.length s ≤ 2 ^ w) :
    x ∈ L ↔ ∃ u < 2 ^ w, pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N ∧
      ∃ v < 2 ^ w, pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N ∧
        Reach (2 ^ w) (StepRel N x s) w u v := by
  constructor
  · intro hx
    obtain ⟨t, c, ht, hinit, hstep, hacc, hlt⟩ := (mem_iff_codeChain h x s hs).mp hx
    have hK : ∀ j ≤ t, c j < 2 ^ w := fun j hj =>
      (hlt j hj).trans_le (Nat.pow_le_pow_right (by norm_num) hw)
    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t
      (fun j hj => stepRel_iff_mem.mpr (hstep j hj)) hK w 0 t (by omega) (ht.trans hcb)
    rw [zero_add] at hr
    exact ⟨c 0, hK 0 (Nat.zero_le _), hinit, c t, hK t le_rfl, hacc, hr⟩
  · rintro ⟨u, -, hinit, v, -, hacc, hr⟩
    exact mem_of_codePath h x s u v hinit (reflTransGen_of_reach _ _ w u v hr) hacc

end SavitchARM

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.Machines.VWord

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic walk for `PATH`: walks and the instance layout

[AB09, §4.1.2]: `PATH ∈ NL` by guessing a path vertex by vertex. This file holds the
combinatorics of the proof in `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof`,
over the raw instance format `⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩` (row-major adjacency word `M` of
length `n²`), so that it does not depend on `TCSlib.Complexity.SpaceComplexity.Logspace.Path`.

* **Walks.** `Complexity.WalkLe E n j c t`: `t` is reachable from `c` in at most `j` edges of
  `E` through vertices `< n`. Every reachable vertex is reachable in at most `n` edges
  (`Complexity.walkLe_short`, a pigeonhole on the sets reachable within `j` edges).
* **Layout.** `Complexity.DblAt x q u` (the input carries `dbl u ++ [0, 1]` at position `q`)
  and `Complexity.PlainAt x r u` (the input ends with `u` from position `r`), and the
  decomposition of the raw instance format into them (`Complexity.eq_pathRaw_iff`).
* **What the walk machine checks.** `Complexity.PathAcc x` — a unary prefix, a matrix field of
  `n²` aligned pairs, endpoint fields of values `s, t < n`, and a walk of at most `n` edges of
  the matrix read off the input — is membership in the raw language
  (`Complexity.pathAcc_iff`).

## Main definitions

* `Complexity.WalkLe`, `Complexity.DblAt`, `Complexity.PlainAt`.
* `Complexity.pathRaw`, `Complexity.rawEdge`, `Complexity.pathRawLang` — the raw `PATH`
  language.
* `Complexity.pathEdge`, `Complexity.UnaryRest`, `Complexity.MatRest`, `Complexity.PathAcc`.

## Main results

* `Complexity.walkLe_short`, `Complexity.reach_iff_walkLe` — path shortening.
* `Complexity.walkLe_zero_iff` — a walk of no edges stays put.
* `Complexity.walkLe_succ_iff_head` — a longer walk stays put or begins with an edge.
* `Complexity.eq_pathRaw_iff` — the layout of a raw instance.
* `Complexity.pathAcc_iff` — what the machine checks is membership in `pathRawLang`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2.)
-/

namespace Complexity

open Turing

/-! ## Walks of bounded length -/

section Walks

variable (E : ℕ → ℕ → Prop) (n : ℕ)

/-- `WalkLe E n j c t`: `t` is reachable from `c` by at most `j` edges of `E`, every vertex
after `c` below `n`. -/
def WalkLe : ℕ → ℕ → ℕ → Prop
  | 0, c, t => c = t
  | j + 1, c, t => c = t ∨ ∃ v, v < n ∧ E c v ∧ WalkLe j v t

variable {E n}

/-- `Complexity.WalkLe` with no edge allowed: the endpoints are equal. -/
lemma walkLe_zero_iff {c t : ℕ} : WalkLe E n 0 c t ↔ c = t := Iff.rfl

/-- `Complexity.WalkLe` with at most `j + 1` edges, read at the front: the endpoints are equal,
or an edge from `c` to some `v < n` is followed by a walk of at most `j` edges from `v` to `t`. -/
lemma walkLe_succ_iff_head {j c t : ℕ} :
    WalkLe E n (j + 1) c t ↔ c = t ∨ ∃ v, v < n ∧ E c v ∧ WalkLe E n j v t := Iff.rfl

/-- Every vertex reaches itself. -/
lemma walkLe_refl (j c : ℕ) : WalkLe E n j c c := by
  cases j
  · rfl
  · exact Or.inl rfl

/-- One more allowed edge. -/
lemma walkLe_succ {j c t : ℕ} (h : WalkLe E n j c t) : WalkLe E n (j + 1) c t := by
  induction j generalizing c with
  | zero => exact Or.inl h
  | succ j ih =>
    rcases h with h | ⟨v, hv, he, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, he, ih hw⟩

/-- More allowed edges. -/
lemma walkLe_mono {j k c t : ℕ} (hjk : j ≤ k) (h : WalkLe E n j c t) : WalkLe E n k c t := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact walkLe_succ ih

/-- A bounded walk from a vertex below `n` is a path of the edge relation on vertices
below `n`. -/
lemma walkLe_reach {j c t : ℕ} (hc : c < n) (h : WalkLe E n j c t) :
    Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t := by
  induction j generalizing c with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ j ih =>
    rcases h with rfl | ⟨v, hv, he, hw⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨hc, hv, he⟩ (ih hv hw)

/-- A path is a walk of some length. -/
lemma exists_walkLe {c t : ℕ}
    (h : Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t) :
    ∃ j, WalkLe E n j c t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨j + 1, Or.inr ⟨_, hab.2.1, hab.2.2, hj⟩⟩

/-- **Path shortening**: a vertex below `n` reachable within some number of edges is
reachable within `n` edges.

**Proof sketch.** Let `S j` be the set of vertices below `n` reaching `t` within `j` edges.
The sets grow with `j`, and once `S j = S (j + 1)` they are constant from `j` on (`S (j + 2)`
is determined by `S (j + 1)` as `S (j + 1)` is by `S j`). They cannot grow strictly `n` times,
since `t ∈ S 0` and `|S j| ≤ n`; so some `j < n` has `S j = S (j + 1)`, and every `S k` is
contained in `S n`. -/
lemma walkLe_short {j c t : ℕ} (ht : t < n) (hc : c < n) (h : WalkLe E n j c t) :
    WalkLe E n n c t := by
  classical
  let S : ℕ → Finset ℕ := fun j => (Finset.range n).filter fun c => WalkLe E n j c t
  have memS : ∀ j c, c ∈ S j ↔ c < n ∧ WalkLe E n j c t := by
    intro j c; simp [S]
  have hmono : ∀ j k, j ≤ k → S j ⊆ S k := by
    intro j k hjk c hcj
    rw [memS] at hcj ⊢
    exact ⟨hcj.1, walkLe_mono hjk hcj.2⟩
  have hstab : ∀ j, S j = S (j + 1) → S (j + 1) = S (j + 2) := by
    intro j he
    ext c
    rw [memS, memS]
    have key : ∀ v, v < n → (WalkLe E n (j + 1) v t ↔ WalkLe E n j v t) := by
      intro v hv
      have := congrArg (fun S : Finset ℕ => v ∈ S) he
      simp only [memS, eq_iff_iff] at this
      exact ⟨fun h => (this.mpr ⟨hv, h⟩).2, fun h => (this.mp ⟨hv, h⟩).2⟩
    constructor
    · rintro ⟨hc, h | ⟨v, hv, he, hw⟩⟩
      · exact ⟨hc, Or.inl h⟩
      · exact ⟨hc, Or.inr ⟨v, hv, he, (key v hv).mpr hw⟩⟩
    · rintro ⟨hc, h | ⟨v, hv, he, hw⟩⟩
      · exact ⟨hc, Or.inl h⟩
      · exact ⟨hc, Or.inr ⟨v, hv, he, (key v hv).mp hw⟩⟩
  have hex : ∃ j₀, j₀ ≤ n ∧ S j₀ = S (j₀ + 1) := by
    by_contra hne
    push_neg at hne
    have hcard : ∀ j, j ≤ n → j + 1 ≤ (S j).card := by
      intro j hj
      induction j with
      | zero =>
        exact Finset.card_pos.mpr ⟨t, (memS 0 t).mpr ⟨ht, rfl⟩⟩
      | succ j ih =>
        have hlt : (S j).card < (S (j + 1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hmono j (j + 1) (by omega), hne j (by omega)⟩)
        have := ih (by omega)
        omega
    have h1 := hcard n le_rfl
    have h2 : (S n).card ≤ n := by
      calc (S n).card ≤ (Finset.range n).card := Finset.card_filter_le _ _
        _ = n := Finset.card_range n
    omega
  obtain ⟨j₀, hj₀, he⟩ := hex
  have hconst : ∀ i, S (j₀ + i) = S (j₀ + i + 1) := by
    intro i
    induction i with
    | zero => exact he
    | succ i ih => exact hstab (j₀ + i) ih
  have hfix : ∀ i, S (j₀ + i) = S j₀ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← Nat.add_assoc, ← hconst i, ih]
  have hsub : S j ⊆ S n := by
    rcases Nat.le_total j n with hjn | hnj
    · exact hmono j n hjn
    · obtain ⟨i, rfl⟩ : ∃ i, j = j₀ + i := ⟨j - j₀, by omega⟩
      rw [hfix i]
      exact hmono j₀ n hj₀
  exact ((memS n c).mp (hsub ((memS j c).mpr ⟨hc, h⟩))).2

/-- **Reachability is walking within `n` edges** (for endpoints below `n`). -/
lemma reach_iff_walkLe {c t : ℕ} (hc : c < n) (ht : t < n) :
    Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t ↔ WalkLe E n n c t := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_walkLe h
    exact walkLe_short ht hc hj
  · exact walkLe_reach hc

end Walks

/-! ## The layout of an instance -/

section Layout

/-- A `true` bit read with default `false` is inside the word. -/
lemma lt_of_getD_true {l : List Bool} {i : ℕ} (h : l.getD i false = true) : i < l.length := by
  by_contra hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

/-- Two words agreeing in length and at every position are equal. -/
lemma ext_getD' {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ∀ i < l₁.length, l₁.getD i false = l₂.getD i false) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this

/-- `DblAt x q u`: the input `x` carries `dbl u` followed by the separator `[0, 1]` at
position `q`. -/
def DblAt (x : List Bool) (q : ℕ) (u : List Bool) : Prop :=
  (∀ i < u.length, x.getD (q + 2 * i) false = u.getD i false ∧
    x.getD (q + 2 * i + 1) false = u.getD i false) ∧
  x.getD (q + 2 * u.length) false = false ∧ x.getD (q + 2 * u.length + 1) false = true

/-- `PlainAt x r u`: the input `x` ends with `u`, from position `r`. -/
def PlainAt (x : List Bool) (r : ℕ) (u : List Bool) : Prop :=
  (∀ i < u.length, x.getD (r + i) false = u.getD i false) ∧ x.length = r + u.length

/-- Dropping the first component of a pair. -/
private lemma drop_pairEncode (u w : List Bool) : (pairEncode u w).drop (2 * u.length + 2) = w := by
  rw [pairEncode_eq_dbl, List.drop_left']
  simp

/-- **The layout at a position**: `x` carries `dbl u ++ [0, 1]` at `q` iff the suffix from
`q` is a pair with first component `u`.

**Proof sketch.** Read positions of the suffix with `pairEncode_getD`; conversely the
separator bit `1` places `q + 2|u| + 1` inside `x`, the lengths agree, and every position
of the suffix is a doubled bit, a separator bit, or a bit of the rest. -/
lemma dblAt_iff (x : List Bool) (q : ℕ) (u : List Bool) :
    DblAt x q u ↔ x.drop q = pairEncode u (x.drop (q + 2 * u.length + 2)) := by
  constructor
  · rintro ⟨hb, h0, h1⟩
    have hlen := lt_of_getD_true h1
    refine ext_getD' (by simp only [List.length_drop, length_pairEncode]; omega) fun i _ => ?_
    rw [getD_drop, pairEncode_getD]
    split_ifs with c1 c2 c3
    · have := hb (i / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [show q + i = q + 2 * (i / 2) by omega]; exact this.1
      · rw [show q + i = q + 2 * (i / 2) + 1 by omega]; exact this.2
    · subst c2; exact h0
    · subst c3; rw [← Nat.add_assoc]; exact h1
    · rw [getD_drop]; congr 1; omega
  · intro h
    have key : ∀ j, x.getD (q + j) false = (pairEncode u (x.drop (q + 2 * u.length + 2))).getD j
        false := by intro j; rw [← h, getD_drop]
    refine ⟨fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [key, pairEncode_getD, if_pos (by omega)]; congr 1; omega
    · rw [Nat.add_assoc, key, pairEncode_getD, if_pos (by omega)]; congr 1; omega
    · rw [key, pairEncode_getD, if_neg (by omega), if_pos rfl]
    · rw [Nat.add_assoc, key, pairEncode_getD, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- The input ends with `u` from position `r` iff `r` is inside and the suffix is `u`. -/
lemma plainAt_iff (x : List Bool) (r : ℕ) (u : List Bool) :
    PlainAt x r u ↔ r ≤ x.length ∧ x.drop r = u := by
  constructor
  · rintro ⟨hb, hl⟩
    refine ⟨by omega, ext_getD' (by simp; omega) fun i hi => ?_⟩
    rw [getD_drop]
    exact hb i (by simp at hi; omega)
  · rintro ⟨hr, rfl⟩
    refine ⟨fun i hi => by rw [getD_drop], by simp; omega⟩

/-- **The raw `PATH` instance** `⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩`. -/
def pathRaw (n : ℕ) (M : List Bool) (s t : ℕ) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)))

/-- The edge relation of the row-major adjacency word `M` on vertices below `n`. -/
def rawEdge (n : ℕ) (M : List Bool) (u v : ℕ) : Prop :=
  u < n ∧ v < n ∧ M.getD (u * n + v) false = true

/-- **The raw `PATH` language**: raw instances (matrix word of length `n²`, endpoints
below `n`) whose target is reachable from their source. -/
def pathRawLang : Language Bool :=
  {x | ∃ (n : ℕ) (M : List Bool) (s t : ℕ), M.length = n * n ∧ s < n ∧ t < n ∧
    x = pathRaw n M s t ∧ Relation.ReflTransGen (rawEdge n M) s t}

/-- **The layout of a raw instance**: `x = ⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩` iff `x` carries the
four fields at the positions `0`, `2n + 2`, `2n + 2 + 2|M| + 2` and
`2n + 2 + 2|M| + 2 + 2|bits s| + 2`.

**Proof sketch.** `dblAt_iff` three times and `plainAt_iff` once, peeling one pair at a
time (`drop_pairEncode`, `List.drop_drop`). -/
lemma eq_pathRaw_iff (x : List Bool) (n : ℕ) (M : List Bool) (s t : ℕ) :
    x = pathRaw n M s t ↔
      DblAt x 0 (List.replicate n true) ∧ DblAt x (2 * n + 2) M ∧
      DblAt x (2 * n + 2 + 2 * M.length + 2) (Nat.bits s) ∧
      PlainAt x (2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t) := by
  constructor
  · rintro rfl
    have d1 : (pathRaw n M s t).drop (2 * n + 2) =
        pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)) := by
      have := drop_pairEncode (List.replicate n true)
        (pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)))
      simpa using this
    have d2 : (pathRaw n M s t).drop (2 * n + 2 + 2 * M.length + 2) =
        pairEncode (Nat.bits s) (Nat.bits t) := by
      rw [show 2 * n + 2 + 2 * M.length + 2 = (2 * n + 2) + (2 * M.length + 2) by omega,
        ← List.drop_drop, d1, drop_pairEncode]
    have d3 : (pathRaw n M s t).drop
        (2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2) = Nat.bits t := by
      rw [show 2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2 =
        (2 * n + 2 + 2 * M.length + 2) + (2 * (Nat.bits s).length + 2) by omega,
        ← List.drop_drop, d2, drop_pairEncode]
    refine ⟨(dblAt_iff _ _ _).mpr ?_, (dblAt_iff _ _ _).mpr ?_, (dblAt_iff _ _ _).mpr ?_,
      (plainAt_iff _ _ _).mpr ⟨?_, d3⟩⟩
    · simp only [List.drop_zero, Nat.zero_add, List.length_replicate]
      rw [show (pathRaw n M s t).drop (2 * n + 2) = _ from d1]; rfl
    · rw [d1, show 2 * n + 2 + 2 * M.length + 2 = (2 * n + 2) + (2 * M.length + 2) by omega,
        ← List.drop_drop, d1, drop_pairEncode]
    · rw [d2, show 2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2 =
        (2 * n + 2 + 2 * M.length + 2) + (2 * (Nat.bits s).length + 2) by omega,
        ← List.drop_drop, d2, drop_pairEncode]
    · simp [pathRaw, length_pairEncode]; omega
  · rintro ⟨h1, h2, h3, h4⟩
    rw [dblAt_iff] at h1 h2 h3
    rw [plainAt_iff] at h4
    simp only [List.drop_zero, Nat.zero_add, List.length_replicate] at h1
    rw [h1, h2, h3, h4.2]
    rfl

/-- A row-major index is below `n²`. -/
lemma rowMajor_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  rw [Nat.succ_mul] at this
  omega

end Layout

/-! ## What the machine checks -/

/-- The matrix bit of the edge `u → v`, read off the input at its row-major position. -/
def pathEdge (x : List Bool) (n u v : ℕ) : Prop :=
  x.getD (2 * n + 2 + 2 * (u * n + v)) false = true

/-- The unary prefix from pair `k` on: aligned `11` pairs up to pair `n`, then `01`. -/
def UnaryRest (x : List Bool) (k n : ℕ) : Prop :=
  (∀ i, k ≤ i → i < n → x.getD (2 * i) false = true ∧ x.getD (2 * i + 1) false = true) ∧
  x.getD (2 * n) false = false ∧ x.getD (2 * n + 1) false = true

/-- The matrix field from pair `i` on: aligned data pairs up to pair `n²`, then `01`. -/
def MatRest (x : List Bool) (n i : ℕ) : Prop :=
  (∀ j, i ≤ j → j < n * n →
    x.getD (2 * n + 2 + 2 * j) false = x.getD (2 * n + 2 + 2 * j + 1) false) ∧
  x.getD (2 * n + 2 + 2 * (n * n)) false = false ∧
  x.getD (2 * n + 2 + 2 * (n * n) + 1) false = true

/-- **What the walk machine accepts**: a unary prefix `1ⁿ`, a matrix field of `n²` aligned
pairs, a doubled source field `bits s` and a plain target field `bits t` ending the input,
with `s, t < n` and `t` reachable from `s` within `n` edges of `pathEdge`. -/
def PathAcc (x : List Bool) : Prop :=
  ∃ n, UnaryRest x 0 n ∧ MatRest x n 0 ∧
    ∃ s, s < n ∧ DblAt x (2 * n + 2 + 2 * (n * n) + 2) (Nat.bits s) ∧
      ∃ t, t < n ∧
        PlainAt x (2 * n + 2 + 2 * (n * n) + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t) ∧
        WalkLe (pathEdge x n) n n s t

/-- The unary prefix is the doubled word `1ⁿ` followed by the separator. -/
lemma unaryRest_iff (x : List Bool) (n : ℕ) :
    UnaryRest x 0 n ↔ DblAt x 0 (List.replicate n true) := by
  have hr : ∀ i < n, (List.replicate n true).getD i false = true := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl
  simp only [UnaryRest, DblAt, List.length_replicate, Nat.zero_add, Nat.zero_le, true_imp_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i hi => by rw [hr i hi]; exact h1 i hi, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i hi => by rw [← hr i hi]; exact h1 i hi, h2, h3⟩

/-- The matrix field is a doubled word of length `n²` followed by the separator. -/
lemma matRest_iff (x : List Bool) (n : ℕ) :
    MatRest x n 0 ↔ ∃ M : List Bool, M.length = n * n ∧ DblAt x (2 * n + 2) M := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    let M := (List.range (n * n)).map fun j => x.getD (2 * n + 2 + 2 * j) false
    have hM : M.length = n * n := by simp [M]
    have hg : ∀ j < n * n, M.getD j false = x.getD (2 * n + 2 + 2 * j) false := by
      intro j hj
      simp [M, List.getD_eq_getElem?_getD, List.getElem?_range hj]
    refine ⟨M, hM, fun i hi => ?_, by rw [hM]; exact h2, by rw [hM]; exact h3⟩
    rw [hM] at hi
    rw [hg i hi]
    exact ⟨rfl, (h1 i (Nat.zero_le _) hi).symm⟩
  · rintro ⟨M, hM, h1, h2, h3⟩
    rw [hM] at h1 h2 h3
    refine ⟨fun j _ hj => ?_, h2, h3⟩
    have := h1 j hj
    rw [this.1, this.2]

/-- **`PathAcc` is membership in the raw `PATH` language.**

**Proof sketch.** `eq_pathRaw_iff` matches the four fields; the matrix word is read off the
input (`matRest_iff`), so `pathEdge` is its edge relation below `n`; reachability is walking
within `n` edges (`reach_iff_walkLe`). -/
theorem pathAcc_iff (x : List Bool) : PathAcc x ↔ x ∈ pathRawLang := by
  have hedge : ∀ n (M : List Bool), M.length = n * n → DblAt x (2 * n + 2) M →
      ∀ u v, u < n → v < n → (pathEdge x n u v ↔ M.getD (u * n + v) false = true) := by
    intro n M hM hD u v hu hv
    have := (hD.1 (u * n + v) (by rw [hM]; exact rowMajor_lt hu hv)).1
    simp only [pathEdge, this]
  constructor
  · rintro ⟨n, hU, hMat, s, hs, hD, t, ht, hP, hW⟩
    obtain ⟨M, hM, hDM⟩ := (matRest_iff x n).mp hMat
    refine ⟨n, M, s, t, hM, hs, ht, (eq_pathRaw_iff x n M s t).mpr
      ⟨(unaryRest_iff x n).mp hU, hDM, by rwa [hM], by rwa [hM]⟩, ?_⟩
    refine ((reach_iff_walkLe hs ht).mpr hW).mono fun u v ⟨hu, hv, he⟩ => ?_
    exact ⟨hu, hv, (hedge n M hM hDM u v hu hv).mp he⟩
  · rintro ⟨n, M, s, t, hM, hs, ht, hx, hr⟩
    obtain ⟨h1, h2, h3, h4⟩ := (eq_pathRaw_iff x n M s t).mp hx
    rw [hM] at h3 h4
    refine ⟨n, (unaryRest_iff x n).mpr h1, (matRest_iff x n).mpr ⟨M, hM, h2⟩, s, hs, h3, t, ht,
      h4, (reach_iff_walkLe hs ht).mp (hr.mono fun u v ⟨hu, hv, he⟩ => ?_)⟩
    exact ⟨hu, hv, (hedge n M hM h2 u v hu hv).mpr he⟩

/-! ## Fields and counters -/

/-- The binary digits of a positive number: its parity, then the digits of its half. -/
lemma bits_eq_cons {w : ℕ} (hw : w ≠ 0) :
    Nat.bits w = decide (w % 2 = 1) :: Nat.bits (w / 2) := by
  have h1 := LogProg.bits_head_odd w
  rw [if_neg hw] at h1
  have h2 := LogProg.bits_half w
  cases hl : Nat.bits w with
  | nil => rw [hl] at h1; simp at h1
  | cons b t =>
    rw [hl] at h1 h2
    simp only [List.head?_cons, Option.some.injEq, List.tail_cons] at h1 h2
    rw [h1, h2]

/-- A doubled field with a first bit. -/
lemma dblAt_cons (x : List Bool) (q : ℕ) (b : Bool) (u : List Bool) :
    DblAt x q (b :: u) ↔
      (x.getD q false = b ∧ x.getD (q + 1) false = b) ∧ DblAt x (q + 2) u := by
  simp only [DblAt, List.length_cons]
  have e1 : ∀ i, q + 2 * (i + 1) = q + 2 + 2 * i := fun i => by ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, ?_, ?_⟩
    · have := h1 (i + 1) (by omega)
      rw [e1, List.getD_cons_succ] at this
      exact this
    · rw [← e1]; exact h2
    · rw [← e1]; exact h3
  · rintro ⟨⟨h0, h0'⟩, h1, h2, h3⟩
    refine ⟨fun i hi => ?_, by rw [e1]; exact h2, by rw [e1]; exact h3⟩
    cases i with
    | zero => simpa using ⟨h0, h0'⟩
    | succ i => rw [e1, List.getD_cons_succ]; exact h1 i (by omega)

/-- A plain suffix with a first bit. -/
lemma plainAt_cons (x : List Bool) (r : ℕ) (b : Bool) (u : List Bool) :
    PlainAt x r (b :: u) ↔ x.getD r false = b ∧ PlainAt x (r + 1) u := by
  simp only [PlainAt, List.length_cons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, by omega⟩
    have := h1 (i + 1) (by omega)
    rw [← Nat.add_assoc, List.getD_cons_succ] at this
    rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]; exact this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun i hi => ?_, by omega⟩
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [show r + (i + 1) = r + 1 + i by omega, List.getD_cons_succ]; exact h1 i (by omega)

/-- Advancing a row-major counter: the column wraps at `n` into the next row. -/
lemma divmod_succ {n i : ℕ} (hn : 0 < n) :
    (i % n + 1 = n → (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0) ∧
    (i % n + 1 ≠ n → (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1) := by
  have h1 := Nat.div_add_mod i n
  have h2 := Nat.mod_lt i hn
  refine ⟨fun h => (Nat.div_mod_unique hn).mpr ⟨?_, hn⟩, fun h => (Nat.div_mod_unique hn).mpr
    ⟨by omega, by omega⟩⟩
  rw [Nat.mul_succ]; omega

/-- The row counter reaches `n` exactly at pair `n²`. -/
lemma div_eq_self_iff {n i : ℕ} (hi : i ≤ n * n) : i / n = n ↔ i = n * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hi ⊢; omega
  · constructor
    · intro h
      have := Nat.div_mul_le_self i n
      rw [h] at this; omega
    · rintro rfl; exact Nat.mul_div_cancel n hn

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Checks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance as a chain of codes

The bridge between a space-bounded nondeterministic decider and the code languages: for a
window radius `s` at least the space bound on `x`, `x` is accepted exactly when there is a
chain of codes `c₀, …, c_t` — the initial code, configuration-graph edges between
consecutive codes, an accepting last code — of length at most the vertex count
`Turing.FinNDTM.configBound |x| s`, every code below `2 ^ (codeK N · (s + logSpace |x| + 1))`.
This is the form in which configuration-graph algorithms (Savitch's midpoint recursion, the
`PATH` reduction, inductive counting) consume a nondeterministic decider [AB09, §4.1.1,
§4.2, §4.3]: they search for such chains over register-held codes, calling the logspace
deciders of the code languages.

The window of a space-bounded branch and the step "an accepting branch of any length gives
membership" are those of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`
(`Turing.NDTM.runWith_take_inWindow`, `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`),
over the window predicate `Turing.Cfg.InWindow`. Within the codec, the path-to-membership
argument exists once (`mem_of_codePath`); `mem_iff_codeChain` and the Savitch machine
(`Complexity.LogProg.SavitchARM.mem_iff_reach`) both use it.

## Main definitions

* `Complexity.Codec.StepRel` — the code-level step relation of a decider.

## Main results

* `Complexity.Codec.configBound_mono` — a helper.
* `Complexity.Codec.stepRel_iff_mem` — `StepRel`'s defining equation.
* `Complexity.Codec.mem_of_codePath` — a `StepRel`-path of any length from an initial to an
  accepting code gives membership.
* `Complexity.Codec.mem_iff_codeChain` — the bridge lemma. [AB09, §4.1.1, Claim 4.4(1) in
  code form]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## The bridge -/

/-- The vertex count is monotone in the window radius. -/
lemma configBound_mono (N : FinNDTM Bool) (n : ℕ) {s s' : ℕ} (h : s ≤ s') :
    N.configBound n s ≤ N.configBound n s' := by
  unfold FinNDTM.configBound
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  · exact Nat.pow_le_pow_left (by omega) _

/-- **The code-level step relation** of `N` on `x` at radius `s`: `⟨x, ⟨bits a, ⟨bits b,
bits s⟩⟩⟩` is a step pair (a member of `Complexity.Codec.stepLang N`). -/
def StepRel (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (a b : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits s))) ∈ stepLang N

/-- `Complexity.Codec.StepRel`'s defining equation: a step pair is a member of the step
language. -/
theorem stepRel_iff_mem {s a b : ℕ} :
    StepRel N x s a b ↔
      pairEncode x (pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits s))) ∈
        stepLang N :=
  Iff.rfl

/-- **A code path from an initial to an accepting code makes the input a member**: if `N`
decides `L` (in any space bound), `u` is the initial code and `v` an accepting code at
radius `s`, and `v` is reachable from `u` along step pairs (`Relation.ReflTransGen` of
`StepRel N x s`, of any length), then `x ∈ L`. This is the direction `⇐` of
`Complexity.Codec.mem_iff_codeChain`, without its length and size bounds. [AB09, §4.1.1:
a path from the initial to an accepting configuration in the configuration graph is an
accepting branch]

**Proof sketch.** By induction along the path, some choice word reaches a configuration with
the vertex of the current code: codes determine vertices on window-bounded configurations
(`coreSum_eq_of_cfgWord_eq`) and steps respect vertices (`Turing.NDTM.coreSum_stepWith`).
At the accepting code the vertex is halted with output `[true]`, so the word accepts, and an
accepting branch of any length gives membership
(`Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`). -/
theorem mem_of_codePath {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s u v : ℕ)
    (hinit : pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N)
    (hpath : Relation.ReflTransGen (StepRel N x s) u v)
    (hacc : pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N) : x ∈ L := by
  rw [mem_initLang] at hinit
  have chain : ∀ c, Relation.ReflTransGen (StepRel N x s) u c → ∃ w : List Bool,
      ∃ D : Cfg N.k Bool N.State x, Cfg.InWindow s D ∧ cfgCode s D = c ∧
        NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum D := by
    intro c hc
    induction hc with
    | refl =>
      exact ⟨[], N.tm.initCfg x, Cfg.inWindow_init _ x s, hinit, rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, D, hD, hcD, hcore⟩ := ih
      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
      have hDC : NDTM.coreSum D = NDTM.coreSum C :=
        coreSum_eq_of_cfgWord_eq hD hC (by rw [← bits_cfgCode, ← bits_cfgCode, hcD, hcC])
      refine ⟨w ++ [b], C', hC', hcC', ?_⟩
      rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil, ← hb]
      exact NDTM.coreSum_stepWith N.tm b (hcore.trans hDC)
  obtain ⟨w, D, hD, hcD, hcore⟩ := chain v hpath
  obtain ⟨C, hC, hcC, hst, hout⟩ := (mem_acceptLang N x _ s).mp hacc
  have hDC : NDTM.coreSum D = NDTM.coreSum C :=
    coreSum_eq_of_cfgWord_eq hD hC (by rw [← bits_cfgCode, ← bits_cfgCode, hcD, hcC])
  have hfin := hcore.trans hDC
  apply h.mem_of_acceptsWithin (t := w.length)
  refine ⟨w, rfl, ?_, ?_⟩
  · have := congrArg (fun z => z.1.1) hfin
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at this
    rw [this, hst]
  · have := congrArg Prod.snd hfin
    simp only [NDTM.coreSum] at this
    rw [hout] at this
    exact (outSummary_eq_accept_iff _).mp this

/-- **Acceptance as a chain of codes** (the bridge lemma): let `N` decide `L` in space `sp`,
and let `s ≥ sp |x|`. Then `x ∈ L` iff there are `t ≤ configBound |x| s` and codes
`c 0, …, c t` such that `c 0` is the initial code, each `(c i, c (i + 1))` is a step pair,
`c t` is an accepting code (all at radius `s`, as memberships in the code languages), and
every code is below `2 ^ (codeK N · (s + logSpace |x| + 1))`. [AB09, §4.1.1: the machine
accepts iff the configuration graph has a path from the initial to an accepting
configuration; Claim 4.4(1) bounds its length by the vertex count]

**Proof sketch.** (⇒) Take an accepting branch of length the vertex count at the space bound
(`DecidesInSpace.mem_iff_acceptsWithin_configBound`, `configBound_mono`); its prefixes stay in
the window `[-s, s]` (`Turing.NDTM.runWith_take_inWindow`: compare with a branch of the
halting budget — padding the accepting word, or truncating it where every branch has halted);
the codes of
the prefix configurations form the chain, consecutive prefixes differing by one step, the
last halted with output `[true]`; codes are short (`cfgCode_lt`). (⇐) The chain is a
`StepRel`-path from the initial to the accepting code, which gives membership
(`mem_of_codePath`). -/
theorem mem_iff_codeChain {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s : ℕ) (hs : sp x.length ≤ s) :
    x ∈ L ↔ ∃ (t : ℕ) (c : ℕ → ℕ), t ≤ N.configBound x.length s ∧
      pairEncode x (pairEncode (Nat.bits (c 0)) (Nat.bits s)) ∈ initLang N ∧
      (∀ i < t, pairEncode x (pairEncode (Nat.bits (c i))
        (pairEncode (Nat.bits (c (i + 1))) (Nat.bits s))) ∈ stepLang N) ∧
      pairEncode x (pairEncode (Nat.bits (c t)) (Nat.bits s)) ∈ acceptLang N ∧
      ∀ i ≤ t, c i < 2 ^ (codeK N * (s + logSpace x.length + 1)) := by
  constructor
  · intro hx
    obtain ⟨w, hw, hhalt, hout⟩ := (h.mem_iff_acceptsWithin_configBound x).mp hx
    set tb := N.configBound x.length (sp x.length)
    obtain ⟨T, hHalt, hSpace, -⟩ := h x
    -- every prefix configuration is in the window
    have hwin : ∀ j, Cfg.InWindow s (N.tm.runWith (w.take j) (N.tm.initCfg x)) := by
      by_cases hT : tb ≤ T
      · intro j
        set w' := w ++ List.replicate (T - tb) false
        have hw' : w'.length = T := by simp [w', hw]; omega
        have hsp := (hSpace w' hw').trans hs
        by_cases hj : j ≤ tb
        · have e : w'.take j = w.take j := by
            simp only [w']; rw [List.take_append_of_le_length (by omega)]
          rw [← e]; exact NDTM.runWith_take_inWindow N.tm w' hsp j
        · have e1 : w.take j = w := List.take_of_length_le (by omega)
          have e2 : w'.take tb = w := by
            simp only [w']; rw [List.take_append_of_le_length (by omega),
              List.take_of_length_le (by omega)]
          rw [e1, ← e2]; exact NDTM.runWith_take_inWindow N.tm w' hsp tb
      · intro j
        have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
        have hsp := (hSpace (w.take T) hlen).trans hs
        by_cases hj : j ≤ T
        · have e : (w.take T).take j = w.take j := by rw [List.take_take, Nat.min_eq_left hj]
          rw [← e]; exact NDTM.runWith_take_inWindow N.tm (w.take T) hsp j
        · have frozen : N.tm.runWith (w.take j) (N.tm.initCfg x) =
              N.tm.runWith (w.take T) (N.tm.initCfg x) := by
            have : w.take j = w.take T ++ (w.take j).drop T := by
              conv_lhs => rw [← List.take_append_drop T (w.take j)]
              rw [List.take_take, Nat.min_eq_left (by omega : T ≤ j)]
            rw [this, NDTM.runWith_append, NDTM.runWith_of_halt _ (hHalt _ hlen)]
          rw [frozen, show w.take T = (w.take T).take T by simp]
          exact NDTM.runWith_take_inWindow N.tm (w.take T) hsp T
    refine ⟨tb, fun i => cfgCode s (N.tm.runWith (w.take i) (N.tm.initCfg x)),
      configBound_mono N _ hs, ?_, fun i hi => ?_, ?_, fun i _ => cfgCode_lt s _⟩
    · rw [mem_initLang]; simp
    · rw [mem_stepLang]
      refine ⟨_, hwin i, rfl, _, ⟨w[i]'(by omega), ?_⟩, hwin (i + 1), rfl⟩
      rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
      rfl
    · rw [mem_acceptLang]
      refine ⟨_, hwin tb, rfl, ?_, ?_⟩
      · rw [← hw, List.take_length]; exact hhalt
      · rw [← hw, List.take_length]; exact hout
  · rintro ⟨t, c, -, hinit, hstep, hacc, -⟩
    have hpath : ∀ j ≤ t, Relation.ReflTransGen (StepRel N x s) (c 0) (c j) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih => intro hj; exact (ih (by omega)).tail (hstep j (by omega))
    exact mem_of_codePath h x s (c 0) (c t) hinit (hpath t le_rfl) hacc

end Complexity.Codec
```

## ===== TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Run
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The midpoint recursion of the Savitch register machine

The recursive part of `Complexity.LogProg.SavitchARM.A` computes midpoint reachability:
started at label `cl` on a node `(U, V)` at level `I = i`, with any stack contents of the
right size below it, the machine returns at label `rt b` with `b` the truth value of
`Reach (2 ^ w) R i U V` — with the same registers, except the scratch midpoint register `M`
(`Complexity.LogProg.SavitchARM.call_spec`). Here `R` is the step relation answered by
decider `3` on codes at radius `s`.

The proof is an induction on the level, mirroring the recursion of [AB09, §4.2.1, proof of
Theorem 4.14]: at a positive level the midpoint loop (`loop_spec`) descends into the first
half (`desc1`, pushing `(V, 0)`), and, if that half is reachable, into the second half
(`desc2`, pushing `(U, 1)`); every return pops the frame it pushed (`pop_run`) and dispatches
on its phase bit. The stack invariant `Complexity.LogProg.SavitchARM.Inv` bounds the
`w`-bit-digit stack `SE` by `2 ^ (w (w - i))` and the phase stack `SP` by `2 ^ (w - i)`, so
every register stays below `2 ^ (w · w)`.

## Main definitions

* `Complexity.LogProg.SavitchARM.Rel` — the step relation read from the oracle, with its
  defining equation `rel_iff_orc`.
* `Complexity.LogProg.SavitchARM.Inv` — the register invariant at a level.

## Main results

* `Complexity.LogProg.SavitchARM.call_spec` — the recursion computes `Reach`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- **The step relation read from the oracle**: decider `3` accepts
`⟨x, ⟨bits u, ⟨bits v, bits s⟩⟩⟩`. -/
def Rel (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s u v : ℕ) : Prop :=
  orc 3 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) = true

/-- `Rel orc x s u v` holds exactly when decider `3` accepts `⟨x, ⟨bits u, ⟨bits v, bits s⟩⟩⟩`:
`orc 3 (pairEncode x (pairEncode (bits u) (pairEncode (bits v) (bits s)))) = true`. -/
theorem rel_iff_orc {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s u v : ℕ} :
    Rel orc x s u v ↔
      orc 3 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) =
        true :=
  Iff.rfl

/-- **The register invariant at level `i`**: the setup registers and the scratch registers
are clear, the radius, width and code bound are in place, the node's codes are below
`2 ^ w`, the midpoint is at most `2 ^ w`, and the two stacks hold at most `w - i` frames. -/
structure Inv (s w i : ℕ) (st : St) : Prop where
  /-- the input-length counter is clear -/
  hn : st.n = 0
  /-- the base register is clear -/
  ha : st.a = 0
  /-- the exponent counter is clear -/
  hX : st.X = 0
  /-- the power accumulator is clear -/
  hP : st.P = 0
  /-- the scratch register `T` is clear -/
  hT : st.T = 0
  /-- the scratch register `Z` is clear -/
  hZ : st.Z = 0
  /-- the loop counter is clear -/
  hC : st.C = 0
  /-- the scratch register `Q` is clear -/
  hQ : st.Q = 0
  /-- the popped-endpoint register is clear -/
  hE : st.E = 0
  /-- the radius is `s` -/
  hs : st.s = s
  /-- the width is `w` -/
  hw : st.w = w
  /-- the code bound is `2 ^ w` -/
  hK : st.K = 2 ^ w
  /-- the source code is below `2 ^ w` -/
  hU : st.U < 2 ^ w
  /-- the target code is below `2 ^ w` -/
  hV : st.V < 2 ^ w
  /-- the midpoint is at most `2 ^ w` -/
  hM : st.M ≤ 2 ^ w
  /-- the level is `i` -/
  hI : st.I = i
  /-- the endpoint stack holds at most `w - i` digits of `w` bits -/
  hSE : st.SE < 2 ^ (w * (w - i))
  /-- the phase stack holds at most `w - i` bits -/
  hSP : st.SP < 2 ^ (w - i)

/-- The basic size facts: `w ≤ 2 ^ w ≤ 2 ^ (w · w)`. -/
lemma size_facts (w : ℕ) : w < 2 ^ w ∧ 2 ^ w ≤ 2 ^ (w * w) :=
  ⟨Nat.lt_two_pow_self, Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self w)⟩

/-- **The invariant bounds the registers** by `2 ^ (w · w)`. -/
lemma Inv.bd {s w i : ℕ} {st : St} (h : Inv s w i st) (hsw : s ≤ w) (hi : i ≤ w) :
    st.Bd (2 ^ (w * w)) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h.hn; have := h.ha; have := h.hX; have := h.hP; have := h.hT; have := h.hZ
  have := h.hC; have := h.hQ; have := h.hE; have := h.hs; have := h.hw; have := h.hK
  have := h.hU; have := h.hV; have := h.hM; have := h.hI; have := h.hSE; have := h.hSP
  simp only [St.Bd]
  omega

/-- **Pushing a digit keeps the stack within one more frame**: `SE < 2 ^ (w (w - (i + 1)))`
and `v < 2 ^ w` give `SE · 2 ^ w + v < 2 ^ (w (w - i))`. -/
lemma push_lt {w i SE v : ℕ} (hi : i + 1 ≤ w) (hSE : SE < 2 ^ (w * (w - (i + 1))))
    (hv : v < 2 ^ w) : SE * 2 ^ w + v < 2 ^ (w * (w - i)) := by
  have e : w * (w - i) = w * (w - (i + 1)) + w := by
    rw [show w - i = w - (i + 1) + 1 by omega, Nat.mul_succ]
  rw [e, pow_add]
  have : (SE + 1) * 2 ^ w ≤ 2 ^ (w * (w - (i + 1))) * 2 ^ w :=
    Nat.mul_le_mul_right _ hSE
  rw [Nat.add_mul, one_mul] at this
  omega

/-- Pushing a phase bit keeps the phase stack within one more frame. -/
lemma pushP_lt {w i SP : ℕ} (hi : i + 1 ≤ w) (hSP : SP < 2 ^ (w - (i + 1))) :
    2 * SP + 1 < 2 ^ (w - i) := by
  rw [show w - i = w - (i + 1) + 1 by omega, pow_succ]
  omega

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s w : ℕ}

open Classical in
/-- **The base case**: at level `0` the machine answers `U = V ∨ R U V`.

**Proof sketch.** `cl` sees `I = 0` and calls decider `3` on `⟨x, ⟨bits U, ⟨bits V, bits s⟩⟩⟩`;
on a negative answer it compares `U` with `V`. -/
theorem base_spec (hsw : s ≤ w) (st : St) (h : Inv s w 0 st) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .cl, st.toV, none)
      (some (.rt (decide (Reach (2 ^ w) (Rel orc x s) 0 st.U st.V))), st.toV, none) := by
  have hbd := h.bd hsw (Nat.zero_le _)
  refine step_of hbd ?_
  regs [astep, A, h.hI, ↓reduceIte]
  refine step_of hbd ?_
  simp only [astep, A, vword_whole₃]
  regs [h.hs]
  by_cases hr : Rel orc x s st.U st.V
  · have hr' : orc 3 (pairEncode x (pairEncode (Nat.bits st.U)
        (pairEncode (Nat.bits st.V) (Nat.bits s)))) = true := hr
    rw [if_pos hr', decide_eq_true (show Reach (2 ^ w) (Rel orc x s) 0 st.U st.V from Or.inr hr)]
    exact AReach.refl _
  · have hr' : ¬ orc 3 (pairEncode x (pairEncode (Nat.bits st.U)
        (pairEncode (Nat.bits st.V) (Nat.bits s)))) = true := hr
    rw [if_neg hr']
    refine step_of hbd ?_
    regs [astep, A]
    by_cases he : st.U = st.V
    · rw [if_pos he, decide_eq_true (show Reach (2 ^ w) (Rel orc x s) 0 st.U st.V from Or.inl he)]
      exact AReach.refl _
    · rw [if_neg he, decide_eq_false (show ¬ Reach (2 ^ w) (Rel orc x s) 0 st.U st.V by
        rintro (h1 | h1) <;> contradiction)]
      exact AReach.refl _

/-- Close a register-file bound from the unfolded bounds in context. -/
scoped macro "bdt" : tactic => `(tactic| (simp only [St.Bd]; omega))

variable (E orc x s w) in
open Classical in
/-- **The recursion is correct at level `i`**: from `cl` on any register file meeting the
invariant at level `i`, the machine reaches `rt b`, `b` the truth value of
`Reach (2 ^ w) R i U V`, changing only the midpoint register (to a value at most `2 ^ w`). -/
def CallOK (i : ℕ) : Prop :=
  ∀ st, Inv s w i st → ∃ M', M' ≤ 2 ^ w ∧
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .cl, st.toV, none)
      (some (.rt (decide (Reach (2 ^ w) (Rel orc x s) i st.U st.V))),
        St.toV { st with M := M' }, none)

open Classical in
/-- **The first descent**: from `loop` at level `i + 1` with midpoint `m = M < 2 ^ w`, the
machine pushes `(V, 0)`, evaluates the first half `(U, m)` at level `i`, pops the frame, and
reaches `cp (push true)` if the first half is reachable and `a0F` otherwise, with `V = m`
and the popped endpoint in `E`.

**Proof sketch.** `pushV_run`, the move of `M` into `V` and the decrement of `I`; the
recursion at level `i` (`CallOK`); at `rt b` the level is below `w`, so `pop_run` restores
`SE` and returns the saved `V` in `E`; `I` is incremented, the even phase stack selects
`h0`, which halves it back. -/
theorem desc1 (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) (st : St)
    (h : Inv s w (i + 1) st) (hm : st.M < 2 ^ w) :
    ∃ M1, M1 ≤ 2 ^ w ∧ AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .loop, st.toV, none)
      (some (if decide (Reach (2 ^ w) (Rel orc x s) i st.U st.M) then .cp (.push true) 0
        else .a0F), St.toV { st with V := st.M, M := M1, E := st.V }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hbd := h.bd hsw hi
  have hSE1 := push_lt hi h.hSE h.hV
  have hSP1 := pushP_lt hi h.hSP
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : Inv s w i
      { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := 0, I := i } :=
    ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, h.hU, hm,
      Nat.zero_le _, rfl, hSE1, by show 2 * st.SP < 2 ^ (w - i); omega⟩
  obtain ⟨M1, hM1, hc⟩ := IH _ h3
  dsimp only at hc
  refine ⟨M1, hM1, ?_⟩
  have hw := h.hw
  -- `loop`: the midpoint is below `K`
  refine step_of hbd ?_
  regs [astep, A, if_neg (show st.M ≠ st.K by rw [h.hK]; exact hm.ne)]
  -- push `(V, 0)`
  refine (pushV_run st h.hC h.hT h.hZ hbd (by rw [hw]; omega) (by omega)).trans ?_
  have hbd1 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ st.w + st.V, V := 0, SP := 2 * st.SP } := by
    have := hbd; simp only [St.Bd] at this ⊢; rw [hw]; omega
  have hMB : st.M ≤ 2 ^ (w * w) := by omega
  refine (mv_run .descM _ hbd1 (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  have hbd2 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ st.w + st.V, V := st.M, SP := 2 * st.SP, M := 0 } := by
    have := hbd; simp only [St.Bd] at this ⊢; rw [hw]; omega
  refine step_of hbd2 ?_
  regs [astep, A]
  refine cont (by ext <;> simp [hw, h.hI]) (hc.trans ?_)
  -- `rt b`: not the root, pop the frame
  have hbd4 := (h3.bd hsw (by omega))
  have hbd4' : St.Bd (2 ^ (w * w))
      { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := M1, I := i } := by
    simp only [St.Bd] at hbd4 ⊢; omega
  refine step_of hbd4' ?_
  regs [astep, A, if_neg (show i ≠ st.w by omega)]
  refine (pop_run _
    { st with SE := st.SE * 2 ^ w + st.V, V := st.M, SP := 2 * st.SP, M := M1, I := i }
    st.SE st.V h.hC h.hT h.hZ h.hQ h.hE hbd4' (by simp [hw]) (by simp [hw]; exact h.hV)).trans ?_
  have hbd5 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE, V := st.M, SP := 2 * st.SP, M := M1, I := i, E := st.V } := by
    have := Nat.le_mul_of_pos_right st.SE (Nat.two_pow_pos w)
    simp only [St.Bd] at hbd4 ⊢; have := h.hV; omega
  refine step_of hbd5 ?_
  regs [astep, A]
  have hbd6 : St.Bd (2 ^ (w * w))
      { st with SE := st.SE, V := st.M, SP := 2 * st.SP, M := M1, I := i + 1, E := st.V } := by
    simp only [St.Bd] at hbd5 ⊢; omega
  refine step_of hbd6 ?_
  regs [astep, A, Nat.mul_mod_right, zero_ne_one, if_false]
  refine step_of hbd6 ?_
  regs [astep, A]
  refine reach_of_eq (AReach.refl _) ?_
  congr 3
  ext <;> simp [h.hI]

open Classical in
/-- **The second descent**: from `cp (push true)` after a reachable first half (`V = m`,
`E` the saved target), the machine pushes `(U, 1)`, evaluates the second half `(m, V)` at
level `i`, pops the frame, and reaches `a1T` if the second half is reachable and `a1F`
otherwise, with `U = m` and the saved source in `E`.

**Proof sketch.** `pushU_run`, the increment of the phase stack, the moves `V → U`,
`E → V` and the decrement of `I`; the recursion at level `i`; `pop_run` restores `SE` and
returns the saved `U` in `E`; the odd phase stack selects `h1`, which halves it back. -/
theorem desc2 (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) (st : St)
    (h : Inv s w (i + 1) st) (hm : st.M < 2 ^ w) (M1 : ℕ) (hM1 : M1 ≤ 2 ^ w) :
    ∃ M2, M2 ≤ 2 ^ w ∧ AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some (.cp (.push true) 0), St.toV { st with V := st.M, M := M1, E := st.V }, none)
      (some (if decide (Reach (2 ^ w) (Rel orc x s) i st.M st.V) then .a1T else .a1F),
        St.toV { st with U := st.M, M := M2, E := st.U }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hbd := h.bd hsw hi
  have hB := hbd
  simp only [St.Bd] at hB
  have hSE1 := push_lt hi h.hSE h.hU
  have hSP1 := pushP_lt hi h.hSP
  have g1 : 2 ^ (w * (w - i)) ≤ 2 ^ (w * w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have g2 : 2 ^ (w - i) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := Nat.le_mul_of_pos_right st.SE (Nat.two_pow_pos w)
  have h3 : Inv s w i
      { st with SE := st.SE * 2 ^ w + st.U, U := st.M, SP := 2 * st.SP + 1, M := M1, I := i } :=
    ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, hm, h.hV,
      hM1, rfl, hSE1, hSP1⟩
  obtain ⟨M2, hM2, hc⟩ := IH _ h3
  dsimp only at hc
  refine ⟨M2, hM2, ?_⟩
  have hw := h.hw
  have hV := h.hV
  have hU := h.hU
  have hSEw : st.SE * 2 ^ st.w = st.SE * 2 ^ w := by rw [hw]
  -- push `(U, 1)`
  refine (pushU_run { st with V := st.M, M := M1, E := st.V } h.hC h.hT h.hZ (by bdt)
    (by show st.SE * 2 ^ st.w + st.U ≤ _; rw [hw]; omega)
    (by show 2 * st.SP ≤ _; omega)).trans ?_
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a0T1 _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine (mv_run .a0T2 _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine cont (by ext <;> simp [hw, h.hI, h.hE]) (hc.trans ?_)
  -- `rt b`: not the root, pop the frame
  have hB3 := h3.bd hsw (by omega)
  simp only [St.Bd] at hB3
  refine step_of (by bdt) ?_
  regs [astep, A, if_neg (show i ≠ st.w by omega)]
  refine (pop_run _
    { st with SE := st.SE * 2 ^ w + st.U, U := st.M, SP := 2 * st.SP + 1, M := M2, I := i }
    st.SE st.U h.hC h.hT h.hZ h.hQ h.hE (by bdt) (by simp [hw]) (by simp [hw]; exact hU)).trans ?_
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine step_of (by bdt) ?_
  regs [astep, A, Nat.mul_add_mod, if_true]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (AReach.refl _) ?_
  congr 3
  ext <;> simp [h.hI]
  omega

/-- **The tail after an unreachable first half**: from `a0F`, the machine sets `M := V + 1`,
moves the saved target back into `V`, and returns to `loop`.

**Proof sketch.** A clear, two moves and an increment. -/
theorem tail0F (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (hm : st.M < 2 ^ w) (M1 : ℕ) (hM1 : M1 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a0F, St.toV { st with V := st.M, M := M1, E := st.V }, none)
      (some .loop, St.toV { st with M := st.M + 1 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hV := h.hV
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a0FM _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a0FV _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- **The tail after a reachable second half**: from `a1T`, the machine moves the saved
source back into `U` and answers `true`.

**Proof sketch.** A clear and a move. -/
theorem tail1T (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (M2 : ℕ) (hM2 : M2 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a1T, St.toV { st with U := st.M, M := M2, E := st.U }, none)
      (some (.rt true), St.toV { st with M := M2 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hU := h.hU
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a1TU _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- **The tail after an unreachable second half**: from `a1F`, the machine sets
`M := U + 1`, moves the saved source back into `U`, and returns to `loop`.

**Proof sketch.** A clear, two moves and an increment. -/
theorem tail1F (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (st : St) (h : Inv s w (i + 1) st)
    (hm : st.M < 2 ^ w) (M2 : ℕ) (hM2 : M2 ≤ 2 ^ w) :
    AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .a1F, St.toV { st with U := st.M, M := M2, E := st.U }, none)
      (some .loop, St.toV { st with M := st.M + 1 }, none) := by
  obtain ⟨f1, f2⟩ := size_facts w
  have hB := h.bd hsw hi
  simp only [St.Bd] at hB
  have hU := h.hU
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine (mv_run .a1FM _ (by bdt) (by regs [mvDst, mvSrc]; omega)).trans ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  refine step_of (by bdt) ?_
  regs [astep, A]
  refine reach_of_eq (mv_run .a1FU _ (by bdt) (by regs [mvDst, mvSrc]; omega)) ?_
  regs [mvDst, mvSrc, mvExit, zero_add]
  congr 3
  ext <;> simp [h.hE]

/-- The invariant does not constrain the midpoint beyond `M ≤ 2 ^ w`. -/
lemma Inv.setM {s w i : ℕ} {st : St} (h : Inv s w i st) {M' : ℕ} (hM : M' ≤ 2 ^ w) :
    Inv s w i { st with M := M' } :=
  ⟨h.hn, h.ha, h.hX, h.hP, h.hT, h.hZ, h.hC, h.hQ, h.hE, h.hs, h.hw, h.hK, h.hU, h.hV, hM,
    h.hI, h.hSE, h.hSP⟩

/-- Skipping a failing candidate does not change a bounded search. -/
lemma exists_shift {R₁ R₂ : ℕ → Prop} {a K : ℕ} (h : ¬ (R₁ a ∧ R₂ a)) :
    (∃ m, a + 1 ≤ m ∧ m < K ∧ R₁ m ∧ R₂ m) ↔ (∃ m, a ≤ m ∧ m < K ∧ R₁ m ∧ R₂ m) := by
  constructor
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, by omega, h2, h3⟩
  · rintro ⟨m, h1, h2, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact absurd h3 h
    · exact ⟨m, h1, h2, h3⟩

open Classical in
/-- **The midpoint loop**: from `loop` at level `i + 1` with midpoint `M`, the machine
answers at `rt b` whether some `m` with `M ≤ m < 2 ^ w` has both halves reachable at level
`i`, changing only `M`.

**Proof sketch.** Induction on `2 ^ w - M`. At `M = 2 ^ w` the machine answers `false`.
Below, the first descent (`desc1`) evaluates the first half; if it fails, `tail0F` moves to
`M + 1`; otherwise the second descent (`desc2`) evaluates the second half, and `tail1T`
answers `true` or `tail1F` moves to `M + 1`. Moving past a failing candidate leaves the
answer unchanged (`exists_shift`). -/
theorem loop_spec (hsw : s ≤ w) (i : ℕ) (hi : i + 1 ≤ w) (IH : CallOK E orc x s w i) :
    ∀ k (st : St), Inv s w (i + 1) st → st.M + k = 2 ^ w → ∃ M', M' ≤ 2 ^ w ∧
      AReach (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .loop, st.toV, none)
        (some (.rt (decide (∃ m, st.M ≤ m ∧ m < 2 ^ w ∧ Reach (2 ^ w) (Rel orc x s) i st.U m ∧
          Reach (2 ^ w) (Rel orc x s) i m st.V))), St.toV { st with M := M' }, none) := by
  intro k
  induction k with
  | zero =>
    intro st h hk
    refine ⟨st.M, h.hM, ?_⟩
    refine step_of (h.bd hsw hi) ?_
    regs [astep, A, if_pos (show st.M = st.K by rw [h.hK]; omega)]
    rw [decide_eq_false (by rintro ⟨m, h1, h2, -⟩; omega)]
    exact AReach.refl _
  | succ k ih =>
    intro st h hk
    have hm : st.M < 2 ^ w := by omega
    have hnext := h.setM (M' := st.M + 1) (by omega)
    obtain ⟨M1, hM1, h1⟩ := desc1 hsw i hi IH st h hm
    by_cases r1 : Reach (2 ^ w) (Rel orc x s) i st.U st.M
    · simp only [r1, decide_true, if_true] at h1
      obtain ⟨M2, hM2, h2⟩ := desc2 hsw i hi IH st h hm M1 hM1
      by_cases r2 : Reach (2 ^ w) (Rel orc x s) i st.M st.V
      · simp only [r2, decide_true, if_true] at h2
        refine ⟨M2, hM2, ?_⟩
        rw [decide_eq_true ⟨st.M, le_rfl, hm, r1, r2⟩]
        exact h1.trans (h2.trans (tail1T hsw i hi st h M2 hM2))
      · simp only [r2, decide_false, Bool.false_eq_true, if_false] at h2
        obtain ⟨M', hM', h3⟩ := ih _ hnext (by show st.M + 1 + k = 2 ^ w; omega)
        dsimp only at h3
        have e := exists_shift (R₁ := fun m => Reach (2 ^ w) (Rel orc x s) i st.U m)
          (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) i m st.V) (a := st.M) (K := 2 ^ w)
          (fun hh => r2 hh.2)
        beta_reduce at e
        rw [decide_eq_decide.mpr e] at h3
        exact ⟨M', hM', h1.trans (h2.trans ((tail1F hsw i hi st h hm M2 hM2).trans h3))⟩
    · simp only [r1, decide_false, Bool.false_eq_true, if_false] at h1
      obtain ⟨M', hM', h3⟩ := ih _ hnext (by show st.M + 1 + k = 2 ^ w; omega)
      dsimp only at h3
      have e := exists_shift (R₁ := fun m => Reach (2 ^ w) (Rel orc x s) i st.U m)
        (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) i m st.V) (a := st.M) (K := 2 ^ w)
        (fun hh => r1 hh.1)
      beta_reduce at e
      rw [decide_eq_decide.mpr e] at h3
      exact ⟨M', hM', h1.trans ((tail0F hsw i hi st h hm M1 hM1).trans h3)⟩

/-- **The recursion computes midpoint reachability** [AB09, §4.2.1, proof of
Theorem 4.14]: for every level `i ≤ w`, from `cl` on a register file meeting the invariant at
level `i`, the machine reaches `rt b` with `b` the truth value of `Reach (2 ^ w) R i U V`,
changing only `M` (`CallOK`).

**Proof sketch.** Induction on `i`. Level `0` is `base_spec`. At level `i + 1`, `cl` clears
`M` and enters the midpoint loop (`loop_spec`, using the induction hypothesis for the two
descents); the loop's answer from `M = 0` is `Reach (2 ^ w) R (i + 1) U V` by definition. -/
theorem call_spec (hsw : s ≤ w) : ∀ i, i ≤ w → CallOK E orc x s w i := by
  intro i
  induction i with
  | zero =>
    intro _ st h
    exact ⟨st.M, h.hM, base_spec hsw st h⟩
  | succ i ih =>
    intro hi st h
    have IH := ih (by omega)
    have hbd := h.bd hsw hi
    obtain ⟨M', hM', hl⟩ := loop_spec hsw i hi IH (2 ^ w) _ (h.setM (M' := 0) (Nat.zero_le _))
      (by show 0 + 2 ^ w = 2 ^ w; omega)
    refine ⟨M', hM', ?_⟩
    refine step_of hbd ?_
    regs [astep, A, if_neg (show st.I ≠ 0 by rw [h.hI]; omega)]
    refine step_of hbd ?_
    regs [astep, A]
    dsimp only at hl
    have e : (∃ m, 0 ≤ m ∧ m < 2 ^ w ∧ Reach (2 ^ w) (Rel orc x s) i st.U m ∧
        Reach (2 ^ w) (Rel orc x s) i m st.V) ↔ Reach (2 ^ w) (Rel orc x s) (i + 1) st.U st.V :=
      ⟨fun ⟨m, _, h1, h2⟩ => ⟨m, h1, h2⟩, fun ⟨m, h1, h2⟩ => ⟨m, Nat.zero_le _, h1, h2⟩⟩
    rw [decide_eq_decide.mpr e] at hl
    exact hl

end SavitchARM

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The outer search of the Savitch register machine

After the setup, `Complexity.LogProg.SavitchARM.A` runs a register `U` through the codes
below `K = 2 ^ w`, keeping those the initial-code decider accepts, and for each such `U` a
register `V` through the codes the accepting-code decider accepts; for each candidate pair
it evaluates the midpoint recursion at the root level `w`
(`Complexity.LogProg.SavitchARM.call_spec`) and accepts on success
(`outerV_run`, `outerU_run`). Together with the setup (`setup_run`), the machine answers
whether some initial code reaches some accepting code by midpoint reachability
(`savitch_halts`).

Infrastructure for [AB09, §4.2.1, proof of Theorem 4.14]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.SavitchARM.outerSt` — the register files of the outer search.
* `Complexity.LogProg.SavitchARM.InitO`, `AccO` — the code tests read from the oracle, with
  their defining equations `initO_iff_orc`, `accO_iff_orc`.

## Main results

* `Complexity.LogProg.SavitchARM.outerU_run` — the outer search.
* `Complexity.LogProg.SavitchARM.outerSt_toV` — the outer search's register files, as registers.
* `Complexity.LogProg.SavitchARM.savitch_halts` — the whole run.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- **The register files of the outer search**: after the setup, with candidate codes `u`,
`v` and midpoint register `M`. -/
def outerSt (s w u v M : ℕ) : St := { setSt s w with U := u, V := v, M := M }

/-- The initial-code test read from the oracle: decider `1` accepts `⟨x, ⟨bits u, bits s⟩⟩`. -/
def InitO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s u : ℕ) : Prop :=
  orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true

/-- `InitO orc x s u` holds exactly when decider `1` accepts `⟨x, ⟨bits u, bits s⟩⟩`:
`orc 1 (pairEncode x (pairEncode (bits u) (bits s))) = true`. -/
theorem initO_iff_orc {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s u : ℕ} :
    InitO orc x s u ↔ orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true :=
  Iff.rfl

/-- The accepting-code test read from the oracle: decider `2` accepts
`⟨x, ⟨bits v, bits s⟩⟩`. -/
def AccO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s v : ℕ) : Prop :=
  orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true

/-- `AccO orc x s v` holds exactly when decider `2` accepts `⟨x, ⟨bits v, bits s⟩⟩`:
`orc 2 (pairEncode x (pairEncode (bits v) (bits s))) = true`. -/
theorem accO_iff_orc {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s v : ℕ} :
    AccO orc x s v ↔ orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true :=
  Iff.rfl

section Outer

variable {s w u v M : ℕ}

/-- The `U` register of an outer-search file. -/
@[simp] lemma outerSt_U : (outerSt s w u v M).U = u := rfl
/-- The `V` register of an outer-search file. -/
@[simp] lemma outerSt_V : (outerSt s w u v M).V = v := rfl
/-- The `M` register of an outer-search file. -/
@[simp] lemma outerSt_M : (outerSt s w u v M).M = M := rfl
/-- The `I` register of an outer-search file. -/
@[simp] lemma outerSt_I : (outerSt s w u v M).I = 0 := rfl
/-- The `K` register of an outer-search file. -/
@[simp] lemma outerSt_K : (outerSt s w u v M).K = 2 ^ w := rfl
/-- The `w` register of an outer-search file. -/
@[simp] lemma outerSt_w : (outerSt s w u v M).w = w := rfl
/-- The `s` register of an outer-search file. -/
@[simp] lemma outerSt_s : (outerSt s w u v M).s = s := rfl

/-- **The outer search's register files, as registers**: the setup's file with the candidate
registers `U`, `V` and `M` written. -/
theorem outerSt_toV (s w u v M : ℕ) : (outerSt s w u v M).toV =
    Function.update (Function.update (Function.update (setSt s w).toV rU u) rV v) rM M := by
  rw [St.upd_U, St.upd_V, St.upd_M]
  rfl

/-- The register files of the outer search are bounded by `2 ^ (w · w)`. -/
lemma outerSt_bd (hsw : s ≤ w) (hu : u ≤ 2 ^ w) (hv : v ≤ 2 ^ w) (hM : M ≤ 2 ^ w) :
    (outerSt s w u v M).Bd (2 ^ (w * w)) := by
  obtain ⟨f1, f2⟩ := size_facts w
  simp only [St.Bd, outerSt, setSt, St.zero]
  omega

/-- The register files of the outer search, with the level set to `w`, meet the invariant
of the root level. -/
lemma outerSt_inv (hu : u < 2 ^ w) (hv : v < 2 ^ w) (hM : M ≤ 2 ^ w) :
    Inv s w w { outerSt s w u v M with I := w } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, hv, hM, rfl,
    by simp [outerSt, setSt, St.zero], by simp [outerSt, setSt, St.zero]⟩

end Outer

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s w : ℕ}

open Classical in
/-- **The inner search**: from `OV` with candidate initial code `u` and counter `v`, the
machine answers whether some accepting code `v' ∈ [v, 2 ^ w)` has
`Reach (2 ^ w) R w u v'`, and otherwise continues as from `NU` (answering `b₀`).

**Proof sketch.** Induction on `2 ^ w - v`. At `v = 2 ^ w` the machine clears `V` and goes
to `NU`. Below, it asks decider `2` about `v`; on acceptance it sets `I := w` and runs the
recursion (`call_spec`), accepting if it answers `true`; otherwise it moves to `v + 1`. -/
theorem outerV_run (hsw : s ≤ w) (u : ℕ) (hu : u < 2 ^ w) (b₀ : Bool)
    (hNU : ∀ M ≤ 2 ^ w, AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .NU, (outerSt s w u 0 M).toV, none) b₀) :
    ∀ k v M, v + k = 2 ^ w → M ≤ 2 ^ w →
      AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .OV, (outerSt s w u v M).toV, none)
        (decide (∃ v', v ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
          Reach (2 ^ w) (Rel orc x s) w u v') || b₀) := by
  intro k
  induction k with
  | zero =>
    intro v M hk hM
    have hbd := outerSt_bd hsw hu.le (le_of_eq (by omega)) hM
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_V, outerSt_K, if_pos (show v = 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A]
    rw [decide_eq_false (by rintro ⟨v', h1, h2, -⟩; omega), Bool.false_or]
    exact hNU M hM
  | succ k ih =>
    intro v M hk hM
    have hv : v < 2 ^ w := by omega
    have hbd := outerSt_bd hsw hu.le hv.le hM
    obtain ⟨f1, f2⟩ := size_facts w
    have shift : ∀ (hn : ¬ (AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u v)) (M' : ℕ),
        M' ≤ 2 ^ w → AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
          (some .NV, (outerSt s w u v M').toV, none)
          (decide (∃ v', v ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
            Reach (2 ^ w) (Rel orc x s) w u v') || b₀) := by
      intro hn M' hM'
      refine AHalt.step (gb_of (outerSt_bd hsw hu.le hv.le hM') _) ?_
      regs [astep, A, outerSt_V]
      have e := exists_shift (R₁ := fun m => AccO orc x s m)
        (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) w u m) (a := v) (K := 2 ^ w) hn
      beta_reduce at e
      rw [← decide_eq_decide.mpr e]
      exact ih (v + 1) M' (by omega) hM'
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_V, outerSt_K, if_neg (show v ≠ 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    simp only [astep, A, vword_whole₂]
    regs [outerSt_V, outerSt_s]
    by_cases ha : AccO orc x s v
    · have ha' : orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true := ha
      rw [if_pos ha']
      -- `root`: set `I := w` and run the recursion
      refine AHalt.step (gb_of hbd _) ?_
      regs [astep, A]
      refine (cp_run .rootW _ (by simp only [St.Bd, outerSt, setSt, St.zero]; omega) rfl
        (by regs [cpDst, cpSrc]; simp only [outerSt, setSt, St.zero]; omega)).halt ?_
      regs [cpDst, cpSrc, cpExit]
      obtain ⟨M', hM', hc⟩ := call_spec (E := E) (orc := orc) (x := x) hsw w le_rfl _
        (outerSt_inv (s := s) hu hv hM)
      refine contH (st' := { outerSt s w u v M with I := w }) (by ext <;> simp [outerSt, setSt,
        St.zero]) (hc.halt ?_)
      dsimp only
      have hbd' : St.Bd (2 ^ (w * w)) { outerSt s w u v M' with I := w } := by
        simp only [St.Bd, outerSt, setSt, St.zero]; omega
      refine AHalt.step (gb_of hbd' _) ?_
      regs [astep, A, outerSt_U, outerSt_V, outerSt_w, if_true]
      by_cases hr : Reach (2 ^ w) (Rel orc x s) w u v
      · simp only [hr, decide_true, ↓reduceIte]
        rw [decide_eq_true ⟨v, le_rfl, hv, ha, hr⟩, Bool.true_or]
        exact AHalt.ret rfl (gb_of hbd' _)
      · simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine AHalt.step (gb_of hbd' _) ?_
        regs [astep, A]
        exact shift (fun hh => hr hh.2) M' hM'
    · have ha' : ¬ orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true := ha
      rw [if_neg ha']
      exact shift (fun hh => ha hh.1) M hM

open Classical in
/-- **The outer search**: from `OU` with candidate `u` (and `V = 0`), the machine answers
whether some initial code `u' ∈ [u, 2 ^ w)` reaches some accepting code `v < 2 ^ w` by
midpoint reachability at level `w`.

**Proof sketch.** Induction on `2 ^ w - u`. At `u = 2 ^ w` the machine rejects. Below, it
asks decider `1` about `u`; on acceptance it runs the inner search (`outerV_run`), which
falls through to `u + 1` (the induction hypothesis, through `NU`); otherwise it moves to
`u + 1` directly. -/
theorem outerU_run (hsw : s ≤ w) : ∀ k u M, u + k = 2 ^ w → M ≤ 2 ^ w →
    AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .OU, (outerSt s w u 0 M).toV, none)
      (decide (∃ u', u ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
        ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
  intro k
  induction k with
  | zero =>
    intro u M hk hM
    have hbd := outerSt_bd hsw (le_of_eq (by omega)) (Nat.zero_le _) hM
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_U, outerSt_K, if_pos (show u = 2 ^ w by omega)]
    rw [decide_eq_false (by rintro ⟨u', h1, h2, -⟩; omega)]
    exact AHalt.ret rfl (gb_of hbd _)
  | succ k ih =>
    intro u M hk hM
    have hu : u < 2 ^ w := by omega
    have hbd := outerSt_bd hsw hu.le (Nat.zero_le _) hM
    have hNU : ∀ M' ≤ 2 ^ w, AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
        (some .NU, (outerSt s w u 0 M').toV, none)
        (decide (∃ u', u + 1 ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
          ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
      intro M' hM'
      refine AHalt.step (gb_of (outerSt_bd hsw hu.le (Nat.zero_le _) hM') _) ?_
      regs [astep, A, outerSt_U]
      exact ih (u + 1) M' (by omega) hM'
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_U, outerSt_K, if_neg (show u ≠ 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    simp only [astep, A, vword_whole₂]
    regs [outerSt_U, outerSt_s]
    by_cases hi : InitO orc x s u
    · have hi' : orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true := hi
      rw [if_pos hi']
      have h := outerV_run hsw u hu _ hNU (2 ^ w) 0 M (by omega) hM
      have e : decide (∃ u', u ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
          ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v) =
          (decide (∃ v', 0 ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
            Reach (2 ^ w) (Rel orc x s) w u v') ||
          decide (∃ u', u + 1 ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
            ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨u', h1, h2, h3, v, hv, h4, h5⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact Or.inl ⟨v, Nat.zero_le _, hv, h4, h5⟩
          · exact Or.inr ⟨u', h1, h2, h3, v, hv, h4, h5⟩
        · rintro (⟨v, -, hv, h4, h5⟩ | ⟨u', h1, h2, h3, h4⟩)
          · exact ⟨u, le_rfl, hu, hi, v, hv, h4, h5⟩
          · exact ⟨u', by omega, h2, h3, h4⟩
      rw [e]
      exact h
    · have hi' : ¬ orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true := hi
      rw [if_neg hi']
      have e := exists_shift (R₁ := fun m => InitO orc x s m)
        (R₂ := fun m => ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w m v)
        (a := u) (K := 2 ^ w) (fun hh => hi hh.1)
      beta_reduce at e
      rw [← decide_eq_decide.mpr e]
      exact hNU M hM

open Classical in
/-- **The run of the Savitch machine** [AB09, §4.2.1, proof of Theorem 4.14]: with
`n = |x|`, `s = (n + 2) ^ E` and `w = (n + 2) ^ (2E)`, the machine `A E` (with `E ≥ 1`),
started with all registers clear and decider `0` answering length queries, answers whether
some initial code `u < 2 ^ w` reaches some accepting code `v < 2 ^ w` by midpoint
reachability at level `w`, through register values at most `2 ^ (w · w)`.

**Proof sketch.** `setup_run` followed by `outerU_run` from `u = 0`. -/
theorem savitch_halts (hE : 1 ≤ E)
    (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length)) :
    AHalt (A E) orc x (GuardLe (A E) x (2 ^ ((x.length + 2) ^ (2 * E) * (x.length + 2) ^ (2 * E))))
      (some .scan, fun _ => 0, none)
      (decide (∃ u < 2 ^ (x.length + 2) ^ (2 * E), InitO orc x ((x.length + 2) ^ E) u ∧
        ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
          Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
            ((x.length + 2) ^ (2 * E)) u v)) := by
  have hsw : (x.length + 2) ^ E ≤ (x.length + 2) ^ (2 * E) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨-, f2⟩ := size_facts ((x.length + 2) ^ (2 * E))
  rw [St.toV_zero]
  refine (setup_run hE hq f2).halt ?_
  have h := outerU_run (E := E) (orc := orc) (x := x) hsw _ 0 0 (zero_add _) (Nat.zero_le _)
  have e : (∃ u', 0 ≤ u' ∧ u' < 2 ^ (x.length + 2) ^ (2 * E) ∧
      InitO orc x ((x.length + 2) ^ E) u' ∧
      ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
        Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
          ((x.length + 2) ^ (2 * E)) u' v) ↔
      ∃ u < 2 ^ (x.length + 2) ^ (2 * E), InitO orc x ((x.length + 2) ^ E) u ∧
        ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
          Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
            ((x.length + 2) ^ (2 * E)) u v :=
    ⟨fun ⟨u, _, h1, h2⟩ => ⟨u, h1, h2⟩, fun ⟨u, h1, h2⟩ => ⟨u, Nat.zero_le _, h1, h2⟩⟩
  rw [decide_eq_decide.mpr e] at h
  exact h

end SavitchARM

end Complexity.LogProg
```
