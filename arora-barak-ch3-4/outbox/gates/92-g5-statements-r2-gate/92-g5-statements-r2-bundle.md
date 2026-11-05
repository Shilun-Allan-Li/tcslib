## ===== campaign/gates/92-g5-statements/pack-r2.md =====

# External audit pack, round 2: G5's statements (PR #189, a statement gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`) was **DO NOT CLOSE,
0 blockers, 1 major, 3 minors**. The statements were found sound, and the Hennie–Stearns
admission is authorized. **Ruled (user, 2026-11-04): fix all now.**

**The PR now:** #189 at `9e96f6463e840ee775d8e6025bd245b45d68f5bd`:
- `caa6bf53`, the fixes (`evidence/round2/patches/`);
- then a merge of campaign records, which changes no Lean.

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1, `two_work_tapes_binary` | `(computesFunInTime_iff _ _ _).2 fun x => h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)`; no reduction of `FinTM.ComputesFunInTime` |
| 2, `FinTM.stateEquivFin` | `FinTM.stateEquivFin_eq`, its defining equation (`rfl`, no `simp` attribute) |
| 3, `alphabet_reduction_run`'s docstring | "Without an image hypothesis the converse cannot in general assert `o = w.map e`: …" |
| 4, the replay | `replay-lg5` passed (325/325, its log in `evidence/merged-tree/`); round 2's is `replay-lg5b` |

## Brief for the auditor

1. Are the fixes correct, statement-preserving and rule-10 compliant?
2. **The seal now covers `two_work_tapes_binary`** (`evidence/round2/rule10/`): five sealed copies
   (`ARSealed`, `ENSealed`, `C2Sealed`, `TTSealed`, `UTSealed`) under a seal of 15 definitions,
   `FinTM.ComputesFunInTime` added. Each copy elaborates with 0 errors; the only output is the
   pre-existing `sorry` warnings. Controls: 30 of 30 pass unsealed, and 0 of 30 pass sealed. Is
   any proof site of the PR still uncovered?
3. Do the record corrections answer findings 2–4?

## Repository-side attestations (verify or challenge)

- **Compilation:** the five changed modules recompiled into the round-1 clone with only the
  expected warnings (`two_work_tapes_run`'s `sorry`, and `Encoding`'s pre-existing one).
- **Axioms** (`evidence/round2/axioms/`): as in round 1, plus `stateEquivFin_eq` on the standard
  three.
- **Lint:** campaign lint 0 FAIL / 71 WARN. Check 8 no longer lists `stateEquivFin`.
- **Replay:** `replay-lg5b` (`evidence/round2/merged-tree/`), 325 modules from `oleans-ledge`, at
  the head.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/92-g5-statements/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-statements-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

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

## ===== campaign/gates/92-g5-statements/pack.md =====

# External audit pack: G5's statements, two work tapes and the efficient universal machine (PR #189, a statement gate)

## Why this PR

G5 is the reduction from `k` work tapes to two (Hennie–Stearns) for binary machines, stated run
by run and with the converse. It is the input to Theorem 1.9 at `T log T` [AB09], and through
`Diagonal.lean`'s parameterization to the `f log f` time hierarchy (book-form Theorem 3.1). The U2
design probe drafted the statements (`campaign/items/u2/probes/U2DiagParam.lean.txt`). The plan is
`campaign/items/u2/G5-statements-plan.md`, with its rulings:
- (D1) `universal_TlogT` in a small sibling module;
- (D2) the image form of the per-run alphabet reduction's converse.

This PR lands G5's interface. The Hennie–Stearns simulation itself (`two_work_tapes_run`) stays
`sorry`, for a later fill.

**The PR:** #189 on `lean/g5-statements`, head `2339d2df69a02be3cf396733268e80bb0d7c8627`
(`evidence/patches/`). Against the campaign it changes six Lean files. Two are new:
`Robustness/TwoTapes.lean` and `UniversalTlogT.lean`. Four are edited: `Robustness/AlphabetReduction`,
`Codes2Tape`, `Encoding` and the facade `TuringMachine.lean`.

## What changed (verify)

| File · declaration | Change |
|---|---|
| `Robustness/AlphabetReduction` · `Turing.FinTM.alphabet_reduction_run` (new) | alphabet reduction run by run: `∃ c M', M'.k = M.k ∧ (∀ x w t, M.ComputesInTime (x.map e) (w.map e) t → M'.ComputesInTime x w (c * t)) ∧ ∀ x w, (∃ t, M'.ComputesInTime x w t) → ∃ t o, M.ComputesInTime (x.map e) o t ∧ ∀ v, o = v.map e → v = w`; **proved** from the file's private run correspondence (`arCfg_init`, `arCfg_run`, `arTM_computes`, `arBit_embed`) |
| `Robustness/TwoTapes` (new) · `Turing.FinTM.two_work_tapes_run` | `∃ M' c, M'.k = 2 ∧ (∀ x o t, M.ComputesInTime x o t → M'.ComputesInTime x o (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧ ∀ x o, (∃ t, M'.ComputesInTime x o t) → ∃ t, M.ComputesInTime x o t`, the probe's statement verbatim; **`sorry`** |
| `Robustness/TwoTapes` · `Turing.FinTM.two_work_tapes_binary` | the function-level form, `one_work_tape_binary`'s mirror; proved from the above in two lines |
| `UniversalTlogT` (new) · `Turing.universal_TlogT` | Theorem 1.9 at `T log T`, per run with the converse, over a two-tape scheme `c : EffectiveMachineCode2`; proved from `two_work_tapes_run`, `exists_code2TM` and `universalK 2 c.toK` |
| `Codes2Tape` · `Turing.exists_code2TM` (new) | every two-work-tape binary machine has a coded equivalent (the two-tape counterpart of `exists_codeTM`) |
| `Encoding` · `Turing.FinTM.computesInTime_relabelState`, `Turing.FinTM.stateEquivFin` (new) | renaming a bundled machine's states along an equivalence preserves `ComputesInTime`; a machine's states as `Fin (|State| - 1 + 1)`. `exists_codeTM_spaceUsed`'s time clause, `FinTM.toCodeTM`'s body and `toCodeTM_computesInTime_iff` now use them, and so does `exists_code2TM` (ruled by the user, 2026-11-04: the renaming argument is factored once rather than repeated) |
| `TuringMachine.lean` | imports the two new modules; their lines in the module list |

**The freeze:** every existing public statement is unchanged. The bodies change only in
`exists_codeTM_spaceUsed`, `toCodeTM` and `toCodeTM_computesInTime_iff` (`evidence/freeze/`).

## Brief for the auditor

1. **The statements.**
   - `two_work_tapes_run`: is it true as stated, for every `M`, `k = 0` and `k = 1` included?
     Is the bound `c · (t + 1)(log₂(t + 1) + 1)` the right form for the Hennie–Stearns
     simulation (`t` the source's halting time, the constant depending on `M`)? Is the converse
     what a universal machine needs?
   - `alphabet_reduction_run`'s converse, the image form (D2): `M'` decodes emitted symbols
     through a private total decoder, so only images `v.map e` determine `w`. Is the form
     adequate for G5's fill, and is anything stronger provable from the construction?
   - `universal_TlogT`: does it say Theorem 1.9 (with the relaxed code quantifier of
     `universal_quadratic`, as recorded in the module's deviations)?
2. **The proofs** of `alphabet_reduction_run`, `exists_code2TM`, the `Encoding` refactor,
   `two_work_tapes_binary` and `universal_TlogT`. Are they correct, and statement-preserving where
   they replace existing proofs? `toCodeTM`'s value changes; it has no use outside `Encoding`.
3. **Axioms** (`evidence/axioms/`):
   - `alphabet_reduction_run`, `exists_code2TM` and `computesInTime_relabelState` must be on
     `[propext, Classical.choice, Quot.sound]`;
   - `two_work_tapes_*` and `universal_TlogT` add `sorryAx`, which must come only through
     `two_work_tapes_run` (`universalK` is admission-free).
4. **Rule 10** (`evidence/rule10/`): four sealed copies (`AlphabetReduction`'s new theorem,
   `Encoding`'s relabelling section, `exists_code2TM` and `UniversalTlogT`) under a seal of 14
   definitions, with `attribute [-simp]` on three. Each copy elaborates with 0 errors; the only
   output is `Encoding`'s pre-existing `sorry`. Controls: 28 of 28 pass unsealed, and 0 of 28 pass
   sealed. Is any other-file definition unfolded or closed by reduction?
5. **Homes (D1):** `TwoTapes` beside `SingleTape`; `UniversalTlogT` as a sibling, since the
   `Robustness` layer does not import `UniversalK`. `alphabet_reduction_run` must be in
   `AlphabetReduction`, since it uses the file's private run lemmas. Its downstream is 325
   modules, the replay below.
6. **Duplication** (`evidence/screen/`): the v3 screen of 13 files, base the campaign tip
   `057da7a7` (1,004 declarations, 692 pairs), head `2339d2df` (1,010, 697): 5 new pairs, none gone
   (`pairdiff.txt`).
   - `exists_codeTM_spaceUsed` and `exists_code2TM` (94% and 73%), and `exists_code2TM` against
     `toCodeTM_computesInTime_iff` (74%). **Disposition: idiom.** After the factoring, each is a
     four-line invocation of `FinTM.computesInTime_relabelState` (with `stateEquivFin`) around its
     own code type's constructor. The renaming argument is stated once; nothing is re-derived.
     Before the factoring, the pair was 67% of a re-derived argument
     (`evidence/superseded-6bd12e68/screen/`).
   - `alphabet_reduction_run` against `Universal`'s `timedCut_live_before` (70%) and
     `timedPrefix_live` (50%). **Disposition: idiom.** The shared text is the invocation of
     `Nat.exists_eq_add_of_le`, `MultiTapeTM.runFrom_add` and `MultiTapeTM.runFrom_of_halt` (a
     halted run is stationary). No published lemma states the whole configuration's stationarity
     past a halt; `runFrom_output_eq_of_halt` states its output only.

   Does anything else re-derive existing material?
7. **Names** (`evidence/names/`): the new names on every ref.
8. **Public-facing text and lint** (`evidence/lint/`): the docstrings' sketches and references
   (`[HS66]`, `[AB09, Theorem 1.9]`).
   - **Campaign lint:** 0 FAIL / 71 WARN at base and head. One WARN line changes: `Encoding`'s
     check-8 list gains `FinTM.stateEquivFin`, an `Equiv` whose API is Mathlib's `Equiv` lemmas,
     so no own lemma is added.
   - **The policy linter:** the base's five findings on the edited files, at shifted lines, and
     none on the new files.

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): the change compiled with `lean -o`, in dependency order,
  into a copy-on-write clone of `oleans-larm2` (the campaign after #182). All 42 modules on the
  path to the targets and `Universal` exit 0. The only new warning is `two_work_tapes_run`'s
  `sorry`; `Encoding` keeps its one pre-existing `sorry` warning.
- **Replay:** `replay-lg5` (`evidence/merged-tree/`), the six files' downstream closure,
  325 modules, chained from `oleans-ledge` (the campaign after #184).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/92-g5-statements/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `g5-statements-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/92-g5-statements/findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `Robustness/TwoTapes.lean:78–83` · `two_work_tapes_binary`; `evidence/rule10/mkseal_g5.py` | The new function-level proof violates rule 10, and the sealed checks omit it. | `Finite.lean:281` defines `ComputesFunInTime` with `def`, not `abbrev`. Both `hM x` and the concluding `fun x => …` read that other-file definition by reduction. The published interface `computesFunInTime_iff` is available at line 289. The seal generator includes neither this proof nor `FinTM.ComputesFunInTime`; its 28 controls therefore do not establish compliance here. This is an interface-policy failure, not a false theorem. | Use `computesFunInTime_iff` to obtain the inputwise hypothesis and construct the conclusion. Add a sealed copy of this proof, seal `FinTM.ComputesFunInTime`, and include its unsealed/sealed controls. |
| 2 | minor | `Encoding.lean:716` · `FinTM.stateEquivFin`; `policy.md` §1 | The new public definition lacks the equation/projection API required by the supplied policy. | The definition chooses the finite-state equivalence supplied by `Fintype.equivFinOfCardEq`. Generic `Equiv` laws suffice for the present consumers, but do not characterize this definition's chosen map. The policy explicitly requires new public definitions to land with their equations; it supplies no exemption for equivalence-valued definitions. The new check-8 warning is therefore not fully discharged by the pack's explanation. | Add the appropriate non-`simp` equation/projection lemmas, or record an explicit policy exception for this opaque equivalence witness. No mathematical correction is needed. |
| 3 | minor | `Robustness/AlphabetReduction.lean:606–648` · `alphabet_reduction_run` | The image converse is correct and adequate for G5, but “The converse cannot say more” overstates its limitation. | The actual construction proves `o.map (fun a => decide (a = e true)) = w`, hence also `o.length = w.length`; the proof's witness even halts within the simulator's supplied time `t`. What fails without an image hypothesis is `o = w.map e`: take `Γ = Fin 3`, `e false = 0`, `e true = 1`, and a machine that emits `2` and halts. Its simulated output is `[false]`. The forward proof uses `arTM_computes`; the converse correctly extends the halted simulator to `c * t`, uses `arCfg_run`, and projects state and output. For G5, proving that every completed intermediate output is a bit-image lets the existing implication recover exactly that binary output. | Replace the absolute wording with “The converse cannot in general assert `o = w.map e` without an image hypothesis.” Retain D2; exporting the stronger decoder relation is optional. |
| 4 | minor | `pack.md` · repository-side replay attestation; `evidence/merged-tree/` | The bundle does not establish completion of the 325-module replay. | It contains the replay script and a list of 325 distinct modules, but neither `replay-lg5.log` nor its static-sorry result. A script with success checks is not evidence that those checks passed. Separately, `evidence/chain/chain.log` does record 42 module compilations, all with exit 0. I did not independently rerun Lean: no Lean executable is available in this workspace. | Supply the completed replay and static-sorry logs tied to the audited source, or label this replay explicitly as pending rather than an established result. |
| 5 | note | Bundle; six changed Lean files; `evidence/freeze/` | Integrity and the stated signature freeze check out. | SHA-256 is exactly `8fbe17172056ae669d35253e70b77f3bc31d1abc1fd3c37fa294dad2578cd954`; there are 257 sections. All six extracted Lean files match the Git blob hashes pinned by the replay script. The three freeze-head copies match the corresponding bundled sources. The base/head comparisons preserve existing public types and change only the three authorized existing bodies. In particular, `toCodeTM` retains type `(M : FinTM Bool) → M.k = 1 → CodeTM`; the freeze tool's pattern-arm warning is not a signature change. | None. |
| 6 | note | `Robustness/TwoTapes.lean` · `two_work_tapes_run`, `two_work_tapes_binary` | The stated two-work-tape contract is mathematically sound, including the boundary cases; its Lean fill remains open. | The Hennie–Stearns construction simulates work tapes using geometric zones and a scratch tape, with total cost `O(t log t)`; fixed-width alphabet reduction preserves two work tapes, while direct input access avoids a mandatory input-length scan ([AB09, §1.7](https://kubokovac.eu/zlozitost/arora.pdf)). Output forwarding and halting only at a simulated halt give the required converse. Adversarial cases: `k = 0` and `k = 1` permit direct simulation with idle extra tapes; `t = 0` has an impossible premise by `not_computesInTime_zero`; a one-step halt on arbitrarily long input requires no input copy; and a forever-looping source cannot acquire a completed simulator output. The padded bound covers small times, and the function-level statement follows by specializing the forward clause at `T x.length`. | None to the statements. Repair the function-level proof's interface use as in finding 1. |
| 7 | note | `Encoding.lean` · state renaming, `stateEquivFin`, `toCodeTM`, `exists_codeTM_spaceUsed`; `Codes2Tape.lean` · `exists_code2TM` | The definitions and coding proofs preserve the intended machine semantics. | `stateEquivFin` chooses a bijection from the finite state set to `Fin (Fintype.card M.State - 1 + 1)`; the start state proves the cardinality is positive, including the singleton case. `toCodeTM` keeps a one-work-tape machine's transition behavior and replaces only its state labels. The shared theorem reads initialized runs through `relabelState_runFrom_init` and the state/output projection lemmas, preserving completed outputs at every time budget. Both coding witnesses instantiate it; the one-tape space clause still uses `relabelState_spaceUsed`. An empty state type cannot instantiate a machine with a start state. | None to the definitions' meanings or the proofs; address the API obligation in finding 2. |
| 8 | note | `UniversalTlogT.lean:57` · `universal_TlogT` | The theorem correctly gives the declared existential-code version of efficient universality. | `U` is selected before `M`; its code and constant are selected before all inputs and times. The proof composes the two-tape simulation, coding equivalence at every time budget, and `universalK`. Since `(t + 1) * (Nat.log 2 (t + 1) + 1) ≥ 1`, the final constant `C * (c₁ + 1)` absorbs the universal simulator's additive step. The reverse implications compose in the correct direction. This is weaker than [AB09, Theorem 1.9](https://kubokovac.eu/zlozitost/arora.pdf)'s every-description formulation, as disclosed: it supplies neither an arbitrary-code guarantee nor an effective compiler from `M` to the selected code. The supplied scheme-existence theorem ensures that the scheme parameter is not a vacuous premise. | None within the expressly accepted code-quantifier relaxation. |
| 9 | note | `evidence/axioms/`; four supplied sealed copies | The axiom reports and the covered sealed checks agree with the visible dependency chain. | The reports give only `propext, Classical.choice, Quot.sound` for alphabet reduction, coding, the shared renaming lemma, the changed one-tape proof clauses, and `universalK`. The two-tape statements and `universal_TlogT` additionally use `sorryAx`; the only new admission is `two_work_tapes_run`. Encoding's existing `pairDiagTM_computes` admission is absent from these reported dependencies. Each sealed copy matches its source except for the seal wrapper; the logs contain 28/28 passing unsealed controls and 0/28 passing sealed controls, with only Encoding's existing sorry warning. No further other-file unfolding was found in those changed proof blocks. | Extend coverage as in finding 1; do not describe this statement gate as completing Hennie–Stearns or yielding an admission-free `universal_TlogT`. |
| 10 | note | Module homes, duplication screen, names, public text and lint | The remaining organization, duplication dispositions, and reported lint deltas are supported. | `AlphabetReduction` houses its private-run consumer; `TwoTapes` belongs beside `SingleTape`; the sibling `UniversalTlogT` joins robustness to universality without reversing that dependency. The facade imports and lists both new modules. Independently comparing the screen outputs reproduces 692 → 697 pairs, exactly the five listed additions and no removals. The short coding wrappers reuse the shared renaming proof; the stationarity fragment composes existing run lemmas rather than copying a simulation. No further duplicated proof was found in the changed blocks. Name-search records show no pre-existing collision. The current lint logs confirm 0 FAIL / 71 WARN and the five inherited policy findings; the extra `stateEquivFin` warning is addressed in finding 2. | None beyond findings 1–4. |

Verdict: **DO NOT CLOSE — 0 blockers, 1 major, 3 minors.** The remaining Hennie–Stearns admission is authorized for this statement gate.


## ===== campaign/gates/92-g5-statements/resolutions.md =====

# G5's statements (PR #189, a statement gate): resolutions

**Staged (2026-11-04):** `pack.md`, at #189's head `2339d2df`. Bundle `92-g5-statements-bundle.md`,
SHA-256 `8fbe17172056ae669d35253e70b77f3bc31d1abc1fd3c37fa294dad2578cd954` (257 sections), the records at
`48275d52`; in the exchange `arora-barak-ch3-4/outbox/gates/92-g5-statements-gate/`. `replay-lg5` running.
**Dispatched (user, 2026-11-04);** the folder archived.
**`replay-lg5` passed** (2026-11-04): 325 of 325 at `2339d2df`, 0 failed, static-equal (73, all pre-existing); snapshot `oleans-lg5`.

**Round 1** (`pack.md`, head `2339d2df`). **Findings** (`findings.md`, verbatim, SHA-256
`7e55640611312b810b5629b84e9b9d5a4c345023904e2692291bdaec1ef092b5`; received 2026-11-04): **DO NOT CLOSE, 0
blockers, 1 major, 3 minors, 6 notes.** The statements are sound, including the boundary cases;
the remaining Hennie–Stearns admission is authorized for this statement gate.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `two_work_tapes_binary` reads `FinTM.ComputesFunInTime` by reduction (rule 10), and the seal did not cover it. | **True; fixed** (`caa6bf53`): the hypothesis and the conclusion pass through `computesFunInTime_iff`. The seal gains a fifth copy, `TTSealed`, with `FinTM.ComputesFunInTime` sealed: 15 definitions, 5 copies, controls 30/30 unsealed and 0/30 sealed (`evidence/round2/rule10/`). |
| 2 | minor | `FinTM.stateEquivFin` lacks an equation (policy §1, check 8). | **True. Ruled (user, 2026-11-04): fix all now.** `FinTM.stateEquivFin_eq`, its defining equation (`rfl`); check 8 no longer lists it. |
| 3 | minor | "The converse cannot say more" overstates the limitation. | **True; reworded** as the auditor proposed: without an image hypothesis the converse cannot in general assert `o = w.map e`. |
| 4 | minor | The bundle lacked the replay's log. | **True:** `replay-lg5` passed after staging (325/325; `evidence/merged-tree/`, now with its log). Round 2's replay is `replay-lg5b`. |
| 5–10 | note | Integrity and freeze; the two-tape contract; the coding semantics; `universal_TlogT`'s relaxed quantifier; axioms and seals; homes, screen, names, lint. | Agreed. On note 9, `universal_TlogT` is not claimed admission-free: it reaches `sorryAx` through `two_work_tapes_run` until G5's fill. |

## ===== campaign/gates/92-g5-statements/evidence/merged-tree/down-lg5.txt =====

TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/ClassNP/PolyTimePairing
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/ClassNP/Reductions
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGamesDefinitions
TCSlib/BooleanAnalysis/GaussianSpace/MaxCutAlgorithm
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGames
TCSlib/BooleanAnalysis/GaussianSpace
TCSlib/Complexity/CircuitComplexity/Advice
TCSlib/Complexity/CircuitComplexity/CircuitEvalSpec
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect
TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine
TCSlib/Complexity/CircuitComplexity/CircuitEvalRun
TCSlib/Complexity/CircuitComplexity/CircuitEval
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine
TCSlib/Complexity/ClassNP/Transducer
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction
TCSlib/Complexity/CircuitComplexity/PUniformP
TCSlib/Complexity/CircuitComplexity/UniformTableau
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/PolyTimePrefix
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed
TCSlib/Complexity/TuringMachine/Build/EmitIterBody
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
TCSlib/Complexity/ClassNP/PolyTimeBlockTests
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
TCSlib/Complexity/ClassNP/PClosure
TCSlib/Complexity/PolyHierarchy/Padding
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix
TCSlib/Complexity/PolyHierarchy/Defs
TCSlib/Complexity/PolyHierarchy/Normalize
TCSlib/Complexity/PolyHierarchy/Levels
TCSlib/Complexity/PolyHierarchy/Collapse
TCSlib/Complexity/CircuitComplexity/KarpLipton
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily
TCSlib/Complexity/SpaceComplexity/Basic
TCSlib/Complexity/SpaceComplexity/ConfigCount
TCSlib/Complexity/SpaceComplexity/Machines/Layout
TCSlib/Complexity/SpaceComplexity/Machines/Program
TCSlib/Complexity/SpaceComplexity/Machines/Sim
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn
TCSlib/Complexity/SpaceComplexity/Machines/Call
TCSlib/Complexity/SpaceComplexity/Machines/Compile
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep
TCSlib/Complexity/SpaceComplexity/Machines/Clean
TCSlib/Complexity/SpaceComplexity/Machines/Bank
TCSlib/Complexity/SpaceComplexity/Machines/Lib
TCSlib/Complexity/SpaceComplexity/ImplicitPoly
TCSlib/Complexity/CircuitComplexity/LogspaceUniform
TCSlib/Complexity/SpaceComplexity/Machines/FragDec
TCSlib/Complexity/SpaceComplexity/Machines/Frag
TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain
TCSlib/Complexity/SpaceComplexity/Machines/Parse
TCSlib/Complexity/SpaceComplexity/Machines/Parse2
TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp
TCSlib/Complexity/SpaceComplexity/Machines/ARM
TCSlib/Complexity/SpaceComplexity/Machines/ARMSim
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof
TCSlib/Complexity/SpaceComplexity/Machines/ARMKit
TCSlib/Complexity/SpaceComplexity/Machines/DblLang
TCSlib/Complexity/SpaceComplexity/UnaryLogspace
TCSlib/Complexity/SpaceComplexity/CounterProgSim
TCSlib/Complexity/SpaceComplexity/CounterProgSimRun
TCSlib/Complexity/CircuitComplexity/LogspaceTableau
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic
TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan
TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj
TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon
TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample
TCSlib/Complexity/CircuitComplexity/MeyerTab
TCSlib/Complexity/CircuitComplexity/MeyerTableau
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue
TCSlib/Complexity/CircuitComplexity/MeyerVerifier
TCSlib/Complexity/CircuitComplexity/MeyerSound
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput
TCSlib/Complexity/CircuitComplexity/MeyerComplete
TCSlib/Complexity/CircuitComplexity/MeyerSigma
TCSlib/Complexity/ClassNP/ExpPoly
TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP
TCSlib/Complexity/TimeHierarchy/CodePrefix
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeFormat
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TimeHierarchy/Diagonal
TCSlib/Complexity/TimeHierarchy/Separation
TCSlib/Complexity/CircuitComplexity/Meyer
TCSlib/Complexity/CircuitComplexity/PPolyAdvice
TCSlib/Complexity/CircuitComplexity/UHaltMachine
TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly
TCSlib/Complexity/TuringMachine/Build/WordTests
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/CircuitComplexity/PSubsetPPoly
TCSlib/Complexity/CircuitComplexity/PairEncode
TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/TuringMachine/Build/Catalog
TCSlib/Complexity/TuringMachine/Build/Scan
TCSlib/Complexity/TuringMachine/Build/CounterLoop
TCSlib/Complexity/TuringMachine/Build/StepClock
TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/ClassNP/ExhaustiveReplay
TCSlib/Complexity/ClassNP/NDNormalForm
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP
TCSlib/Complexity/TuringMachine/Build/InputCall
TCSlib/Complexity/TuringMachine/Build/OracleSim
TCSlib/Complexity/ClassOracle/Classes
TCSlib/Complexity/ClassOracle/SATOracle
TCSlib/Complexity/ClassOracle
TCSlib/Complexity/ClassP/BinaryArith/Iterate
TCSlib/Complexity/ClassP/BinaryArith/Basic
TCSlib/Complexity/ClassP/BinaryArith/AddSub
TCSlib/Complexity/ClassP/BinaryArith/Mul
TCSlib/Complexity/ClassP/BinaryArith/Div
TCSlib/Complexity/ClassP/BinaryArith/ModPow
TCSlib/Complexity/ClassP/BinaryArith/Words
TCSlib/Complexity/ClassP/BinaryArith/DetMod
TCSlib/Complexity/ClassP/BinaryArith/Jacobi
TCSlib/Complexity/ClassP/BinaryArith/Loops
TCSlib/Complexity/ClassP/BinaryArith/PrimeFind
TCSlib/Complexity/ClassP/BinaryArith
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP
TCSlib/Complexity/Formulas/QBFEncoding
TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops
TCSlib/Complexity/SpaceComplexity/NSPACE
TCSlib/Complexity/SpaceComplexity/SpaceClasses
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth
TCSlib/Complexity/SpaceComplexity/Machines/VWord
TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine
TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf
TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk
TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct
TCSlib/Complexity/TuringMachine/Build/InputLength
TCSlib/Complexity/SpaceComplexity/Constructible
TCSlib/Complexity/TuringMachine/Build/Contract/Catalog
TCSlib/Complexity/TuringMachine/Build/Contract/Counter
TCSlib/Complexity/TuringMachine/Build/Contract
TCSlib/Complexity/TuringMachine/Build/CfgRecord
TCSlib/Complexity/TuringMachine/Build/RecordTable
TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/Codec/Word
TCSlib/Complexity/SpaceComplexity/Codec/Valid
TCSlib/Complexity/SpaceComplexity/Codec/Step
TCSlib/Complexity/SpaceComplexity/Codec/Langs
TCSlib/Complexity/SpaceComplexity/Codec/Checks
TCSlib/Complexity/SpaceComplexity/Codec/Bridge
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine
TCSlib/Complexity/SpaceComplexity/Codec/Engine
TCSlib/Complexity/SpaceComplexity/Codec/Machine
TCSlib/Complexity/SpaceComplexity/Codec/Run
TCSlib/Complexity/SpaceComplexity/Codec/Parse
TCSlib/Complexity/SpaceComplexity/Codec/Layout
TCSlib/Complexity/SpaceComplexity/Codec/Deciders
TCSlib/Complexity/SpaceComplexity/Codec/Layout2
TCSlib/Complexity/SpaceComplexity/Codec/StepDecider
TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier
TCSlib/Complexity/ClassPSPACE/TQBFHardBridge
TCSlib/Complexity/ClassPSPACE/TQBFHardParams
TCSlib/Complexity/ClassPSPACE/TQBFHard
TCSlib/Complexity/FormulaKit/Emit
TCSlib/Complexity/SpaceComplexity/Inclusions
TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE
TCSlib/Complexity/CookLevin
TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/InputDevice
TCSlib/Complexity/TuringMachine/Build/InputWindow
TCSlib/Complexity/TuringMachine/Build/Rewind
TCSlib/Complexity/TuringMachine/Build/SeamLayout
TCSlib/Complexity/TuringMachine/Build/StepBlock
TCSlib/Complexity/TuringMachine/Build/InterpreterStartup
TCSlib/Complexity/TuringMachine/Build/StepBlockLoop
TCSlib/Complexity/TuringMachine/CodeSimulator
TCSlib/Complexity/Diagonalization/EXPCOM
TCSlib/Complexity/Diagonalization/NTimeDiagonalizer
TCSlib/Complexity/TuringMachine/Build/NDHost
TCSlib/Complexity/TuringMachine/NDCodeSimulator
TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/Relativization
TCSlib/Complexity/Diagonalization
TCSlib/Complexity/FormulaKit
TCSlib/Complexity/Formulas
TCSlib/Complexity/PolyHierarchy
TCSlib/Complexity/RAMSimulation/WordSize
TCSlib/Complexity/RAMSimulation/Simulation
TCSlib/Complexity/RAMSimulation/Classes
TCSlib/Complexity/RAMSimulation
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach
TCSlib/Complexity/SpaceComplexity/Machines/NARM
TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile
TCSlib/Complexity/SpaceComplexity/Machines/NARMRun
TCSlib/Complexity/SpaceComplexity/Machines/NARMProb
TCSlib/Complexity/Randomized/SpaceAmplify
TCSlib/Complexity/Randomized/SpaceAmplifyRun
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius
TCSlib/Complexity/SpaceComplexity/Machines/MARM
TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile
TCSlib/Complexity/SpaceComplexity/Machines/MARMTime
TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run
TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax
TCSlib/Complexity/SpaceComplexity/ExpBFS/Search
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main
TCSlib/Complexity/SpaceComplexity/ExpTime
TCSlib/Complexity/Randomized/Space
TCSlib/Complexity/Randomized/BPLInPCount
TCSlib/Complexity/Randomized/BPLInPWords
TCSlib/Complexity/Randomized/BPLInP
TCSlib/Complexity/Randomized/PolyTimeModel
TCSlib/Complexity/Randomized/Inclusions
TCSlib/Complexity/Randomized/PTMEquiv
TCSlib/Complexity/Randomized/Reductions
TCSlib/Complexity/Randomized/BPOperator
TCSlib/Complexity/Randomized/BPPAmplify
TCSlib/Complexity/Randomized/BPPHard
TCSlib/Complexity/Randomized/QuasiPolyHierarchy
TCSlib/Complexity/Randomized/BPPEqP
TCSlib/Complexity/Randomized/BPTIMEThreshold
TCSlib/Complexity/Randomized/BiasedCoin
TCSlib/Complexity/Randomized/BiasedCoinHalting
TCSlib/Complexity/Randomized/Primality
TCSlib/Complexity/Randomized/Matching
TCSlib/Complexity/Randomized/NPPoly
TCSlib/Complexity/Randomized/RPExpected
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode
TCSlib/Complexity/SpaceComplexity/Machines/NARMKit
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace
TCSlib/Complexity/Randomized/SpaceAmplifyPoly
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
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
TCSlib/Complexity/Randomized/UniformSample
TCSlib/Complexity/Randomized/Yap
TCSlib/Complexity/Randomized/ZPPEquiv
TCSlib/Complexity/Randomized/ZPPHosts
TCSlib/Complexity/Randomized/ZPPHostsClasses
TCSlib/Complexity/Randomized/ZeroPEval
TCSlib/Complexity/Randomized/ZeroPRun
TCSlib/Complexity/Randomized/ZeroP
TCSlib/Complexity/Randomized/ZeroPPIT
TCSlib/Complexity/Randomized/ZeroPReduce
TCSlib/Complexity/Randomized
TCSlib/Complexity/SpaceComplexity/Examples
TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach
TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine
TCSlib/Complexity/SpaceComplexity/SavitchARM/Run
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
TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample
TCSlib/Complexity/SpaceComplexity/Machines/NARMExample
TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/TuringMachine/Build/WindowRun
TCSlib/Complexity/SpaceComplexity/WindowClock
TCSlib/Complexity/SpaceComplexity/ZeroSpace
TCSlib/Complexity/SpaceComplexity
TCSlib/Complexity/TimeHierarchy
TCSlib/Complexity/TuringMachine/Build/StepBlockForward
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance
TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes
TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/SelfUniversal
TCSlib/Complexity/TuringMachine/UniversalTlogT
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/Uncomputability

## ===== campaign/gates/92-g5-statements/evidence/merged-tree/replay-lg5-static.txt =====

modules 325, mismatches 0, static total 73

## ===== campaign/gates/92-g5-statements/evidence/merged-tree/replay-lg5.log =====

# replay-lg5 at 2339d2df: #189 (G5's statements) merged with the campaign after #184 (325 modules), fresh .oleans into oleans-lg5
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding exit=0 errors=0 sorry=1
TCSlib/Complexity/ClassP/TimeConstructible exit=0 errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Build/Primitives exit=0 errors=0 sorry=3
TCSlib/Complexity/ClassNP/PolyTimePairing exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/EXP exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalStartup exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalInterpreter exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalBlock exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Universal exit=0 errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Diagonalization exit=0 errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Halting exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/Reductions exit=0 errors=0 sorry=0
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGamesDefinitions exit=0 errors=0 sorry=0
TCSlib/BooleanAnalysis/GaussianSpace/MaxCutAlgorithm exit=0 errors=0 sorry=2
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGames exit=0 errors=0 sorry=8
TCSlib/BooleanAnalysis/GaussianSpace exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Advice exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalSpec exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalRun exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEval exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/Transducer exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PUniformP exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UniformTableau exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/CoNP exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Padding exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Defs exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Normalize exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Levels exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Collapse exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Basic exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ConfigCount exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Layout exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Program exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Sim exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Call exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Compile exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Clean exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Bank exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Lib exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ImplicitPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniform exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/FragDec exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Frag exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Parse exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Parse2 exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARM exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMSim exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMKit exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/DblLang exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/UnaryLogspace exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/CounterProgSim exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/CounterProgSimRun exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceTableau exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerTab exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerTableau exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifier exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSound exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerComplete exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigma exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/ExpPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/CodePrefix exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CodeParser exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CodeFormat exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/MathlibBridge exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/Diagonal exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/Separation exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PPolyAdvice exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UHaltMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/WordTests exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/TMSAT exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/Oblivious exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PSubsetPPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PairEncode exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Catalog exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Scan exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/CounterLoop exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/StepClock exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/NDCodes exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/ExhaustiveReplay exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/NDNormalForm exit=0 errors=0 sorry=1
TCSlib/Complexity/ClassNP/Nondeterminism exit=0 errors=0 sorry=0
TCSlib/Complexity/CookLevin/Hardness exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP/Tautology exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassNP exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputCall exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/OracleSim exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassOracle/Classes exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassOracle/SATOracle exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassOracle exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Iterate exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Basic exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/AddSub exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Mul exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Div exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/ModPow exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Words exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/DetMod exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Jacobi exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Loops exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/PrimeFind exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP/ModelInvariance exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassP exit=0 errors=0 sorry=0
TCSlib/Complexity/Formulas/QBFEncoding exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/NSPACE exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SpaceClasses exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/VWord exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputLength exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Constructible exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Catalog exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Counter exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/CfgRecord exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/RecordTable exit=0 errors=0 sorry=4
TCSlib/Complexity/SpaceComplexity/ConfigGraph exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Word exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Valid exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Step exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Langs exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Checks exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Bridge exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Engine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Machine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Run exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Parse exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Layout exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Deciders exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Layout2 exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/StepDecider exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardBridge exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardParams exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard exit=0 errors=0 sorry=0
TCSlib/Complexity/FormulaKit/Emit exit=0 errors=0 sorry=10
TCSlib/Complexity/SpaceComplexity/Inclusions exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF exit=0 errors=0 sorry=21
TCSlib/Complexity/ClassPSPACE exit=0 errors=0 sorry=0
TCSlib/Complexity/CookLevin exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/CertShell exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputDevice exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputWindow exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Rewind exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/SeamLayout exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/StepBlock exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InterpreterStartup exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/StepBlockLoop exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CodeSimulator exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/EXPCOM exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/NTimeDiagonalizer exit=0 errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Build/NDHost exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/NDCodeSimulator exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/NTimeHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/NotTimeConstructible exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/Relativization exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization exit=0 errors=0 sorry=0
TCSlib/Complexity/FormulaKit exit=0 errors=0 sorry=0
TCSlib/Complexity/Formulas exit=0 errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/RAMSimulation/WordSize exit=0 errors=0 sorry=3
TCSlib/Complexity/RAMSimulation/Simulation exit=0 errors=0 sorry=2
TCSlib/Complexity/RAMSimulation/Classes exit=0 errors=0 sorry=9
TCSlib/Complexity/RAMSimulation exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARM exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMProb exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplify exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARM exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARMTime exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Search exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpTime exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Space exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInPCount exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInPWords exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyTimeModel exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Inclusions exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPHard exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/QuasiPolyHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPEqP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMKit exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions exit=0 errors=0 sorry=0
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
TCSlib/Complexity/Randomized/UniformSample exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPEval exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPRun exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Examples exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Hierarchy exit=0 errors=0 sorry=4
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Run exit=0 errors=0 sorry=0
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
TCSlib/Complexity/SpaceComplexity/Logspace/Mult exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMExample exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Savitch exit=0 errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Build/WindowRun exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/WindowClock exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ZeroSpace exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/StepBlockForward exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Codes2Tape exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes exit=0 errors=0 sorry=1
TCSlib/Complexity/TuringMachine/UniversalK exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/SelfUniversal exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalTlogT exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Uncomputability exit=0 errors=0 sorry=0
# modules=325 failed=0

## ===== campaign/gates/92-g5-statements/evidence/merged-tree/replay-lg5.sh =====

#!/usr/bin/env bash
# Replay lg5 (#189 (G5's statements) merged with the campaign after #184; branch lean/g5-statements, stacked on the campaign tip after #184): its downstream closure (325 modules),
# fresh .oleans into oleans-lg5, a copy of oleans-ledge, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g5"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg5.txt"
LOG="$S/fills/replay/replay-lg5.log"
PINS="TCSlib/Complexity/TuringMachine.lean:579fcc579bba922b098b4ad9c3afd0f976718877
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:06d9339d3f17bc38bda991ccd68185d1fcb57eff
TCSlib/Complexity/TuringMachine/Encoding.lean:c0fe678412984e3ea7e99f2cfb16533a08e39449
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:e95cd630f4eb2303c3f1a1cc789013b73a24cbee
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:6cf70886a3f50df59554948a90980c755ae8167b
TCSlib/Complexity/TuringMachine/UniversalTlogT.lean:666b3f8324c616500a5febfa3ee317f45d446366"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g5-statements 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD || { echo "precheck: the head must contain the campaign tip after #184; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #184 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-ledge.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "325" ] || { echo "precheck: the replay list must have 325 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg5" ] && { echo "precheck: $S/oleans-lg5 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-ledge" ] || { echo "precheck: oleans-ledge is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-ledge" "$S/oleans-lg5" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg5 at $(git rev-parse --short HEAD): #189 (G5's statements) merged with the campaign after #184 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg5"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg5 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=325 failed=0" || { echo "replay: a module failed, or the count is not 325" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/92-g5-statements/evidence/round2/axioms/Ax.lean.txt =====

import TCSlib.Complexity.TuringMachine.UniversalTlogT
#print axioms Turing.FinTM.alphabet_reduction_run
#print axioms Turing.exists_code2TM
#print axioms Turing.FinTM.computesInTime_relabelState
#print axioms Turing.FinTM.stateEquivFin_eq
#print axioms Turing.exists_codeTM_spaceUsed
#print axioms Turing.FinTM.toCodeTM_computesInTime_iff
#print axioms Turing.FinTM.two_work_tapes_run
#print axioms Turing.FinTM.two_work_tapes_binary
#print axioms Turing.universal_TlogT
#print axioms Turing.universalK

## ===== campaign/gates/92-g5-statements/evidence/round2/axioms/Ax.out =====

'Turing.FinTM.alphabet_reduction_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_code2TM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesInTime_relabelState' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.stateEquivFin_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_codeTM_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.toCodeTM_computesInTime_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.two_work_tapes_run' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.two_work_tapes_binary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.universal_TlogT' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.universalK' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== campaign/gates/92-g5-statements/evidence/round2/merged-tree/down-lg5b.txt =====

TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/ClassNP/PolyTimePairing
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/ClassNP/Reductions
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGamesDefinitions
TCSlib/BooleanAnalysis/GaussianSpace/MaxCutAlgorithm
TCSlib/BooleanAnalysis/GaussianSpace/UniqueGames
TCSlib/BooleanAnalysis/GaussianSpace
TCSlib/Complexity/CircuitComplexity/Advice
TCSlib/Complexity/CircuitComplexity/CircuitEvalSpec
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect
TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine
TCSlib/Complexity/CircuitComplexity/CircuitEvalRun
TCSlib/Complexity/CircuitComplexity/CircuitEval
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine
TCSlib/Complexity/ClassNP/Transducer
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction
TCSlib/Complexity/CircuitComplexity/PUniformP
TCSlib/Complexity/CircuitComplexity/UniformTableau
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/PolyTimePrefix
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed
TCSlib/Complexity/TuringMachine/Build/EmitIterBody
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
TCSlib/Complexity/ClassNP/PolyTimeBlockTests
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
TCSlib/Complexity/ClassNP/PClosure
TCSlib/Complexity/PolyHierarchy/Padding
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix
TCSlib/Complexity/PolyHierarchy/Defs
TCSlib/Complexity/PolyHierarchy/Normalize
TCSlib/Complexity/PolyHierarchy/Levels
TCSlib/Complexity/PolyHierarchy/Collapse
TCSlib/Complexity/CircuitComplexity/KarpLipton
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily
TCSlib/Complexity/SpaceComplexity/Basic
TCSlib/Complexity/SpaceComplexity/ConfigCount
TCSlib/Complexity/SpaceComplexity/Machines/Layout
TCSlib/Complexity/SpaceComplexity/Machines/Program
TCSlib/Complexity/SpaceComplexity/Machines/Sim
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn
TCSlib/Complexity/SpaceComplexity/Machines/Call
TCSlib/Complexity/SpaceComplexity/Machines/Compile
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep
TCSlib/Complexity/SpaceComplexity/Machines/Clean
TCSlib/Complexity/SpaceComplexity/Machines/Bank
TCSlib/Complexity/SpaceComplexity/Machines/Lib
TCSlib/Complexity/SpaceComplexity/ImplicitPoly
TCSlib/Complexity/CircuitComplexity/LogspaceUniform
TCSlib/Complexity/SpaceComplexity/Machines/FragDec
TCSlib/Complexity/SpaceComplexity/Machines/Frag
TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain
TCSlib/Complexity/SpaceComplexity/Machines/Parse
TCSlib/Complexity/SpaceComplexity/Machines/Parse2
TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp
TCSlib/Complexity/SpaceComplexity/Machines/ARM
TCSlib/Complexity/SpaceComplexity/Machines/ARMSim
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof
TCSlib/Complexity/SpaceComplexity/Machines/ARMKit
TCSlib/Complexity/SpaceComplexity/Machines/DblLang
TCSlib/Complexity/SpaceComplexity/UnaryLogspace
TCSlib/Complexity/SpaceComplexity/CounterProgSim
TCSlib/Complexity/SpaceComplexity/CounterProgSimRun
TCSlib/Complexity/CircuitComplexity/LogspaceTableau
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic
TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan
TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk
TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj
TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon
TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample
TCSlib/Complexity/CircuitComplexity/MeyerTab
TCSlib/Complexity/CircuitComplexity/MeyerTableau
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue
TCSlib/Complexity/CircuitComplexity/MeyerVerifier
TCSlib/Complexity/CircuitComplexity/MeyerSound
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput
TCSlib/Complexity/CircuitComplexity/MeyerComplete
TCSlib/Complexity/CircuitComplexity/MeyerSigma
TCSlib/Complexity/ClassNP/ExpPoly
TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP
TCSlib/Complexity/TimeHierarchy/CodePrefix
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeFormat
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TimeHierarchy/Diagonal
TCSlib/Complexity/TimeHierarchy/Separation
TCSlib/Complexity/CircuitComplexity/Meyer
TCSlib/Complexity/CircuitComplexity/PPolyAdvice
TCSlib/Complexity/CircuitComplexity/UHaltMachine
TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly
TCSlib/Complexity/TuringMachine/Build/WordTests
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/CircuitComplexity/PSubsetPPoly
TCSlib/Complexity/CircuitComplexity/PairEncode
TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/TuringMachine/Build/Catalog
TCSlib/Complexity/TuringMachine/Build/Scan
TCSlib/Complexity/TuringMachine/Build/CounterLoop
TCSlib/Complexity/TuringMachine/Build/StepClock
TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/ClassNP/ExhaustiveReplay
TCSlib/Complexity/ClassNP/NDNormalForm
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP
TCSlib/Complexity/TuringMachine/Build/InputCall
TCSlib/Complexity/TuringMachine/Build/OracleSim
TCSlib/Complexity/ClassOracle/Classes
TCSlib/Complexity/ClassOracle/SATOracle
TCSlib/Complexity/ClassOracle
TCSlib/Complexity/ClassP/BinaryArith/Iterate
TCSlib/Complexity/ClassP/BinaryArith/Basic
TCSlib/Complexity/ClassP/BinaryArith/AddSub
TCSlib/Complexity/ClassP/BinaryArith/Mul
TCSlib/Complexity/ClassP/BinaryArith/Div
TCSlib/Complexity/ClassP/BinaryArith/ModPow
TCSlib/Complexity/ClassP/BinaryArith/Words
TCSlib/Complexity/ClassP/BinaryArith/DetMod
TCSlib/Complexity/ClassP/BinaryArith/Jacobi
TCSlib/Complexity/ClassP/BinaryArith/Loops
TCSlib/Complexity/ClassP/BinaryArith/PrimeFind
TCSlib/Complexity/ClassP/BinaryArith
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP
TCSlib/Complexity/Formulas/QBFEncoding
TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops
TCSlib/Complexity/SpaceComplexity/NSPACE
TCSlib/Complexity/SpaceComplexity/SpaceClasses
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth
TCSlib/Complexity/SpaceComplexity/Machines/VWord
TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine
TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf
TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk
TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct
TCSlib/Complexity/TuringMachine/Build/InputLength
TCSlib/Complexity/SpaceComplexity/Constructible
TCSlib/Complexity/TuringMachine/Build/Contract/Catalog
TCSlib/Complexity/TuringMachine/Build/Contract/Counter
TCSlib/Complexity/TuringMachine/Build/Contract
TCSlib/Complexity/TuringMachine/Build/CfgRecord
TCSlib/Complexity/TuringMachine/Build/RecordTable
TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/Codec/Word
TCSlib/Complexity/SpaceComplexity/Codec/Valid
TCSlib/Complexity/SpaceComplexity/Codec/Step
TCSlib/Complexity/SpaceComplexity/Codec/Langs
TCSlib/Complexity/SpaceComplexity/Codec/Checks
TCSlib/Complexity/SpaceComplexity/Codec/Bridge
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine
TCSlib/Complexity/SpaceComplexity/Codec/Engine
TCSlib/Complexity/SpaceComplexity/Codec/Machine
TCSlib/Complexity/SpaceComplexity/Codec/Run
TCSlib/Complexity/SpaceComplexity/Codec/Parse
TCSlib/Complexity/SpaceComplexity/Codec/Layout
TCSlib/Complexity/SpaceComplexity/Codec/Deciders
TCSlib/Complexity/SpaceComplexity/Codec/Layout2
TCSlib/Complexity/SpaceComplexity/Codec/StepDecider
TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier
TCSlib/Complexity/ClassPSPACE/TQBFHardBridge
TCSlib/Complexity/ClassPSPACE/TQBFHardParams
TCSlib/Complexity/ClassPSPACE/TQBFHard
TCSlib/Complexity/FormulaKit/Emit
TCSlib/Complexity/SpaceComplexity/Inclusions
TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE
TCSlib/Complexity/CookLevin
TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/InputDevice
TCSlib/Complexity/TuringMachine/Build/InputWindow
TCSlib/Complexity/TuringMachine/Build/Rewind
TCSlib/Complexity/TuringMachine/Build/SeamLayout
TCSlib/Complexity/TuringMachine/Build/StepBlock
TCSlib/Complexity/TuringMachine/Build/InterpreterStartup
TCSlib/Complexity/TuringMachine/Build/StepBlockLoop
TCSlib/Complexity/TuringMachine/CodeSimulator
TCSlib/Complexity/Diagonalization/EXPCOM
TCSlib/Complexity/Diagonalization/NTimeDiagonalizer
TCSlib/Complexity/TuringMachine/Build/NDHost
TCSlib/Complexity/TuringMachine/NDCodeSimulator
TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/Relativization
TCSlib/Complexity/Diagonalization
TCSlib/Complexity/FormulaKit
TCSlib/Complexity/Formulas
TCSlib/Complexity/PolyHierarchy
TCSlib/Complexity/RAMSimulation/WordSize
TCSlib/Complexity/RAMSimulation/Simulation
TCSlib/Complexity/RAMSimulation/Classes
TCSlib/Complexity/RAMSimulation
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach
TCSlib/Complexity/SpaceComplexity/Machines/NARM
TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile
TCSlib/Complexity/SpaceComplexity/Machines/NARMRun
TCSlib/Complexity/SpaceComplexity/Machines/NARMProb
TCSlib/Complexity/Randomized/SpaceAmplify
TCSlib/Complexity/Randomized/SpaceAmplifyRun
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius
TCSlib/Complexity/SpaceComplexity/Machines/MARM
TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile
TCSlib/Complexity/SpaceComplexity/Machines/MARMTime
TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run
TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax
TCSlib/Complexity/SpaceComplexity/ExpBFS/Search
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main
TCSlib/Complexity/SpaceComplexity/ExpTime
TCSlib/Complexity/Randomized/Space
TCSlib/Complexity/Randomized/BPLInPCount
TCSlib/Complexity/Randomized/BPLInPWords
TCSlib/Complexity/Randomized/BPLInP
TCSlib/Complexity/Randomized/PolyTimeModel
TCSlib/Complexity/Randomized/Inclusions
TCSlib/Complexity/Randomized/PTMEquiv
TCSlib/Complexity/Randomized/Reductions
TCSlib/Complexity/Randomized/BPOperator
TCSlib/Complexity/Randomized/BPPAmplify
TCSlib/Complexity/Randomized/BPPHard
TCSlib/Complexity/Randomized/QuasiPolyHierarchy
TCSlib/Complexity/Randomized/BPPEqP
TCSlib/Complexity/Randomized/BPTIMEThreshold
TCSlib/Complexity/Randomized/BiasedCoin
TCSlib/Complexity/Randomized/BiasedCoinHalting
TCSlib/Complexity/Randomized/Primality
TCSlib/Complexity/Randomized/Matching
TCSlib/Complexity/Randomized/NPPoly
TCSlib/Complexity/Randomized/RPExpected
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode
TCSlib/Complexity/SpaceComplexity/Machines/NARMKit
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace
TCSlib/Complexity/Randomized/SpaceAmplifyPoly
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
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
TCSlib/Complexity/Randomized/UniformSample
TCSlib/Complexity/Randomized/Yap
TCSlib/Complexity/Randomized/ZPPEquiv
TCSlib/Complexity/Randomized/ZPPHosts
TCSlib/Complexity/Randomized/ZPPHostsClasses
TCSlib/Complexity/Randomized/ZeroPEval
TCSlib/Complexity/Randomized/ZeroPRun
TCSlib/Complexity/Randomized/ZeroP
TCSlib/Complexity/Randomized/ZeroPPIT
TCSlib/Complexity/Randomized/ZeroPReduce
TCSlib/Complexity/Randomized
TCSlib/Complexity/SpaceComplexity/Examples
TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach
TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine
TCSlib/Complexity/SpaceComplexity/SavitchARM/Run
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
TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample
TCSlib/Complexity/SpaceComplexity/Machines/NARMExample
TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/TuringMachine/Build/WindowRun
TCSlib/Complexity/SpaceComplexity/WindowClock
TCSlib/Complexity/SpaceComplexity/ZeroSpace
TCSlib/Complexity/SpaceComplexity
TCSlib/Complexity/TimeHierarchy
TCSlib/Complexity/TuringMachine/Build/StepBlockForward
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance
TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes
TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/SelfUniversal
TCSlib/Complexity/TuringMachine/UniversalTlogT
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/Uncomputability

## ===== campaign/gates/92-g5-statements/evidence/round2/merged-tree/replay-lg5b.sh =====

#!/usr/bin/env bash
# Replay lg5b (#189 round 2 (gate 92's fixes) merged with the campaign after #184; branch lean/g5-statements, stacked on the campaign tip after #184): its downstream closure (325 modules),
# fresh .oleans into oleans-lg5b, a copy of oleans-ledge, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g5"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg5b.txt"
LOG="$S/fills/replay/replay-lg5b.log"
PINS="TCSlib/Complexity/TuringMachine.lean:579fcc579bba922b098b4ad9c3afd0f976718877
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:06d9339d3f17bc38bda991ccd68185d1fcb57eff
TCSlib/Complexity/TuringMachine/Encoding.lean:11ed81dfdc7077e35da0921c657b89669fc7fe7b
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:7a62c01f42d3240f1231b12de84b703c92619ce6
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:cc35767342620a3be6331c57239e5eafa5ea4c45
TCSlib/Complexity/TuringMachine/UniversalTlogT.lean:666b3f8324c616500a5febfa3ee317f45d446366"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g5-statements 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0189e66cc2fd38a9a6b4a865e3c253bf0dc4f3bd HEAD || { echo "precheck: the head must contain the campaign tip after #184; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0189e66cc2fd38a9a6b4a865e3c253bf0dc4f3bd HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #184 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-ledge.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "325" ] || { echo "precheck: the replay list must have 325 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg5b" ] && { echo "precheck: $S/oleans-lg5b already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-ledge" ] || { echo "precheck: oleans-ledge is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-ledge" "$S/oleans-lg5b" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg5b at $(git rev-parse --short HEAD): #189 round 2 (gate 92's fixes) merged with the campaign after #184 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg5b"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg5b nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=325 failed=0" || { echo "replay: a module failed, or the count is not 325" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/92-g5-statements/evidence/round2/patches/0001-Two-work-tapes-the-function-level-form-reads-Compute.patch =====

From caa6bf534653796aaee098bcb9b88fb7a17a1cec Mon Sep 17 00:00:00 2001
From: Seyoon Ragavan <complexzetaprime@gmail.com>
Date: Wed, 4 Nov 2026 23:05:48 -0800
Subject: [PATCH] Two work tapes: the function-level form reads
 ComputesFunInTime through computesFunInTime_iff; stateEquivFin's defining
 equation; the per-run converse's limitation stated exactly

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
---
 TCSlib/Complexity/TuringMachine/Encoding.lean             | 8 ++++++++
 .../TuringMachine/Robustness/AlphabetReduction.lean       | 5 +++--
 TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean  | 3 ++-
 3 files changed, 13 insertions(+), 3 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Encoding.lean b/TCSlib/Complexity/TuringMachine/Encoding.lean
index c0fe6784..11ed81df 100644
--- a/TCSlib/Complexity/TuringMachine/Encoding.lean
+++ b/TCSlib/Complexity/TuringMachine/Encoding.lean
@@ -719,6 +719,14 @@ noncomputable def FinTM.stateEquivFin {Symbol : Type} (M : FinTM Symbol) :
     have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
     omega)
 
+/-- `Turing.FinTM.stateEquivFin` is the bijection that `Fintype.equivFinOfCardEq` gives for the
+state count, which the start state makes positive (its defining equation). -/
+theorem FinTM.stateEquivFin_eq {Symbol : Type} (M : FinTM Symbol) :
+    M.stateEquivFin = Fintype.equivFinOfCardEq (by
+      have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
+      omega) :=
+  rfl
+
 /-- **The space-faithful coding step.** Every one-work-tape binary machine `M` is equivalent
 to a coded machine `M'` that halts with the same outputs at the same times
 (`Turing.exists_codeTM`'s clause) **and uses the same space at every time**. This is the space
diff --git a/TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean b/TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
index e95cd630..7a62c01f 100644
--- a/TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
+++ b/TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
@@ -603,8 +603,9 @@ output `w.map e`, within `c · t` steps for a run of `t` steps. Conversely, when
 `x` with output `w`, `M` halts on `x.map e` with some output `o`, and if `o` is the image `v.map e`
 of a binary word then `v = w`.
 
-The converse cannot say more: `M'` decodes each emitted symbol through a total decoder, so an
-output of `M` outside the image of `e` is decoded too. A machine that writes only images of bits
+Without an image hypothesis the converse cannot in general assert `o = w.map e`: `M'` decodes
+each emitted symbol through a total decoder, so an output of `M` outside the image of `e` is
+decoded too. A machine that writes only images of bits
 (as every machine computing a binary function via `e` does) has `o = w.map e`.
 
 **Proof sketch.** `M'` is the block simulation of `Turing.FinTM.alphabet_reduction`, whose
diff --git a/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean b/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
index 6cf70886..cc357673 100644
--- a/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
+++ b/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
@@ -80,6 +80,7 @@ theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T
     ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
       M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
   obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
-  exact ⟨M', c, hk, fun x => h x (f x) _ (hM x)⟩
+  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
+    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩
 
 end Turing.FinTM
-- 
2.50.1 (Apple Git-155)


## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/ARSealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  fixed-width blocks — the original sketch proposed `⌈log₂ |Γ|⌉` bits, and the
  delivered implementation uses a **one-hot code of width `|Γ| + 1`** (see the
  theorem's implementation note; the wider fixed width only changes the
  existential constant — epoch-2 audit, finding 1) — and decodes each emitted
  symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].
* `Turing.FinTM.alphabet_reduction_run` — the same, run by run, with the converse.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

noncomputable section

private abbrev ArBlock (N : ℕ) := Fin (N + 1) → Option Bool

private def arCell (N : ℕ) (p : ℤ) : ℤ := p / ((N : ℤ) + 1)

private def arIndex (N : ℕ) (p : ℤ) : Fin (N + 1) :=
  ⟨(p % ((N : ℤ) + 1)).toNat, by
    have h₁ := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
    have h₂ := Int.emod_lt_of_pos p (show 0 < (N : ℤ) + 1 by omega)
    omega⟩

private def arPos (N : ℕ) (z : ℤ) (j : ℕ) : ℤ := ((N : ℤ) + 1) * z + j

private lemma arCoords (N : ℕ) (z : ℤ) (j : Fin (N + 1)) :
    arCell N (arPos N z j.val) = z ∧ arIndex N (arPos N z j.val) = j := by
  have hj := j.isLt
  have h := (Int.ediv_emod_unique (show 0 < (N : ℤ) + 1 by omega)).2
    (show (j.val : ℤ) + ((N : ℤ) + 1) * z = arPos N z j.val ∧
      0 ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (N : ℤ) + 1 from
      ⟨by simp [arPos, add_comm], by omega, by omega⟩)
  refine ⟨h.1, Fin.ext ?_⟩
  simp only [arIndex, h.2, Int.toNat_natCast]

private lemma arPos_coords (N : ℕ) (p : ℤ) :
    arPos N (arCell N p) (arIndex N p).val = p := by
  have h := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
  simp only [arPos, arCell, arIndex, Int.toNat_of_nonneg h]
  exact Int.mul_ediv_add_emod p ((N : ℤ) + 1)

private lemma arPos_eq {N : ℕ} (z z' : ℤ) (j j' : Fin (N + 1)) :
    arPos N z j.val = arPos N z' j'.val ↔ z = z' ∧ j = j' := by
  constructor
  · intro h
    have h₁ := congrArg (arCell N) h
    have h₂ := congrArg (arIndex N) h
    rw [(arCoords N z j).1, (arCoords N z' j').1] at h₁
    rw [(arCoords N z j).2, (arCoords N z' j').2] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

private def arTape {N : ℕ} (F : ℤ → ArBlock N) (p : ℤ) : Option Bool :=
  F (arCell N p) (arIndex N p)

private lemma arTape_at {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ) (j : Fin (N + 1)) :
    arTape F (arPos N z j.val) = F z j := by
  simp only [arTape, (arCoords N z j).1, (arCoords N z j).2]

private lemma arTape_ext {N : ℕ} (u v : ℤ → Option Bool)
    (h : ∀ z (j : Fin (N + 1)), u (arPos N z j.val) = v (arPos N z j.val)) : u = v := by
  funext p
  simpa only [arPos_coords] using h (arCell N p) (arIndex N p)

private lemma arTape_update {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ)
    (j : Fin (N + 1)) (b : Option Bool) :
    Function.update (arTape F) (arPos N z j.val) b =
      arTape (fun z' j' => if z' = z ∧ j' = j then b else F z' j') := by
  apply arTape_ext (N := N)
  intro z' j'
  simp only [Function.update_apply, arTape_at, arPos_eq]

/-- A fixed-width one-hot code for nonblank symbols, with an all-blank code for
logical blank. Testing the position assigned to a symbol proves injectivity. -/
private def arCode {Γ : Type} [Fintype Γ] : Option Γ ↪ ArBlock (Fintype.card Γ) where
  toFun a j := a.map fun x => decide (j.val = (Fintype.equivFin Γ x).val)
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have := congrFun h 0; simp at this
    | some a =>
      cases b with
      | none => have := congrFun h 0; simp at this
      | some b =>
        have ha := (Fintype.equivFin Γ a).isLt
        have h₁ := congrFun h ⟨(Fintype.equivFin Γ a).val, by omega⟩
        have h₂ : (Fintype.equivFin Γ a).val = (Fintype.equivFin Γ b).val := by simpa using h₁
        exact congrArg some ((Fintype.equivFin Γ).injective (Fin.ext h₂))

private def arDecode {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) :
    ArBlock N → Option Γ := Function.invFun E

private lemma arDecode_code {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) (a : Option Γ) :
    arDecode E (E a) = a := Function.leftInverse_invFun E.injective a

private def arBit {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (a : Γ) : Bool :=
  decide (a = e true)

private lemma arBit_embed {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    arBit e (e b) = b := by
  cases b <;> simp [arBit, e.injective.eq_iff]

private abbrev ArPending (Γ S : Type) (k : ℕ) :=
  Option S × (Fin k → Option Γ) × (Fin k → SignType)

private abbrev ArState (Γ S : Type) (k N : ℕ) :=
  (S × Fin (N + 2) × (Fin k → ArBlock N)) ⊕
    (ArPending Γ S k × (Fin (N + 1) ⊕ Fin (N + 2)))

private def arReady {Γ S : Type} {k N : ℕ} (q : S) : ArState Γ S k N :=
  .inl (q, 0, fun _ _ => none)

private def arPending {Γ S : Type} {k : ℕ} (read : Fin k → Option Γ)
    (a : Action k Γ S) : ArPending Γ S k :=
  (a.state, fun i => (a.workTapes i).1.getD (read i), fun i => (a.workTapes i).2)

/-- A block cycle reads right, writes left, and then moves a whole block in each
source direction. Even with zero work tapes the finite controller performs the same
positive number of steps. Input motion and the possible emission occur only once,
at the transition between reading and writing. -/
private def arTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) : FinTM Bool where
  k := M.k
  State := ArState Γ M.State M.k N
  decEqState := Classical.decEq _
  tm :=
    { q₀ := arReady M.tm.q₀
      tr := fun q inp work => match q with
        | .inl (q, j, buf) =>
          if h : j.val < N + 1 then
            ⟨0, fun _ => (none, .pos), none,
              some (.inl (q, ⟨j.val + 1, by omega⟩,
                fun i => Function.update (buf i) ⟨j.val, h⟩ (work i)))⟩
          else
            let a := M.tm.tr q (inp.map e) (fun i => arDecode E (buf i))
            ⟨a.inputTape, fun _ => (none, .neg), a.output.map (arBit e),
              some (.inr (arPending (fun i => arDecode E (buf i)) a, .inl ⟨N, by omega⟩))⟩
        | .inr (a, .inl j) =>
          if h : j.val = 0 then
            ⟨0, fun i => (some (E (a.2.1 i) j), 0), none,
              some (.inr (a, .inr ⟨N + 1, by omega⟩))⟩
          else
            ⟨0, fun i => (some (E (a.2.1 i) j), .neg), none,
              some (.inr (a, .inl ⟨j.val - 1, by omega⟩))⟩
        | .inr (a, .inr r) =>
          if h : r.val = 0 then
            ⟨0, fun _ => (none, 0), none, a.1.map arReady⟩
          else
            ⟨0, fun i => (none, a.2.2 i), none,
              some (.inr (a, .inr ⟨r.val - 1, by omega⟩))⟩ }

/-- Canonical macro-boundary representation. Output is mapped through the total
bit decoder; under the computation premise `arEmission_in_image` additionally shows
that every emission is in the bit embedding's image, so its default case is unused. -/
private def arCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    Cfg k Bool (ArState Γ S k N) x where
  state := c.state.map arReady
  inputPos := ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩
  workTapes i := arTape (fun z => E (c.workTapes i z))
  workTapePos i := arPos N (c.workTapePos i) 0
  output := c.output.map (arBit e)

private lemma arCfg_input {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    (arCfg E e c).inputSymbol.map e = c.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [arCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private def arBuffer {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : ℕ) : Fin k → ArBlock N :=
  fun i b => if b.val < j then E (read i) b else none

private lemma arBuffer_zero {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read 0 = fun _ _ => none := by
  funext i b
  simp [arBuffer]

private lemma arBuffer_full {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read (N + 1) = fun i => E (read i) := by
  funext i b
  simp only [arBuffer, if_pos b.isLt]

private lemma arBuffer_update {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : Fin (N + 1)) :
    (fun i => Function.update (arBuffer E read j.val i) j (E (read i) j)) =
      arBuffer E read (j.val + 1) := by
  funext i b
  by_cases h : b = j
  · subst b
    simp [arBuffer]
  · have hv : b.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, arBuffer]
    split_ifs <;> first | rfl | omega

private def arReadCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e c with
    state := some (.inl (q, j, arBuffer E c.workTapeSymbols j.val))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arReadCfg_zero {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (hc : c.state = some q) : arReadCfg E e c q 0 = arCfg E e c := by
  simp [arReadCfg, arCfg, hc, arReady, arBuffer_zero]

private lemma arReadCfg_symbols {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arReadCfg E e c q j).workTapeSymbols = fun i => E (c.workTapeSymbols i) ⟨j.val, hj⟩ := by
  funext i
  exact arTape_at (fun z => E (c.workTapes i z)) (c.workTapePos i) ⟨j.val, hj⟩

private lemma arReadCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State)
    (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arTM E e M).tm.step (arReadCfg E e c q j) =
      arReadCfg E e c q ⟨j.val + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val < N + 1 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_pos hj]
  rw [arReadCfg_symbols E e c q j hj]
  refine Cfg.ext ?_ ?_ rfl ?_ ?_
  · have hb := arBuffer_update E c.workTapeSymbols ⟨j.val, hj⟩
    dsimp only at hb
    simp only [Action.apply, arReadCfg, hb]
  · simp [arReadCfg, arCfg, Action.apply]
  · funext i
    simp [arReadCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arReadCfg, arCfg, Action.apply]

private lemma arReadCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) (hc : c.state = some q) :
    ∀ j (hj : j ≤ N + 1), (arTM E e M).tm.runFrom (arCfg E e c) j =
      arReadCfg E e c q ⟨j, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact (arReadCfg_zero E e c q hc).symm
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact arReadCfg_step E e M c q ⟨j, by omega⟩ (by dsimp only; omega)

private def arTail {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (r : ℕ) : ℤ → ArBlock N :=
  fun z j => if z = p ∧ r ≤ j.val then E w j else E (t z) j

private lemma arTail_full {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w (N + 1) = fun z => E (t z) := by
  funext z j
  have := j.isLt
  simp [arTail, show ¬N + 1 ≤ j.val by omega]

private lemma arTail_zero {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w 0 = fun z => E (Function.update t p w z) := by
  funext z j
  simp only [arTail, Nat.zero_le, and_true, Function.update_apply]
  split <;> rfl

/-- One leftward write extends the completed suffix by one bit. Distinct blocks
remain unchanged; within this block the only new index is the written index. -/
private lemma arTail_update {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (j : Fin (N + 1)) :
    Function.update (arTape (arTail E t p w (j.val + 1))) (arPos N p j.val) (E w j) =
      arTape (arTail E t p w j.val) := by
  apply arTape_ext (N := N)
  intro z b
  simp only [Function.update_apply, arTape_at, arPos_eq, arTail]
  by_cases hz : z = p
  · subst z
    by_cases hj : b = j
    · subst b; simp
    · have hv : b.val ≠ j.val := fun h => hj (Fin.ext h)
      simp only [true_and, hj, and_false, if_false]
      split_ifs <;> first | rfl | omega
  · simp [hz]

private def arMoveCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (r : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inr r))
    workTapePos := fun i => arPos N (c.workTapePos i) 0 +
      (((N : ℤ) + 1) - r.val) * ((a.workTapes i).2 : ℤ) }

private def arWriteCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (j : Fin (N + 1)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inl j))
    workTapes := fun i => arTape (arTail E (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) (j.val + 1))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arMoveCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (r : Fin (N + 2)) (hr : r.val ≠ 0) :
    (arTM E e M).tm.step (arMoveCfg E e c a r) =
      arMoveCfg E e c a ⟨r.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : r.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hr]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    have hcast : ((r.val - 1 : ℕ) : ℤ) = (r.val : ℤ) - 1 := by omega
    simp only [Action.apply, arMoveCfg, arPending, hcast]
    ring
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arMoveCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arMoveCfg E e c a 0) = arCfg E e (a.apply c) := by
  unfold MultiTapeTM.step
  dsimp only [arMoveCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 2)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arCfg, arPos, Fin.val_zero, SignType.coe_zero]
    ring
  · simp [arCfg, Action.apply]

private lemma arMoveCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ r (hr : r ≤ N + 1), (arTM E e M).tm.runFrom (arMoveCfg E e c a ⟨r, by omega⟩)
      (r + 1) = arCfg E e (a.apply c) := by
  intro r
  induction r with
  | zero => intro hr; exact arMoveCfg_finish E e M c a
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step, arMoveCfg_step E e M c a ⟨r + 1, by omega⟩ (by simp)]
    exact ih (by omega)

private lemma arWriteCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (j : Fin (N + 1)) (hj : j.val ≠ 0) :
    (arTM E e M).tm.step (arWriteCfg E e c a j) =
      arWriteCfg E e c a ⟨j.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hj]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arWriteCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arWriteCfg, arPending]
    rw [arTail_update]
    congr 2
    omega
  · funext i
    simp [Action.apply, arWriteCfg, arPos, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply]

private lemma arWriteCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arWriteCfg E e c a 0) =
      arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arWriteCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 1)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arMoveCfg, arCfg, arPending]
    rw [arTail_update]
    simp only [Fin.val_zero, arTail_zero]
    change arTape (fun z => E (Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) z)) =
      arTape (fun z => E ((a.apply c).workTapes i z))
    rw [Action.apply_workTapes]
  · funext i
    simp [arMoveCfg, arPos, Action.apply]
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arWriteCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ j (hj : j ≤ N), (arTM E e M).tm.runFrom (arWriteCfg E e c a ⟨j, by omega⟩)
      (j + 1) = arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact arWriteCfg_finish E e M c a
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, arWriteCfg_step E e M c a ⟨j + 1, by omega⟩ (by simp)]
    exact ih (by omega)

/-- At the end of the read sweep, decoding recovers all scanned source symbols.
Execute the source input move and emission, save its pending work update in finite
control, and move left to the last bit of each block to start the write sweep. -/
private lemma arReadCfg_dispatch {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) :
    (arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩) =
      arWriteCfg E e c (M.tm.tr q c.inputSymbol c.workTapeSymbols) ⟨N, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arReadCfg, arTM]
  rw [dif_neg (show ¬N + 1 < N + 1 by omega)]
  simp only [arBuffer_full, arDecode_code]
  have hi : (arReadCfg E e c q ⟨N + 1, by omega⟩).inputSymbol.map e =
      c.inputSymbol := arCfg_input E e c
  simp only [arReadCfg, arBuffer_full] at hi
  rw [hi]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · apply Fin.ext
    simp [arWriteCfg, arCfg, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    simp only [Action.apply, arWriteCfg, arCfg, arTail_full]
  · funext i
    simp [arWriteCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply, List.map_append, Option.toList_map]

/-- Three sweeps plus two control transitions simulate one source step. Once the
source has halted, both represented configurations are absorbing. -/
private lemma arCfg_cycle {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) :
    (arTM E e M).tm.runFrom (arCfg E e c) (3 * (N + 1) + 2) =
      arCfg E e (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.runFrom_of_halt _ (show (arCfg E e c).state = none by simp [arCfg, hs])]
  | some q =>
    rw [show 3 * (N + 1) + 2 = (N + 1) + (1 + ((N + 1) + ((N + 1) + 1))) by omega,
      MultiTapeTM.runFrom_add, arReadCfg_run E e M c q hs (N + 1) (le_refl _)]
    rw [MultiTapeTM.runFrom_add]
    change (arTM E e M).tm.runFrom
      ((arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩)) _ = _
    rw [arReadCfg_dispatch, MultiTapeTM.runFrom_add,
      arWriteCfg_run E e M c _ N (le_refl _), arMoveCfg_run E e M c _ (N + 1) (le_refl _)]
    simp only [MultiTapeTM.step, hs]

private lemma arCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.runFrom (arCfg E e c) ((3 * (N + 1) + 2) * t) =
      arCfg E e (M.tm.runFrom c t) := by
  induction t with
  | zero => simp only [Nat.mul_zero, MultiTapeTM.runFrom_zero]
  | succ t ih =>
    rw [Nat.mul_succ, MultiTapeTM.runFrom_add, ih, arCfg_cycle,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma arCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) :
    (arTM E e M).tm.initCfg x = arCfg E e (M.tm.initCfg (x.map e)) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [arCfg]
  · funext i p
    simp only [MultiTapeTM.initCfg, Cfg.init, arCfg, arTape, hE]
  · funext i
    simp [arCfg, arPos]

/-- The output decoder is total, with `false` for every non-image symbol. In the
computation invariant those cases are unreachable: an emitted source symbol remains
in the append-only output, which is a prefix of the completed embedded output. -/
private lemma arEmission_in_image {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) (x : List Bool) (t : ℕ) (a : Γ)
    (ha : M.tm.outputSymbol (M.tm.runFrom (M.tm.initCfg (x.map e)) t) = some a) :
    ∃ b, e b = a := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 (hM x)
  by_cases ht : t < T x.length
  · have hp := M.tm.output_prefix (M.tm.initCfg (x.map e)) (show t + 1 ≤ T x.length by omega)
    rw [ho] at hp
    have hm : a ∈ (M.tm.runFrom (M.tm.initCfg (x.map e)) (t + 1)).output := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ha]
      simp
    obtain ⟨b, _, hb⟩ := List.mem_map.1 (hp.sublist.subset hm)
    exact ⟨b, hb⟩
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show T x.length ≤ t by omega)
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs,
      MultiTapeTM.outputSymbol_of_halt hs] at ha
    cases ha

private lemma arTM_computes {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) (w : List Bool) (t : ℕ)
    (h : M.ComputesInTime (x.map e) (w.map e) t) :
    (arTM E e M).ComputesInTime x w ((3 * (N + 1) + 2) * t) := by
  rw [computesInTime_iff, arCfg_init E hE, arCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 h
  simp only [arCfg, hs, ho, Option.map_none, true_and, List.map_map]
  simp only [Function.comp_def, arBit_embed]
  exact List.map_id w

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O((k + 1) · L)` — the
`+ 1` covering the input-read, state-update, and emission work that remains even for
`k = 0` — plus a constant start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers.

**Implementation note (epoch 2, batch C).** As permitted by the brief's arbitrary
fixed-width scheme, the implementation uses a one-hot binary code of width
`L = Fintype.card Γ + 1` for nonblank symbols; logical blank remains all-`none`.
The proof factors through any injective code of positive width with this blank
property. All work tapes are swept simultaneously: `L` reads, one dispatch,
`L` writes, `L` moves, and one final control transition, for exactly `3 * L + 2`
steps per live source step. This also covers zero work tapes. The input is never
block-encoded. `arEmission_in_image` formalizes the output-prefix argument, while
the run correspondence maps the entire output through a total decoder. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_⟩
  intro x
  exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
    (Nat.mul_le_mul_left _ (Nat.le_succ _))

section G5Sealed

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init

/-- **Alphabet reduction, run by run** [AB09, Claim 1.5]: for every machine `M` over a finite
alphabet `Γ` and every embedding `e : Bool ↪ Γ`, a binary machine `M'` with the same number of
work tapes reproduces each halting run of `M` on an encoded input `x.map e` with an encoded
output `w.map e`, within `c · t` steps for a run of `t` steps. Conversely, whenever `M'` halts on
`x` with output `w`, `M` halts on `x.map e` with some output `o`, and if `o` is the image `v.map e`
of a binary word then `v = w`.

Without an image hypothesis the converse cannot in general assert `o = w.map e`: `M'` decodes
each emitted symbol through a total decoder, so an output of `M` outside the image of `e` is
decoded too. A machine that writes only images of bits
(as every machine computing a binary function via `e` does) has `o = w.map e`.

**Proof sketch.** `M'` is the block simulation of `Turing.FinTM.alphabet_reduction`, whose
run correspondence maps `M`'s configuration after `t` steps to `M'`'s after `c · t`. The
forward direction is that correspondence at the halting time. For the converse, let `M'`
halt at `t`. Since `c ≥ 1` and a halted run is stationary, `M'`'s configuration at `c · t` is
the one at `t`, so the correspondence says that `M`'s configuration after `t` steps is
halted, and that `w` is its output decoded. If that output is `v.map e`, decoding returns
`v`. -/
theorem alphabet_reduction_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      (∀ (x w : List Bool) (t : ℕ), M.ComputesInTime (x.map e) (w.map e) t →
        M'.ComputesInTime x w (c * t)) ∧
      ∀ (x w : List Bool), (∃ t, M'.ComputesInTime x w t) →
        ∃ (t : ℕ) (o : List Γ), M.ComputesInTime (x.map e) o t ∧
          ∀ v : List Bool, o = v.map e → v = w := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl,
    fun x w t h => arTM_computes E hE e M x w t h, ?_⟩
  rintro x w ⟨t, ht⟩
  obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).1 ht
  have hrun := arCfg_run E e M (M.tm.initCfg (x.map e)) t
  rw [← arCfg_init E hE] at hrun
  have hle : t ≤ (3 * (Fintype.card Γ + 1) + 2) * t := by
    calc t = 1 * t := (one_mul t).symm
      _ ≤ _ := Nat.mul_le_mul_right t (by omega)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at hrun
  refine ⟨t, (M.tm.runFrom (M.tm.initCfg (x.map e)) t).output, ?_, fun v hv => ?_⟩
  · rw [computesInTime_iff]
    refine ⟨?_, rfl⟩
    have h1 := congrArg Cfg.state hrun
    rw [hs] at h1
    simp only [arCfg] at h1
    exact Option.map_eq_none_iff.1 h1.symm
  · have h2 := congrArg Cfg.output hrun
    rw [ho] at h2
    simp only [arCfg, hv, List.map_map, Function.comp_def, arBit_embed, List.map_id'] at h2
    exact h2.symm

end G5Sealed

end

end Turing.FinTM

/-! ### Space annotation (§13 Z4; additive, shared-file mechanism, flagged
for the A-S2 audit) -/

namespace Turing.FinTM

/-- The four configurations already used by the block simulation cover every
physical instant: a macro boundary, a read, a write, or a move. -/
private def arSpacePhase {Γ : Type} [DecidableEq Γ] {N k : ℕ} {Q : Type}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (tm : MultiTapeTM k Γ Q)
    {x : List Bool} (c : Cfg k Γ Q (x.map e))
    (d : Cfg k Bool (ArState Γ Q k N) x) : Prop :=
  d = arCfg E e c ∨ ∃ q, c.state = some q ∧
    ((∃ j, d = arReadCfg E e c q j) ∨
      (∃ j, d = arWriteCfg E e c (tm.tr q c.inputSymbol c.workTapeSymbols) j) ∨
      (∃ r, d = arMoveCfg E e c (tm.tr q c.inputSymbol c.workTapeSymbols) r))

/-- One physical transition stays in the current source cycle, or completes it.
**Proof sketch.** Split the four phases and cite the existing transition lemmas.
Only finishing the move advances the source; a halted boundary is absorbing. -/
private lemma arSpacePhase_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e))
    (d : Cfg M.k Bool (ArState Γ M.State M.k N) x)
    (h : arSpacePhase E e M.tm c d) :
    arSpacePhase E e M.tm c ((arTM E e M).tm.step d) ∨
      arSpacePhase E e M.tm (M.tm.step c) ((arTM E e M).tm.step d) := by
  rcases h with rfl | ⟨q, hq, h⟩
  · cases hq : c.state with
    | none =>
      left; left
      exact MultiTapeTM.step_of_halt (by simp [arCfg, hq])
    | some q =>
      left; right
      refine ⟨q, hq, Or.inl ⟨⟨1, by omega⟩, ?_⟩⟩
      rw [← arReadCfg_zero E e c q hq]
      exact arReadCfg_step E e M c q 0 (by simp)
  · rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨r, rfl⟩
    · left; right
      refine ⟨q, hq, ?_⟩
      by_cases hj : j.val < N + 1
      · exact Or.inl ⟨⟨j.val + 1, by omega⟩, arReadCfg_step E e M c q j hj⟩
      · have he : j = ⟨N + 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [he]
        exact Or.inr (Or.inl ⟨⟨N, by omega⟩, arReadCfg_dispatch E e M c q⟩)
    · left; right
      refine ⟨q, hq, Or.inr ?_⟩
      by_cases hj : j.val = 0
      · have he : j = 0 := Fin.ext hj
        subst j
        exact Or.inr ⟨⟨N + 1, by omega⟩, arWriteCfg_finish E e M c _⟩
      · exact Or.inl ⟨⟨j.val - 1, by omega⟩, arWriteCfg_step E e M c _ j hj⟩
    · by_cases hr : r.val = 0
      · have he : r = 0 := Fin.ext hr
        subst r
        right; left
        rw [arMoveCfg_finish]
        simp only [MultiTapeTM.step, hq]
      · left; right
        exact ⟨q, hq, Or.inr (Or.inr
          ⟨⟨r.val - 1, by omega⟩, arMoveCfg_step E e M c _ r hr⟩)⟩

/-- Every physical horizon belongs to a source cycle whose index is no larger.
**Proof sketch.** Induct over physical time and use the phase transition lemma;
its second branch advances both the source-cycle index and the time bound. -/
private lemma arSpacePhase_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    ∃ s ≤ t, arSpacePhase E e M.tm (M.tm.runFrom c s)
      ((arTM E e M).tm.runFrom (arCfg E e c) t) := by
  induction t with
  | zero => exact ⟨0, le_refl _, Or.inl rfl⟩
  | succ t ih =>
    obtain ⟨s, hs, hp⟩ := ih
    rcases arSpacePhase_step E e M _ _ hp with h | h
    · refine ⟨s, by omega, ?_⟩
      simpa only [MultiTapeTM.runFrom_succ_eq_step'] using h
    · refine ⟨s + 1, by omega, ?_⟩
      simpa only [MultiTapeTM.runFrom_succ_eq_step'] using h

/-- During a whole-block move a physical head lies in the closed block of
one of the two source endpoints. The closed upper endpoint counts the read
pass's one-cell overshoot as well. -/
private lemma arMoveCfg_position {Γ Q : Type} [DecidableEq Γ] {N k : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) {x : List Bool}
    (c : Cfg k Γ Q (x.map e)) (a : Action k Γ Q) (r : Fin (N + 2)) (i : Fin k) :
    (∃ j ≤ N + 1, (arMoveCfg E e c a r).workTapePos i =
      arPos N (c.workTapePos i) j) ∨
    (∃ j ≤ N + 1, (arMoveCfg E e c a r).workTapePos i =
      arPos N ((a.apply c).workTapePos i) j) := by
  have hr : r.val ≤ N + 1 := by have := r.isLt; omega
  cases hd : (a.workTapes i).2 with
  | neg =>
    right
    refine ⟨r.val, hr, ?_⟩
    simp only [arMoveCfg, arPos, Action.apply, hd, SignType.cast, Nat.cast_zero]
    ring
  | zero =>
    left
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp [arMoveCfg, arPos, hd]
  | pos =>
    left
    refine ⟨N + 1 - r.val, by omega, ?_⟩
    have hcast : ((N + 1 - r.val : ℕ) : ℤ) = (N : ℤ) + 1 - r.val := by omega
    simp [arMoveCfg, arPos, hd, hcast]

/-- Trajectory containment at every physical instant: the head is in a closed
block belonging to a source position visited by the following source horizon.
This includes intermediate reads, writes, moves, and every post-halt instant.
**Proof sketch.** The phase invariant gives a source cycle. Read and write
positions are explicit offsets; a move uses one of that cycle's endpoints. -/
private lemma arTM_position_visited {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) (i : Fin M.k) :
    ∃ s ≤ t + 1, ∃ j ≤ N + 1,
      ((arTM E e M).tm.runFrom (arCfg E e c) t).workTapePos i =
        arPos N ((M.tm.runFrom c s).workTapePos i) j := by
  obtain ⟨s, hs, hp⟩ := arSpacePhase_run E e M c t
  rcases hp with h | ⟨q, hq, h⟩
  · exact ⟨s, by omega, 0, Nat.zero_le _, congrArg (fun d => d.workTapePos i) h⟩
  · rcases h with ⟨j, h⟩ | ⟨j, h⟩ | ⟨r, h⟩
    · exact ⟨s, by omega, j.val, by have := j.isLt; omega,
        congrArg (fun d => d.workTapePos i) h⟩
    · exact ⟨s, by omega, j.val, by have := j.isLt; omega,
        congrArg (fun d => d.workTapePos i) h⟩
    · rw [h]
      rcases arMoveCfg_position E e (M.tm.runFrom c s) _ r i with h | h
      · obtain ⟨j, hj, hp⟩ := h
        exact ⟨s, by omega, j, hj, hp⟩
      · obtain ⟨j, hj, hp⟩ := h
        refine ⟨s + 1, by omega, j, hj, ?_⟩
        simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step, hq] using hp

/-- A source cell's closed physical block includes the extra read boundary. -/
private def arSpaceBlock (N : ℕ) (z : ℤ) : Finset ℤ :=
  Finset.Icc (arPos N z 0) (arPos N z (N + 1))

/-- A closed block has its width plus one cells. -/
private lemma arSpaceBlock_card (N : ℕ) (z : ℤ) :
    (arSpaceBlock N z).card = N + 2 := by
  have he : arPos N z (N + 1) + 1 - arPos N z 0 = ((N + 2 : ℕ) : ℤ) := by
    simp only [arPos, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero]
    omega
  rw [arSpaceBlock, Int.card_Icc, he, Int.toNat_natCast]

/-- Closed blocks at consecutive (or equal) source positions overlap. -/
private lemma arSpaceBlock_inter (N : ℕ) (p q : ℤ) (h : |p - q| ≤ 1) :
    (arSpaceBlock N p ∩ arSpaceBlock N q).Nonempty := by
  have habs := abs_le.mp h
  have hW : 0 ≤ (N : ℤ) + 1 := by omega
  by_cases hp : p ≤ q
  · refine ⟨arPos N q 0, ?_⟩
    have hlo := Int.mul_le_mul_of_nonneg_left hp hW
    have hhi := Int.mul_le_mul_of_nonneg_left (show q ≤ p + 1 by omega) hW
    simp only [mul_add, mul_one] at hhi
    simp only [Finset.mem_inter, arSpaceBlock, Finset.mem_Icc, arPos,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    omega
  · refine ⟨arPos N p 0, ?_⟩
    have hlo := Int.mul_le_mul_of_nonneg_left (show q ≤ p by omega) hW
    have hhi := Int.mul_le_mul_of_nonneg_left (show p ≤ q + 1 by omega) hW
    simp only [mul_add, mul_one] at hhi
    simp only [Finset.mem_inter, arSpaceBlock, Finset.mem_Icc, arPos,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    omega

/-- Expanding a source trajectory into closed blocks costs its width per
visited source cell, with just one extra boundary cell on each tape.
**Proof sketch.** Initially there is one closed block. A repeated source
position adds nothing. A new position is adjacent to the preceding one,
so its block overlaps the existing cover and adds at most its width.
This is the cardinality ledger for the source's visited interval. -/
private lemma arSpaceCover_card {Γ Q : Type} {k : ℕ} {x : List Γ}
    (tm : MultiTapeTM k Γ Q) (c : Cfg k Γ Q x) (i : Fin k) (N t : ℕ) :
    ((tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N)).card ≤
      (N + 1) * tm.spaceUsedByTape c t i + 1 := by
  have hvis (s : ℕ) : tm.visitedByTapeHead c (s + 1) i =
      insert ((tm.runFrom c (s + 1)).workTapePos i) (tm.visitedByTapeHead c s i) := by
    simp only [MultiTapeTM.visitedByTapeHead, Finset.range_add_one, Finset.image_insert]
  unfold MultiTapeTM.spaceUsedByTape
  induction t with
  | zero => simp [MultiTapeTM.visitedByTapeHead, arSpaceBlock_card]
  | succ t ih =>
    rw [hvis]
    by_cases hp : (tm.runFrom c (t + 1)).workTapePos i ∈ tm.visitedByTapeHead c t i
    · simpa only [Finset.insert_eq_of_mem hp] using ih
    · rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hp]
      have hprev : (tm.runFrom c t).workTapePos i ∈ tm.visitedByTapeHead c t i :=
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
      have hd : |(tm.runFrom c (t + 1)).workTapePos i -
          (tm.runFrom c t).workTapePos i| ≤ 1 := by
        rw [MultiTapeTM.runFrom_succ_eq_step']
        exact tm.workTapePos_step_le _ i
      obtain ⟨p, hp⟩ := arSpaceBlock_inter N _ _ hd
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
      have hinter : 1 ≤ (arSpaceBlock N ((tm.runFrom c (t + 1)).workTapePos i) ∩
          (tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N)).card := by
        apply Finset.one_le_card.mpr
        exact ⟨p, Finset.mem_inter.mpr ⟨hp₁,
          Finset.mem_biUnion.mpr ⟨_, hprev, hp₂⟩⟩⟩
      have hc := Finset.card_union_add_card_inter
        (arSpaceBlock N ((tm.runFrom c (t + 1)).workTapePos i))
        ((tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N))
      rw [arSpaceBlock_card] at hc
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- At every horizon, alphabet reduction uses at most the block width times
source space through `t+1`, plus one boundary cell per work tape.
**Proof sketch.** Include every physical visit in the closed-block cover
of the source trajectory, apply its cardinality bound, and sum over tapes. -/
private lemma arTM_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.spaceUsed (arCfg E e c) t ≤
      (N + 1) * M.tm.spaceUsed c (t + 1) + M.k := by
  have htape (i : Fin M.k) :
      (arTM E e M).tm.spaceUsedByTape (arCfg E e c) t i ≤
        (N + 1) * M.tm.spaceUsedByTape c (t + 1) i + 1 := by
    have hsub : (arTM E e M).tm.visitedByTapeHead (arCfg E e c) t i ⊆
        (M.tm.visitedByTapeHead c (t + 1) i).biUnion (arSpaceBlock N) := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      have hu' : u ≤ t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu
      obtain ⟨s, hs, j, hj, he⟩ := arTM_position_visited E e M c u i
      refine Finset.mem_biUnion.mpr ⟨(M.tm.runFrom c s).workTapePos i,
        Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      rw [he]
      simp only [arSpaceBlock, Finset.mem_Icc, arPos, Nat.cast_zero, add_zero,
        Nat.cast_add, Nat.cast_one]
      omega
    exact (Finset.card_le_card hsub).trans (arSpaceCover_card M.tm c i N (t + 1))
  have hmul := Finset.sum_nsmul (M := ℕ) Finset.univ (N + 1)
    (fun i => M.tm.spaceUsedByTape c (t + 1) i)
  simp only [Nat.nsmul_eq_mul] at hmul
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htape i)
  simpa only [MultiTapeTM.spaceUsed, Finset.sum_add_distrib, hmul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- The alphabet reduction preserves space up to a constant: the binary
machine of `Turing.FinTM.alphabet_reduction` can be taken with an all-time
space bound of coefficient-constant shape in the source's. Part of the Z4
space annotation (`machine-library-design.md` §13), plan §2.7's fallback
route to the space-efficient universal (Ex 4.1).

**Proof sketch.** The received `arTM` witness codes each source cell as a
fixed-width block of the fixed code `arCode`; a visited binary cell lies
inside the block of a visited source cell (plus the block in progress), so
each tape's visited set scales by the block width plus a boundary
allowance, all-time because a halted simulation is fixed and a mid-block
head stays inside its block. The `+ 1` absorbs the origin of an untouched
tape. -/
theorem alphabet_reduction_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) (M : FinTM Γ) (f : List Bool → List Bool) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f (fun n => c * (T n + 1)) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_, ?_⟩
  · intro x
    exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
      (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · intro x t
    rw [arCfg_init E hE]
    have hs := hS (x.map e) (t + 1)
    simp only [List.length_map] at hs
    have hk : M.k ≤ S x.length := by
      have hz := hS (x.map e) 0
      simpa [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape,
        MultiTapeTM.visitedByTapeHead] using hz
    calc
      _ ≤ (Fintype.card Γ + 1) * M.tm.spaceUsed (M.tm.initCfg (x.map e)) (t + 1) +
          M.k := arTM_spaceUsed E e M _ t
      _ ≤ (Fintype.card Γ + 1) * S x.length + S x.length :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hs) hk
      _ = (Fintype.card Γ + 2) * S x.length := by ring
      _ ≤ (3 * (Fintype.card Γ + 1) + 2) * (S x.length + 1) :=
        Nat.mul_le_mul (by omega) (Nat.le_succ _)

end Turing.FinTM

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/ARSealed.out =====



## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/C2Sealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.MathlibBridge
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Catalog
-- B5a sanctioned import: the shared canonizer and uniform simulator.
import TCSlib.Complexity.TuringMachine.CodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic two-work-tape machine codes (Z3)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`Turing.CodeTM`/`Turing.MachineCode`/
`Turing.EffectiveMachineCode`, `Encoding.lean`), which is why the received
time hierarchy arrives at `f²` strength (plan §2.1): converting to that
normal form costs a square. This file is §13's Z3: the **deterministic
two-work-tape** code scheme, the codes the two-work-tape universal machine
(stage 1, plan §4b) reads, over **the same `Turing.actionBits₂` record
format** that `Turing.CodeNDTM` fixed for the nondeterministic two-tape
codes (design §13a: one branch instead of two — never a second
serialization). The file name reads *codes for two-tape machines*
(decision 13.3, renamed from `Codes2` by the user).

Mirrors: `Turing.CodeTM` → `Turing.Code2TM`; `Turing.MachineCode` →
`Turing.MachineCode2`; `Turing.EffectiveMachineCode` →
`Turing.EffectiveMachineCode2`; and, per the P3.2 lesson (a variable-code
consumer needs uniformly timed decoding — `EffectiveMachineCode` bounds no
decoding time), `UniformMachineCode` (`Diagonalization/EXPCOM.lean`) →
`Turing.UniformMachineCode2`.

## Status

The effective and the uniform schemes are proved, with no admission. The uniform scheme
instantiates the shared canonizer and the uniform simulator of `CodeSimulator`
(`Turing.MachineFormat.exists_polyCanonizer`, `Turing.MachineFormat.exists_uniformSimulator`) at
two work tapes.

## Main definitions and results

* `Turing.Code2TM`, `Turing.Code2TM.serialize` — the deterministic
  two-work-tape normal form and its fixed, scheme-independent
  serialization (27 `Turing.actionBits₂` records per state: three input
  reads by three reads on each of the two work tapes).
* `Turing.MachineCode2`, `Turing.EffectiveMachineCode2`,
  `Turing.UniformMachineCode2` — the scheme laws, the effective scheme,
  and the uniformly timed scheme.
* `Turing.Code2TM.serialize_eq_serializeK` — the frozen serialization is the generic
  `k`-record one at two work tapes.
* `Turing.exists_effectiveMachineCode2`,
  `Turing.exists_uniformMachineCode2` — proved existence statements (the latter
  modulo the uniform simulator).
* `Turing.exists_code2TM` — every two-work-tape binary machine has a coded equivalent.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.4, machine codes;
  §1.7/§3.1 for the two-tape consumer.)

**ZF-B status appendix.** The skeleton-status text above records the received
statement phase. `exists_effectiveMachineCode2` is now proved; the uniform
simulator remains the continuation target. The new implementation includes
private adaptations of inaccessible helpers in `CodeParser.lean` and
`MathlibBridge.lean`, with declaration-level provenance in `REPORT.md`.

**ZF-B2 cleanup appendix.** The ZF-B provenance above records the original
delivery. Its 46 format-independent local copies have now been deleted:
all uses cite the promoted public readers and primitive-recursion lemmas.
The 24 remaining private declarations implement the two-tape format and
its 354-bit regression; their one-tape counterparts and retained proof
material are itemized in this delivery's duplication ledger.

## Item-8 appendix

The two-work-tape parser and canonizer now instantiate the shared `CodeFormat`
layer. ZF-B3 consumes its decoded-size and guard corollaries, with the existing
silent fallback and every public scheme statement preserved.
-/

namespace Turing

/-- The coded normal form of a deterministic machine with **two** work
tapes: a binary-alphabet machine with state space `Fin (numStates + 1)`
(never empty). Two work tapes, not one, because the Hennie-Stearns
conversion lands there at `O(T log T)` and the two-tape universal machine
(its consumer) runs such codes at linear overhead — the whole point of
strengthening past `Turing.CodeTM`'s square. Mirrors `Turing.CodeTM` and
`Turing.CodeNDTM`. [AB09, §1.4, §1.7] -/
structure Code2TM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape deterministic machine -/
  tm : MultiTapeTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded two-tape machine. -/
def Code2TM.toFinTM (M : Code2TM) : FinTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The **fixed, scheme-independent** canonical serialization, mirroring
`Turing.CodeTM.serialize` and `Turing.CodeNDTM.serialize` over the same
`Turing.actionBits₂` record: the state count, the initial state, then the
full transition table in the fixed enumeration order — states in `Fin`
order, then the input read and the two work reads each over `none`,
`some false`, `some true` (27 records per state; the nondeterministic
table's outermost choice bit is absent). This is the target format of
`Turing.EffectiveMachineCode2.canonizer` and the input format of the
two-work-tape universal machine. -/
def Code2TM.serialize (M : Code2TM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded two-tape
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations). -/
structure MachineCode2 where
  /-- encode a machine as a binary string -/
  encode : Code2TM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → Code2TM
  /-- a code followed by any amount of `true`-padding decodes to the
  machine (property 2) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine (padding by zero symbols).
Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem MachineCode2.decode_encode (c : MachineCode2) (M : Code2TM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for two-tape machines: the
algebraic laws together with a machine of this development computing the
fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale (the
target `Turing.Code2TM.serialize` is scheme-independent). As there, the
canonizer's time bound is arbitrary: fixed-code consumers absorb it into
their constants, and variable-code consumers must use
`Turing.UniformMachineCode2` instead. -/
structure EffectiveMachineCode2 extends MachineCode2 where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-! ### Private parser and canonizer implementation (ZF-B)

The fixed silent fallback and the two-work-tape instance of `CodeFormat` supply
this format's parser and canonizer. The common record, table and primitive-recursion
laws live in `CodeFormat` and `MathlibBridge`; `zfBDecode` remains a typed alias
for the frozen uniform-simulator statements.
-/



/-- The fallback is the one-state, immediately halting, silent machine. -/
private def zfBFallback : Code2TM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- The one-state halting fallback has the audited 354-bit serialization.
The closed computation includes its header and all 27 thirteen-bit records. -/
private lemma zfBFallback_serialize_length : zfBFallback.serialize.length = 354 := by
  unfold Code2TM.serialize
  dsimp only [zfBFallback]
  set_option maxRecDepth 10000 in
    norm_num [length_pairEncode, unaryFin, actionBits₂, signBits, optOptBoolBits,
      optBoolBits, optStateBits, List.finRange_succ, List.finRange_zero]

/-- The deterministic two-work-tape code format, with 27 records per state
and the fixed silent fallback. [AB09, §1.4] -/
private def twoTapeFormat : CodeFormat where
  Code := Code2TM
  Table := CodeTable2
  numStates := Code2TM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun s inp w => t s inp (w 0) (w 1)⟩⟩
  serialize := Code2TM.serialize
  tableBits := fun t => codeTable2Bits t
  readTable := codeReadTable2
  skipTable := codeSkipTable2
  guard := 351
  fallback := zfBFallback
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => by
    simp [Code2TM.serialize, codeTable2Bits, actionBits₂_eq_actionBitsK, workPair]
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, fun s inp w₀ w₁ => tr s inp (workPair w₀ w₁), ?_⟩
    show Code2TM.mk n ⟨q, fun s inp w => tr s inp (workPair (w 0) (w 1))⟩ = Code2TM.mk n ⟨q, tr⟩
    congr 1
    congr 1
    funext s inp w
    apply congrArg (tr s inp)
    funext i
    fin_cases i <;> simp [workPair]
  readTable_append := fun _ t xs => codeReadTable2_append t xs
  readTable_sound := fun _ xs t rest h => codeReadTable2_sound xs t rest h
  readTable_erase := codeEraseTable2
  tableBits_length := fun _ t => codeTable2Bits_length t

/-- Total decoding: every malformed string denotes the fixed fallback. -/
private def zfBDecode (xs : List Bool) : Code2TM := twoTapeFormat.decode xs

/-- **An effective two-tape code scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** Mirror the received constructions over the
single-branch table: `encode := Code2TM.serialize` itself; `decode`
parses the `Turing.pairEncode`d state count, the initial state, and the
transition table by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record at **27 records per state** — the
nondeterministic retarget's `2 · 27 = 54` without the choice bit, so its
minimum-length guard scales by exactly half), with the single-state
do-nothing machine as the fallback on parse failure and trailing
`true`-padding tolerated by the end-marker discipline (property 2); the
canonizer re-serializes the parsed record by the arbitrary-time
computability route of the received deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`), so no polynomial
canonizer is claimed. Fill obligations, named: the record parser and its
fallback totalization; the pad-tolerance lemma; the canonizer assembly
and its time bound.

**ZF-B implementation appendix.** The private seven-field parser and its
suffix scanner implement this route, including the up-front 351-per-state
length guard. The scanner-based canonizer is proved primitive recursive,
then compiled by the public `codePrim_machine` theorem. Its arbitrary
length-only time bound is supplied by that theorem. The private parser and
primitive-recursion adaptations are itemized in the delivery's duplication
ledger; no ND existence theorem is used. 

**Item-8 appendix.** The two-work-tape instance now consumes the shared
`CodeFormat` parser, padded round trip and canonizer construction. The 351-per-state
guard and fixed fallback are unchanged; the private parser copies are removed. -/
theorem exists_effectiveMachineCode2 : Nonempty EffectiveMachineCode2 := by
  obtain ⟨M, T, h⟩ := twoTapeFormat.exists_canonizer codePrimSkipTable2
  exact ⟨⟨⟨Code2TM.serialize, zfBDecode, twoTapeFormat.decode_serialize_pad⟩, M, T, h⟩⟩

/-- A *uniformly timed* scheme for two-tape codes: the effective scheme
together with a bounded-acceptance simulator whose budget is one
polynomial **jointly** in the code length, input length, and time bound —
the mirror of `UniformMachineCode` (`Diagonalization/EXPCOM.lean`), which
exists because `EffectiveMachineCode2` deliberately bounds no decoding
time (the P3.2 lesson: with an arbitrary scheme, a variable-code consumer
can be made to pay unboundedly for decoding). -/
structure UniformMachineCode2 extends EffectiveMachineCode2 where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-! ### Uniform-simulator instance (B5a, D4)

The specialized ZF-B3 preparation is superseded by `MachineFormat`. Its seven
output-summary/clock declarations moved, generalized, to `CodeSimulator`;
the nine remaining private preparation declarations were removed.
The 354-bit fallback regression above is retained.
-/

/-- **The two-tape serialization is the generic one** [AB09, §1.4]: for every coded two-tape
machine `M`, the frozen serialization `M.serialize` is the fixed `k`-record serialization
`serializeK M.tm` at two work tapes. (Promoted from the private `twoTape_serialize_eq` for the
two-tape scheme's `k`-tape view `Turing.EffectiveMachineCode2.toK`; statement and proof
unchanged.) -/
lemma Code2TM.serialize_eq_serializeK (M : Code2TM) : M.serialize = serializeK M.tm := by
  unfold Code2TM.serialize serializeK
  rw [tableBitsK_two]
  simp only [codeTable2Bits, actionBits₂_eq_actionBitsK]

/-- The existing two-tape parser equipped with its fixed machine semantics. -/
private def twoTapeMachineFormat : MachineFormat :=
  MachineFormat.mk twoTapeFormat 2 Code2TM.tm
    Code2TM.serialize_eq_serializeK codeSkipTable2_eq_codeSkipTableK

/-- **A uniformly timed two-tape scheme exists**.

**Proof sketch.** The concrete scheme of
`Turing.exists_effectiveMachineCode2` with the uniform simulator built as
in the received `exists_uniformMachineCode` route
(`Diagonalization/EXPCOM.lean`, P3.2 round 2): parse the nested input
keeping the deadline in binary; check the table's minimum-length guard by
binary arithmetic before any per-state iteration (a huge declared state
count is never expanded in unary; the guard constant halves against the
nondeterministic table); then run the clocked step-by-step simulation of
the decoded two-tape machine, charging one uniform polynomial jointly in
`|α| + |x| + t + 1`. The two-work-tape simulation is *easier* than the
received one-tape case for the step itself (the simulator hosts the two
coded tapes on two physical tapes — no tape reduction), and the Z1
virtual-input layer supplies the input discipline.

**Fill appendix (B5a).** This is the two-tape instance of the shared §12.11
canonizer and H1, as in the statement probe's `uniform_two`. The two-tape
writer and skipper bridges supply the format laws. The canonizer and the
uniform simulator are proved; no specialized interpreter is introduced. -/
theorem exists_uniformMachineCode2 : Nonempty UniformMachineCode2 := by
  obtain ⟨C, dC, hC⟩ := twoTapeMachineFormat.exists_polyCanonizer
  obtain ⟨S, d, hS⟩ := twoTapeMachineFormat.exists_uniformSimulator
  exact ⟨{
    toEffectiveMachineCode2 := {
      toMachineCode2 := ⟨Code2TM.serialize, twoTapeMachineFormat.decode,
        twoTapeFormat.decode_serialize_pad⟩
      canonizer := C
      canonizerTime := fun n => dC * (n + 1) ^ dC
      canonizer_computes := hC }
    simulator := S
    simDegree := d
    simulator_accepts := fun α x t h => (hS α x t).1 h
    simulator_rejects := fun α x t h => (hS α x t).2 h }⟩

section G5Sealed

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.MultiTapeTM.relabelState
  Turing.Cfg.mapState
  Turing.FinTM.stateEquivFin

/-- Every two-work-tape binary machine is equivalent, input by input and step for step, to a
coded two-tape machine (the two-tape counterpart of `Turing.exists_codeTM`). [AB09, §1.4]

**Proof sketch.** The coded machine is the original one with its states renamed along
`Turing.FinTM.stateEquivFin` (`State ≃ Fin (n + 1)`); by
`Turing.FinTM.computesInTime_relabelState` it computes the same outputs in the same times. -/
theorem exists_code2TM (M : FinTM Bool) (hk : M.k = 2) :
    ∃ M' : Code2TM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  let M₀ : FinTM Bool := ⟨2, Q, tm⟩
  exact ⟨⟨Fintype.card Q - 1, tm.relabelState M₀.stateEquivFin⟩,
    M₀.computesInTime_relabelState M₀.stateEquivFin⟩

end G5Sealed

end Turing

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/C2Sealed.out =====



## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/ENSealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim); `Turing.dbl` — the doubling.
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.
* `Turing.pairDiagTM` — the diagonal pairing machine `α ↦ pairEncode α α` (MIG-1).
* `Turing.FinTM.toCodeTM` — the code normal form of a one-work-tape binary machine
  (MIG-1).

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.length_pairEncode`, `Turing.pairEncode_eq_dbl`, `Turing.pairDecode_eq_none`,
  `Turing.eq_pairEncode_of_pairDecode`, `Turing.pairEncode_replicate_inj` — the shape of
  the pairing, shared by the machine-side developments.
* `Turing.length_bits_le_self` — `|bits m| ≤ m`.
* `Turing.bits_two_pow_mul`, `Turing.bits_two_pow_eq_replicate` — the `Nat.bits` shift law
  `(2^j·m).bits = 0^j ++ m.bits` and its case `m = 1` (CH34-D4).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
  Its witness's spec is `Turing.pairDiagTM_computes` (MIG-1; sorried until the fill
  F-A).
* `Turing.FinTM.toCodeTM_computesInTime_iff` — the code normal form halts with the same
  outputs at the same times (MIG-1).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).
* `Turing.exists_codeTM_spaceUsed` — the same coded machine also uses the same space at
  every time; `Turing.CodeTM.one_le_spaceUsed` — every coded run visits a cell.

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.
* `Turing.pairEncode_eq`, `Turing.unaryFin_eq` — the two encodings as equations, the
  specification API (user, 2026-10-16).
* `Turing.signBits_neg`/`_zero`/`_pos`, `Turing.optBoolBits_none`/`_some_false`/`_some_true`,
  `Turing.optOptBoolBits_none`/`_some_none`/`_some_false`/`_some_true`,
  `Turing.optStateBits_none`/`_some` — the record fields' encoders, case by case (the ND inventory
  API, round 2; gate 37, finding 1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- **The pairing as an equation** (the specification API, user 2026-10-16): the code doubled,
the separator `false, true`, then the second word. -/
theorem pairEncode_eq (x α : List Bool) :
    pairEncode x α = (x.flatMap fun b => [b, b]) ++ [false, true] ++ α :=
  rfl

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-! ### Shape of the pairing

Generic list facts about `pairEncode` and `pairDecode`, shared by the machine-side
developments (the time hierarchy, the polynomial hierarchy, logspace machines, and
the circuit-evaluation machines). -/

/-- A word with every bit written twice — the first component of `Turing.pairEncode`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [b, b]

/-- Doubling the empty word gives the empty word. -/
@[simp] lemma dbl_nil : dbl [] = [] := rfl

/-- Doubling `b :: w` is `b b` followed by doubling `w`. -/
@[simp] lemma dbl_cons (b : Bool) (w : List Bool) : dbl (b :: w) = b :: b :: dbl w := rfl

/-- Doubling a word doubles its length. -/
@[simp] lemma length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; ring

/-- Both copies of bit `c` of a doubled word read `w[c]`. -/
lemma getElem?_dbl (w : List Bool) (c : ℕ) (hc : c < w.length) (p : Bool) :
    (dbl w)[2 * c + p.toNat]? = some w[c] := by
  induction w generalizing c with
  | nil => simp at hc
  | cons b w ih =>
    cases c with
    | zero => cases p <;> simp
    | succ c =>
      have := ih c (by simpa using hc)
      simp only [dbl_cons, List.getElem_cons_succ]
      rw [show 2 * (c + 1) + p.toNat = (2 * c + p.toNat) + 1 + 1 by ring]
      simpa using this

/-- `pairEncode x y` is the doubled first word, the separator `[false, true]`, and the
second word. -/
lemma pairEncode_eq_dbl (x y : List Bool) : pairEncode x y = dbl x ++ [false, true] ++ y :=
  rfl

/-- The length of a pair: `|pairEncode x y| = 2|x| + 2 + |y|`. -/
theorem length_pairEncode (x y : List Bool) :
    (pairEncode x y).length = 2 * x.length + 2 + y.length := by
  simp [pairEncode_eq_dbl]
  omega

/-- A string that is not a pair is a doubled word followed by a malformed tail: the end
of the string, a lone bit, or the aligned pair `10`.

**Proof sketch.** Functional induction along `pairDecode`: aligned `00`/`11` pairs extend
the doubled prefix; in the remaining case the string matches none of `00`, `11`, `01`,
so it is empty, a single bit, or starts with `10`. -/
theorem pairDecode_eq_none (z : List Bool) (h : pairDecode z = none) :
    ∃ w tail, z = dbl w ++ tail ∧
      (tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) := by
  induction z using pairDecode.induct with
  | case1 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨false :: w, tail, by simp [hw], ht⟩
  | case2 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨true :: w, tail, by simp [hw], ht⟩
  | case3 xs => simp [pairDecode] at h
  | case4 xs h₁ h₂ h₃ =>
    refine ⟨[], xs, by simp, ?_⟩
    rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · cases b <;> cases c
      · exact absurd rfl (h₁ r)
      · exact absurd rfl (h₃ r)
      · exact Or.inr (Or.inr ⟨r, rfl⟩)
      · exact absurd rfl (h₂ r)

/-- A successfully decoded string is the pairing of its components.

**Proof sketch.** Functional induction along `pairDecode`, inverting
`pairDecode_pairEncode` one aligned pair at a time. -/
theorem eq_pairEncode_of_pairDecode (z a b : List Bool) (h : pairDecode z = some (a, b)) :
    z = pairEncode a b := by
  induction z using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode] at h

/-- A unary-first pair `⟨1ⁿ, u⟩` determines both `n` and `u`. -/
lemma pairEncode_replicate_inj {n n' : ℕ} {u u' : List Bool}
    (h : pairEncode (List.replicate n true) u = pairEncode (List.replicate n' true) u') :
    n = n' ∧ u = u' := by
  have := pairEncode_injective (a₁ := (List.replicate n true, u))
    (a₂ := (List.replicate n' true, u')) h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨by simpa using congrArg List.length h1, h2⟩

/-- The binary expansion of `m` has at most `m` bits. -/
lemma length_bits_le_self (m : ℕ) : m.bits.length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- **The `Nat.bits` shift law**: multiplying a positive `m` by `2 ^ j`
prepends `j` low zero bits to its little-endian binary expansion,
`(2^j·m).bits = 0^j ++ m.bits`. (Positivity is needed: `Nat.bits 0 = []`.)
The public home of the law, promoted per the fills-6 request F6-1(a)
(CH34-D4).

**Proof sketch.** Induct on `j`. A positive number stays positive after
multiplication by a power of two, and doubling a nonzero number prepends one
low zero bit to its expansion; induction counts the prepended zeros. -/
theorem bits_two_pow_mul (j m : ℕ) (hm : 0 < m) :
    (2 ^ j * m).bits = List.replicate j false ++ m.bits := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, Nat.bit0_bits _ (Nat.mul_pos (Nat.two_pow_pos j) hm).ne']
    simp only [ih, List.replicate_succ, List.cons_append]

/-- The little-endian binary expansion of `2 ^ n` is `n` zero bits followed by
one high bit: `(2^n).bits = 0^n 1`. The case `m = 1` of
`Turing.bits_two_pow_mul`, since the expansion of `1` is the single bit `1`. -/
theorem bits_two_pow_eq_replicate (n : ℕ) :
    (2 ^ n).bits = List.replicate n false ++ [true] := by
  simpa using bits_two_pow_mul n 1 Nat.one_pos

/-- **The diagonal pairing machine**. A six-state machine with no work tapes that, on input `α`,
writes each symbol of `α` twice, then the separator `false, true`, rewinds the input, and copies `α`
once more, so that it outputs `pairEncode α α`. It is also the witness of
`Turing.FinTM.computesFunInTime_pairDup` (consolidation: Primitives' private `pairDupTM`, which
computes the same function, retires). [AB09, proof of Theorem 1.11: the self-application input of
the `HALT` reduction] -/
def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- **The diagonal pairing machine's time**. On input `α` the diagonal pairing machine halts within
`4|α| + 5` steps with output `pairEncode α α`.

**Proof sketch.** The `have h` of today's `computesFunInTime_pairEncode_diag`, from the private
`pairDiag_run`: the doubling pass takes `2|α|` steps, the two separator steps and the first left
move `3`, the rewind `|α| + 1`, the copy `|α|`, and the halting transition `1`. -/
theorem pairDiagTM_computes (x : List Bool) :
    pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
  sorry

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- **A left move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .neg = [true, true]`. -/
theorem signBits_neg : signBits .neg = [true, true] := rfl

/-- **A stay's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .zero = [false, false]`. -/
theorem signBits_zero : signBits .zero = [false, false] := rfl

/-- **A right move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .pos = [true, false]`. -/
theorem signBits_pos : signBits .pos = [true, false] := rfl

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- **No bit's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits none = [false, false]`. -/
theorem optBoolBits_none : optBoolBits none = [false, false] := rfl

/-- **The bit `false`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some false) = [true, false]`. -/
theorem optBoolBits_some_false : optBoolBits (some false) = [true, false] := rfl

/-- **The bit `true`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some true) = [true, true]`. -/
theorem optBoolBits_some_true : optBoolBits (some true) = [true, true] := rfl

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- **No write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits none = [false, false]`. -/
theorem optOptBoolBits_none : optOptBoolBits none = [false, false] := rfl

/-- **A blank write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some none) = [false, true]`. -/
theorem optOptBoolBits_some_none : optOptBoolBits (some none) = [false, true] := rfl

/-- **Writing `false`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some false)) = [true, false]`. -/
theorem optOptBoolBits_some_false : optOptBoolBits (some (some false)) = [true, false] := rfl

/-- **Writing `true`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some true)) = [true, true]`. -/
theorem optOptBoolBits_some_true : optOptBoolBits (some (some true)) = [true, true] := rfl

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- **The unary state word as an equation** (the specification API, user 2026-10-16): `s`
`true`s, then the delimiter `false`. -/
theorem unaryFin_eq {n : ℕ} (s : Fin n) : unaryFin s = List.replicate (s : ℕ) true ++ [false] :=
  rfl

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- **Halting's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits none = [false]`. -/
theorem optStateBits_none {n : ℕ} : optStateBits (none : Option (Fin n)) = [false] := rfl

/-- **A successor state's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits (some s) = true :: unaryFin s`. -/
theorem optStateBits_some {n : ℕ} (s : Fin n) : optStateBits (some s) = true :: unaryFin s := rfl

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- **A coded run visits at least one cell.** Every run of a coded machine, at every time,
has visited at least one work cell: its one work head starts somewhere. So every qualifying
budget `s` of `Complexity.space_universal` is positive, which is what lets its addend-free bound
`C · s` absorb a ruler of the header's length (the RD-3 statement gate's row-1 calculation).

**Proof sketch.** The visited set of tape `0` contains the head's initial position, and it
is one summand of the space. -/
theorem CodeTM.one_le_spaceUsed (M : CodeTM) (x : List Bool) (t : ℕ) :
    1 ≤ M.toFinTM.tm.spaceUsed (M.toFinTM.tm.initCfg x) t := by
  let i₀ : Fin M.toFinTM.k := ⟨0, by simp⟩
  have hne : (M.toFinTM.tm.visitedByTapeHead (M.toFinTM.tm.initCfg x) t i₀).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), rfl⟩⟩
  exact (Finset.card_pos.mpr hne).trans_le
    (M.toFinTM.tm.spaceUsedByTape_le_spaceUsed _ t i₀)

section G5Sealed

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.MultiTapeTM.relabelState
  Turing.Cfg.mapState

/-- **Renaming a machine's states preserves its computations.** Renaming the states of a bundled
machine along an equivalence `e` gives a machine that halts on the same inputs at the same times,
with the same outputs.

**Proof sketch.** The renamed machine's initialized runs are the original runs with renamed
states (`Turing.MultiTapeTM.relabelState_runFrom_init`), and renaming changes neither halting nor
the output. -/
theorem FinTM.computesInTime_relabelState {Symbol : Type} (M : FinTM Symbol) {Q : Type}
    [Fintype Q] [DecidableEq Q] (e : M.State ≃ Q) (x output : List Symbol) (t : ℕ) :
    (FinTM.mk (k := M.k) (State := Q) (M.tm.relabelState e)).ComputesInTime x output t ↔
      M.ComputesInTime x output t := by
  rw [FinTM.computesInTime_iff, FinTM.computesInTime_iff]
  dsimp only
  rw [MultiTapeTM.relabelState_runFrom_init, Cfg.mapState_state, Cfg.mapState_output,
    Option.map_eq_none_iff]

/-- **A machine's states as an initial segment of `ℕ`.** The states of a bundled machine are in
bijection with `Fin (n + 1)` for `n = |State| - 1`: the state type is finite, and inhabited by the
start state. Noncomputable, through `Fintype.equivFinOfCardEq`. -/
noncomputable def FinTM.stateEquivFin {Symbol : Type} (M : FinTM Symbol) :
    M.State ≃ Fin (Fintype.card M.State - 1 + 1) :=
  Fintype.equivFinOfCardEq (by
    have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
    omega)

/-- `Turing.FinTM.stateEquivFin` is the bijection that `Fintype.equivFinOfCardEq` gives for the
state count, which the start state makes positive (its defining equation). -/
theorem FinTM.stateEquivFin_eq {Symbol : Type} (M : FinTM Symbol) :
    M.stateEquivFin = Fintype.equivFinOfCardEq (by
      have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
      omega) :=
  rfl

/-- **The space-faithful coding step.** Every one-work-tape binary machine `M` is equivalent
to a coded machine `M'` that halts with the same outputs at the same times
(`Turing.exists_codeTM`'s clause) **and uses the same space at every time**. This is the space
clause of the coding step named by `Complexity.space_hierarchy`'s sketch. [AB09, §1.4]

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited by `q₀`,
so `Fintype.equivFinOfCardEq` gives an equivalence with `Fin (|Q| - 1 + 1)`. Relabel the states
along it (`Turing.MultiTapeTM.relabelState`): by `Turing.MultiTapeTM.relabelState_runFrom_init`
the relabelled run is the original run with renamed states, so halting and outputs correspond
at every time, and the space clause is `Turing.MultiTapeTM.relabelState_spaceUsed`. The
tape-count cast uses `hk : M.k = 1`, eliminated after destructuring the bundle. -/
theorem exists_codeTM_spaceUsed (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM,
      (∀ (x output : List Bool) (t : ℕ),
        M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t) ∧
      ∀ (x : List Bool) (t : ℕ),
        M'.toFinTM.tm.spaceUsed (M'.toFinTM.tm.initCfg x) t =
          M.tm.spaceUsed (M.tm.initCfg x) t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  let M₀ : FinTM Bool := ⟨1, Q, tm⟩
  exact ⟨⟨Fintype.card Q - 1, tm.relabelState M₀.stateEquivFin⟩,
    M₀.computesInTime_relabelState M₀.stateEquivFin,
    fun x t => MultiTapeTM.relabelState_spaceUsed tm M₀.stateEquivFin x t⟩

/-- **The code normal form of a one-work-tape machine**. For a binary machine `M` with one work
tape, the coded machine with `|Q| - 1` as its state index bound, whose transition function is `M`'s
transported along the canonical bijection `Q ≃ Fin |Q|` (`Turing.FinTM.stateEquivFin`; `Q` is
inhabited by the start state). [AB09, §1.4] Noncomputable, through `Fintype.equivFinOfCardEq`. -/
noncomputable def FinTM.toCodeTM : (M : FinTM Bool) → M.k = 1 → CodeTM
  | @FinTM.mk _ _ Q _hQ _dQ tm, rfl =>
    ⟨Fintype.card Q - 1, tm.relabelState (FinTM.stateEquivFin ⟨1, Q, tm⟩)⟩

/-- **The code normal form is equivalent**. For a one-work-tape binary machine `M`, its code normal
form halts on `x` with output `w` within `t` steps if and only if `M` does. [AB09, §1.4]

**Proof sketch.** The relabelled machine's run is the image of `M`'s run under the state
bijection (`Turing.MultiTapeTM.relabelState_runFrom_init`); halting and output are preserved. -/
theorem FinTM.toCodeTM_computesInTime_iff (M : FinTM Bool) (hk : M.k = 1)
    (x output : List Bool) (t : ℕ) :
    (M.toCodeTM hk).toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  exact FinTM.computesInTime_relabelState ⟨1, Q, tm⟩ _ x output t

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation is the time clause of `Turing.exists_codeTM_spaceUsed`, whose witness
is this relabelling (`Turing.MultiTapeTM.relabelState`, from the shared state-renaming module
`TCSlib.Complexity.TuringMachine.StateRenaming`), so that the relabelling is built once. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  obtain ⟨M', h, -⟩ := exists_codeTM_spaceUsed M hk
  exact ⟨M', h⟩

end G5Sealed

end Turing

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/ENSealed.out =====

/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/g5ps/rule10c/ENSealed.lean:506:8: warning: declaration uses 'sorry'

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/SealControl_sealed.lean.txt =====

/-
Seal controls for G5's statement PR's rule-10 checks: a delta goal (`#ctl_rfl`) and an equation
goal (`#ctl_eqn`) for each of the 15 definitions sealed in the three sealed copies (the
union). Expected: unsealed, every control passes except recursive definitions' delta goals;
sealed, every control fails. A probe record, not library code.
-/
import TCSlib.Complexity.TuringMachine.UniversalTlogT

open Lean Elab Command Meta in
elab "#ctl_rfl " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} rfl {n}"

open Lean Elab Command Meta in
elab "#ctl_eqn " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ok ← liftTermElabM do
    try
      let some eqs ← getEqnsFor? n | return false
      let ty := (← getConstInfo eqs[0]!).type
      let ty ← instantiateForall ty #[]
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType (← `(by intros; rfl)) ty
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} eqn {n}"

open Lean Elab Command Meta in
elab "#ctl_simp " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let c := mkConst n (ci.levelParams.map Level.param)
        let goal ← forallTelescopeReducing ci.type fun xs _ => do
          mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)
        let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} simp {n}"



section Controls

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.Cfg.init
  Turing.Cfg.mapState
  Turing.Code2TM.toFinTM
  Turing.EffectiveCodeK.ofSerialize
  Turing.EffectiveCodeK.toFinTM
  Turing.EffectiveMachineCode2.toK
  Turing.FinTM.ComputesFunInTime
  Turing.FinTM.ComputesInTime
  Turing.FinTM.stateEquivFin
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.initCfg
  Turing.MultiTapeTM.relabelState
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.pairEncode

#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.Code2TM.toFinTM
#ctl_rfl Turing.EffectiveCodeK.ofSerialize
#ctl_rfl Turing.EffectiveCodeK.toFinTM
#ctl_rfl Turing.EffectiveMachineCode2.toK
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.stateEquivFin
#ctl_rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.MultiTapeTM.relabelState
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.pairEncode
#ctl_eqn Turing.Cfg.init
#ctl_eqn Turing.Cfg.mapState
#ctl_eqn Turing.Code2TM.toFinTM
#ctl_eqn Turing.EffectiveCodeK.ofSerialize
#ctl_eqn Turing.EffectiveCodeK.toFinTM
#ctl_eqn Turing.EffectiveMachineCode2.toK
#ctl_eqn Turing.FinTM.ComputesFunInTime
#ctl_eqn Turing.FinTM.ComputesInTime
#ctl_eqn Turing.FinTM.stateEquivFin
#ctl_eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_eqn Turing.MultiTapeTM.initCfg
#ctl_eqn Turing.MultiTapeTM.relabelState
#ctl_eqn Turing.MultiTapeTM.runFrom
#ctl_eqn Turing.MultiTapeTM.step
#ctl_eqn Turing.pairEncode

end Controls

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/SealControl_sealed.out =====

CONTROL_FAIL rfl Turing.Cfg.init
CONTROL_FAIL rfl Turing.Cfg.mapState
CONTROL_FAIL rfl Turing.Code2TM.toFinTM
CONTROL_FAIL rfl Turing.EffectiveCodeK.ofSerialize
CONTROL_FAIL rfl Turing.EffectiveCodeK.toFinTM
CONTROL_FAIL rfl Turing.EffectiveMachineCode2.toK
CONTROL_FAIL rfl Turing.FinTM.ComputesFunInTime
CONTROL_FAIL rfl Turing.FinTM.ComputesInTime
CONTROL_FAIL rfl Turing.FinTM.stateEquivFin
CONTROL_FAIL rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_FAIL rfl Turing.MultiTapeTM.initCfg
CONTROL_FAIL rfl Turing.MultiTapeTM.relabelState
CONTROL_FAIL rfl Turing.MultiTapeTM.runFrom
CONTROL_FAIL rfl Turing.MultiTapeTM.step
CONTROL_FAIL rfl Turing.pairEncode
CONTROL_FAIL eqn Turing.Cfg.init
CONTROL_FAIL eqn Turing.Cfg.mapState
CONTROL_FAIL eqn Turing.Code2TM.toFinTM
CONTROL_FAIL eqn Turing.EffectiveCodeK.ofSerialize
CONTROL_FAIL eqn Turing.EffectiveCodeK.toFinTM
CONTROL_FAIL eqn Turing.EffectiveMachineCode2.toK
CONTROL_FAIL eqn Turing.FinTM.ComputesFunInTime
CONTROL_FAIL eqn Turing.FinTM.ComputesInTime
CONTROL_FAIL eqn Turing.FinTM.stateEquivFin
CONTROL_FAIL eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_FAIL eqn Turing.MultiTapeTM.initCfg
CONTROL_FAIL eqn Turing.MultiTapeTM.relabelState
CONTROL_FAIL eqn Turing.MultiTapeTM.runFrom
CONTROL_FAIL eqn Turing.MultiTapeTM.step
CONTROL_FAIL eqn Turing.pairEncode

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/SealControl_unsealed.lean.txt =====

/-
Seal controls for G5's statement PR's rule-10 checks: a delta goal (`#ctl_rfl`) and an equation
goal (`#ctl_eqn`) for each of the 15 definitions sealed in the three sealed copies (the
union). Expected: unsealed, every control passes except recursive definitions' delta goals;
sealed, every control fails. A probe record, not library code.
-/
import TCSlib.Complexity.TuringMachine.UniversalTlogT

open Lean Elab Command Meta in
elab "#ctl_rfl " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} rfl {n}"

open Lean Elab Command Meta in
elab "#ctl_eqn " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ok ← liftTermElabM do
    try
      let some eqs ← getEqnsFor? n | return false
      let ty := (← getConstInfo eqs[0]!).type
      let ty ← instantiateForall ty #[]
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType (← `(by intros; rfl)) ty
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} eqn {n}"

open Lean Elab Command Meta in
elab "#ctl_simp " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let c := mkConst n (ci.levelParams.map Level.param)
        let goal ← forallTelescopeReducing ci.type fun xs _ => do
          mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)
        let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} simp {n}"



section Controls


#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.Code2TM.toFinTM
#ctl_rfl Turing.EffectiveCodeK.ofSerialize
#ctl_rfl Turing.EffectiveCodeK.toFinTM
#ctl_rfl Turing.EffectiveMachineCode2.toK
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.stateEquivFin
#ctl_rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.MultiTapeTM.relabelState
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.pairEncode
#ctl_eqn Turing.Cfg.init
#ctl_eqn Turing.Cfg.mapState
#ctl_eqn Turing.Code2TM.toFinTM
#ctl_eqn Turing.EffectiveCodeK.ofSerialize
#ctl_eqn Turing.EffectiveCodeK.toFinTM
#ctl_eqn Turing.EffectiveMachineCode2.toK
#ctl_eqn Turing.FinTM.ComputesFunInTime
#ctl_eqn Turing.FinTM.ComputesInTime
#ctl_eqn Turing.FinTM.stateEquivFin
#ctl_eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_eqn Turing.MultiTapeTM.initCfg
#ctl_eqn Turing.MultiTapeTM.relabelState
#ctl_eqn Turing.MultiTapeTM.runFrom
#ctl_eqn Turing.MultiTapeTM.step
#ctl_eqn Turing.pairEncode

end Controls

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/SealControl_unsealed.out =====

CONTROL_PASS rfl Turing.Cfg.init
CONTROL_PASS rfl Turing.Cfg.mapState
CONTROL_PASS rfl Turing.Code2TM.toFinTM
CONTROL_PASS rfl Turing.EffectiveCodeK.ofSerialize
CONTROL_PASS rfl Turing.EffectiveCodeK.toFinTM
CONTROL_PASS rfl Turing.EffectiveMachineCode2.toK
CONTROL_PASS rfl Turing.FinTM.ComputesFunInTime
CONTROL_PASS rfl Turing.FinTM.ComputesInTime
CONTROL_PASS rfl Turing.FinTM.stateEquivFin
CONTROL_PASS rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_PASS rfl Turing.MultiTapeTM.initCfg
CONTROL_PASS rfl Turing.MultiTapeTM.relabelState
CONTROL_PASS rfl Turing.MultiTapeTM.runFrom
CONTROL_PASS rfl Turing.MultiTapeTM.step
CONTROL_PASS rfl Turing.pairEncode
CONTROL_PASS eqn Turing.Cfg.init
CONTROL_PASS eqn Turing.Cfg.mapState
CONTROL_PASS eqn Turing.Code2TM.toFinTM
CONTROL_PASS eqn Turing.EffectiveCodeK.ofSerialize
CONTROL_PASS eqn Turing.EffectiveCodeK.toFinTM
CONTROL_PASS eqn Turing.EffectiveMachineCode2.toK
CONTROL_PASS eqn Turing.FinTM.ComputesFunInTime
CONTROL_PASS eqn Turing.FinTM.ComputesInTime
CONTROL_PASS eqn Turing.FinTM.stateEquivFin
CONTROL_PASS eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_PASS eqn Turing.MultiTapeTM.initCfg
CONTROL_PASS eqn Turing.MultiTapeTM.relabelState
CONTROL_PASS eqn Turing.MultiTapeTM.runFrom
CONTROL_PASS eqn Turing.MultiTapeTM.step
CONTROL_PASS eqn Turing.pairEncode

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/TTSealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the `log₂ t + 1` zones a
run of `t` steps reaches gives `O(t log t)` steps in all. The converse holds because `M'` writes
an output symbol exactly when `M` does, in the same order, and halts only when `M` halts. With
no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  sorry

section G5Sealed

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.FinTM.ComputesFunInTime

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end G5Sealed

end Turing.FinTM

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/TTSealed.out =====

/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/g5ps/rule10c/TTSealed.lean:64:8: warning: declaration uses 'sorry'

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/UTSealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.TwoTapes
import TCSlib.Complexity.TuringMachine.UniversalK

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient universal machine

[AB09, Theorem 1.9]: one machine `U` simulates every machine `M`, given a code `α` of `M`, with
overhead `C · T log T` for a run of `T` steps, where `C` depends on `M` but not on the input.

## Deviations from [AB09]

* The code quantifier is relaxed as in `Turing.universal_quadratic`: every machine has some code
  `α` with which `U` simulates it. [AB09] states the simulation for every code of every machine;
  here the code is one of the two-work-tape normal form's, through the two-tape reduction.
* The statement is per run and includes the converse: every completed output of `U` on
  `⟨α, x⟩` is an output of `M` on `x`.
* The overhead is `C · (t + 1)(log₂(t + 1) + 1)`, padded so that it covers `t = 0`.

## Main definitions

No new definitions: the universal machine is an existential contract.

## Main results

* `Turing.universal_TlogT` — [AB09, Theorem 1.9].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 1.9 and its proof, §1.7.)
-/

namespace Turing

section G5Sealed

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg
attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.EffectiveMachineCode2.toK
  Turing.EffectiveCodeK.toFinTM
  Turing.EffectiveCodeK.ofSerialize
  Turing.Code2TM.toFinTM
  Turing.pairEncode

/-- **The efficient universal machine** [AB09, Theorem 1.9]: there is one binary machine `U`
such that every binary machine `M` has a code `α` and a constant `C` with which `U` reproduces
each halting run of `M` of `t` steps on input `x`, on the paired input `⟨α, x⟩`, within
`C · (t + 1)(log₂(t + 1) + 1)` steps; and every completed output of `U` on `⟨α, x⟩` is an
output of `M` on `x`.

**Proof sketch.** Take `U` to be the code-first evaluator `Turing.universalK` at two work tapes,
over the two-tape scheme `c`. Given `M`, reduce it to two work tapes
(`Turing.FinTM.two_work_tapes_run`, overhead `c₁ · (t + 1)(log₂(t + 1) + 1)`) and code the result
(`Turing.exists_code2TM`); `α` is that code. `U` simulates the coded machine within linear
overhead `C (t' + 1)`, so a run of `M` of `t` steps costs at most
`C (c₁ (t + 1)(log₂(t + 1) + 1) + 1) ≤ C (c₁ + 1)(t + 1)(log₂(t + 1) + 1)` steps of `U`. The
converse composes the converses of the two steps. -/
theorem universal_TlogT (c : EffectiveMachineCode2) :
    ∃ U : FinTM Bool, ∀ M : FinTM Bool, ∃ (α : List Bool) (C : ℕ),
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨U, hU⟩ := universalK 2 c.toK
  refine ⟨U, fun M => ?_⟩
  obtain ⟨M', c₁, hk, hfwd, hback⟩ := FinTM.two_work_tapes_run M
  obtain ⟨N, hN⟩ := exists_code2TM M' hk
  have hdec : c.toK.toFinTM (c.encode N) = N.toFinTM := by
    rw [EffectiveMachineCode2.toK_toFinTM, c.toMachineCode2.decode_encode N]
  obtain ⟨C, hC⟩ := hU (c.encode N)
  refine ⟨c.encode N, C * (c₁ + 1), fun x output t h => ?_, fun x output h => ?_⟩
  · have h₁ := (hN x output _).2 (hfwd x output t h)
    rw [← hdec] at h₁
    apply ((hC x).1 output _ h₁).mono
    have hpos : 1 ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc C * (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)) + 1)
        ≤ C * ((c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1))) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = C * (c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by ring
  · obtain ⟨t, ht⟩ := (hC x).2 output h
    rw [hdec] at ht
    exact hback x output ⟨t, (hN x output t).1 ht⟩

end G5Sealed

end Turing

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/UTSealed.out =====



## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/mkseal_g5.py =====

```
"""Sealed copies and seal controls for G5's statement PR (rule 10).
Usage: python3 -I mkseal_g5.py <worktree> <outdir>
Each new proof runs under a seal of the other-file TCSlib definitions it could reach:
alphabet_reduction_run (AlphabetReduction), the relabelling section from
FinTM.computesInTime_relabelState to the end of Encoding (the generic lemma, stateEquivFin and the
re-pointed coding steps), exists_code2TM (Codes2Tape), two_work_tapes_binary (TwoTapes; gate 92 finding 1),
universal_TlogT (UniversalTlogT). Controls: a delta and an equation control per sealed definition, unsealed and
sealed (the generic control commands of the earlier gates)."""
import sys, pathlib
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
T = 'TCSlib/Complexity/TuringMachine/'
ERASE = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg'
def seal(names):
    return ERASE + '\nattribute [local irreducible]\n' + '\n'.join('  ' + n for n in names) + '\n'
RUN = ['Turing.FinTM.ComputesInTime', 'Turing.MultiTapeTM.ComputesInTimeAndSpace',
       'Turing.MultiTapeTM.runFrom', 'Turing.MultiTapeTM.step', 'Turing.MultiTapeTM.initCfg',
       'Turing.Cfg.init']
AR = RUN
EN = RUN + ['Turing.MultiTapeTM.relabelState', 'Turing.Cfg.mapState']
C2 = EN + ['Turing.FinTM.stateEquivFin']
TT = RUN + ['Turing.FinTM.ComputesFunInTime']
UT = RUN + ['Turing.EffectiveMachineCode2.toK', 'Turing.EffectiveCodeK.toFinTM',
            'Turing.EffectiveCodeK.ofSerialize', 'Turing.Code2TM.toFinTM', 'Turing.pairEncode']
def wrap(path, start, stop, names, outname):
    t = (wt / path).read_text()
    assert t.count(start) == 1 and t.count(stop) == 1, (path, t.count(start), t.count(stop))
    i = t.index(start); j = t.index(stop, i)
    t = t[:i] + 'section G5Sealed\n\n' + seal(names) + '\n' + t[i:j] + '\nend G5Sealed\n' + t[j:]
    (out / outname).write_text(t)
wrap(T + 'Robustness/AlphabetReduction.lean', '/-- **Alphabet reduction, run by run**',
     '\nend\n\nend Turing.FinTM\n\n/-! ### Space annotation', AR, 'ARSealed.lean')
wrap(T + 'Encoding.lean', '/-- **Renaming a machine\'s states preserves its computations.**',
     '\nend Turing\n', EN, 'ENSealed.lean')
wrap(T + 'Codes2Tape.lean', '/-- Every two-work-tape binary machine is equivalent',
     '\nend Turing\n', C2, 'C2Sealed.lean')
wrap(T + 'Robustness/TwoTapes.lean', '/-- **Two work tapes suffice** for computing a function',
     '\nend Turing.FinTM\n', TT, 'TTSealed.lean')
wrap(T + 'UniversalTlogT.lean', '/-- **The efficient universal machine**', '\nend Turing\n', UT,
     'UTSealed.lean')
union = sorted(set(AR + EN + C2 + TT + UT))
hdr = (pathlib.Path(__file__).parent / 'ctl_header.lean.part.txt').read_text()
doc = f"""/-
Seal controls for G5's statement PR's rule-10 checks: a delta goal (`#ctl_rfl`) and an equation
goal (`#ctl_eqn`) for each of the {len(union)} definitions sealed in the three sealed copies (the
union). Expected: unsealed, every control passes except recursive definitions' delta goals;
sealed, every control fails. A probe record, not library code.
-/
import TCSlib.Complexity.TuringMachine.UniversalTlogT
"""
ctl = ''.join(f'#ctl_rfl {n}\n' for n in union) + ''.join(f'#ctl_eqn {n}\n' for n in union)
for name, s in (('unsealed', ''), ('sealed', seal(union))):
    (out / f'SealControl_{name}.lean').write_text(doc + hdr + '\n\nsection Controls\n\n' + s + '\n' + ctl + '\nend Controls\n')
(out / 'union.txt').write_text('\n'.join(union) + '\n')
print(len(union), 'sealed definitions')
```

## ===== campaign/gates/92-g5-statements/evidence/round2/rule10/union.txt =====

Turing.Cfg.init
Turing.Cfg.mapState
Turing.Code2TM.toFinTM
Turing.EffectiveCodeK.ofSerialize
Turing.EffectiveCodeK.toFinTM
Turing.EffectiveMachineCode2.toK
Turing.FinTM.ComputesFunInTime
Turing.FinTM.ComputesInTime
Turing.FinTM.stateEquivFin
Turing.MultiTapeTM.ComputesInTimeAndSpace
Turing.MultiTapeTM.initCfg
Turing.MultiTapeTM.relabelState
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.step
Turing.pairEncode

## ===== TCSlib/Complexity/TuringMachine.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.OracleFinite
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.TuringMachine.OracleAgreement
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.UnaryTape
import TCSlib.Complexity.TuringMachine.CounterProg
import TCSlib.Complexity.TuringMachine.CounterProgRun
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.WordTests
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Zone
import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.OracleCall
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.CertShell
import TCSlib.Complexity.TuringMachine.Build.OracleSim
import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.NDCombinators
import TCSlib.Complexity.TuringMachine.Build.NDClockHost
import TCSlib.Complexity.TuringMachine.Build.NDClockHostRun
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.StepBlockLoop
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.ChoiceWords
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.TwoTapes
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.UniversalK
import TCSlib.Complexity.TuringMachine.UniversalTlogT
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.UniversalInterpreter
import TCSlib.Complexity.TuringMachine.UniversalBlock
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.NDCodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `CodeFormat` — shared transition-record and table-format parsers, with the one-tape instance.
* `Codes2Tape` — the deterministic two-work-tape code scheme (§13, Z3), an instance of
  `CodeFormat`, with its uniform scheme from `CodeSimulator`.

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Nondeterministic` — binary-choice nondeterministic machines [AB09, §2.1.2]:
  choice-word run semantics, all-branch halting, the bundled `FinNDTM` layer, the
  deterministic embedding, and the run-level transfer, slice, relabelling and input-locality
  lemmas (the classes live in `ClassNP/NTIME`).
* `NondeterministicSpace` — the space measure of binary-choice NDTMs along choice-word
  runs: visited cells, as for the deterministic `SPACE` [AB09, Definition 4.1].
* `ChoiceReplay` — choice-tape determinization: the replay machine of an NDTM, which reads its
  choices from an extra work tape, and the replay lemma [AB09, §2.1.2, Theorem 2.6]. Proved.
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `OracleFinite` — the bundled finite layer `FinOracleTM`, carrying well-formedness as a
  field, over which the oracle classes are stated [AB09, Definition 3.5].
* `OracleNondeterministic` — nondeterministic oracle machines [AB09, Definition 3.4], for
  `NPOracle` and the relativization theorem.
* `OracleAgreement` — oracle locality: runs under oracles agreeing on every submitted
  string coincide [AB09, Theorem 3.7].
* `NDCodes` — codes for nondeterministic machines [AB09, §1.4, §3.2]: the two-work-tape
  coded normal form, its fixed serialization, and the scheme laws with the effective
  (canonizer) form.
* `NDCodeSimulator` — the interpreter core for nondeterministic codes (C1): the serialization
  bridge, the per-code replay canonizer and the core `R` [AB09, Exercise 2.6]. The core is
  proved; the canonizer is sorried.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `BufferWords` — the cells of a buffer tape holding a composite word: a suffix at an offset, a
  middle word's letters, prefixes and suffixes, the blank cells off the word, and a unary word
  with its terminator. Proved.
* `Sweep` — the generic zipper/transduction layer for sweep-based tape
  simulations, with the initialized-run head/support bound.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `UnaryTape` — work tapes holding a number in unary.
* `CounterProg`, `CounterProgRun` — counter programs (goto programs over unary registers)
  compiled into machines, with Hoare-style run lemmas; the model of the polynomial-time
  emitters of [AB09, Remark 6.7] (polynomial time: `ClassNP/CounterProgPolyTime`).
* `Build/Embed`, `Build/Seam`, `Build/Catalog` — the §12 routine layer
  (`machine-library-design.md` §12, gate closed round 3): the bank-embedding
  transformers with their returning flavors, seam composition with the
  general-configuration forms and the release adapter, and the space-annotated
  catalog rows.
* `Build/NDHost` — the nondeterministic phase host over NDTM phases and the choice writer, for
  the guess-first route of the nondeterministic time hierarchy (C1). Proved, the writer's
  bounded contract included (C1-W, 2026-10-17).
* `Build/VirtualInput` — virtual-input hosting (`machine-library-design.md` §13, Z1): a
  machine whose input is a buffered work-tape word runs inside a host, one step per step.
* `Build/Zone` — the pure zone layer (§13, Z2, as revised by §13d): zone contents, the
  guarded pairwise ops, the cascade and its mirror, the scanned index, the total rebalance,
  the extension by one level, and the virtual tape a track represents.
* `Build/ZoneTape` — the multi-track zoned carrier over `ZoneSym k` (§13d, G3): the layout
  with blank separators, the inner-packed encoding `zonedTape` and its invariants.
* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts.
  Proved.
* `Build/OracleCall` — the oracle-machine rows (`machine-library-design.md` §12.9):
  W1 capture onto the query tape, landing in `qQuery`, and the two-step answer tail.
* `SymbolLift` — the embedding transport (`machine-library-design.md` §12.8, R8.0): a
  `Bool` machine run on a richer alphabet along `e : Bool ↪ Γ`, with time and space
  unchanged.
* `Build/CounterLoop` — the counter-driven loop (§12.7) and the pattern expansion
  `expandTM` (§12.8, R8.6).
* `Build/InputWindow` — the counter-driven copy of a bounded window of the native input onto a
  work tape, for the nondeterministic time hierarchy [AB09, Theorem 3.2]. Proved.
* `Build/SeamLayout` — the step block's table and summary tapes from a captured serialization,
  the one redistribution the step-block startups cite. Proved.
* `Build/Rewind` — the rewind of a work-tape head to the start of a word, from any cell of the
  word or just past it, the empty word included. Proved.
* `Build/InputRewind` — the rewind of the native input head to the first input cell: its exact
  time, its first arrival at the park, and its unchanged work tapes, heads and output; and the
  composition of two state relabelings of a configuration. Proved.
* `Build/InterpreterStartup` — the pieces of a universal machine's startup on a timed paired
  input: the header projections and their capture, the suffix window, the released install call,
  the table-and-summary layout, the seam step, a fresh capture's start. Proved.
* `Build/Scan`, `Build/InputCall`, `Build/CfgRecord` — the §12.8 rows, with the field
  layout, compare, seeks and two-pass scan in `Build/Catalog`'s Part 3: the constant and
  advancing writers and the native-input copy and fold; the input call and input seek;
  the rich configuration-record carrier and the record rows. All proved (§12.8 fill gate
  closed).
* `Build/InputLength`, `Build/RecordTable` — the deferred §12.8 rows (`machine-library-design.md`
  §12.8b): the input length `Nat.bits |x|` (R8.5c), and the table layer over records (header,
  sentinels, find, append, template, init, validity, odometer next, the end-to-start adapter).
  Fills in progress; each module's header carries its status.
* `Build/OracleSim`, `Build/CertShell` — oracle-call simulation (§12.10, the B1b extension): one
  plain host simulating an oracle machine with queries answered by a plain decider, the
  choice-word machine of an oracle NDTM, and the plain certificate shell. Fills in progress;
  each module's header carries its status.
* `Build/StepBlock` — the step block (host H2, `machine-library-design.md` §14): one finite
  machine per work-tape count `k` that performs one simulated transition of a `k`-tape
  binary table held as data, with its contract `Turing.StepBlock.roundTM_effect`, the
  record skipper and fixed-field reader, the per-round space ledger and the cofinal
  iteration. Proved; promoted from `CodeSimulator` (H2-S gate closed, round 2).
* `Build/StepBlockLoop` — the step block's counter loop (host H2's loop form, H2-L,
  `machine-library-design.md` §14): the binary deadline clock over the step block, native and on
  a buffered input, from any represented live start, with its early-escape bound and live
  exits. Proved; harvested from `CodeSimulator` (H1 harvest gate passed, 2026-10-14).
* `Build/StepBlockForward` — the step block's forwarding round loop (host H2's unclocked loop form,
  H2-F, `machine-library-design.md` §14): any `k`-tape table simulated in macro-step lockstep with
  its emissions forwarded, per-step cost bounded by the table's length, and a space ledger.
  Statement gate passed 2026-10-15; the contract is sorried.
* `CodeSimulator` — the format-parameterized uniform simulator over item 8's code formats
  (B5a): one bounded-acceptance interpreter and canonizer whose one- and two-tape instances are
  the EXPCOM and Codes2Tape code schemes. Fills in progress; the module header carries its
  status.
* `ChoiceWords` — certificate and choice words: split uniqueness for length-determined
  suffixes, the exact NP certificate length's monotonicity, the choice budget, and the
  truncation of halted branch runs. Shared by the plain Theorem 2.6, the oracle simulation's
  choice-word law and the certificate shell (wave-1 statement gate, round 1).
* `CounterProgInput` — transport a counter-program run past an input prefix
  that has already been consumed.
* `Build/Contract` — the framed-contract library (MIG-0a and MIG-0b, `machine-library-design.md`
  §16a), the facade of `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`: exact time, an endpoint
  function, an exit set with a no-earlier-exit cut and head envelopes, a derived frames layer,
  the compositions `trans`, `seq`, `inPhase`, `embed`, `branch` and the releases as thin
  wrappers over the public rows, and the segment, round and joint-trajectory layers with state
  renaming and the macro-step lockstep. The core, `Build/Contract/Basic`, imports only the
  machine core. Proved; the MIG-0a and MIG-0b gates closed.
* `Build/NDCombinators`, `Build/NDClockHost`, `Build/NDClockHostRun` — the nondeterministic
  construction rows: run locality, output maps and the coin dispatcher for binary-choice
  machines, and the clocked restart host `Turing.FinNDTM.clockHost` (clocked runner and
  restart loop of [AB09, §7.4.2, Exercise 7.6(a)]) with its startup and round contracts.
* `Build/StepClock`, `Build/WindowRun` — host H3 (`machine-library-design.md` §14): the
  step-clocked runner, shared with the nondeterministic time hierarchy; the semantic windowed
  run `windowRun`; the windowed round loop and the step-clocked windowed runner. Statement gate
  passed 2026-10-14; the specification is proved, the machine contracts are sorried.
* `Build/InputDevice` — host H5: the input-device interface, the native device, and the
  bounded-prefix ruler device with its boundary test, call rows and host. Proved.
* `Build/Convention`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives` — the
  machine-construction library (`machine-library-design.md`): the `Cfg.ofWords` seam
  discipline, the capture/silence and halt-redirect wrappers with the timed branch,
  the bounded-loop combinator, and the primitive catalog of timed string functions.
  Proved, and audited at the shared-infrastructure gates.
* `Build/WordTests` — two linear-time one-bit word tests, equality with a fixed word and the
  all-`true` word, in the form the timed conditional takes as its test. Proved.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/TwoTapes` — two work tapes suffice, with logarithmic overhead, run by run
  (Hennie–Stearns; the simulation is stated, and its proof is open).
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
* `UniversalK` — the `k`-generic universal machine (U2) [AB09, Theorem 1.9]: the `k`-tape
  scheme interface `EffectiveCodeK` with the one- and two-tape schemes as instances, the startup,
  the self-application universal machine with time and space ledgers, and the code-first
  evaluator, all proved.
* `UniversalTlogT` — the efficient universal machine [AB09, Theorem 1.9] at `T log T`, per run
  and with the converse, proved from `Robustness/TwoTapes`'s reduction and `UniversalK`.
* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Both are proved, as the `k = 1` cases of `UniversalK`'s statements.
-/
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the `log₂ t + 1` zones a
run of `t` steps reaches gives `O(t log t)` steps in all. The converse holds because `M'` writes
an output symbol exactly when `M` does, in the same order, and halts only when `M` halts. With
no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  sorry

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/UniversalTlogT.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.TwoTapes
import TCSlib.Complexity.TuringMachine.UniversalK

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient universal machine

[AB09, Theorem 1.9]: one machine `U` simulates every machine `M`, given a code `α` of `M`, with
overhead `C · T log T` for a run of `T` steps, where `C` depends on `M` but not on the input.

## Deviations from [AB09]

* The code quantifier is relaxed as in `Turing.universal_quadratic`: every machine has some code
  `α` with which `U` simulates it. [AB09] states the simulation for every code of every machine;
  here the code is one of the two-work-tape normal form's, through the two-tape reduction.
* The statement is per run and includes the converse: every completed output of `U` on
  `⟨α, x⟩` is an output of `M` on `x`.
* The overhead is `C · (t + 1)(log₂(t + 1) + 1)`, padded so that it covers `t = 0`.

## Main definitions

No new definitions: the universal machine is an existential contract.

## Main results

* `Turing.universal_TlogT` — [AB09, Theorem 1.9].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 1.9 and its proof, §1.7.)
-/

namespace Turing

/-- **The efficient universal machine** [AB09, Theorem 1.9]: there is one binary machine `U`
such that every binary machine `M` has a code `α` and a constant `C` with which `U` reproduces
each halting run of `M` of `t` steps on input `x`, on the paired input `⟨α, x⟩`, within
`C · (t + 1)(log₂(t + 1) + 1)` steps; and every completed output of `U` on `⟨α, x⟩` is an
output of `M` on `x`.

**Proof sketch.** Take `U` to be the code-first evaluator `Turing.universalK` at two work tapes,
over the two-tape scheme `c`. Given `M`, reduce it to two work tapes
(`Turing.FinTM.two_work_tapes_run`, overhead `c₁ · (t + 1)(log₂(t + 1) + 1)`) and code the result
(`Turing.exists_code2TM`); `α` is that code. `U` simulates the coded machine within linear
overhead `C (t' + 1)`, so a run of `M` of `t` steps costs at most
`C (c₁ (t + 1)(log₂(t + 1) + 1) + 1) ≤ C (c₁ + 1)(t + 1)(log₂(t + 1) + 1)` steps of `U`. The
converse composes the converses of the two steps. -/
theorem universal_TlogT (c : EffectiveMachineCode2) :
    ∃ U : FinTM Bool, ∀ M : FinTM Bool, ∃ (α : List Bool) (C : ℕ),
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨U, hU⟩ := universalK 2 c.toK
  refine ⟨U, fun M => ?_⟩
  obtain ⟨M', c₁, hk, hfwd, hback⟩ := FinTM.two_work_tapes_run M
  obtain ⟨N, hN⟩ := exists_code2TM M' hk
  have hdec : c.toK.toFinTM (c.encode N) = N.toFinTM := by
    rw [EffectiveMachineCode2.toK_toFinTM, c.toMachineCode2.decode_encode N]
  obtain ⟨C, hC⟩ := hU (c.encode N)
  refine ⟨c.encode N, C * (c₁ + 1), fun x output t h => ?_, fun x output h => ?_⟩
  · have h₁ := (hN x output _).2 (hfwd x output t h)
    rw [← hdec] at h₁
    apply ((hC x).1 output _ h₁).mono
    have hpos : 1 ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc C * (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)) + 1)
        ≤ C * ((c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1))) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = C * (c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by ring
  · obtain ⟨t, ht⟩ := (hC x).2 output h
    rw [hdec] at ht
    exact hback x output ⟨t, (hN x output t).1 ht⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  fixed-width blocks — the original sketch proposed `⌈log₂ |Γ|⌉` bits, and the
  delivered implementation uses a **one-hot code of width `|Γ| + 1`** (see the
  theorem's implementation note; the wider fixed width only changes the
  existential constant — epoch-2 audit, finding 1) — and decodes each emitted
  symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].
* `Turing.FinTM.alphabet_reduction_run` — the same, run by run, with the converse.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

noncomputable section

private abbrev ArBlock (N : ℕ) := Fin (N + 1) → Option Bool

private def arCell (N : ℕ) (p : ℤ) : ℤ := p / ((N : ℤ) + 1)

private def arIndex (N : ℕ) (p : ℤ) : Fin (N + 1) :=
  ⟨(p % ((N : ℤ) + 1)).toNat, by
    have h₁ := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
    have h₂ := Int.emod_lt_of_pos p (show 0 < (N : ℤ) + 1 by omega)
    omega⟩

private def arPos (N : ℕ) (z : ℤ) (j : ℕ) : ℤ := ((N : ℤ) + 1) * z + j

private lemma arCoords (N : ℕ) (z : ℤ) (j : Fin (N + 1)) :
    arCell N (arPos N z j.val) = z ∧ arIndex N (arPos N z j.val) = j := by
  have hj := j.isLt
  have h := (Int.ediv_emod_unique (show 0 < (N : ℤ) + 1 by omega)).2
    (show (j.val : ℤ) + ((N : ℤ) + 1) * z = arPos N z j.val ∧
      0 ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (N : ℤ) + 1 from
      ⟨by simp [arPos, add_comm], by omega, by omega⟩)
  refine ⟨h.1, Fin.ext ?_⟩
  simp only [arIndex, h.2, Int.toNat_natCast]

private lemma arPos_coords (N : ℕ) (p : ℤ) :
    arPos N (arCell N p) (arIndex N p).val = p := by
  have h := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
  simp only [arPos, arCell, arIndex, Int.toNat_of_nonneg h]
  exact Int.mul_ediv_add_emod p ((N : ℤ) + 1)

private lemma arPos_eq {N : ℕ} (z z' : ℤ) (j j' : Fin (N + 1)) :
    arPos N z j.val = arPos N z' j'.val ↔ z = z' ∧ j = j' := by
  constructor
  · intro h
    have h₁ := congrArg (arCell N) h
    have h₂ := congrArg (arIndex N) h
    rw [(arCoords N z j).1, (arCoords N z' j').1] at h₁
    rw [(arCoords N z j).2, (arCoords N z' j').2] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

private def arTape {N : ℕ} (F : ℤ → ArBlock N) (p : ℤ) : Option Bool :=
  F (arCell N p) (arIndex N p)

private lemma arTape_at {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ) (j : Fin (N + 1)) :
    arTape F (arPos N z j.val) = F z j := by
  simp only [arTape, (arCoords N z j).1, (arCoords N z j).2]

private lemma arTape_ext {N : ℕ} (u v : ℤ → Option Bool)
    (h : ∀ z (j : Fin (N + 1)), u (arPos N z j.val) = v (arPos N z j.val)) : u = v := by
  funext p
  simpa only [arPos_coords] using h (arCell N p) (arIndex N p)

private lemma arTape_update {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ)
    (j : Fin (N + 1)) (b : Option Bool) :
    Function.update (arTape F) (arPos N z j.val) b =
      arTape (fun z' j' => if z' = z ∧ j' = j then b else F z' j') := by
  apply arTape_ext (N := N)
  intro z' j'
  simp only [Function.update_apply, arTape_at, arPos_eq]

/-- A fixed-width one-hot code for nonblank symbols, with an all-blank code for
logical blank. Testing the position assigned to a symbol proves injectivity. -/
private def arCode {Γ : Type} [Fintype Γ] : Option Γ ↪ ArBlock (Fintype.card Γ) where
  toFun a j := a.map fun x => decide (j.val = (Fintype.equivFin Γ x).val)
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have := congrFun h 0; simp at this
    | some a =>
      cases b with
      | none => have := congrFun h 0; simp at this
      | some b =>
        have ha := (Fintype.equivFin Γ a).isLt
        have h₁ := congrFun h ⟨(Fintype.equivFin Γ a).val, by omega⟩
        have h₂ : (Fintype.equivFin Γ a).val = (Fintype.equivFin Γ b).val := by simpa using h₁
        exact congrArg some ((Fintype.equivFin Γ).injective (Fin.ext h₂))

private def arDecode {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) :
    ArBlock N → Option Γ := Function.invFun E

private lemma arDecode_code {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) (a : Option Γ) :
    arDecode E (E a) = a := Function.leftInverse_invFun E.injective a

private def arBit {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (a : Γ) : Bool :=
  decide (a = e true)

private lemma arBit_embed {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    arBit e (e b) = b := by
  cases b <;> simp [arBit, e.injective.eq_iff]

private abbrev ArPending (Γ S : Type) (k : ℕ) :=
  Option S × (Fin k → Option Γ) × (Fin k → SignType)

private abbrev ArState (Γ S : Type) (k N : ℕ) :=
  (S × Fin (N + 2) × (Fin k → ArBlock N)) ⊕
    (ArPending Γ S k × (Fin (N + 1) ⊕ Fin (N + 2)))

private def arReady {Γ S : Type} {k N : ℕ} (q : S) : ArState Γ S k N :=
  .inl (q, 0, fun _ _ => none)

private def arPending {Γ S : Type} {k : ℕ} (read : Fin k → Option Γ)
    (a : Action k Γ S) : ArPending Γ S k :=
  (a.state, fun i => (a.workTapes i).1.getD (read i), fun i => (a.workTapes i).2)

/-- A block cycle reads right, writes left, and then moves a whole block in each
source direction. Even with zero work tapes the finite controller performs the same
positive number of steps. Input motion and the possible emission occur only once,
at the transition between reading and writing. -/
private def arTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) : FinTM Bool where
  k := M.k
  State := ArState Γ M.State M.k N
  decEqState := Classical.decEq _
  tm :=
    { q₀ := arReady M.tm.q₀
      tr := fun q inp work => match q with
        | .inl (q, j, buf) =>
          if h : j.val < N + 1 then
            ⟨0, fun _ => (none, .pos), none,
              some (.inl (q, ⟨j.val + 1, by omega⟩,
                fun i => Function.update (buf i) ⟨j.val, h⟩ (work i)))⟩
          else
            let a := M.tm.tr q (inp.map e) (fun i => arDecode E (buf i))
            ⟨a.inputTape, fun _ => (none, .neg), a.output.map (arBit e),
              some (.inr (arPending (fun i => arDecode E (buf i)) a, .inl ⟨N, by omega⟩))⟩
        | .inr (a, .inl j) =>
          if h : j.val = 0 then
            ⟨0, fun i => (some (E (a.2.1 i) j), 0), none,
              some (.inr (a, .inr ⟨N + 1, by omega⟩))⟩
          else
            ⟨0, fun i => (some (E (a.2.1 i) j), .neg), none,
              some (.inr (a, .inl ⟨j.val - 1, by omega⟩))⟩
        | .inr (a, .inr r) =>
          if h : r.val = 0 then
            ⟨0, fun _ => (none, 0), none, a.1.map arReady⟩
          else
            ⟨0, fun i => (none, a.2.2 i), none,
              some (.inr (a, .inr ⟨r.val - 1, by omega⟩))⟩ }

/-- Canonical macro-boundary representation. Output is mapped through the total
bit decoder; under the computation premise `arEmission_in_image` additionally shows
that every emission is in the bit embedding's image, so its default case is unused. -/
private def arCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    Cfg k Bool (ArState Γ S k N) x where
  state := c.state.map arReady
  inputPos := ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩
  workTapes i := arTape (fun z => E (c.workTapes i z))
  workTapePos i := arPos N (c.workTapePos i) 0
  output := c.output.map (arBit e)

private lemma arCfg_input {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    (arCfg E e c).inputSymbol.map e = c.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [arCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private def arBuffer {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : ℕ) : Fin k → ArBlock N :=
  fun i b => if b.val < j then E (read i) b else none

private lemma arBuffer_zero {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read 0 = fun _ _ => none := by
  funext i b
  simp [arBuffer]

private lemma arBuffer_full {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read (N + 1) = fun i => E (read i) := by
  funext i b
  simp only [arBuffer, if_pos b.isLt]

private lemma arBuffer_update {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : Fin (N + 1)) :
    (fun i => Function.update (arBuffer E read j.val i) j (E (read i) j)) =
      arBuffer E read (j.val + 1) := by
  funext i b
  by_cases h : b = j
  · subst b
    simp [arBuffer]
  · have hv : b.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, arBuffer]
    split_ifs <;> first | rfl | omega

private def arReadCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e c with
    state := some (.inl (q, j, arBuffer E c.workTapeSymbols j.val))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arReadCfg_zero {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (hc : c.state = some q) : arReadCfg E e c q 0 = arCfg E e c := by
  simp [arReadCfg, arCfg, hc, arReady, arBuffer_zero]

private lemma arReadCfg_symbols {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arReadCfg E e c q j).workTapeSymbols = fun i => E (c.workTapeSymbols i) ⟨j.val, hj⟩ := by
  funext i
  exact arTape_at (fun z => E (c.workTapes i z)) (c.workTapePos i) ⟨j.val, hj⟩

private lemma arReadCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State)
    (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arTM E e M).tm.step (arReadCfg E e c q j) =
      arReadCfg E e c q ⟨j.val + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val < N + 1 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_pos hj]
  rw [arReadCfg_symbols E e c q j hj]
  refine Cfg.ext ?_ ?_ rfl ?_ ?_
  · have hb := arBuffer_update E c.workTapeSymbols ⟨j.val, hj⟩
    dsimp only at hb
    simp only [Action.apply, arReadCfg, hb]
  · simp [arReadCfg, arCfg, Action.apply]
  · funext i
    simp [arReadCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arReadCfg, arCfg, Action.apply]

private lemma arReadCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) (hc : c.state = some q) :
    ∀ j (hj : j ≤ N + 1), (arTM E e M).tm.runFrom (arCfg E e c) j =
      arReadCfg E e c q ⟨j, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact (arReadCfg_zero E e c q hc).symm
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact arReadCfg_step E e M c q ⟨j, by omega⟩ (by dsimp only; omega)

private def arTail {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (r : ℕ) : ℤ → ArBlock N :=
  fun z j => if z = p ∧ r ≤ j.val then E w j else E (t z) j

private lemma arTail_full {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w (N + 1) = fun z => E (t z) := by
  funext z j
  have := j.isLt
  simp [arTail, show ¬N + 1 ≤ j.val by omega]

private lemma arTail_zero {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w 0 = fun z => E (Function.update t p w z) := by
  funext z j
  simp only [arTail, Nat.zero_le, and_true, Function.update_apply]
  split <;> rfl

/-- One leftward write extends the completed suffix by one bit. Distinct blocks
remain unchanged; within this block the only new index is the written index. -/
private lemma arTail_update {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (j : Fin (N + 1)) :
    Function.update (arTape (arTail E t p w (j.val + 1))) (arPos N p j.val) (E w j) =
      arTape (arTail E t p w j.val) := by
  apply arTape_ext (N := N)
  intro z b
  simp only [Function.update_apply, arTape_at, arPos_eq, arTail]
  by_cases hz : z = p
  · subst z
    by_cases hj : b = j
    · subst b; simp
    · have hv : b.val ≠ j.val := fun h => hj (Fin.ext h)
      simp only [true_and, hj, and_false, if_false]
      split_ifs <;> first | rfl | omega
  · simp [hz]

private def arMoveCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (r : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inr r))
    workTapePos := fun i => arPos N (c.workTapePos i) 0 +
      (((N : ℤ) + 1) - r.val) * ((a.workTapes i).2 : ℤ) }

private def arWriteCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (j : Fin (N + 1)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inl j))
    workTapes := fun i => arTape (arTail E (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) (j.val + 1))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arMoveCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (r : Fin (N + 2)) (hr : r.val ≠ 0) :
    (arTM E e M).tm.step (arMoveCfg E e c a r) =
      arMoveCfg E e c a ⟨r.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : r.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hr]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    have hcast : ((r.val - 1 : ℕ) : ℤ) = (r.val : ℤ) - 1 := by omega
    simp only [Action.apply, arMoveCfg, arPending, hcast]
    ring
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arMoveCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arMoveCfg E e c a 0) = arCfg E e (a.apply c) := by
  unfold MultiTapeTM.step
  dsimp only [arMoveCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 2)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arCfg, arPos, Fin.val_zero, SignType.coe_zero]
    ring
  · simp [arCfg, Action.apply]

private lemma arMoveCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ r (hr : r ≤ N + 1), (arTM E e M).tm.runFrom (arMoveCfg E e c a ⟨r, by omega⟩)
      (r + 1) = arCfg E e (a.apply c) := by
  intro r
  induction r with
  | zero => intro hr; exact arMoveCfg_finish E e M c a
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step, arMoveCfg_step E e M c a ⟨r + 1, by omega⟩ (by simp)]
    exact ih (by omega)

private lemma arWriteCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (j : Fin (N + 1)) (hj : j.val ≠ 0) :
    (arTM E e M).tm.step (arWriteCfg E e c a j) =
      arWriteCfg E e c a ⟨j.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hj]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arWriteCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arWriteCfg, arPending]
    rw [arTail_update]
    congr 2
    omega
  · funext i
    simp [Action.apply, arWriteCfg, arPos, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply]

private lemma arWriteCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arWriteCfg E e c a 0) =
      arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arWriteCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 1)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arMoveCfg, arCfg, arPending]
    rw [arTail_update]
    simp only [Fin.val_zero, arTail_zero]
    change arTape (fun z => E (Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) z)) =
      arTape (fun z => E ((a.apply c).workTapes i z))
    rw [Action.apply_workTapes]
  · funext i
    simp [arMoveCfg, arPos, Action.apply]
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arWriteCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ j (hj : j ≤ N), (arTM E e M).tm.runFrom (arWriteCfg E e c a ⟨j, by omega⟩)
      (j + 1) = arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact arWriteCfg_finish E e M c a
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, arWriteCfg_step E e M c a ⟨j + 1, by omega⟩ (by simp)]
    exact ih (by omega)

/-- At the end of the read sweep, decoding recovers all scanned source symbols.
Execute the source input move and emission, save its pending work update in finite
control, and move left to the last bit of each block to start the write sweep. -/
private lemma arReadCfg_dispatch {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) :
    (arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩) =
      arWriteCfg E e c (M.tm.tr q c.inputSymbol c.workTapeSymbols) ⟨N, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arReadCfg, arTM]
  rw [dif_neg (show ¬N + 1 < N + 1 by omega)]
  simp only [arBuffer_full, arDecode_code]
  have hi : (arReadCfg E e c q ⟨N + 1, by omega⟩).inputSymbol.map e =
      c.inputSymbol := arCfg_input E e c
  simp only [arReadCfg, arBuffer_full] at hi
  rw [hi]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · apply Fin.ext
    simp [arWriteCfg, arCfg, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    simp only [Action.apply, arWriteCfg, arCfg, arTail_full]
  · funext i
    simp [arWriteCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply, List.map_append, Option.toList_map]

/-- Three sweeps plus two control transitions simulate one source step. Once the
source has halted, both represented configurations are absorbing. -/
private lemma arCfg_cycle {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) :
    (arTM E e M).tm.runFrom (arCfg E e c) (3 * (N + 1) + 2) =
      arCfg E e (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.runFrom_of_halt _ (show (arCfg E e c).state = none by simp [arCfg, hs])]
  | some q =>
    rw [show 3 * (N + 1) + 2 = (N + 1) + (1 + ((N + 1) + ((N + 1) + 1))) by omega,
      MultiTapeTM.runFrom_add, arReadCfg_run E e M c q hs (N + 1) (le_refl _)]
    rw [MultiTapeTM.runFrom_add]
    change (arTM E e M).tm.runFrom
      ((arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩)) _ = _
    rw [arReadCfg_dispatch, MultiTapeTM.runFrom_add,
      arWriteCfg_run E e M c _ N (le_refl _), arMoveCfg_run E e M c _ (N + 1) (le_refl _)]
    simp only [MultiTapeTM.step, hs]

private lemma arCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.runFrom (arCfg E e c) ((3 * (N + 1) + 2) * t) =
      arCfg E e (M.tm.runFrom c t) := by
  induction t with
  | zero => simp only [Nat.mul_zero, MultiTapeTM.runFrom_zero]
  | succ t ih =>
    rw [Nat.mul_succ, MultiTapeTM.runFrom_add, ih, arCfg_cycle,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma arCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) :
    (arTM E e M).tm.initCfg x = arCfg E e (M.tm.initCfg (x.map e)) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [arCfg]
  · funext i p
    simp only [MultiTapeTM.initCfg, Cfg.init, arCfg, arTape, hE]
  · funext i
    simp [arCfg, arPos]

/-- The output decoder is total, with `false` for every non-image symbol. In the
computation invariant those cases are unreachable: an emitted source symbol remains
in the append-only output, which is a prefix of the completed embedded output. -/
private lemma arEmission_in_image {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) (x : List Bool) (t : ℕ) (a : Γ)
    (ha : M.tm.outputSymbol (M.tm.runFrom (M.tm.initCfg (x.map e)) t) = some a) :
    ∃ b, e b = a := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 (hM x)
  by_cases ht : t < T x.length
  · have hp := M.tm.output_prefix (M.tm.initCfg (x.map e)) (show t + 1 ≤ T x.length by omega)
    rw [ho] at hp
    have hm : a ∈ (M.tm.runFrom (M.tm.initCfg (x.map e)) (t + 1)).output := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ha]
      simp
    obtain ⟨b, _, hb⟩ := List.mem_map.1 (hp.sublist.subset hm)
    exact ⟨b, hb⟩
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show T x.length ≤ t by omega)
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs,
      MultiTapeTM.outputSymbol_of_halt hs] at ha
    cases ha

private lemma arTM_computes {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) (w : List Bool) (t : ℕ)
    (h : M.ComputesInTime (x.map e) (w.map e) t) :
    (arTM E e M).ComputesInTime x w ((3 * (N + 1) + 2) * t) := by
  rw [computesInTime_iff, arCfg_init E hE, arCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 h
  simp only [arCfg, hs, ho, Option.map_none, true_and, List.map_map]
  simp only [Function.comp_def, arBit_embed]
  exact List.map_id w

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O((k + 1) · L)` — the
`+ 1` covering the input-read, state-update, and emission work that remains even for
`k = 0` — plus a constant start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers.

**Implementation note (epoch 2, batch C).** As permitted by the brief's arbitrary
fixed-width scheme, the implementation uses a one-hot binary code of width
`L = Fintype.card Γ + 1` for nonblank symbols; logical blank remains all-`none`.
The proof factors through any injective code of positive width with this blank
property. All work tapes are swept simultaneously: `L` reads, one dispatch,
`L` writes, `L` moves, and one final control transition, for exactly `3 * L + 2`
steps per live source step. This also covers zero work tapes. The input is never
block-encoded. `arEmission_in_image` formalizes the output-prefix argument, while
the run correspondence maps the entire output through a total decoder. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_⟩
  intro x
  exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
    (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- **Alphabet reduction, run by run** [AB09, Claim 1.5]: for every machine `M` over a finite
alphabet `Γ` and every embedding `e : Bool ↪ Γ`, a binary machine `M'` with the same number of
work tapes reproduces each halting run of `M` on an encoded input `x.map e` with an encoded
output `w.map e`, within `c · t` steps for a run of `t` steps. Conversely, whenever `M'` halts on
`x` with output `w`, `M` halts on `x.map e` with some output `o`, and if `o` is the image `v.map e`
of a binary word then `v = w`.

Without an image hypothesis the converse cannot in general assert `o = w.map e`: `M'` decodes
each emitted symbol through a total decoder, so an output of `M` outside the image of `e` is
decoded too. A machine that writes only images of bits
(as every machine computing a binary function via `e` does) has `o = w.map e`.

**Proof sketch.** `M'` is the block simulation of `Turing.FinTM.alphabet_reduction`, whose
run correspondence maps `M`'s configuration after `t` steps to `M'`'s after `c · t`. The
forward direction is that correspondence at the halting time. For the converse, let `M'`
halt at `t`. Since `c ≥ 1` and a halted run is stationary, `M'`'s configuration at `c · t` is
the one at `t`, so the correspondence says that `M`'s configuration after `t` steps is
halted, and that `w` is its output decoded. If that output is `v.map e`, decoding returns
`v`. -/
theorem alphabet_reduction_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      (∀ (x w : List Bool) (t : ℕ), M.ComputesInTime (x.map e) (w.map e) t →
        M'.ComputesInTime x w (c * t)) ∧
      ∀ (x w : List Bool), (∃ t, M'.ComputesInTime x w t) →
        ∃ (t : ℕ) (o : List Γ), M.ComputesInTime (x.map e) o t ∧
          ∀ v : List Bool, o = v.map e → v = w := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl,
    fun x w t h => arTM_computes E hE e M x w t h, ?_⟩
  rintro x w ⟨t, ht⟩
  obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).1 ht
  have hrun := arCfg_run E e M (M.tm.initCfg (x.map e)) t
  rw [← arCfg_init E hE] at hrun
  have hle : t ≤ (3 * (Fintype.card Γ + 1) + 2) * t := by
    calc t = 1 * t := (one_mul t).symm
      _ ≤ _ := Nat.mul_le_mul_right t (by omega)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at hrun
  refine ⟨t, (M.tm.runFrom (M.tm.initCfg (x.map e)) t).output, ?_, fun v hv => ?_⟩
  · rw [computesInTime_iff]
    refine ⟨?_, rfl⟩
    have h1 := congrArg Cfg.state hrun
    rw [hs] at h1
    simp only [arCfg] at h1
    exact Option.map_eq_none_iff.1 h1.symm
  · have h2 := congrArg Cfg.output hrun
    rw [ho] at h2
    simp only [arCfg, hv, List.map_map, Function.comp_def, arBit_embed, List.map_id'] at h2
    exact h2.symm

end

end Turing.FinTM

/-! ### Space annotation (§13 Z4; additive, shared-file mechanism, flagged
for the A-S2 audit) -/

namespace Turing.FinTM

/-- The four configurations already used by the block simulation cover every
physical instant: a macro boundary, a read, a write, or a move. -/
private def arSpacePhase {Γ : Type} [DecidableEq Γ] {N k : ℕ} {Q : Type}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (tm : MultiTapeTM k Γ Q)
    {x : List Bool} (c : Cfg k Γ Q (x.map e))
    (d : Cfg k Bool (ArState Γ Q k N) x) : Prop :=
  d = arCfg E e c ∨ ∃ q, c.state = some q ∧
    ((∃ j, d = arReadCfg E e c q j) ∨
      (∃ j, d = arWriteCfg E e c (tm.tr q c.inputSymbol c.workTapeSymbols) j) ∨
      (∃ r, d = arMoveCfg E e c (tm.tr q c.inputSymbol c.workTapeSymbols) r))

/-- One physical transition stays in the current source cycle, or completes it.
**Proof sketch.** Split the four phases and cite the existing transition lemmas.
Only finishing the move advances the source; a halted boundary is absorbing. -/
private lemma arSpacePhase_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e))
    (d : Cfg M.k Bool (ArState Γ M.State M.k N) x)
    (h : arSpacePhase E e M.tm c d) :
    arSpacePhase E e M.tm c ((arTM E e M).tm.step d) ∨
      arSpacePhase E e M.tm (M.tm.step c) ((arTM E e M).tm.step d) := by
  rcases h with rfl | ⟨q, hq, h⟩
  · cases hq : c.state with
    | none =>
      left; left
      exact MultiTapeTM.step_of_halt (by simp [arCfg, hq])
    | some q =>
      left; right
      refine ⟨q, hq, Or.inl ⟨⟨1, by omega⟩, ?_⟩⟩
      rw [← arReadCfg_zero E e c q hq]
      exact arReadCfg_step E e M c q 0 (by simp)
  · rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨r, rfl⟩
    · left; right
      refine ⟨q, hq, ?_⟩
      by_cases hj : j.val < N + 1
      · exact Or.inl ⟨⟨j.val + 1, by omega⟩, arReadCfg_step E e M c q j hj⟩
      · have he : j = ⟨N + 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [he]
        exact Or.inr (Or.inl ⟨⟨N, by omega⟩, arReadCfg_dispatch E e M c q⟩)
    · left; right
      refine ⟨q, hq, Or.inr ?_⟩
      by_cases hj : j.val = 0
      · have he : j = 0 := Fin.ext hj
        subst j
        exact Or.inr ⟨⟨N + 1, by omega⟩, arWriteCfg_finish E e M c _⟩
      · exact Or.inl ⟨⟨j.val - 1, by omega⟩, arWriteCfg_step E e M c _ j hj⟩
    · by_cases hr : r.val = 0
      · have he : r = 0 := Fin.ext hr
        subst r
        right; left
        rw [arMoveCfg_finish]
        simp only [MultiTapeTM.step, hq]
      · left; right
        exact ⟨q, hq, Or.inr (Or.inr
          ⟨⟨r.val - 1, by omega⟩, arMoveCfg_step E e M c _ r hr⟩)⟩

/-- Every physical horizon belongs to a source cycle whose index is no larger.
**Proof sketch.** Induct over physical time and use the phase transition lemma;
its second branch advances both the source-cycle index and the time bound. -/
private lemma arSpacePhase_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    ∃ s ≤ t, arSpacePhase E e M.tm (M.tm.runFrom c s)
      ((arTM E e M).tm.runFrom (arCfg E e c) t) := by
  induction t with
  | zero => exact ⟨0, le_refl _, Or.inl rfl⟩
  | succ t ih =>
    obtain ⟨s, hs, hp⟩ := ih
    rcases arSpacePhase_step E e M _ _ hp with h | h
    · refine ⟨s, by omega, ?_⟩
      simpa only [MultiTapeTM.runFrom_succ_eq_step'] using h
    · refine ⟨s + 1, by omega, ?_⟩
      simpa only [MultiTapeTM.runFrom_succ_eq_step'] using h

/-- During a whole-block move a physical head lies in the closed block of
one of the two source endpoints. The closed upper endpoint counts the read
pass's one-cell overshoot as well. -/
private lemma arMoveCfg_position {Γ Q : Type} [DecidableEq Γ] {N k : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) {x : List Bool}
    (c : Cfg k Γ Q (x.map e)) (a : Action k Γ Q) (r : Fin (N + 2)) (i : Fin k) :
    (∃ j ≤ N + 1, (arMoveCfg E e c a r).workTapePos i =
      arPos N (c.workTapePos i) j) ∨
    (∃ j ≤ N + 1, (arMoveCfg E e c a r).workTapePos i =
      arPos N ((a.apply c).workTapePos i) j) := by
  have hr : r.val ≤ N + 1 := by have := r.isLt; omega
  cases hd : (a.workTapes i).2 with
  | neg =>
    right
    refine ⟨r.val, hr, ?_⟩
    simp only [arMoveCfg, arPos, Action.apply, hd, SignType.cast, Nat.cast_zero]
    ring
  | zero =>
    left
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp [arMoveCfg, arPos, hd]
  | pos =>
    left
    refine ⟨N + 1 - r.val, by omega, ?_⟩
    have hcast : ((N + 1 - r.val : ℕ) : ℤ) = (N : ℤ) + 1 - r.val := by omega
    simp [arMoveCfg, arPos, hd, hcast]

/-- Trajectory containment at every physical instant: the head is in a closed
block belonging to a source position visited by the following source horizon.
This includes intermediate reads, writes, moves, and every post-halt instant.
**Proof sketch.** The phase invariant gives a source cycle. Read and write
positions are explicit offsets; a move uses one of that cycle's endpoints. -/
private lemma arTM_position_visited {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) (i : Fin M.k) :
    ∃ s ≤ t + 1, ∃ j ≤ N + 1,
      ((arTM E e M).tm.runFrom (arCfg E e c) t).workTapePos i =
        arPos N ((M.tm.runFrom c s).workTapePos i) j := by
  obtain ⟨s, hs, hp⟩ := arSpacePhase_run E e M c t
  rcases hp with h | ⟨q, hq, h⟩
  · exact ⟨s, by omega, 0, Nat.zero_le _, congrArg (fun d => d.workTapePos i) h⟩
  · rcases h with ⟨j, h⟩ | ⟨j, h⟩ | ⟨r, h⟩
    · exact ⟨s, by omega, j.val, by have := j.isLt; omega,
        congrArg (fun d => d.workTapePos i) h⟩
    · exact ⟨s, by omega, j.val, by have := j.isLt; omega,
        congrArg (fun d => d.workTapePos i) h⟩
    · rw [h]
      rcases arMoveCfg_position E e (M.tm.runFrom c s) _ r i with h | h
      · obtain ⟨j, hj, hp⟩ := h
        exact ⟨s, by omega, j, hj, hp⟩
      · obtain ⟨j, hj, hp⟩ := h
        refine ⟨s + 1, by omega, j, hj, ?_⟩
        simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step, hq] using hp

/-- A source cell's closed physical block includes the extra read boundary. -/
private def arSpaceBlock (N : ℕ) (z : ℤ) : Finset ℤ :=
  Finset.Icc (arPos N z 0) (arPos N z (N + 1))

/-- A closed block has its width plus one cells. -/
private lemma arSpaceBlock_card (N : ℕ) (z : ℤ) :
    (arSpaceBlock N z).card = N + 2 := by
  have he : arPos N z (N + 1) + 1 - arPos N z 0 = ((N + 2 : ℕ) : ℤ) := by
    simp only [arPos, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero]
    omega
  rw [arSpaceBlock, Int.card_Icc, he, Int.toNat_natCast]

/-- Closed blocks at consecutive (or equal) source positions overlap. -/
private lemma arSpaceBlock_inter (N : ℕ) (p q : ℤ) (h : |p - q| ≤ 1) :
    (arSpaceBlock N p ∩ arSpaceBlock N q).Nonempty := by
  have habs := abs_le.mp h
  have hW : 0 ≤ (N : ℤ) + 1 := by omega
  by_cases hp : p ≤ q
  · refine ⟨arPos N q 0, ?_⟩
    have hlo := Int.mul_le_mul_of_nonneg_left hp hW
    have hhi := Int.mul_le_mul_of_nonneg_left (show q ≤ p + 1 by omega) hW
    simp only [mul_add, mul_one] at hhi
    simp only [Finset.mem_inter, arSpaceBlock, Finset.mem_Icc, arPos,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    omega
  · refine ⟨arPos N p 0, ?_⟩
    have hlo := Int.mul_le_mul_of_nonneg_left (show q ≤ p by omega) hW
    have hhi := Int.mul_le_mul_of_nonneg_left (show p ≤ q + 1 by omega) hW
    simp only [mul_add, mul_one] at hhi
    simp only [Finset.mem_inter, arSpaceBlock, Finset.mem_Icc, arPos,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    omega

/-- Expanding a source trajectory into closed blocks costs its width per
visited source cell, with just one extra boundary cell on each tape.
**Proof sketch.** Initially there is one closed block. A repeated source
position adds nothing. A new position is adjacent to the preceding one,
so its block overlaps the existing cover and adds at most its width.
This is the cardinality ledger for the source's visited interval. -/
private lemma arSpaceCover_card {Γ Q : Type} {k : ℕ} {x : List Γ}
    (tm : MultiTapeTM k Γ Q) (c : Cfg k Γ Q x) (i : Fin k) (N t : ℕ) :
    ((tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N)).card ≤
      (N + 1) * tm.spaceUsedByTape c t i + 1 := by
  have hvis (s : ℕ) : tm.visitedByTapeHead c (s + 1) i =
      insert ((tm.runFrom c (s + 1)).workTapePos i) (tm.visitedByTapeHead c s i) := by
    simp only [MultiTapeTM.visitedByTapeHead, Finset.range_add_one, Finset.image_insert]
  unfold MultiTapeTM.spaceUsedByTape
  induction t with
  | zero => simp [MultiTapeTM.visitedByTapeHead, arSpaceBlock_card]
  | succ t ih =>
    rw [hvis]
    by_cases hp : (tm.runFrom c (t + 1)).workTapePos i ∈ tm.visitedByTapeHead c t i
    · simpa only [Finset.insert_eq_of_mem hp] using ih
    · rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hp]
      have hprev : (tm.runFrom c t).workTapePos i ∈ tm.visitedByTapeHead c t i :=
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
      have hd : |(tm.runFrom c (t + 1)).workTapePos i -
          (tm.runFrom c t).workTapePos i| ≤ 1 := by
        rw [MultiTapeTM.runFrom_succ_eq_step']
        exact tm.workTapePos_step_le _ i
      obtain ⟨p, hp⟩ := arSpaceBlock_inter N _ _ hd
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
      have hinter : 1 ≤ (arSpaceBlock N ((tm.runFrom c (t + 1)).workTapePos i) ∩
          (tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N)).card := by
        apply Finset.one_le_card.mpr
        exact ⟨p, Finset.mem_inter.mpr ⟨hp₁,
          Finset.mem_biUnion.mpr ⟨_, hprev, hp₂⟩⟩⟩
      have hc := Finset.card_union_add_card_inter
        (arSpaceBlock N ((tm.runFrom c (t + 1)).workTapePos i))
        ((tm.visitedByTapeHead c t i).biUnion (arSpaceBlock N))
      rw [arSpaceBlock_card] at hc
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- At every horizon, alphabet reduction uses at most the block width times
source space through `t+1`, plus one boundary cell per work tape.
**Proof sketch.** Include every physical visit in the closed-block cover
of the source trajectory, apply its cardinality bound, and sum over tapes. -/
private lemma arTM_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.spaceUsed (arCfg E e c) t ≤
      (N + 1) * M.tm.spaceUsed c (t + 1) + M.k := by
  have htape (i : Fin M.k) :
      (arTM E e M).tm.spaceUsedByTape (arCfg E e c) t i ≤
        (N + 1) * M.tm.spaceUsedByTape c (t + 1) i + 1 := by
    have hsub : (arTM E e M).tm.visitedByTapeHead (arCfg E e c) t i ⊆
        (M.tm.visitedByTapeHead c (t + 1) i).biUnion (arSpaceBlock N) := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      have hu' : u ≤ t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu
      obtain ⟨s, hs, j, hj, he⟩ := arTM_position_visited E e M c u i
      refine Finset.mem_biUnion.mpr ⟨(M.tm.runFrom c s).workTapePos i,
        Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      rw [he]
      simp only [arSpaceBlock, Finset.mem_Icc, arPos, Nat.cast_zero, add_zero,
        Nat.cast_add, Nat.cast_one]
      omega
    exact (Finset.card_le_card hsub).trans (arSpaceCover_card M.tm c i N (t + 1))
  have hmul := Finset.sum_nsmul (M := ℕ) Finset.univ (N + 1)
    (fun i => M.tm.spaceUsedByTape c (t + 1) i)
  simp only [Nat.nsmul_eq_mul] at hmul
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htape i)
  simpa only [MultiTapeTM.spaceUsed, Finset.sum_add_distrib, hmul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- The alphabet reduction preserves space up to a constant: the binary
machine of `Turing.FinTM.alphabet_reduction` can be taken with an all-time
space bound of coefficient-constant shape in the source's. Part of the Z4
space annotation (`machine-library-design.md` §13), plan §2.7's fallback
route to the space-efficient universal (Ex 4.1).

**Proof sketch.** The received `arTM` witness codes each source cell as a
fixed-width block of the fixed code `arCode`; a visited binary cell lies
inside the block of a visited source cell (plus the block in progress), so
each tape's visited set scales by the block width plus a boundary
allowance, all-time because a halted simulation is fixed and a mid-block
head stays inside its block. The `+ 1` absorbs the origin of an untouched
tape. -/
theorem alphabet_reduction_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) (M : FinTM Γ) (f : List Bool → List Bool) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f (fun n => c * (T n + 1)) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_, ?_⟩
  · intro x
    exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
      (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · intro x t
    rw [arCfg_init E hE]
    have hs := hS (x.map e) (t + 1)
    simp only [List.length_map] at hs
    have hk : M.k ≤ S x.length := by
      have hz := hS (x.map e) 0
      simpa [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape,
        MultiTapeTM.visitedByTapeHead] using hz
    calc
      _ ≤ (Fintype.card Γ + 1) * M.tm.spaceUsed (M.tm.initCfg (x.map e)) (t + 1) +
          M.k := arTM_spaceUsed E e M _ t
      _ ≤ (Fintype.card Γ + 1) * S x.length + S x.length :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hs) hk
      _ = (Fintype.card Γ + 2) * S x.length := by ring
      _ ≤ (3 * (Fintype.card Γ + 1) + 2) * (S x.length + 1) :=
        Nat.mul_le_mul (by omega) (Nat.le_succ _)

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Codes2Tape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.MathlibBridge
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Catalog
-- B5a sanctioned import: the shared canonizer and uniform simulator.
import TCSlib.Complexity.TuringMachine.CodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic two-work-tape machine codes (Z3)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`Turing.CodeTM`/`Turing.MachineCode`/
`Turing.EffectiveMachineCode`, `Encoding.lean`), which is why the received
time hierarchy arrives at `f²` strength (plan §2.1): converting to that
normal form costs a square. This file is §13's Z3: the **deterministic
two-work-tape** code scheme, the codes the two-work-tape universal machine
(stage 1, plan §4b) reads, over **the same `Turing.actionBits₂` record
format** that `Turing.CodeNDTM` fixed for the nondeterministic two-tape
codes (design §13a: one branch instead of two — never a second
serialization). The file name reads *codes for two-tape machines*
(decision 13.3, renamed from `Codes2` by the user).

Mirrors: `Turing.CodeTM` → `Turing.Code2TM`; `Turing.MachineCode` →
`Turing.MachineCode2`; `Turing.EffectiveMachineCode` →
`Turing.EffectiveMachineCode2`; and, per the P3.2 lesson (a variable-code
consumer needs uniformly timed decoding — `EffectiveMachineCode` bounds no
decoding time), `UniformMachineCode` (`Diagonalization/EXPCOM.lean`) →
`Turing.UniformMachineCode2`.

## Status

The effective and the uniform schemes are proved, with no admission. The uniform scheme
instantiates the shared canonizer and the uniform simulator of `CodeSimulator`
(`Turing.MachineFormat.exists_polyCanonizer`, `Turing.MachineFormat.exists_uniformSimulator`) at
two work tapes.

## Main definitions and results

* `Turing.Code2TM`, `Turing.Code2TM.serialize` — the deterministic
  two-work-tape normal form and its fixed, scheme-independent
  serialization (27 `Turing.actionBits₂` records per state: three input
  reads by three reads on each of the two work tapes).
* `Turing.MachineCode2`, `Turing.EffectiveMachineCode2`,
  `Turing.UniformMachineCode2` — the scheme laws, the effective scheme,
  and the uniformly timed scheme.
* `Turing.Code2TM.serialize_eq_serializeK` — the frozen serialization is the generic
  `k`-record one at two work tapes.
* `Turing.exists_effectiveMachineCode2`,
  `Turing.exists_uniformMachineCode2` — proved existence statements (the latter
  modulo the uniform simulator).
* `Turing.exists_code2TM` — every two-work-tape binary machine has a coded equivalent.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.4, machine codes;
  §1.7/§3.1 for the two-tape consumer.)

**ZF-B status appendix.** The skeleton-status text above records the received
statement phase. `exists_effectiveMachineCode2` is now proved; the uniform
simulator remains the continuation target. The new implementation includes
private adaptations of inaccessible helpers in `CodeParser.lean` and
`MathlibBridge.lean`, with declaration-level provenance in `REPORT.md`.

**ZF-B2 cleanup appendix.** The ZF-B provenance above records the original
delivery. Its 46 format-independent local copies have now been deleted:
all uses cite the promoted public readers and primitive-recursion lemmas.
The 24 remaining private declarations implement the two-tape format and
its 354-bit regression; their one-tape counterparts and retained proof
material are itemized in this delivery's duplication ledger.

## Item-8 appendix

The two-work-tape parser and canonizer now instantiate the shared `CodeFormat`
layer. ZF-B3 consumes its decoded-size and guard corollaries, with the existing
silent fallback and every public scheme statement preserved.
-/

namespace Turing

/-- The coded normal form of a deterministic machine with **two** work
tapes: a binary-alphabet machine with state space `Fin (numStates + 1)`
(never empty). Two work tapes, not one, because the Hennie-Stearns
conversion lands there at `O(T log T)` and the two-tape universal machine
(its consumer) runs such codes at linear overhead — the whole point of
strengthening past `Turing.CodeTM`'s square. Mirrors `Turing.CodeTM` and
`Turing.CodeNDTM`. [AB09, §1.4, §1.7] -/
structure Code2TM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape deterministic machine -/
  tm : MultiTapeTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded two-tape machine. -/
def Code2TM.toFinTM (M : Code2TM) : FinTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The **fixed, scheme-independent** canonical serialization, mirroring
`Turing.CodeTM.serialize` and `Turing.CodeNDTM.serialize` over the same
`Turing.actionBits₂` record: the state count, the initial state, then the
full transition table in the fixed enumeration order — states in `Fin`
order, then the input read and the two work reads each over `none`,
`some false`, `some true` (27 records per state; the nondeterministic
table's outermost choice bit is absent). This is the target format of
`Turing.EffectiveMachineCode2.canonizer` and the input format of the
two-work-tape universal machine. -/
def Code2TM.serialize (M : Code2TM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded two-tape
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations). -/
structure MachineCode2 where
  /-- encode a machine as a binary string -/
  encode : Code2TM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → Code2TM
  /-- a code followed by any amount of `true`-padding decodes to the
  machine (property 2) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine (padding by zero symbols).
Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem MachineCode2.decode_encode (c : MachineCode2) (M : Code2TM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for two-tape machines: the
algebraic laws together with a machine of this development computing the
fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale (the
target `Turing.Code2TM.serialize` is scheme-independent). As there, the
canonizer's time bound is arbitrary: fixed-code consumers absorb it into
their constants, and variable-code consumers must use
`Turing.UniformMachineCode2` instead. -/
structure EffectiveMachineCode2 extends MachineCode2 where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-! ### Private parser and canonizer implementation (ZF-B)

The fixed silent fallback and the two-work-tape instance of `CodeFormat` supply
this format's parser and canonizer. The common record, table and primitive-recursion
laws live in `CodeFormat` and `MathlibBridge`; `zfBDecode` remains a typed alias
for the frozen uniform-simulator statements.
-/



/-- The fallback is the one-state, immediately halting, silent machine. -/
private def zfBFallback : Code2TM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- The one-state halting fallback has the audited 354-bit serialization.
The closed computation includes its header and all 27 thirteen-bit records. -/
private lemma zfBFallback_serialize_length : zfBFallback.serialize.length = 354 := by
  unfold Code2TM.serialize
  dsimp only [zfBFallback]
  set_option maxRecDepth 10000 in
    norm_num [length_pairEncode, unaryFin, actionBits₂, signBits, optOptBoolBits,
      optBoolBits, optStateBits, List.finRange_succ, List.finRange_zero]

/-- The deterministic two-work-tape code format, with 27 records per state
and the fixed silent fallback. [AB09, §1.4] -/
private def twoTapeFormat : CodeFormat where
  Code := Code2TM
  Table := CodeTable2
  numStates := Code2TM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun s inp w => t s inp (w 0) (w 1)⟩⟩
  serialize := Code2TM.serialize
  tableBits := fun t => codeTable2Bits t
  readTable := codeReadTable2
  skipTable := codeSkipTable2
  guard := 351
  fallback := zfBFallback
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => by
    simp [Code2TM.serialize, codeTable2Bits, actionBits₂_eq_actionBitsK, workPair]
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, fun s inp w₀ w₁ => tr s inp (workPair w₀ w₁), ?_⟩
    show Code2TM.mk n ⟨q, fun s inp w => tr s inp (workPair (w 0) (w 1))⟩ = Code2TM.mk n ⟨q, tr⟩
    congr 1
    congr 1
    funext s inp w
    apply congrArg (tr s inp)
    funext i
    fin_cases i <;> simp [workPair]
  readTable_append := fun _ t xs => codeReadTable2_append t xs
  readTable_sound := fun _ xs t rest h => codeReadTable2_sound xs t rest h
  readTable_erase := codeEraseTable2
  tableBits_length := fun _ t => codeTable2Bits_length t

/-- Total decoding: every malformed string denotes the fixed fallback. -/
private def zfBDecode (xs : List Bool) : Code2TM := twoTapeFormat.decode xs

/-- **An effective two-tape code scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** Mirror the received constructions over the
single-branch table: `encode := Code2TM.serialize` itself; `decode`
parses the `Turing.pairEncode`d state count, the initial state, and the
transition table by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record at **27 records per state** — the
nondeterministic retarget's `2 · 27 = 54` without the choice bit, so its
minimum-length guard scales by exactly half), with the single-state
do-nothing machine as the fallback on parse failure and trailing
`true`-padding tolerated by the end-marker discipline (property 2); the
canonizer re-serializes the parsed record by the arbitrary-time
computability route of the received deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`), so no polynomial
canonizer is claimed. Fill obligations, named: the record parser and its
fallback totalization; the pad-tolerance lemma; the canonizer assembly
and its time bound.

**ZF-B implementation appendix.** The private seven-field parser and its
suffix scanner implement this route, including the up-front 351-per-state
length guard. The scanner-based canonizer is proved primitive recursive,
then compiled by the public `codePrim_machine` theorem. Its arbitrary
length-only time bound is supplied by that theorem. The private parser and
primitive-recursion adaptations are itemized in the delivery's duplication
ledger; no ND existence theorem is used. 

**Item-8 appendix.** The two-work-tape instance now consumes the shared
`CodeFormat` parser, padded round trip and canonizer construction. The 351-per-state
guard and fixed fallback are unchanged; the private parser copies are removed. -/
theorem exists_effectiveMachineCode2 : Nonempty EffectiveMachineCode2 := by
  obtain ⟨M, T, h⟩ := twoTapeFormat.exists_canonizer codePrimSkipTable2
  exact ⟨⟨⟨Code2TM.serialize, zfBDecode, twoTapeFormat.decode_serialize_pad⟩, M, T, h⟩⟩

/-- A *uniformly timed* scheme for two-tape codes: the effective scheme
together with a bounded-acceptance simulator whose budget is one
polynomial **jointly** in the code length, input length, and time bound —
the mirror of `UniformMachineCode` (`Diagonalization/EXPCOM.lean`), which
exists because `EffectiveMachineCode2` deliberately bounds no decoding
time (the P3.2 lesson: with an arbitrary scheme, a variable-code consumer
can be made to pay unboundedly for decoding). -/
structure UniformMachineCode2 extends EffectiveMachineCode2 where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-! ### Uniform-simulator instance (B5a, D4)

The specialized ZF-B3 preparation is superseded by `MachineFormat`. Its seven
output-summary/clock declarations moved, generalized, to `CodeSimulator`;
the nine remaining private preparation declarations were removed.
The 354-bit fallback regression above is retained.
-/

/-- **The two-tape serialization is the generic one** [AB09, §1.4]: for every coded two-tape
machine `M`, the frozen serialization `M.serialize` is the fixed `k`-record serialization
`serializeK M.tm` at two work tapes. (Promoted from the private `twoTape_serialize_eq` for the
two-tape scheme's `k`-tape view `Turing.EffectiveMachineCode2.toK`; statement and proof
unchanged.) -/
lemma Code2TM.serialize_eq_serializeK (M : Code2TM) : M.serialize = serializeK M.tm := by
  unfold Code2TM.serialize serializeK
  rw [tableBitsK_two]
  simp only [codeTable2Bits, actionBits₂_eq_actionBitsK]

/-- The existing two-tape parser equipped with its fixed machine semantics. -/
private def twoTapeMachineFormat : MachineFormat :=
  MachineFormat.mk twoTapeFormat 2 Code2TM.tm
    Code2TM.serialize_eq_serializeK codeSkipTable2_eq_codeSkipTableK

/-- **A uniformly timed two-tape scheme exists**.

**Proof sketch.** The concrete scheme of
`Turing.exists_effectiveMachineCode2` with the uniform simulator built as
in the received `exists_uniformMachineCode` route
(`Diagonalization/EXPCOM.lean`, P3.2 round 2): parse the nested input
keeping the deadline in binary; check the table's minimum-length guard by
binary arithmetic before any per-state iteration (a huge declared state
count is never expanded in unary; the guard constant halves against the
nondeterministic table); then run the clocked step-by-step simulation of
the decoded two-tape machine, charging one uniform polynomial jointly in
`|α| + |x| + t + 1`. The two-work-tape simulation is *easier* than the
received one-tape case for the step itself (the simulator hosts the two
coded tapes on two physical tapes — no tape reduction), and the Z1
virtual-input layer supplies the input discipline.

**Fill appendix (B5a).** This is the two-tape instance of the shared §12.11
canonizer and H1, as in the statement probe's `uniform_two`. The two-tape
writer and skipper bridges supply the format laws. The canonizer and the
uniform simulator are proved; no specialized interpreter is introduced. -/
theorem exists_uniformMachineCode2 : Nonempty UniformMachineCode2 := by
  obtain ⟨C, dC, hC⟩ := twoTapeMachineFormat.exists_polyCanonizer
  obtain ⟨S, d, hS⟩ := twoTapeMachineFormat.exists_uniformSimulator
  exact ⟨{
    toEffectiveMachineCode2 := {
      toMachineCode2 := ⟨Code2TM.serialize, twoTapeMachineFormat.decode,
        twoTapeFormat.decode_serialize_pad⟩
      canonizer := C
      canonizerTime := fun n => dC * (n + 1) ^ dC
      canonizer_computes := hC }
    simulator := S
    simDegree := d
    simulator_accepts := fun α x t h => (hS α x t).1 h
    simulator_rejects := fun α x t h => (hS α x t).2 h }⟩

/-- Every two-work-tape binary machine is equivalent, input by input and step for step, to a
coded two-tape machine (the two-tape counterpart of `Turing.exists_codeTM`). [AB09, §1.4]

**Proof sketch.** The coded machine is the original one with its states renamed along
`Turing.FinTM.stateEquivFin` (`State ≃ Fin (n + 1)`); by
`Turing.FinTM.computesInTime_relabelState` it computes the same outputs in the same times. -/
theorem exists_code2TM (M : FinTM Bool) (hk : M.k = 2) :
    ∃ M' : Code2TM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  let M₀ : FinTM Bool := ⟨2, Q, tm⟩
  exact ⟨⟨Fintype.card Q - 1, tm.relabelState M₀.stateEquivFin⟩,
    M₀.computesInTime_relabelState M₀.stateEquivFin⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim); `Turing.dbl` — the doubling.
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.
* `Turing.pairDiagTM` — the diagonal pairing machine `α ↦ pairEncode α α` (MIG-1).
* `Turing.FinTM.toCodeTM` — the code normal form of a one-work-tape binary machine
  (MIG-1).

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.length_pairEncode`, `Turing.pairEncode_eq_dbl`, `Turing.pairDecode_eq_none`,
  `Turing.eq_pairEncode_of_pairDecode`, `Turing.pairEncode_replicate_inj` — the shape of
  the pairing, shared by the machine-side developments.
* `Turing.length_bits_le_self` — `|bits m| ≤ m`.
* `Turing.bits_two_pow_mul`, `Turing.bits_two_pow_eq_replicate` — the `Nat.bits` shift law
  `(2^j·m).bits = 0^j ++ m.bits` and its case `m = 1` (CH34-D4).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
  Its witness's spec is `Turing.pairDiagTM_computes` (MIG-1; sorried until the fill
  F-A).
* `Turing.FinTM.toCodeTM_computesInTime_iff` — the code normal form halts with the same
  outputs at the same times (MIG-1).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).
* `Turing.exists_codeTM_spaceUsed` — the same coded machine also uses the same space at
  every time; `Turing.CodeTM.one_le_spaceUsed` — every coded run visits a cell.

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.
* `Turing.pairEncode_eq`, `Turing.unaryFin_eq` — the two encodings as equations, the
  specification API (user, 2026-10-16).
* `Turing.signBits_neg`/`_zero`/`_pos`, `Turing.optBoolBits_none`/`_some_false`/`_some_true`,
  `Turing.optOptBoolBits_none`/`_some_none`/`_some_false`/`_some_true`,
  `Turing.optStateBits_none`/`_some` — the record fields' encoders, case by case (the ND inventory
  API, round 2; gate 37, finding 1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- **The pairing as an equation** (the specification API, user 2026-10-16): the code doubled,
the separator `false, true`, then the second word. -/
theorem pairEncode_eq (x α : List Bool) :
    pairEncode x α = (x.flatMap fun b => [b, b]) ++ [false, true] ++ α :=
  rfl

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-! ### Shape of the pairing

Generic list facts about `pairEncode` and `pairDecode`, shared by the machine-side
developments (the time hierarchy, the polynomial hierarchy, logspace machines, and
the circuit-evaluation machines). -/

/-- A word with every bit written twice — the first component of `Turing.pairEncode`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [b, b]

/-- Doubling the empty word gives the empty word. -/
@[simp] lemma dbl_nil : dbl [] = [] := rfl

/-- Doubling `b :: w` is `b b` followed by doubling `w`. -/
@[simp] lemma dbl_cons (b : Bool) (w : List Bool) : dbl (b :: w) = b :: b :: dbl w := rfl

/-- Doubling a word doubles its length. -/
@[simp] lemma length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; ring

/-- Both copies of bit `c` of a doubled word read `w[c]`. -/
lemma getElem?_dbl (w : List Bool) (c : ℕ) (hc : c < w.length) (p : Bool) :
    (dbl w)[2 * c + p.toNat]? = some w[c] := by
  induction w generalizing c with
  | nil => simp at hc
  | cons b w ih =>
    cases c with
    | zero => cases p <;> simp
    | succ c =>
      have := ih c (by simpa using hc)
      simp only [dbl_cons, List.getElem_cons_succ]
      rw [show 2 * (c + 1) + p.toNat = (2 * c + p.toNat) + 1 + 1 by ring]
      simpa using this

/-- `pairEncode x y` is the doubled first word, the separator `[false, true]`, and the
second word. -/
lemma pairEncode_eq_dbl (x y : List Bool) : pairEncode x y = dbl x ++ [false, true] ++ y :=
  rfl

/-- The length of a pair: `|pairEncode x y| = 2|x| + 2 + |y|`. -/
theorem length_pairEncode (x y : List Bool) :
    (pairEncode x y).length = 2 * x.length + 2 + y.length := by
  simp [pairEncode_eq_dbl]
  omega

/-- A string that is not a pair is a doubled word followed by a malformed tail: the end
of the string, a lone bit, or the aligned pair `10`.

**Proof sketch.** Functional induction along `pairDecode`: aligned `00`/`11` pairs extend
the doubled prefix; in the remaining case the string matches none of `00`, `11`, `01`,
so it is empty, a single bit, or starts with `10`. -/
theorem pairDecode_eq_none (z : List Bool) (h : pairDecode z = none) :
    ∃ w tail, z = dbl w ++ tail ∧
      (tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) := by
  induction z using pairDecode.induct with
  | case1 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨false :: w, tail, by simp [hw], ht⟩
  | case2 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨true :: w, tail, by simp [hw], ht⟩
  | case3 xs => simp [pairDecode] at h
  | case4 xs h₁ h₂ h₃ =>
    refine ⟨[], xs, by simp, ?_⟩
    rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · cases b <;> cases c
      · exact absurd rfl (h₁ r)
      · exact absurd rfl (h₃ r)
      · exact Or.inr (Or.inr ⟨r, rfl⟩)
      · exact absurd rfl (h₂ r)

/-- A successfully decoded string is the pairing of its components.

**Proof sketch.** Functional induction along `pairDecode`, inverting
`pairDecode_pairEncode` one aligned pair at a time. -/
theorem eq_pairEncode_of_pairDecode (z a b : List Bool) (h : pairDecode z = some (a, b)) :
    z = pairEncode a b := by
  induction z using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode] at h

/-- A unary-first pair `⟨1ⁿ, u⟩` determines both `n` and `u`. -/
lemma pairEncode_replicate_inj {n n' : ℕ} {u u' : List Bool}
    (h : pairEncode (List.replicate n true) u = pairEncode (List.replicate n' true) u') :
    n = n' ∧ u = u' := by
  have := pairEncode_injective (a₁ := (List.replicate n true, u))
    (a₂ := (List.replicate n' true, u')) h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨by simpa using congrArg List.length h1, h2⟩

/-- The binary expansion of `m` has at most `m` bits. -/
lemma length_bits_le_self (m : ℕ) : m.bits.length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- **The `Nat.bits` shift law**: multiplying a positive `m` by `2 ^ j`
prepends `j` low zero bits to its little-endian binary expansion,
`(2^j·m).bits = 0^j ++ m.bits`. (Positivity is needed: `Nat.bits 0 = []`.)
The public home of the law, promoted per the fills-6 request F6-1(a)
(CH34-D4).

**Proof sketch.** Induct on `j`. A positive number stays positive after
multiplication by a power of two, and doubling a nonzero number prepends one
low zero bit to its expansion; induction counts the prepended zeros. -/
theorem bits_two_pow_mul (j m : ℕ) (hm : 0 < m) :
    (2 ^ j * m).bits = List.replicate j false ++ m.bits := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, Nat.bit0_bits _ (Nat.mul_pos (Nat.two_pow_pos j) hm).ne']
    simp only [ih, List.replicate_succ, List.cons_append]

/-- The little-endian binary expansion of `2 ^ n` is `n` zero bits followed by
one high bit: `(2^n).bits = 0^n 1`. The case `m = 1` of
`Turing.bits_two_pow_mul`, since the expansion of `1` is the single bit `1`. -/
theorem bits_two_pow_eq_replicate (n : ℕ) :
    (2 ^ n).bits = List.replicate n false ++ [true] := by
  simpa using bits_two_pow_mul n 1 Nat.one_pos

/-- **The diagonal pairing machine**. A six-state machine with no work tapes that, on input `α`,
writes each symbol of `α` twice, then the separator `false, true`, rewinds the input, and copies `α`
once more, so that it outputs `pairEncode α α`. It is also the witness of
`Turing.FinTM.computesFunInTime_pairDup` (consolidation: Primitives' private `pairDupTM`, which
computes the same function, retires). [AB09, proof of Theorem 1.11: the self-application input of
the `HALT` reduction] -/
def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- **The diagonal pairing machine's time**. On input `α` the diagonal pairing machine halts within
`4|α| + 5` steps with output `pairEncode α α`.

**Proof sketch.** The `have h` of today's `computesFunInTime_pairEncode_diag`, from the private
`pairDiag_run`: the doubling pass takes `2|α|` steps, the two separator steps and the first left
move `3`, the rewind `|α| + 1`, the copy `|α|`, and the halting transition `1`. -/
theorem pairDiagTM_computes (x : List Bool) :
    pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
  sorry

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- **A left move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .neg = [true, true]`. -/
theorem signBits_neg : signBits .neg = [true, true] := rfl

/-- **A stay's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .zero = [false, false]`. -/
theorem signBits_zero : signBits .zero = [false, false] := rfl

/-- **A right move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .pos = [true, false]`. -/
theorem signBits_pos : signBits .pos = [true, false] := rfl

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- **No bit's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits none = [false, false]`. -/
theorem optBoolBits_none : optBoolBits none = [false, false] := rfl

/-- **The bit `false`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some false) = [true, false]`. -/
theorem optBoolBits_some_false : optBoolBits (some false) = [true, false] := rfl

/-- **The bit `true`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some true) = [true, true]`. -/
theorem optBoolBits_some_true : optBoolBits (some true) = [true, true] := rfl

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- **No write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits none = [false, false]`. -/
theorem optOptBoolBits_none : optOptBoolBits none = [false, false] := rfl

/-- **A blank write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some none) = [false, true]`. -/
theorem optOptBoolBits_some_none : optOptBoolBits (some none) = [false, true] := rfl

/-- **Writing `false`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some false)) = [true, false]`. -/
theorem optOptBoolBits_some_false : optOptBoolBits (some (some false)) = [true, false] := rfl

/-- **Writing `true`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some true)) = [true, true]`. -/
theorem optOptBoolBits_some_true : optOptBoolBits (some (some true)) = [true, true] := rfl

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- **The unary state word as an equation** (the specification API, user 2026-10-16): `s`
`true`s, then the delimiter `false`. -/
theorem unaryFin_eq {n : ℕ} (s : Fin n) : unaryFin s = List.replicate (s : ℕ) true ++ [false] :=
  rfl

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- **Halting's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits none = [false]`. -/
theorem optStateBits_none {n : ℕ} : optStateBits (none : Option (Fin n)) = [false] := rfl

/-- **A successor state's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits (some s) = true :: unaryFin s`. -/
theorem optStateBits_some {n : ℕ} (s : Fin n) : optStateBits (some s) = true :: unaryFin s := rfl

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- **A coded run visits at least one cell.** Every run of a coded machine, at every time,
has visited at least one work cell: its one work head starts somewhere. So every qualifying
budget `s` of `Complexity.space_universal` is positive, which is what lets its addend-free bound
`C · s` absorb a ruler of the header's length (the RD-3 statement gate's row-1 calculation).

**Proof sketch.** The visited set of tape `0` contains the head's initial position, and it
is one summand of the space. -/
theorem CodeTM.one_le_spaceUsed (M : CodeTM) (x : List Bool) (t : ℕ) :
    1 ≤ M.toFinTM.tm.spaceUsed (M.toFinTM.tm.initCfg x) t := by
  let i₀ : Fin M.toFinTM.k := ⟨0, by simp⟩
  have hne : (M.toFinTM.tm.visitedByTapeHead (M.toFinTM.tm.initCfg x) t i₀).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), rfl⟩⟩
  exact (Finset.card_pos.mpr hne).trans_le
    (M.toFinTM.tm.spaceUsedByTape_le_spaceUsed _ t i₀)

/-- **Renaming a machine's states preserves its computations.** Renaming the states of a bundled
machine along an equivalence `e` gives a machine that halts on the same inputs at the same times,
with the same outputs.

**Proof sketch.** The renamed machine's initialized runs are the original runs with renamed
states (`Turing.MultiTapeTM.relabelState_runFrom_init`), and renaming changes neither halting nor
the output. -/
theorem FinTM.computesInTime_relabelState {Symbol : Type} (M : FinTM Symbol) {Q : Type}
    [Fintype Q] [DecidableEq Q] (e : M.State ≃ Q) (x output : List Symbol) (t : ℕ) :
    (FinTM.mk (k := M.k) (State := Q) (M.tm.relabelState e)).ComputesInTime x output t ↔
      M.ComputesInTime x output t := by
  rw [FinTM.computesInTime_iff, FinTM.computesInTime_iff]
  dsimp only
  rw [MultiTapeTM.relabelState_runFrom_init, Cfg.mapState_state, Cfg.mapState_output,
    Option.map_eq_none_iff]

/-- **A machine's states as an initial segment of `ℕ`.** The states of a bundled machine are in
bijection with `Fin (n + 1)` for `n = |State| - 1`: the state type is finite, and inhabited by the
start state. Noncomputable, through `Fintype.equivFinOfCardEq`. -/
noncomputable def FinTM.stateEquivFin {Symbol : Type} (M : FinTM Symbol) :
    M.State ≃ Fin (Fintype.card M.State - 1 + 1) :=
  Fintype.equivFinOfCardEq (by
    have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
    omega)

/-- `Turing.FinTM.stateEquivFin` is the bijection that `Fintype.equivFinOfCardEq` gives for the
state count, which the start state makes positive (its defining equation). -/
theorem FinTM.stateEquivFin_eq {Symbol : Type} (M : FinTM Symbol) :
    M.stateEquivFin = Fintype.equivFinOfCardEq (by
      have : 0 < Fintype.card M.State := Fintype.card_pos_iff.mpr ⟨M.tm.q₀⟩
      omega) :=
  rfl

/-- **The space-faithful coding step.** Every one-work-tape binary machine `M` is equivalent
to a coded machine `M'` that halts with the same outputs at the same times
(`Turing.exists_codeTM`'s clause) **and uses the same space at every time**. This is the space
clause of the coding step named by `Complexity.space_hierarchy`'s sketch. [AB09, §1.4]

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited by `q₀`,
so `Fintype.equivFinOfCardEq` gives an equivalence with `Fin (|Q| - 1 + 1)`. Relabel the states
along it (`Turing.MultiTapeTM.relabelState`): by `Turing.MultiTapeTM.relabelState_runFrom_init`
the relabelled run is the original run with renamed states, so halting and outputs correspond
at every time, and the space clause is `Turing.MultiTapeTM.relabelState_spaceUsed`. The
tape-count cast uses `hk : M.k = 1`, eliminated after destructuring the bundle. -/
theorem exists_codeTM_spaceUsed (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM,
      (∀ (x output : List Bool) (t : ℕ),
        M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t) ∧
      ∀ (x : List Bool) (t : ℕ),
        M'.toFinTM.tm.spaceUsed (M'.toFinTM.tm.initCfg x) t =
          M.tm.spaceUsed (M.tm.initCfg x) t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  let M₀ : FinTM Bool := ⟨1, Q, tm⟩
  exact ⟨⟨Fintype.card Q - 1, tm.relabelState M₀.stateEquivFin⟩,
    M₀.computesInTime_relabelState M₀.stateEquivFin,
    fun x t => MultiTapeTM.relabelState_spaceUsed tm M₀.stateEquivFin x t⟩

/-- **The code normal form of a one-work-tape machine**. For a binary machine `M` with one work
tape, the coded machine with `|Q| - 1` as its state index bound, whose transition function is `M`'s
transported along the canonical bijection `Q ≃ Fin |Q|` (`Turing.FinTM.stateEquivFin`; `Q` is
inhabited by the start state). [AB09, §1.4] Noncomputable, through `Fintype.equivFinOfCardEq`. -/
noncomputable def FinTM.toCodeTM : (M : FinTM Bool) → M.k = 1 → CodeTM
  | @FinTM.mk _ _ Q _hQ _dQ tm, rfl =>
    ⟨Fintype.card Q - 1, tm.relabelState (FinTM.stateEquivFin ⟨1, Q, tm⟩)⟩

/-- **The code normal form is equivalent**. For a one-work-tape binary machine `M`, its code normal
form halts on `x` with output `w` within `t` steps if and only if `M` does. [AB09, §1.4]

**Proof sketch.** The relabelled machine's run is the image of `M`'s run under the state
bijection (`Turing.MultiTapeTM.relabelState_runFrom_init`); halting and output are preserved. -/
theorem FinTM.toCodeTM_computesInTime_iff (M : FinTM Bool) (hk : M.k = 1)
    (x output : List Bool) (t : ℕ) :
    (M.toCodeTM hk).toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  exact FinTM.computesInTime_relabelState ⟨1, Q, tm⟩ _ x output t

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation is the time clause of `Turing.exists_codeTM_spaceUsed`, whose witness
is this relabelling (`Turing.MultiTapeTM.relabelState`, from the shared state-renaming module
`TCSlib.Complexity.TuringMachine.StateRenaming`), so that the relabelling is built once. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  obtain ⟨M', h, -⟩ := exists_codeTM_spaceUsed M hk
  exact ⟨M', h⟩

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
