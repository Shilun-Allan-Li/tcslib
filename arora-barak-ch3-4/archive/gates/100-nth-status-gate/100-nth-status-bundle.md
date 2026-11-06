## ===== campaign/gates/100-nth-status/pack.md =====

# External audit pack: NTimeHierarchy's Status paragraph (PR #209, a docstring gate)

## Why this PR

`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`'s module docstring said that
`Complexity.ntime_hierarchy` "is proved from two contracts that are still `sorry`". Both are now
proved and merged: E-D's `Turing.NTimeDiag.exists_diagonalizer` (#188, gate 93) and NF's
`Turing.FinNDTM.exists_codeNDTM_accepts_linear` (#191, gate 95). Gate 95's axiom prints on the
merged tree (`campaign/gates/95-nf-landing-fill/evidence/round5/axioms/NTHAx.out`) put the
hierarchy and its two corollaries on `[propext, Classical.choice, Quot.sound]`.

**The PR:** #209 on `lean/nth-status`, head `0b05cc3aaf2e48a8b8a676d8c6b7214a61848a06`:
`2029a1be` (`evidence/patches/`), then a records-only merge of the campaign. It changes the
Status paragraph and nothing else.

## Brief for the auditor

1. Is the new Status paragraph true at the campaign after #191, #202 and #207 (the hierarchy, its
   two corollaries and both contracts proved, on the standard axioms)?
2. Does the PR change anything but that paragraph?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`): 5 → 5 public, 20 → 20 private, nothing added, removed or
  changed (comment text is not part of a declaration's body).
- **Lint** (`evidence/lint/`): the policy linter's output is identical at base and head.
- **Axioms:** gate 95's `NTHAx.out` (above), on the merged tree.
- **Replay** (`evidence/merged-tree/`): `replay-lnth` at `0b05cc3a`, `NTimeHierarchy` and the
  `Diagonalization` facade, chained from the campaign's snapshot `oleans-lcamp1`: **2 modules, 0
  failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/100-nth-status/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as `nth-status-findings.md`** (the findings table and the verdict line,
no other wrapping): push it to `arora-barak-ch3-4/inbox/` on the branch
`exchange/pass-shelat-ch5-8` (`git pull --rebase` first, add only that file, never force-push, no
PR), and also paste its content in your reply. If you cannot push, say so and paste it only.

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

## ===== campaign/gates/100-nth-status/STATUS.md =====

# Gate 100 (#209, NTimeHierarchy's Status paragraph)

- 2026-11-06: #209 opened (docstring only); `replay-lnth` passed (2 modules, 0 failed, 0 `sorry`).
  Pack and evidence complete.

## ===== campaign/gates/100-nth-status/evidence/freeze/NTimeHierarchy-base.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.NDNormalForm
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.ClassNP.ExhaustiveReplay
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer
import TCSlib.Complexity.TuringMachine.ChoiceWords

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` is proved, from the
interpreter core `Turing.exists_ndInterpreterCore`
(`TCSlib.Complexity.TuringMachine.NDCodeSimulator`), and the exponential decider from it. The
hierarchy `Complexity.ntime_hierarchy` is proved from two contracts that are still `sorry`: the
diagonalizer `Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form
`Turing.FinNDTM.exists_codeNDTM_accepts_linear`. The two corollaries are proved from the
hierarchy.

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`; the normal form is in
  `TCSlib.Complexity.ClassNP.NDNormalForm`.

## Main results

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style), stated in
  `TCSlib.Complexity.ClassNP.NDNormalForm` (moved there, user 2026-10-17).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The universal NDTM from a setup machine.** Given, for the interpreter core's tape count
`K` and stream tape `jR`, a deterministic setup `P` that on `⟨⟨bits t, α⟩, x⟩` first reaches its
exit within `C_P·(t + 1)` steps with a block of exactly `t` nonblank cells on the core's stream
tape from cell `0`, every other tape blank, every head at the origin, the input head at `1` and
empty output, the guess-then-run assembly over the interpreter core is a universal NDTM at
linear overhead.

**Proof sketch.** Take the core `R` of `Turing.exists_ndInterpreterCore` and the setup `P`; the
universal machine is `Turing.guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej`.
For each stream `s` of length `t`, the core reaches its verdict within `C_R·(t + 1)` from
`streamStartCfg` (assembled from its field equations), so `Turing.guessRunTM_silent_spec` gives
halting within `T_P + 2t + C_R·(t + 1) + 11 ≤ (C_P + C_R + 13)·(t + 1)` on every branch, and
acceptance iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.acceptsWithin_iff`). -/
private theorem un_universal_of_setup (c : EffectiveNDMachineCode)
    (hsetup : ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
      cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
        (P : MultiTapeTM k Bool SP) (pexit : SP),
        ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
          ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
            (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
            P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
              ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
            ∀ u < TP,
              (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
                some pexit) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  obtain ⟨K, SR, hfin, hdec, R, jR, entry, acc, rej, hne, hR⟩ := exists_ndInterpreterCore c
  obtain ⟨k, ι, cap, hcap, SP, hfinP, hdecP, P, pexit, hP⟩ := hsetup K jR
  refine ⟨⟨k, Σ i, GuessRunPhase.State SP SR i,
    guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej⟩, fun α => ?_⟩
  obtain ⟨CR, hCR⟩ := hR α
  obtain ⟨CP, hCP⟩ := hP α
  refine ⟨CP + CR + 13, fun x t => ?_⟩
  obtain ⟨TP, hTP, blk, hblk, hrun, hfirst⟩ := hCP x t
  -- the core's verdict on every stream of length `t`
  have hcore : ∀ s : List Bool, s.length = t → ∃ T, T ≤ CR * (t + 1) ∧
      (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s) T).state
        = some (if ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).state = none ∧
            ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).output = [true] then acc else rej) ∧
      ∀ u < T,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, -, hT, hst, hno⟩ := hCR x t s (by omega)
    rw [List.take_of_length_le (by omega)] at hst
    have hss : streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s =
        ⟨some entry, 1, fun i => if i = jR then FinTM.bufferTape s else fun _ => none,
          fun _ => 0, []⟩ :=
      Cfg.ext (streamStartCfg_state _ _ _ _) (streamStartCfg_inputPos _ _ _ _)
        (funext fun i => funext fun a => streamStartCfg_workTapes _ _ _ _ i a)
        (funext fun i => streamStartCfg_workTapePos _ _ _ _ i) (streamStartCfg_output _ _ _ _)
    rw [hss]
    exact ⟨T, hT, hst, hno⟩
  have hR' : ∀ s : List Bool, s.length = t → ∃ TR ≤ CR * (t + 1),
      ((R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some acc ∨
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some rej) ∧
      ∀ u < TR,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, hT, hst, hno⟩ := hcore s hs
    refine ⟨T, hT, ?_, hno⟩
    rw [hst]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hspec := guessRunTM_silent_spec ι cap hcap jR R entry acc rej P pexit TP t blk hblk hrun
    hfirst (CR * (t + 1)) hR'
  have hbud : TP + 2 * t + CR * (t + 1) + 11 ≤ (CP + CR + 13) * (t + 1) := by
    have e : (CP + CR + 13) * (t + 1) = CP * (t + 1) + CR * (t + 1) + 13 * (t + 1) := by
      rw [Nat.add_mul, Nat.add_mul]
    rw [e]
    generalize CP * (t + 1) = a at hTP ⊢
    generalize CR * (t + 1) = b
    omega
  refine ⟨hspec.1.mono hbud, FinNDTM.acceptsWithin_iff.trans ((hspec.2 _ hbud).trans ?_)⟩
  rw [FinNDTM.acceptsWithin_iff]
  constructor
  · rintro ⟨s, hs, TR, hacc, hf⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    have hTR : TR = T := by
      by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact (hno TR h).1 hacc
      · have h' := hf T h
        rw [hst] at h'
        split_ifs at h' with hc
        · exact h'.1 rfl
        · exact h'.2 rfl
    subst hTR
    rw [hst] at hacc
    split_ifs at hacc with hcond
    · exact ⟨s, hs, hcond.1, hcond.2⟩
    · exact absurd (Option.some.inj hacc).symm hne
  · rintro ⟨s, hs, hhalt, hout⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    exact ⟨s, hs, T, by rw [hst, if_pos ⟨hhalt, hout⟩], hno⟩

/-! ### The setup machine's pieces

`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup
hypothesis. The setup built below is a seam chain over `K + kC + 1` tapes — the core's `K`, the
embedded header composite's `kC`, and the capture/counter tape last — whose phases are the
embedded header pass, the code buffer's rewind and clear, a guided erase of the extractor scratch
bank, the expansion of the captured budget word into the unary block, the block rewind, the
counter clear, and the input rewind (`Turing.inputRewindTM`, imported). The pieces here are the
guided bank-erase leaf with its framed run, the seam-step composer, the header composite's exact
first halt, and two small word facts. -/

/-- Flattening `t` copies of the one-symbol pattern gives the length-`t` unary block. -/
private lemma un_flatten (t : ℕ) :
    (List.replicate t [true]).flatten = List.replicate t true := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, ih]

/-- A buffered word is blank at and beyond its length. -/
private lemma un_buffer_ge (w : List Bool) (q : ℤ) (hq : (w.length : ℤ) ≤ q) :
    FinTM.bufferTape w q = none := by
  have h0 : 0 ≤ q := le_trans (Int.natCast_nonneg _) hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [FinTM.bufferTape_nat]
  exact List.getElem?_eq_none (by exact_mod_cast hq)

/-- **The header composite's exact first halt**, uniformly in the input suffix: the buffered
composite of the prefix parser and the first-component extractor, on
`pairEncode (pairEncode a b) x`, halts at exactly `3·|pairEncode a b| + 4 + (4·|a| + 5)` and is
live before.

**Proof sketch.** `Turing.prefixCanon_run` at the extractor's halting time, read through
`Turing.prefixCanonTM_eq` and `Turing.FinTM.pairExtractTM_fst_run`, gives the halt. Before the
parser's `3·|pairEncode a b| + 4` steps the run is live by `Turing.prefixCanon_start`; after
them it is the extractor's run, live before its own halt. -/
private theorem un_canon_halt (a b x : List Bool) :
    ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
          (pairEncode (pairEncode a b) x))
        (3 * (pairEncode a b).length + 4 + (4 * a.length + 5))).state = none ∧
      ∀ v < 3 * (pairEncode a b).length + 4 + (4 * a.length + 5),
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
            (pairEncode (pairEncode a b) x)) v).state ≠ none := by
  obtain ⟨hrun, hlive⟩ := FinTM.pairExtractTM_fst_run a b
  constructor
  · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
      (4 * a.length + 5)
    simp only [prefixCanonTM_eq] at hb
    rw [hb, FinTM.bufferedSecondCfg_state, hrun]
    rfl
  · intro v hv
    by_cases hpre : v < 3 * (pairEncode a b).length + 4
    · have hs := prefixCanon_start (FinTM.pairExtractTM true false) (pairEncode a b) x
      simp only [prefixCanonTM_eq] at hs
      refine MultiTapeTM.runFrom_state_ne_none_of_le _ _
        (3 * (pairEncode a b).length + 4) ?_ v (by omega)
      rw [hs, FinTM.bufferedSecondCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact fun h => Option.noConfusion h
    · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
        (v - (3 * (pairEncode a b).length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * (pairEncode a b).length + 4 ≤ v)] at hb
      rw [hb, FinTM.bufferedSecondCfg_state]
      intro h
      refine hlive (v - (3 * (pairEncode a b).length + 4)) (by omega) ?_
      cases hstv : ((FinTM.pairExtractTM true false).tm.runFrom
          ((FinTM.pairExtractTM true false).tm.initCfg (pairEncode a b))
          (v - (3 * (pairEncode a b).length + 4))).state with
      | none => rfl
      | some q =>
        rw [hstv] at h
        exact Option.noConfusion h

/-- The bank erase's one action: blank the selected tapes and move them with the guide. -/
private def un_bankAct (k : ℕ) (S : Finset (Fin k)) (g : Fin k) (m : SignType) (q' : Fin 3) :
    Action k Bool (Fin 3) :=
  ⟨0, fun i => if i ∈ S then (some none, m) else if i = g then (none, m) else (none, 0),
    none, some q'⟩

private lemma un_bankAct_eq {k : ℕ} (S : Finset (Fin k)) (g : Fin k) (m : SignType)
    (q' : Fin 3) (i : Fin k) :
    ((un_bankAct k S g m q').workTapes i).1 = (if i ∈ S then some none else none) ∧
      (((un_bankAct k S g m q').workTapes i).2 : ℤ) =
        if i ∈ S ∨ i = g then (m : ℤ) else 0 := by
  by_cases hiS : i ∈ S
  · simp [un_bankAct, hiS]
  · by_cases hig : i = g
    · subst hig; simp [un_bankAct, hiS]
    · simp [un_bankAct, hiS, hig]

/-- **The guided bank erase**: one unconditional left step, a left sweep that blanks every
selected tape while the guide tape still shows a symbol under the travelling head, and one
step right into the live park. The guide's head travels with the bank, and when the guide is not
one of the selected tapes its word is kept; every other tape, every other head, the input head and
the output are untouched. -/
private def un_bankTM (k : ℕ) (S : Finset (Fin k)) (g : Fin k) :
    MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr := fun q _ w =>
    if q = 0 then un_bankAct k S g .neg 1
    else if q = 1 then
      match w g with
      | some _ => un_bankAct k S g .neg 1
      | none => un_bankAct k S g .pos 2
    else ⟨0, fun _ => (none, 0), none, some 2⟩

/-- **The guided bank erase, framed.** Take a guide outside the selected bank, and start with
every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks at exactly `L + 2` and not earlier, with the bank blank, the bank and guide heads at the
origin, the guide's word and everything else unchanged.

**Proof sketch.** After `r ≤ L + 1` steps the selected cells right of `L − r` are blank and the
bank and guide heads are at `L − r`, by induction on `r`: the first step is unconditional, and
for `1 ≤ r ≤ L` the guide still reads a symbol of its word. At `L + 1` the guide reads the blank
left of its word, so the last step moves right into the park; before it the state is `0` or
`1`. -/
private theorem un_bank_run {k : ℕ} {z : List Bool} (S : Finset (Fin k)) (g : Fin k)
    (hg : g ∉ S) (L : ℕ) (w : Fin k → List Bool)
    (hw : ∀ i, i ∈ S ∨ i = g → (w i).length = L)
    (d : Cfg k Bool (Fin 3) z) (hstate : d.state = some 0)
    (htape : ∀ i, i ∈ S ∨ i = g → d.workTapes i = FinTM.bufferTape (w i))
    (hpos : ∀ i, i ∈ S ∨ i = g → d.workTapePos i = (L : ℤ)) :
    (un_bankTM k S g).runFrom d (L + 2) =
        { d with
          state := some 2
          workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
          workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } ∧
      ∀ t < L + 2, ((un_bankTM k S g).runFrom d t).state ≠ some 2 := by
  classical
  -- the sweep's trajectory
  let T : ℕ → Cfg k Bool (Fin 3) z := fun r =>
    { d with
      state := some (if r = 0 then 0 else 1)
      workTapes := fun i =>
        if i ∈ S then (fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q)
        else d.workTapes i
      workTapePos := fun i => if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i }
  have hT0 : T 0 = d := by
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · show some (if 0 = 0 then (0 : Fin 3) else 1) = d.state
      rw [if_pos rfl, hstate]
    · funext i q
      show (if i ∈ S then (fun q => if (L : ℤ) - (0 : ℕ) < q then none
          else FinTM.bufferTape (w i) q) else d.workTapes i) q = d.workTapes i q
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, htape i (Or.inl hiS)]
        by_cases hq : (L : ℤ) - (0 : ℕ) < q
        · rw [if_pos hq, eq_comm]
          exact un_buffer_ge _ _ (by rw [hw i (Or.inl hiS)]; push_cast at hq ⊢; omega)
        · rw [if_neg hq]
      · rw [if_neg hiS]
    · funext i
      show (if i ∈ S ∨ i = g then (L : ℤ) - (0 : ℕ) else d.workTapePos i) = d.workTapePos i
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, hpos i hig]
        omega
      · rw [if_neg hig]
  -- one erasing step of the sweep
  have happly : ∀ r : ℕ, r ≤ L →
      (un_bankAct k S g .neg 1).apply (T r) = T (r + 1) := by
    intro r hr
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      show some 1 = some (if r + 1 = 0 then (0 : Fin 3) else 1)
      rw [if_neg (Nat.succ_ne_zero r)]
    · rw [Action.apply_inputPos]
      show moveInputPos (T r).inputPos (un_bankAct k S g .neg 1).inputTape = (T (r + 1)).inputPos
      rw [show (un_bankAct k S g .neg 1).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .neg 1 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        funext q
        rw [Function.update_apply]
        have hps : (T r).workTapePos i = (L : ℤ) - r := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        have htp : (T r).workTapes i =
            fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have htp' : (T (r + 1)).workTapes i =
            fun q => if (L : ℤ) - (r + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        rw [hps, htp, htp']
        dsimp only
        by_cases hq : q = (L : ℤ) - r
        · rw [if_pos hq, eq_comm,
            if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast; omega)]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - r < q
          · rw [if_pos hql,
              if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast at hql ⊢; omega)]
          · rw [if_neg hql, if_neg (show ¬((L : ℤ) - (r + 1 : ℕ) < q) by
              push_cast at hq hql ⊢; omega)]
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T r).workTapes i = (T (r + 1)).workTapes i
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .neg 1 i).2
      show (T r).workTapePos i + (((un_bankAct k S g .neg 1).workTapes i).2 : ℤ) =
        (T (r + 1)).workTapePos i
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) + _ =
        (if i ∈ S ∨ i = g then (L : ℤ) - (r + 1 : ℕ) else d.workTapePos i)
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.neg_eq_neg_one, SignType.coe_neg_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T r).output ++ (none : Option Bool).toList = (T (r + 1)).output
      rw [Option.toList_none, List.append_nil]
  have hstep : ∀ r : ℕ, r ≤ L → (un_bankTM k S g).step (T r) = T (r + 1) := by
    intro r hr
    have hs : (T r).state = some (if r = 0 then 0 else 1) := rfl
    rw [MultiTapeTM.step_of_some hs]
    have htr : (un_bankTM k S g).tr (if r = 0 then 0 else 1) (T r).inputSymbol
        (T r).workTapeSymbols = un_bankAct k S g .neg 1 := by
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        simp only [un_bankTM, ↓reduceIte]
      · rw [if_neg hr0]
        have hread : (T r).workTapeSymbols g =
            FinTM.bufferTape (w g) ((L : ℤ) - r) := by
          rw [Cfg.workTapeSymbols_eq]
          have h1 : (T r).workTapes g = FinTM.bufferTape (w g) := by
            show (if g ∈ S then _ else d.workTapes g) = _
            rw [if_neg hg, htape g (Or.inr rfl)]
          have h2 : (T r).workTapePos g = (L : ℤ) - r := by
            show (if g ∈ S ∨ g = g then (L : ℤ) - r else d.workTapePos g) = _
            rw [if_pos (Or.inr rfl)]
          rw [h1, h2]
        have hsome : ∃ b, FinTM.bufferTape (w g) ((L : ℤ) - r) = some b := by
          have hlt : L - r < (w g).length := by rw [hw g (Or.inr rfl)]; omega
          refine ⟨(w g)[L - r], ?_⟩
          rw [show (L : ℤ) - r = ((L - r : ℕ) : ℤ) by omega,
            FinTM.bufferTape_nat, List.getElem?_eq_getElem hlt]
        obtain ⟨b, hb⟩ := hsome
        simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
        rw [hread, hb]
    rw [htr]
    exact happly r hr
  have hrun : ∀ r : ℕ, r ≤ L + 1 → (un_bankTM k S g).runFrom d r = T r := by
    intro r hr
    induction r with
    | zero => rw [MultiTapeTM.runFrom_zero, hT0]
    | succ r ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep r (by omega)]
  -- the final turning step
  have hfinal : (un_bankTM k S g).step (T (L + 1)) =
      { d with
        state := some 2
        workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
        workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } := by
    have hs : (T (L + 1)).state = some 1 := by
      show some (if L + 1 = 0 then (0 : Fin 3) else 1) = some 1
      rw [if_neg (Nat.succ_ne_zero L)]
    rw [MultiTapeTM.step_of_some hs]
    have hread : (T (L + 1)).workTapeSymbols g = none := by
      rw [Cfg.workTapeSymbols_eq]
      have h1 : (T (L + 1)).workTapes g = FinTM.bufferTape (w g) := by
        show (if g ∈ S then _ else d.workTapes g) = _
        rw [if_neg hg, htape g (Or.inr rfl)]
      have h2 : (T (L + 1)).workTapePos g = (L : ℤ) - (L + 1 : ℕ) := by
        show (if g ∈ S ∨ g = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos g) = _
        rw [if_pos (Or.inr rfl)]
      rw [h1, h2]
      exact FinTM.bufferTape_of_neg _ (by push_cast; omega)
    have htr : (un_bankTM k S g).tr 1 (T (L + 1)).inputSymbol (T (L + 1)).workTapeSymbols =
        un_bankAct k S g .pos 2 := by
      simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
      rw [hread]
    rw [htr]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      rfl
    · rw [Action.apply_inputPos]
      rw [show (un_bankAct k S g .pos 2).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .pos 2 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        show Function.update ((T (L + 1)).workTapes i) ((T (L + 1)).workTapePos i) none =
          (if i ∈ S then (fun _ => none) else d.workTapes i)
        rw [if_pos hiS]
        have htp : (T (L + 1)).workTapes i =
            fun q => if (L : ℤ) - (L + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have hps : (T (L + 1)).workTapePos i = (L : ℤ) - (L + 1 : ℕ) := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        rw [htp, hps]
        funext q
        rw [Function.update_apply]
        try dsimp only
        by_cases hq : q = (L : ℤ) - (L + 1 : ℕ)
        · rw [if_pos hq]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - (L + 1 : ℕ) < q
          · rw [if_pos hql]
          · rw [if_neg hql]
            exact FinTM.bufferTape_of_neg _ (by push_cast at hql ⊢; omega)
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T (L + 1)).workTapes i = (if i ∈ S then _ else d.workTapes i)
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .pos 2 i).2
      show (T (L + 1)).workTapePos i + (((un_bankAct k S g .pos 2).workTapes i).2 : ℤ) =
        (if i ∈ S ∨ i = g then 0 else d.workTapePos i)
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) + _ = _
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.pos_eq_one, SignType.coe_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T (L + 1)).output ++ (none : Option Bool).toList = d.output
      rw [Option.toList_none, List.append_nil]
  constructor
  · rw [show L + 2 = (L + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      hrun (L + 1) le_rfl, hfinal]
  · intro t ht
    rw [hrun t (by omega)]
    show some (if t = 0 then (0 : Fin 3) else 1) ≠ some 2
    by_cases ht0 : t = 0
    · rw [if_pos ht0]; decide
    · rw [if_neg ht0]; decide

/-- One seam step whose previous endpoint arrives as a right-tagged configuration: the
handover's constant relabeling collapses the tag, so the next phase's framed run applies
verbatim. -/
private theorem un_step' {k : ℕ} {S₀ S₁ S₂ : Type} [DecidableEq S₁] {z : List Bool}
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (q₂ : S₂) (g : S₀ → S₁) {c₀ : Cfg k Bool S₁ z} {c₂ : Cfg k Bool S₀ z}
    {c₃ : Cfg k Bool S₂ z} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₂.mapState g) (hexit : (c₂.mapState g).state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₂.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂, (M₂.runFrom (c₂.mapState fun _ => entry) t).state ≠ some q₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₃.mapState Sum.inr ∧
      (c₃.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr q₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr q₂) := by
  have hcomp : (c₂.mapState g).mapState (fun _ => entry) = c₂.mapState fun _ => entry := by
    rw [Cfg.mapState_mapState]; rfl
  exact seamCompTM_step M₁ exit M₂ entry q₂ h₁ hexit hcut (by rw [hcomp]; exact h₂) hq
    (fun t ht => by rw [hcomp] at *; exact hcut₂ t ht)

/-- **The setup machine.** For the interpreter core's tape count `K` and stream tape `jR`,
the seam chain over `K + kC + 1` tapes — the embedded header pass, the code buffer's rewind
and clear, the guided bank erase, the expansion, the block rewind, the counter clear, and the
input rewind — first reaches its park at the setup hypothesis's exit configuration, within a
per-code linear budget.

**Proof sketch.** The header composite halts at `3|u| + 4 + (4|bits t| + 5)` with the code
buffer `u`, the extractor scratch `bits t` and the captured budget word `bits t` on `cap`
(`Turing.prefixCanon_run`, `Turing.FinTM.pairExtractTM_fst_run`, the cast pair and the
tape-block projections, through `Turing.embedSilentRetTM_run`). The buffer rewind and clear
blank the code buffer; the guided bank erase blanks the extractor scratch while rewinding the
capture head; the expansion writes the `t`-cell block on `ι jR` (`Turing.expandTM_run_ofCfg`,
`Turing.counterValue_bits`); the block rewind, the counter clear and the input rewind reach
the exit configuration. Each seam inherits the first-visit cut, and the ledger is linear by
`Turing.counterOverhead_le` and `Turing.length_bits_le_self`. -/
private theorem un_setup :
    ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
    cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
      (P : MultiTapeTM k Bool SP) (pexit : SP),
      ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
        ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
          (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
          P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
            ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
          ∀ u < TP,
            (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
              some pexit := by
  classical
  intro K jR
  set F : FinTM Bool := FinTM.pairExtractTM true false with hF
  set MC : FinTM Bool := FinTM.bufferedCompTM universalPrefixTM F with hMC
  have hkC : MC.k = universalPrefixTM.k + (1 + F.k) := FinTM.bufferedCompTM_k universalPrefixTM F
  have hup : universalPrefixTM.k = 0 := universalPrefixTM_k
  -- the tape layout: the core's `K`, the composite's `MC.k`, the capture/counter tape last
  let ι : Fin K ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.castAdd MC.k j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_castAdd] at hv
      exact Fin.ext hv⟩
  let ιC : Fin MC.k ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.natAdd K j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_natAdd] at hv
      exact Fin.ext (by omega)⟩
  let cap : Fin (K + MC.k + 1) := Fin.last (K + MC.k)
  have hvι : ∀ j : Fin K, (ι j).val = j.val := fun j => by
    simp [ι, Fin.coe_castSucc, Fin.coe_castAdd]
  have hvιC : ∀ j : Fin MC.k, (ιC j).val = K + j.val := fun j => by
    simp [ιC, Fin.coe_castSucc, Fin.coe_natAdd]
  have hvcap : cap.val = K + MC.k := Fin.val_last _
  have hcapr : cap ∉ Set.range ι := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvι j, hvcap] at hv
    have := j.isLt
    omega
  have hcaprC : cap ∉ Set.range ιC := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvιC j, hvcap] at hv
    have := j.isLt
    omega
  -- the composite's buffer and extractor coordinates, and their images
  let jBuf : Fin MC.k := Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0))
  let jEx : Fin F.k → Fin MC.k := fun e =>
    Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e))
  let iBuf : Fin (K + MC.k + 1) := ιC jBuf
  let iEx : Fin F.k → Fin (K + MC.k + 1) := fun e => ιC (jEx e)
  let Sx : Finset (Fin (K + MC.k + 1)) := Finset.univ.image iEx
  have hvjBuf : jBuf.val = 0 := by
    simp only [jBuf, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, hup, Fin.val_eq_zero, add_zero]
  have hvjEx : ∀ e : Fin F.k, (jEx e).val = 1 + e.val := fun e => by
    simp only [jEx, Fin.coe_cast, Fin.coe_natAdd, hup, zero_add]
  have hviBuf : iBuf.val = K := by rw [hvιC, hvjBuf]; omega
  have hviEx : ∀ e : Fin F.k, (iEx e).val = K + 1 + e.val := fun e => by
    rw [hvιC, hvjEx]
    omega
  have hSx : ∀ i, i ∈ Sx ↔ ∃ e : Fin F.k, iEx e = i := fun i => by
    constructor
    · intro hi
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp hi
      exact ⟨e, he⟩
    · rintro ⟨e, he⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩
  have hSxval : ∀ i ∈ Sx, ∃ e : Fin F.k, i.val = K + 1 + e.val := by
    intro i hi
    obtain ⟨e, he⟩ := (hSx i).mp hi
    exact ⟨e, by rw [← he, hviEx]⟩
  have hBufSx : iBuf ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval iBuf hi
    rw [hviBuf] at he
    omega
  have hcapSx : cap ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval cap hi
    rw [hvcap] at he
    have := e.isLt
    omega
  have hBufcap : iBuf ≠ cap := by
    intro h
    have hv := congrArg Fin.val h
    rw [hviBuf, hvcap] at hv
    omega
  have hιBuf : ∀ j : Fin K, ι j ≠ iBuf := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hviBuf] at hv
    have := j.isLt
    omega
  have hιcap : ∀ j : Fin K, ι j ≠ cap := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hvcap] at hv
    have := j.isLt
    omega
  have hιSx : ∀ j : Fin K, ι j ∉ Sx := by
    intro j hi
    obtain ⟨e, he⟩ := hSxval (ι j) hi
    rw [hvι] at he
    have := j.isLt
    omega
  -- the block coordinate inside the expansion's body bank
  let iBlkb : Fin (K + MC.k) := Fin.castAdd MC.k jR
  have hblk_eq : ι jR = iBlkb.castSucc := rfl
  -- the phase machines
  let A1 : MultiTapeTM (K + MC.k + 1) Bool (MC.State ⊕ Unit) := embedSilentRetTM ιC cap MC.tm
  let A2 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) iBuf
  let A3 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) iBuf
  let A4 : MultiTapeTM (K + MC.k + 1) Bool (Fin 3) := un_bankTM (K + MC.k + 1) Sx cap
  let A5 : MultiTapeTM (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) :=
    expandTM (K + MC.k) iBlkb [true]
  let A6 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) (ι jR)
  let A7 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) cap
  let A8 : MultiTapeTM (K + MC.k + 1) Bool InputRewindPhase := inputRewindTM (K + MC.k + 1)
  -- the seam chain and its start override
  let R2 := seamCompTM A1 (Sum.inr ()) A2 RewindPhase.start
  let R3 := seamCompTM R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep
  let R4 := seamCompTM R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3)
  let R5 := seamCompTM R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
  let R6 := seamCompTM R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
  let R7 := seamCompTM R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep
  let R8 := seamCompTM R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
  let P := { R8 with q₀ := (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl
    (Sum.inl MC.tm.q₀))))))))}
  refine ⟨K + MC.k + 1, ι, cap, hcapr, _, inferInstance, inferInstance, P,
    Sum.inr InputRewindPhase.done, fun α => ?_⟩
  refine ⟨7 * α.length + 130, fun x t => ?_⟩
  set bt : List Bool := Nat.bits t with hbt
  set u : List Bool := pairEncode bt α with hu
  set z : List Bool := pairEncode u x with hz
  have hul : u.length = 2 * bt.length + 2 + α.length := by rw [hu, length_pairEncode]
  have hzl : z.length = 2 * u.length + 2 + x.length := by rw [hz, length_pairEncode]
  have hbtt : bt.length ≤ t := length_bits_le_self t
  -- the junction ledgers
  let ip23 : Fin (z.length + 2) := ⟨2 * u.length + 3, by omega⟩
  let tp1 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = iBuf then FinTM.bufferTape u
    else if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let hd1 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = iBuf then (2 * bt.length + 2 : ℤ)
    else if i = cap then (bt.length : ℤ)
    else if i ∈ Sx then (bt.length : ℤ)
    else 0
  let hd2 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0
  let tp3 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let tp4 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt else fun _ => none
  let capW : ℤ → Option Bool := fun q =>
    if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q
  let blk : ℤ → Option Bool := FinTM.bufferTape (List.replicate t true)
  let tp5 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then capW else if i = ι jR then blk else fun _ => none
  let hd5 : Fin (K + MC.k + 1) → ℤ := fun i => if i = ι jR then (t : ℤ) else 0
  let tp7 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = ι jR then blk else fun _ => none
  -- the junction configurations
  let E1 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    ⟨some (Sum.inr ()), ip23, tp1, hd1, []⟩
  let E2 : Cfg (K + MC.k + 1) Bool RewindPhase z := ⟨some RewindPhase.done, ip23, tp1, hd2, []⟩
  let E3 : Cfg (K + MC.k + 1) Bool SweepPhase z := ⟨some SweepPhase.done, ip23, tp3, hd2, []⟩
  let E4 : Cfg (K + MC.k + 1) Bool (Fin 3) z := ⟨some 2, ip23, tp4, fun _ => 0, []⟩
  let E5 : Cfg (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) z :=
    ⟨some CounterLoopState.done, ip23, tp5, hd5, []⟩
  let E6 : Cfg (K + MC.k + 1) Bool RewindPhase z :=
    ⟨some RewindPhase.done, ip23, tp5, fun _ => 0, []⟩
  let E7 : Cfg (K + MC.k + 1) Bool SweepPhase z :=
    ⟨some SweepPhase.done, ip23, tp7, fun _ => 0, []⟩
  let E8 : Cfg (K + MC.k + 1) Bool InputRewindPhase z := ⟨some .done, 1, tp7, fun _ => 0, []⟩
  -- the phase times
  let T1 : ℕ := 3 * u.length + 4 + (4 * bt.length + 5)
  let T2 : ℕ := 2 * bt.length + 2 + 2
  let T3 : ℕ := 2 * u.length + 2
  let T4 : ℕ := bt.length + 2
  let T5 : ℕ := t * ([true].length + 1) + counterOverhead bt (t + 1)
  let T6 : ℕ := t + 2
  let T7 : ℕ := 2 * bt.length + 2
  let T8 : ℕ := 2 * u.length + 3 + 1
  -- phase 1: the embedded header pass with its capture
  let c0 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)).mapState
      Sum.inl
  have hs1 : A1.runFrom c0 T1 = E1 ∧ E1.state = some (Sum.inr ()) ∧
      ∀ v < T1, (A1.runFrom c0 v).state ≠ some (Sum.inr ()) := by
    obtain ⟨hhalt, hlive⟩ := un_canon_halt bt α x
    rw [← hF, ← hMC, ← hu, ← hz] at hhalt hlive
    have hc0' : (MC.tm.initCfg z).state ≠ none := by
      rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact Option.some_ne_none _
    obtain ⟨hlock, hend, hcut1⟩ := embedSilentRetTM_run ιC cap hcaprC MC.tm
      (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)
      (3 * u.length + 4 + (4 * bt.length + 5)) hc0' hlive hhalt
    -- the composite's halting configuration, read through the cast pair
    obtain ⟨b', hb⟩ := prefixCanon_run F u x (4 * bt.length + 5)
    simp only [prefixCanonTM_eq] at hb
    have hextr2 : F.tm.runFrom (F.tm.initCfg u) (4 * bt.length + 5) =
        (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
          fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) :=
      (FinTM.pairExtractTM_fst_run bt α).1
    rw [hextr2] at hb
    obtain ⟨fr1, fr2, hbM⟩ : ∃ fr1 fr2,
        MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) =
          FinTM.bufferedSecondCfg universalPrefixTM F
            (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
              fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) b'
            ⟨2 * u.length + 3, by omega⟩ fr1 fr2 := ⟨_, _, hb⟩
    set CC : Cfg MC.k Bool MC.State z :=
      MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) with hCC
    -- the embedded endpoint's fields
    have hip : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).inputPos =
        ip23 := by
      rw [embedSilentCfg_inputPos, hbM, FinTM.bufferedSecondCfg_inputPos]
    have hout : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).output = [] :=
      embedSilentCfg_output ιC cap _ _ [] [] CC
    have hcBuf : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) jBuf =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0) := by
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjBuf]
      simp [Fin.coe_natAdd, Fin.coe_castAdd, hup]
    have hcEx : ∀ e : Fin F.k, Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) (jEx e) =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e) := by
      intro e
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjEx]
      simp only [Fin.coe_natAdd, hup, zero_add]
    have hnr : ∀ i : Fin (K + MC.k + 1), i ≠ iBuf → i ∉ Sx → i ∉ Set.range ιC := by
      intro i hib hiS
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      rw [hvιC] at hv
      have hjlt : j.val < 1 + F.k := by
        have h := j.isLt
        omega
      by_cases hj0 : j.val = 0
      · exact hib (by rw [← hj, show j = jBuf from Fin.ext (by rw [hvjBuf]; exact hj0)])
      · refine hiS ((hSx i).mpr ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩)
        rw [hviEx]
        show K + 1 + (j.val - 1) = i.val
        omega
    have htap : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapes i
        = tp1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapes jBuf = FinTM.bufferTape u := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcBuf, FinTM.tapeBlocks_buffer]
        refine h1.trans (h2.trans ?_)
        show _ = tp1 iBuf
        show _ = (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).1
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then FinTM.bufferTape u else if cap = cap then
            FinTM.bufferTape bt else if cap ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapes (jEx e) = FinTM.bufferTape bt := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then FinTM.bufferTape u else if iEx e = cap then
              FinTM.bufferTape bt else if iEx e ∈ Sx then FinTM.bufferTape bt
              else fun _ => none)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).1
            refine h1.trans ?_
            show _ = (if i = iBuf then FinTM.bufferTape u else if i = cap then
              FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    have hhd : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapePos i
        = hd1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapePos jBuf = (2 * bt.length + 2 : ℤ) := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcBuf, FinTM.tapeBlocks_buffer]
          push_cast
          ring
        refine h1.trans (h2.trans ?_)
        show _ = (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
          (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).2
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then (2 * bt.length + 2 : ℤ) else if cap = cap then
            (bt.length : ℤ) else if cap ∈ Sx then (bt.length : ℤ) else 0)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapePos (jEx e) = (bt.length : ℤ) := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then (2 * bt.length + 2 : ℤ) else if iEx e = cap then
              (bt.length : ℤ) else if iEx e ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).2
            refine h1.trans ?_
            show _ = (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
              (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    exact ⟨hend.trans (Cfg.ext rfl hip (funext htap) (funext hhd) hout), rfl, hcut1⟩
  -- phase 2: rewind the code buffer's head to the word start
  have hs2 : A2.runFrom (E1.mapState fun _ => RewindPhase.start) T2 = E2 ∧
      E2.state = some RewindPhase.done ∧
      ∀ v < T2, (A2.runFrom (E1.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E1.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((2 * bt.length + 2 : ℕ) : ℤ) →
        (E1.mapState fun _ => RewindPhase.start).workTapes iBuf
          ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
            (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      show tp1 iBuf (hd1 iBuf - (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          ((if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
              (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      rw [if_pos rfl, if_pos rfl]
      congr 1
      push_cast
      ring
    obtain ⟨hrun2, hcut2, -⟩ := rewindTM_run_ofCfg iBuf u (2 * bt.length + 2)
      (by omega) (E1.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun2.trans ?_, rfl, hcut2⟩
    refine Cfg.ext rfl ?_ ?_ ?_ ?_
    · exact Cfg.mapState_inputPos (fun _ => RewindPhase.start) E1
    · funext i q
      exact Cfg.mapState_workTapes (fun _ => RewindPhase.start) E1 i q
    · funext i
      show Function.update (E1.mapState fun _ => RewindPhase.start).workTapePos iBuf
        ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
          ((2 * bt.length + 2 : ℕ) : ℤ)) i = E2.workTapePos i
      rw [Function.update_apply]
      by_cases hib : i = iBuf
      · rw [if_pos hib, hib, Cfg.mapState_workTapePos]
        show hd1 iBuf - (2 * bt.length + 2 : ℕ) = hd2 iBuf
        show (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
            (2 * bt.length + 2 : ℕ) =
          (if iBuf = cap then (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl, if_neg hBufcap, if_neg hBufSx]
        push_cast
        ring
      · rw [if_neg hib, Cfg.mapState_workTapePos]
        show hd1 i = hd2 i
        show (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
            (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
          (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_neg hib]
    · exact Cfg.mapState_output (fun _ => RewindPhase.start) E1
  -- phase 3: clear the code buffer
  have hs3 : A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) T3 = E3 ∧
      E3.state = some SweepPhase.done ∧
      ∀ v < T3, (A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E2.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf = 0 := by
      rw [Cfg.mapState_workTapePos]
      show (if iBuf = cap then (bt.length : ℤ)
        else if iBuf ∈ Sx then (bt.length : ℤ) else 0) = 0
      rw [if_neg hBufcap, if_neg hBufSx]
    have htp : ∀ q', (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf q' =
        FinTM.bufferTape u q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then FinTM.bufferTape bt
        else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none) q' =
        FinTM.bufferTape u q'
      rw [if_pos rfl]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
        (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf
          ((E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf + p) =
          FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add]
    obtain ⟨hrun3, hcut3, -⟩ := clearTM_run_ofCfg iBuf u (E2.mapState fun _ => SweepPhase.sweep)
      hst hhw
    refine ⟨hrun3.trans ?_, rfl, hcut3⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E2) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E2 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E2)
    funext i q
    show (if i = iBuf ∧ (E2.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E2.mapState fun _ => SweepPhase.sweep).workTapePos i + (u.length : ℤ) then none
      else (E2.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp3 i q
    by_cases hib : i = iBuf
    · rw [hib, hps, htp]
      have htp3 : tp3 iBuf q = none := by
        show (if iBuf = cap then FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q = none
        rw [if_neg hBufcap, if_neg hBufSx]
      rw [htp3]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (u.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hib hcon.1), Cfg.mapState_workTapes]
      show (if i = iBuf then FinTM.bufferTape u else if i = cap then FinTM.bufferTape bt
        else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none) q =
        (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q
      rw [if_neg hib]
  -- phase 4: the guided bank erase, which also rewinds the capture head
  have hs4 : A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) T4 = E4 ∧
      E4.state = some 2 ∧
      ∀ v < T4, (A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) v).state ≠ some 2 := by
    have htape4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i = FinTM.bufferTape bt := by
      intro i hi
      funext q
      rw [Cfg.mapState_workTapes]
      show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
        else fun _ => none) q = FinTM.bufferTape bt q
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    have hpos4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i = (bt.length : ℤ) := by
      intro i hi
      rw [Cfg.mapState_workTapePos]
      show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
        (bt.length : ℤ)
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    obtain ⟨hrun4, hcut4⟩ := un_bank_run Sx cap hcapSx bt.length (fun _ => bt)
      (fun _ _ => rfl) (E3.mapState fun _ => (0 : Fin 3))
      (by rw [Cfg.mapState_state]; rfl) htape4 hpos4
    refine ⟨hrun4.trans ?_, rfl, hcut4⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => (0 : Fin 3)) E3) ?_ ?_
      (Cfg.mapState_output (fun _ => (0 : Fin 3)) E3)
    · funext i q
      show (if i ∈ Sx then (fun _ => none) else
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i) q = tp4 i q
      by_cases hiS : i ∈ Sx
      · rw [if_pos hiS]
        have hic : i ≠ cap := fun h => hcapSx (h ▸ hiS)
        show (none : Option Bool) =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        rw [if_neg hic]
      · rw [if_neg hiS, Cfg.mapState_workTapes]
        show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        by_cases hic : i = cap
        · rw [if_pos hic, if_pos hic]
        · rw [if_neg hic, if_neg hic, if_neg hiS]
    · funext i
      show (if i ∈ Sx ∨ i = cap then 0 else
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i) = (0 : ℤ)
      by_cases hig : i ∈ Sx ∨ i = cap
      · rw [if_pos hig]
      · rw [if_neg hig, Cfg.mapState_workTapePos]
        show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) = 0
        rw [if_neg (fun h => hig (Or.inr h)), if_neg (fun h => hig (Or.inl h))]
  -- phase 5: the expansion of the captured budget word into the unary block
  have hd5' : Nat.ofDigits 2 (bt.map Bool.toNat) = t :=
    (counterValue_eq bt).symm.trans (counterValue_bits t)
  have hs5 : A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) T5 = E5 ∧
      E5.state = some CounterLoopState.done ∧
      ∀ v < T5, (A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) v).state ≠
        some CounterLoopState.done := by
    -- the junction into the counter host's layout
    have hJ5 : (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) =
        counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
          (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
            Cfg (K + MC.k) Bool (Fin 2) z) (FinTM.bufferTape bt) 0 := by
      rw [counter_cfg_eq]
      refine Cfg.ext ?_
        (Cfg.mapState_inputPos (fun _ => CounterLoopState.dec FlagPhase.run) E4) ?_ ?_
        (Cfg.mapState_output (fun _ => CounterLoopState.dec FlagPhase.run) E4)
      · rw [Cfg.mapState_state]
        rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          rw [Cfg.mapState_workTapes]
          show (if cap = cap then FinTM.bufferTape bt else fun _ => none) q =
            FinTM.bufferTape bt q
          rw [if_pos rfl]
        · rw [Fin.lastCases_castSucc]
          funext q
          rw [Cfg.mapState_workTapes]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          rw [Cfg.mapState_workTapePos]
        · rw [Fin.lastCases_castSucc]
          rw [Cfg.mapState_workTapePos]
    have hrow := expandTM_run_ofCfg (x := z) iBlkb [true]
      (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
        Cfg (K + MC.k) Bool (Fin 2) z) rfl bt (FinTM.bufferTape bt) 0
      (fun p _ _ => by rw [zero_add]) t hd5'
    have hlen1 : ([true] : List Bool).length = 1 := rfl
    refine ⟨?_, rfl, ?_⟩
    · rw [hJ5]
      refine hrow.1.trans ?_
      rw [counter_cfg_eq]
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) = tp5 (Fin.last (K + MC.k)) q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) =
            (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q
          rw [if_pos rfl, zero_add]
        · rw [Fin.lastCases_castSucc]
          funext q
          show (if j' = iBlkb ∧ (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ) then
              FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
            else tp4 (Fin.castSucc j') q) = tp5 (Fin.castSucc j') q
          have hne : Fin.castSucc j' ≠ cap := by
            intro h
            have hv := congrArg Fin.val h
            rw [Fin.coe_castSucc, hvcap] at hv
            have := j'.isLt
            omega
          by_cases hjb : j' = iBlkb
          · rw [hjb]
            show (if iBlkb = iBlkb ∧ (0 : ℤ) ≤ q ∧
                  q < 0 + ((t * [true].length : ℕ) : ℤ) then
                FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
              else tp4 (Fin.castSucc iBlkb) q) = tp5 (Fin.castSucc iBlkb) q
            have htp5v : tp5 (Fin.castSucc iBlkb) q = blk q := by
              show (if Fin.castSucc iBlkb = cap then capW else if Fin.castSucc iBlkb = ι jR
                then blk else fun _ => none) q = blk q
              rw [if_neg (hjb ▸ hne),
                if_pos (show Fin.castSucc iBlkb = ι jR from rfl)]
            rw [htp5v]
            by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ)
            · rw [if_pos ⟨rfl, hq.1, hq.2⟩, un_flatten, sub_zero]
            · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
              show tp4 (Fin.castSucc iBlkb) q = blk q
              show (if Fin.castSucc iBlkb = cap then FinTM.bufferTape bt else fun _ => none) q =
                blk q
              rw [if_neg (hjb ▸ hne)]
              rw [eq_comm]
              rcases lt_or_ge q 0 with h0 | h0
              · exact FinTM.bufferTape_of_neg _ h0
              · refine un_buffer_ge _ _ ?_
                rw [List.length_replicate]
                rw [hlen1] at hq
                push_cast at hq ⊢
                omega
          · rw [if_neg (fun hcon => hjb hcon.1)]
            have hnj : Fin.castSucc j' ≠ ι jR := by
              intro h
              exact hjb (Fin.castSucc_injective _ h)
            show (if Fin.castSucc j' = cap then FinTM.bufferTape bt else fun _ => none) q =
              (if Fin.castSucc j' = cap then capW else if Fin.castSucc j' = ι jR then blk
                else fun _ => none) q
            rw [if_neg hne, if_neg hne, if_neg hnj]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          show (0 : ℤ) = hd5 (Fin.last (K + MC.k))
          show (0 : ℤ) = (if cap = ι jR then (t : ℤ) else 0)
          rw [if_neg (Ne.symm (hιcap jR))]
        · rw [Fin.lastCases_castSucc]
          rw [Function.update_apply]
          by_cases hjb : j' = iBlkb
          · rw [if_pos hjb, hjb]
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) = hd5 (Fin.castSucc iBlkb)
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) =
              (if Fin.castSucc iBlkb = ι jR then (t : ℤ) else 0)
            rw [if_pos (show Fin.castSucc iBlkb = ι jR from rfl), hlen1]
            push_cast
            ring
          · rw [if_neg hjb]
            have hnj : Fin.castSucc j' ≠ ι jR := fun h => hjb (Fin.castSucc_injective _ h)
            show (0 : ℤ) = (if Fin.castSucc j' = ι jR then (t : ℤ) else 0)
            rw [if_neg hnj]
    · intro v hv
      rw [hJ5]
      exact (hrow.2.1 v hv).1
  -- phase 6: rewind the block head
  have hs6 : A6.runFrom (E5.mapState fun _ => RewindPhase.start) T6 = E6 ∧
      E6.state = some RewindPhase.done ∧
      ∀ v < T6, (A6.runFrom (E5.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E5.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) = (t : ℤ) := by
      rw [Cfg.mapState_workTapePos]
      show (if ι jR = ι jR then (t : ℤ) else 0) = (t : ℤ)
      rw [if_pos rfl]
    have htp : ∀ q', (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR) q' =
        blk q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if ι jR = cap then capW else if ι jR = ι jR then blk else fun _ => none) q' = blk q'
      rw [if_neg (hιcap jR), if_pos rfl]
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((t : ℕ) : ℤ) →
        (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR)
          ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - (t : ℕ) + p) =
          FinTM.bufferTape (List.replicate t true) p := by
      intro p hp1 hp2
      rw [hps, htp]
      show FinTM.bufferTape (List.replicate t true) ((t : ℤ) - (t : ℕ) + p) = _
      congr 1
      ring
    obtain ⟨hrun6, hcut6, -⟩ := rewindTM_run_ofCfg (ι jR) (List.replicate t true) t
      (by simp) (E5.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun6.trans ?_, rfl, hcut6⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => RewindPhase.start) E5) ?_ ?_
      (Cfg.mapState_output (fun _ => RewindPhase.start) E5)
    · funext i q
      show (E5.mapState fun _ => RewindPhase.start).workTapes i q = tp5 i q
      rw [Cfg.mapState_workTapes]
    · funext i
      show Function.update (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR)
        ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - ((t : ℕ) : ℤ)) i =
        (0 : ℤ)
      rw [Function.update_apply]
      by_cases hij : i = ι jR
      · rw [if_pos hij, hps]
        ring
      · rw [if_neg hij, Cfg.mapState_workTapePos]
        show (if i = ι jR then (t : ℤ) else 0) = 0
        rw [if_neg hij]
  -- phase 7: clear the counter word
  have hs7 : A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) T7 = E7 ∧
      E7.state = some SweepPhase.done ∧
      ∀ v < T7, (A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E6.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E6.mapState fun _ => SweepPhase.sweep).workTapePos cap = 0 :=
      Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 cap
    have htp : ∀ q', (E6.mapState fun _ => SweepPhase.sweep).workTapes cap q' = capW q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q' = capW q'
      rw [if_pos rfl]
    have hcapN : ∀ p : ℤ, capW p = FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p
      show (if 0 ≤ p ∧ p < (bt.length : ℤ) then some true else FinTM.bufferTape bt p) = _
      by_cases hp : 0 ≤ p ∧ p < (bt.length : ℤ)
      · rw [if_pos hp]
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
          ⟨p.toNat, (Int.toNat_of_nonneg hp.1).symm⟩
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
          rw [List.length_replicate]
          exact_mod_cast hp.2)]
        rw [List.getElem_replicate]
      · rw [if_neg hp]
        have h1 : FinTM.bufferTape bt p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · exact un_buffer_ge _ _ (by omega)
        have h2 : FinTM.bufferTape (List.replicate bt.length true) p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · refine un_buffer_ge _ _ ?_
            rw [List.length_replicate]
            omega
        rw [h1, h2]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate bt.length true).length : ℤ) →
        (E6.mapState fun _ => SweepPhase.sweep).workTapes cap
          ((E6.mapState fun _ => SweepPhase.sweep).workTapePos cap + p) =
          FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add, hcapN]
    obtain ⟨hrun7, hcut7, -⟩ := clearTM_run_ofCfg cap (List.replicate bt.length true)
      (E6.mapState fun _ => SweepPhase.sweep) hst hhw
    rw [List.length_replicate] at hrun7 hcut7
    refine ⟨hrun7.trans ?_, rfl, hcut7⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E6) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E6)
    funext i q
    show (if i = cap ∧ (E6.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E6.mapState fun _ => SweepPhase.sweep).workTapePos i + (bt.length : ℤ) then none
      else (E6.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp7 i q
    by_cases hic : i = cap
    · rw [hic, hps, htp]
      have htp7 : tp7 cap q = none := by
        show (if cap = ι jR then blk else fun _ => none) q = none
        rw [if_neg (Ne.symm (hιcap jR))]
      rw [htp7]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (bt.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        show capW q = none
        show (if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q) = none
        rw [if_neg (by omega)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hic hcon.1), Cfg.mapState_workTapes]
      show (if i = cap then capW else if i = ι jR then blk else fun _ => none) q =
        (if i = ι jR then blk else fun _ => none) q
      rw [if_neg hic]
  -- phase 8: the input rewind
  have hs8 : A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) T8 = E8 ∧
      E8.state = some .done ∧
      ∀ v < T8, (A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) v).state ≠
        some .done := by
    have hip8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos = ip23 :=
      Cfg.mapState_inputPos _ _
    obtain ⟨hrun8, hcut8, -⟩ := inputRewindTM_run (E7.mapState fun _ => InputRewindPhase.start)
      (by rw [Cfg.mapState_state]; rfl)
      (by rw [hip8]; show 1 ≤ 2 * u.length + 3; omega)
    have hT8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos.val + 1 = T8 := by
      rw [hip8]
    rw [hT8] at hrun8 hcut8
    refine ⟨hrun8.trans ?_, rfl, hcut8⟩
    refine Cfg.ext rfl rfl ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => InputRewindPhase.start) E7 i)
      (Cfg.mapState_output (fun _ => InputRewindPhase.start) E7)
    funext i q
    exact Cfg.mapState_workTapes (fun _ => InputRewindPhase.start) E7 i q
  -- the chain: every seam inherits the run, the exit state and the first-visit cut
  have hch2 := seamCompTM_step A1 (Sum.inr ()) A2 RewindPhase.start RewindPhase.done
    hs1.1 hs1.2.1 hs1.2.2 hs2.1 hs2.2.1 hs2.2.2
  have hch3 := un_step' R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep SweepPhase.done
    Sum.inr hch2.1 hch2.2.1 hch2.2.2 hs3.1 rfl hs3.2.2
  have hch4 := un_step' R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3) (2 : Fin 3)
    Sum.inr hch3.1 hch3.2.1 hch3.2.2 hs4.1 rfl hs4.2.2
  have hch5 := un_step' R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
    CounterLoopState.done Sum.inr hch4.1 hch4.2.1 hch4.2.2 hs5.1 rfl hs5.2.2
  have hch6 := un_step' R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
    RewindPhase.done Sum.inr hch5.1 hch5.2.1 hch5.2.2 hs6.1 rfl hs6.2.2
  have hch7 := un_step' R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep SweepPhase.done
    Sum.inr hch6.1 hch6.2.1 hch6.2.2 hs7.1 rfl hs7.2.2
  have hch8 := un_step' R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
    InputRewindPhase.done Sum.inr hch7.1 hch7.2.1 hch7.2.2 hs8.1 rfl hs8.2.2
  -- the start: the machine's initial configuration is the chain's left seam
  have hstart : P.initCfg z =
      ((((((c0.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState
        Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_with_q₀]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      rfl
    · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    · funext i q
      rw [Cfg.init_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_tape, MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).1,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).1]
    · funext i
      rw [Cfg.init_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_pos, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).2,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, List.length_nil]
          rfl
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).2]
    · rw [Cfg.init_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, embedSilentCfg_output]
  -- the exit configuration and the block property
  have hblk : ∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t := by
    intro p
    constructor
    · intro h
      by_contra hcon
      apply h
      rcases lt_or_ge p 0 with h0 | h0
      · exact FinTM.bufferTape_of_neg _ h0
      · refine un_buffer_ge _ _ ?_
        rw [List.length_replicate]
        push_cast at hcon ⊢
        omega
    · rintro ⟨h0, hlt⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
        ⟨p.toNat, (Int.toNat_of_nonneg h0).symm⟩
      show FinTM.bufferTape (List.replicate t true) ((n : ℕ) : ℤ) ≠ none
      rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
        rw [List.length_replicate]
        exact_mod_cast hlt)]
      simp
  have hfin : (E8.mapState (Sum.inr : InputRewindPhase → _)) =
      (⟨some (Sum.inr InputRewindPhase.done), 1, Function.update (fun _ _ => none) (ι jR) blk,
        fun _ => 0, []⟩ :
        Cfg (K + MC.k + 1) Bool ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          Fin 3) ⊕ CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          InputRewindPhase) z) := by
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · exact (Cfg.mapState_state (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · exact (Cfg.mapState_inputPos (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · funext i q
      refine (Cfg.mapState_workTapes (Sum.inr : InputRewindPhase → _) E8 i q).trans ?_
      show tp7 i q = Function.update (fun _ _ => none) (ι jR) blk i q
      rw [Function.update_apply]
    · funext i
      exact (Cfg.mapState_workTapePos (Sum.inr : InputRewindPhase → _) E8 i).trans rfl
    · exact (Cfg.mapState_output (Sum.inr : InputRewindPhase → _) E8).trans rfl
  -- the budget
  have hco : counterOverhead bt (t + 1) ≤ 4 * t + 2 * bt.length + 2 := by
    have h := counterOverhead_le bt
    rw [hd5'] at h
    exact h
  refine ⟨T1 + 1 + T2 + 1 + T3 + 1 + T4 + 1 + T5 + 1 + T6 + 1 + T7 + 1 + T8, ?_, blk, hblk,
    ?_, ?_⟩
  · show 3 * u.length + 4 + (4 * bt.length + 5) + 1 + (2 * bt.length + 2 + 2) + 1 +
      (2 * u.length + 2) + 1 + (bt.length + 2) + 1 +
      (t * ([true].length + 1) + counterOverhead bt (t + 1)) + 1 + (t + 2) + 1 +
      (2 * bt.length + 2) + 1 + (2 * u.length + 3 + 1) ≤ (7 * α.length + 130) * (t + 1)
    rw [show ([true] : List Bool).length = 1 from rfl]
    have hexp : (7 * α.length + 130) * (t + 1) =
        7 * (α.length * t) + 7 * α.length + 130 * t + 130 := by ring
    rw [hexp]
    have hA : α.length * t ≥ 0 := Nat.zero_le _
    omega
  · have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    show P.runFrom (P.initCfg z) _ = _
    rw [hstart, hPrun]
    exact hch8.1.trans hfin
  · intro v hv
    have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    rw [hstart, hPrun]
    exact hch8.2.2 v hv

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`.

**Implementation.** The setup before the guess is one seam chain of eight phases: the prefix
canonizer `Turing.prefixCanonTM` with the first-component extractor, embedded silently with its
output `bits t` captured on a scratch tape; the code buffer's rewind and clear; an erase of the
extractor's scratch tapes that also rewinds the capture; the expansion of `bits t` into the
unary block (`Turing.expandTM`); the block's rewind; the counter's clear; and the input rewind.
It first reaches its exit within `(7·|α| + 130)·(t + 1)` steps, with no `|x|` term, so the
constant is `C = C_P + C_R + 13` with `C_P = 7·|α| + 130` and `C_R` the core's. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  exact un_universal_of_setup c un_setup

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. `E` itself is
`Turing.FinNDTM.exists_exhaustiveDecider`, proved (iterative deepening over the
choice words of the fixed `UN`, each replayed by its replay machine under the
step-clocked runner, with a window clear between replays; no `|x|` term), so the
decider's only open dependency is the universal NDTM's interpreter core
`Turing.exists_ndInterpreterCore`. The proof applies
`Turing.ndAcceptsWithin_decider_of_universal` to `Turing.exists_timed_universal_NDTM`. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  exact ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)

end Turing

namespace Complexity

open Turing

/-- The chain's induction: `P n ↔ P (n + 1)` for `a ≤ n < b` gives `P a ↔ P b`.

**Proof sketch.** Induction on `b` from `a`, composing the step at `b`. -/
private theorem nh_chain (P : ℕ → Prop) {a b : ℕ} (hab : a ≤ b)
    (step : ∀ n, a ≤ n → n < b → (P n ↔ P (n + 1))) : P a ↔ P b := by
  induction b, hab using Nat.le_induction with
  | base => exact Iff.rfl
  | succ b hab ih =>
    exact (ih fun n h1 h2 => step n h1 (by omega)).trans (step b hab (by omega))

/-- Finite absorption: a function eventually below `g` is below `F · (g + 1)`.

**Proof sketch.** Take `F` one more than the sum of `f` below `N₀`: beyond `N₀` the first summand
pays, below it the sum does. -/
private theorem nh_absorb (f g : ℕ → ℕ) (N₀ : ℕ) (h : ∀ n ≥ N₀, f n ≤ g n) :
    ∃ F : ℕ, ∀ n, f n ≤ F * (g n + 1) := by
  refine ⟨1 + ∑ m ∈ Finset.range N₀, f m, fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · have h1 := h n hn
    nlinarith [Nat.zero_le (∑ m ∈ Finset.range N₀, f m)]
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have h2 := Finset.single_le_sum (fun m _ => Nat.zero_le (f m)) hmem
    nlinarith [Nat.zero_le (g n)]

/-- A constant factor folds into the membership constant: `NTIME (F · T) ⊆ NTIME T`.

**Proof sketch.** A decider within `a · (F · T n)` decides within `(a F) · T n`
(`Complexity.mem_NTIME_iff`, `Turing.FinNDTM.decidesInTime_iff`). -/
private theorem nh_fold {T : ℕ → ℕ} (F : ℕ) : NTIME (fun n => F * T n) ⊆ NTIME T := by
  intro L hL
  obtain ⟨a, N, hN⟩ := mem_NTIME_iff.mp hL
  apply mem_NTIME_iff.mpr
  refine ⟨a * F, N, FinNDTM.decidesInTime_iff.mpr ?_⟩
  intro x
  simpa only [Nat.mul_assoc] using (FinNDTM.decidesInTime_iff.mp hN x)

/-- The inclusion `NTIME f ⊆ NTIME (g + 1)` under the domination hypothesis.

**Proof sketch.** The hypothesis at `A = 1` gives `f n ≤ g n` eventually; absorb the finitely many
smaller lengths (`nh_absorb`), apply `NTIME.mono`, and fold the factor `F` into the membership
constant (`nh_fold`). -/
private theorem nh_inclusion {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊆ NTIME (fun n => g n + 1) := by
  obtain ⟨N₀, hN₀⟩ := hfg 1
  obtain ⟨F, hF⟩ := nh_absorb f g N₀ (fun n hn => by have := hN₀ n hn; omega)
  intro L hL
  have h1 : L ∈ NTIME (fun n => F * (g n + 1)) := NTIME.mono hF hL
  exact nh_fold F h1

/-- The top's threshold: `C · 2^{C (T + 1)} ≤ 2^{T²}` for every large `T`.

**Proof sketch.** `C < 2^C`, so the left side is below `2^{C + C (T + 1)}`, and
`C + C (T + 1) ≤ T²` once `T ≥ 2C + 2`. -/
private theorem nh_top (C : ℕ) : ∃ T₀, ∀ T ≥ T₀, C * 2 ^ (C * (T + 1)) ≤ 2 ^ (T ^ 2) := by
  refine ⟨2 * C + 2, fun T hT => ?_⟩
  have hC : C < 2 ^ C := Nat.lt_two_pow_self
  calc C * 2 ^ (C * (T + 1)) ≤ 2 ^ C * 2 ^ (C * (T + 1)) := Nat.mul_le_mul_right _ hC.le
    _ = 2 ^ (C + C * (T + 1)) := by rw [← pow_add]
    _ ≤ 2 ^ (T ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul_right T hT])

/-- The bottom's threshold: `C₁ (c₀ · fa + 1) ≤ (fa + a + 1)²` once `a ≥ C₁ (c₀ + 1)`.

**Proof sketch.** Then `C₁ c₀ ≤ a` and `C₁ ≤ a`, and the square's cross terms pay for both. -/
private theorem nh_bottom (C₁ c₀ fa a : ℕ) (ha : C₁ * (c₀ + 1) ≤ a) :
    C₁ * (c₀ * fa + 1) ≤ (fa + a + 1) ^ 2 := by
  have h1 : C₁ * c₀ ≤ a := by nlinarith
  have h2 : C₁ ≤ a := by nlinarith
  nlinarith [Nat.mul_le_mul_right fa h1]

/-- The middle's threshold: `C (C₁ (c₀ · f (n + 1) + 1) + 1) ≤ g n` for every large `n`.

**Proof sketch.** The left side is at most `(C C₁ (c₀ + 1) + C) · (f (n + 1) + 1)`, a ring
identity; the domination hypothesis at that constant bounds it by `g n`. -/
private theorem nh_middle {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) (C C₁ c₀ : ℕ) :
    ∃ N, ∀ n ≥ N, C * (C₁ * (c₀ * f (n + 1) + 1) + 1) ≤ g n := by
  obtain ⟨N, hN⟩ := hfg (C * C₁ * (c₀ + 1) + C)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have hid : C * (C₁ * (c₀ * f (n + 1) + 1) + 1) +
      (C * C₁ * f (n + 1) + C * f (n + 1) + C * C₁ * c₀) =
      (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := by ring
  calc C * (C₁ * (c₀ * f (n + 1) + 1) + 1)
      ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := Nat.le.intro hid
    _ ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + f n + n + 1) :=
        Nat.mul_le_mul_left _ (by omega)

/-- A late stage of a code: some stage of `α` has its bottom rung beyond `N`.

**Proof sketch.** Every code recurs at stages beyond any bound
(`Turing.NTimeDiag.stageCode_frequently`), and the ladder dominates the index
(`Turing.NTimeDiag.le_ladder`). -/
private theorem nh_stage (f : ℕ → ℕ) (α : List Bool) (N : ℕ) :
    ∃ i, N ≤ Turing.NTimeDiag.ladder f i ∧ Turing.NTimeDiag.stageCode i = α := by
  obtain ⟨i, hi, hα⟩ := Turing.NTimeDiag.stageCode_frequently α N
  exact ⟨i, by have := Turing.NTimeDiag.le_ladder f i; omega, hα⟩

/-- **Truncation at the all-branch budget.** If every branch of `N` on `x` halts within `T`, an
acceptance of `x` at any length is an acceptance within `T`.

**Proof sketch.** At a length `t ≤ T`, pad (`Turing.FinNDTM.AcceptsWithin.mono`). At `t > T`, the
accepting word runs as its length-`T` prefix, which has halted (`Turing.run_take_of_halted`, with
absorption by `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`), so it accepts. -/
private theorem nh_accepts_of_halts {N : FinNDTM Bool} {x : List Bool} {T t : ℕ}
    (hT : N.tm.HaltsWithin x T) (ht : N.AcceptsWithin x t) : N.AcceptsWithin x T := by
  rcases le_or_gt t T with hle | hlt
  · exact ht.mono hle
  · obtain ⟨w, hw, -, hout⟩ := FinNDTM.acceptsWithin_iff.mp ht
    obtain ⟨hlen, hp, hr⟩ := run_take_of_halted (fun w => N.tm.runWith w (N.tm.initCfg x))
      (fun c => c.state = none)
      (fun w w' h => by simp only [NDTM.runWith_append w w' (N.tm.initCfg x),
        NDTM.runWith_of_halt _ h])
      (NDTM.haltsWithin_iff.mp hT) (w := w) (by omega)
    exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take T, hlen, hp, hr ▸ hout⟩

/-- **A decider's language from an unbounded acceptance.** If `N` decides `L` within `T`, any
acceptance of `x`, at any length, puts `x` in `L`.

**Proof sketch.** Truncate the acceptance at `N`'s all-branch budget on `x`
(`nh_accepts_of_halts`); the decider's clause reads membership off it. -/
private theorem nh_mem_of_accepts {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (hN : N.DecidesInTime L T) {x : List Bool} (ht : ∃ t, N.AcceptsWithin x t) : x ∈ L := by
  obtain ⟨t, ht⟩ := ht
  exact ((FinNDTM.decidesInTime_iff.mp hN x).2).mpr
    (nh_accepts_of_halts (FinNDTM.decidesInTime_iff.mp hN x).1 ht)

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2]; [Coo72]): for
time-constructible `f` and `g`, if every constant multiple of `f(n+1) + f(n) + n + 1` is eventually
below `g(n)` — the book's `f(n+1) = o(g(n))` with the two addends of the module docstring — then
`NTIME f ⊊ NTIME (g + 1)`. The overhead on `f` is linear, as in the book, in contrast to the
received deterministic hierarchy's square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives `f n ≤ g n` eventually, and the
finitely many smaller lengths are absorbed into the constant (no monotonicity of `f` is needed).

*Strictness* is lazy diagonalization [AB09, proof of Theorem 3.2 and Figure 3.1]. Fix an effective
scheme `c` (`Turing.exists_effectiveNDMachineCode`) and take the diagonalizer `D` of
`Turing.NTimeDiag.exists_diagonalizer`, given the exponential decider
`Turing.exists_ndAcceptsWithin_decider`. Its language `L`, acceptance of `x` within
`K · (g |x| + 1)`, is in `NTIME (g + 1)` (`Turing.NTimeDiag.acceptLang_mem_NTIME`). Suppose `N`
decides `L` within `c₀ · f`. The linear coded normal form
(`Turing.FinNDTM.exists_codeNDTM_accepts_linear`) gives a coded machine `M'` and a constant `C₁`:
an acceptance by `N` within `t` is one by `M'` within `C₁ (t + 1)`, and an acceptance by `M'` is
one by `N` at some length. Let `C` be the diagonalizer's constant for `M'`'s code, and take a
stage `i` of that code whose bottom rung `ℓᵢ` lies beyond the three thresholds below
(`Turing.NTimeDiag.stageCode_frequently`). On unary words:
- **the middle**, for `ℓᵢ < n < ℓᵢ₊₁`: `1ⁿ ∈ L ↔ 1ⁿ⁺¹ ∈ L`. Forward, `D`'s acceptance gives
  `M'`'s within `g n`, hence `N`'s at some length; an acceptance at any length is one within
  `N`'s all-branch budget, so `1ⁿ⁺¹ ∈ L`. Backward, `N`'s acceptance within `c₀ · f (n + 1)`
  gives `M'`'s within `t' = C₁ (c₀ · f (n + 1) + 1)`, and the hypothesis puts `C (t' + 1)` below
  `g n`;
- **the chain** of these steps: `1^{ℓᵢ + 1} ∈ L ↔ 1^{ℓᵢ₊₁} ∈ L`;
- **the top**, at `n = ℓᵢ₊₁ = 2^{T*²}` with `T* = budget f ℓᵢ`: `1ⁿ ∈ L` iff `M'` does not accept
  `1^{ℓᵢ + 1}` within `T*`, since `C · 2^{C (T* + 1)} ≤ 2^{T*²}` once `T*` is large;
- **the bottom**, at `a = ℓᵢ + 1`: `M'` accepts `1ᵃ` within `T*` iff `1ᵃ ∈ L`, since
  `T* = (f a + a + 1)² ≥ C₁ (c₀ · f a + 1)` once `a ≥ C₁ (c₀ + 1)`.

Together they give `1ᵃ ∈ L ↔ 1ᵃ ∉ L`.

**Implementation.** The private lemmas before this theorem:
- the chain's induction (`nh_chain`);
- the absorption, the constant fold and the inclusion (`nh_absorb`, `nh_fold`, `nh_inclusion`);
- the three thresholds (`nh_top`, `nh_bottom`, `nh_middle`);
- a late stage of a code (`nh_stage`);
- the truncation of an acceptance at an all-branch budget (`nh_accepts_of_halts`, through
  `Turing.run_take_of_halted`), and its reading for a decider (`nh_mem_of_accepts`).

The diagonalizer and the linear coded normal form are cited as contracts. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  obtain ⟨c⟩ := exists_effectiveNDMachineCode
  obtain ⟨D, K, hhalt, hD⟩ :=
    NTimeDiag.exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)
  refine (Set.ssubset_iff_of_subset (nh_inclusion hfg)).mpr
    ⟨_, NTimeDiag.acceptLang_mem_NTIME D K g hhalt, fun hLf => ?_⟩
  set L : Language Bool := {x | D.AcceptsWithin x (K * (g x.length + 1))} with hL
  have hmemL : ∀ m, List.replicate m true ∈ L ↔
      D.AcceptsWithin (List.replicate m true) (K * (g m + 1)) := by
    intro m
    change D.AcceptsWithin (List.replicate m true)
      (K * (g (List.replicate m true).length + 1)) ↔ _
    rw [List.length_replicate]
  obtain ⟨c₀, N, hN⟩ := mem_NTIME_iff.mp hLf
  have hdec : ∀ m, List.replicate m true ∈ L →
      N.AcceptsWithin (List.replicate m true) (c₀ * f m) := by
    intro m hm
    have h := ((FinNDTM.decidesInTime_iff.mp hN (List.replicate m true)).2).mp hm
    rwa [List.length_replicate] at h
  obtain ⟨M', C₁, hfwd, hbwd⟩ := FinNDTM.exists_codeNDTM_accepts_linear N
  obtain ⟨C, hC⟩ := hD (c.encode M')
  rw [c.toNDMachineCode.decode_encode M'] at hC
  obtain ⟨N₁, hN₁⟩ := nh_middle hfg C C₁ c₀
  obtain ⟨T₀, hT₀⟩ := nh_top C
  obtain ⟨i, hi, hiα⟩ := nh_stage f (c.encode M') (N₁ + T₀ + C₁ * (c₀ + 1))
  have hℓ2 : 2 ≤ NTimeDiag.ladder f i := by have := NTimeDiag.le_ladder f i; omega
  have hlt : NTimeDiag.ladder f i < NTimeDiag.ladder f (i + 1) :=
    NTimeDiag.ladder_strictMono f (Nat.lt_succ_self i)
  -- the middle step, at every `n` with `ℓᵢ < n < ℓᵢ₊₁`
  have hmid : ∀ n, NTimeDiag.ladder f i + 1 ≤ n → n < NTimeDiag.ladder f (i + 1) →
      (List.replicate n true ∈ L ↔ List.replicate (n + 1) true ∈ L) := by
    intro n h1 h2
    have hs : NTimeDiag.stage f n = i := NTimeDiag.stage_eq f (by omega) h2.le
    obtain ⟨hmidC, -⟩ := hC n (by omega) (by rw [hs]; exact hiα)
    obtain ⟨hsound, hcompl⟩ := hmidC (by rw [hs]; omega)
    constructor
    · intro hn
      exact nh_mem_of_accepts hN (hbwd _ _ (hsound ((hmemL n).mp hn)))
    · intro hn1
      exact (hmemL n).mpr (hcompl _ (hfwd _ _ (hdec (n + 1) hn1)) (hN₁ n (by omega)))
  have hchain := nh_chain (fun m => List.replicate m true ∈ L)
    (show NTimeDiag.ladder f i + 1 ≤ NTimeDiag.ladder f (i + 1) by omega) hmid
  -- the top's flip, at `n = ℓᵢ₊₁`
  have htop : List.replicate (NTimeDiag.ladder f (i + 1)) true ∈ L ↔
      ¬M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
        (NTimeDiag.budget f (NTimeDiag.ladder f i)) := by
    have hs : NTimeDiag.stage f (NTimeDiag.ladder f (i + 1)) = i :=
      NTimeDiag.stage_eq f hlt le_rfl
    obtain ⟨-, htopC⟩ := hC (NTimeDiag.ladder f (i + 1)) (by omega) (by rw [hs]; exact hiα)
    rw [hs] at htopC
    have hTle : T₀ ≤ NTimeDiag.budget f (NTimeDiag.ladder f i) := by
      rw [NTimeDiag.budget_eq]
      calc T₀ ≤ f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1 := by omega
        _ ≤ (f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1) ^ 2 :=
          Nat.le_self_pow (by norm_num) _
    have hthr : C * 2 ^ (C * (NTimeDiag.budget f (NTimeDiag.ladder f i) + 1)) ≤
        NTimeDiag.ladder f (i + 1) := by
      rw [NTimeDiag.ladder_succ f i]
      exact hT₀ _ hTle
    rw [hmemL]
    exact htopC rfl hthr
  -- the bottom's transfer, at `a = ℓᵢ + 1` within `T*`
  have hbot : M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
      (NTimeDiag.budget f (NTimeDiag.ladder f i)) ↔
      List.replicate (NTimeDiag.ladder f i + 1) true ∈ L := by
    constructor
    · intro hM
      exact nh_mem_of_accepts hN (hbwd _ _ hM)
    · intro hx
      refine (hfwd _ _ (hdec _ hx)).mono ?_
      rw [NTimeDiag.budget_eq]
      exact nh_bottom C₁ c₀ _ _ (by omega)
  exact iff_not_self (hchain.trans (htop.trans (not_congr hbot)))

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`.

Formally, the factor `2` is absorbed into the membership witness's constant by the private
`nh_fold`, which the inclusion half of `Complexity.ntime_hierarchy` also uses. -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  have hback : NTIME (fun n => g n + 1) ⊆ NTIME g := by
    intro L hL
    have hscale : L ∈ NTIME (fun n => 2 * g n) :=
      NTIME.mono (fun n => by have := hpos n; omega) hL
    exact nh_fold 2 hscale
  have heq : NTIME (fun n => g n + 1) = NTIME g :=
    Set.Subset.antisymm hback (NTIME.mono (fun n => Nat.le_succ (g n)))
  simpa only [heq] using ntime_hierarchy hf hg hfg

/-- **The showcase separation**:
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
The two constructibility witnesses are `Complexity.timeConstructible_poly` at
`(C, c) = (1, 0)` and `(1, 1)`; domination takes `N = 3A + 4` and multiplies `N ≤ n` by `n`. -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  have hf : TimeConstructible (fun n => n + 1) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (0 + 1)) = (fun n => n + 1) := by
      funext n
      simp only [Nat.zero_add, pow_one, one_mul]
    rw [← h]
    exact timeConstructible_poly 1 0 (by decide)
  have hg : TimeConstructible (fun n => (n + 1) ^ 2) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (1 + 1)) = (fun n => (n + 1) ^ 2) := by
      funext n
      simp only [one_mul]
    rw [← h]
    exact timeConstructible_poly 1 1 (by decide)
  apply ntime_hierarchy_of_pos hf hg
  · intro n
    exact pow_pos (Nat.succ_pos n) _
  · intro A
    refine ⟨3 * A + 4, fun n hn => ?_⟩
    nlinarith [Nat.mul_le_mul_right n hn]

end Complexity

## ===== campaign/gates/100-nth-status/evidence/freeze/NTimeHierarchy-head.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.NDNormalForm
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.ClassNP.ExhaustiveReplay
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer
import TCSlib.Complexity.TuringMachine.ChoiceWords

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` is proved, from the
interpreter core `Turing.exists_ndInterpreterCore`
(`TCSlib.Complexity.TuringMachine.NDCodeSimulator`), and the exponential decider from it. The
hierarchy `Complexity.ntime_hierarchy` is proved from the diagonalizer
`Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form
`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, both proved, and the two corollaries are proved
from the hierarchy: all of them rest on the standard axioms alone.

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`; the normal form is in
  `TCSlib.Complexity.ClassNP.NDNormalForm`.

## Main results

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style), stated in
  `TCSlib.Complexity.ClassNP.NDNormalForm` (moved there, user 2026-10-17).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The universal NDTM from a setup machine.** Given, for the interpreter core's tape count
`K` and stream tape `jR`, a deterministic setup `P` that on `⟨⟨bits t, α⟩, x⟩` first reaches its
exit within `C_P·(t + 1)` steps with a block of exactly `t` nonblank cells on the core's stream
tape from cell `0`, every other tape blank, every head at the origin, the input head at `1` and
empty output, the guess-then-run assembly over the interpreter core is a universal NDTM at
linear overhead.

**Proof sketch.** Take the core `R` of `Turing.exists_ndInterpreterCore` and the setup `P`; the
universal machine is `Turing.guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej`.
For each stream `s` of length `t`, the core reaches its verdict within `C_R·(t + 1)` from
`streamStartCfg` (assembled from its field equations), so `Turing.guessRunTM_silent_spec` gives
halting within `T_P + 2t + C_R·(t + 1) + 11 ≤ (C_P + C_R + 13)·(t + 1)` on every branch, and
acceptance iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.acceptsWithin_iff`). -/
private theorem un_universal_of_setup (c : EffectiveNDMachineCode)
    (hsetup : ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
      cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
        (P : MultiTapeTM k Bool SP) (pexit : SP),
        ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
          ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
            (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
            P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
              ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
            ∀ u < TP,
              (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
                some pexit) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  obtain ⟨K, SR, hfin, hdec, R, jR, entry, acc, rej, hne, hR⟩ := exists_ndInterpreterCore c
  obtain ⟨k, ι, cap, hcap, SP, hfinP, hdecP, P, pexit, hP⟩ := hsetup K jR
  refine ⟨⟨k, Σ i, GuessRunPhase.State SP SR i,
    guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej⟩, fun α => ?_⟩
  obtain ⟨CR, hCR⟩ := hR α
  obtain ⟨CP, hCP⟩ := hP α
  refine ⟨CP + CR + 13, fun x t => ?_⟩
  obtain ⟨TP, hTP, blk, hblk, hrun, hfirst⟩ := hCP x t
  -- the core's verdict on every stream of length `t`
  have hcore : ∀ s : List Bool, s.length = t → ∃ T, T ≤ CR * (t + 1) ∧
      (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s) T).state
        = some (if ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).state = none ∧
            ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).output = [true] then acc else rej) ∧
      ∀ u < T,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, -, hT, hst, hno⟩ := hCR x t s (by omega)
    rw [List.take_of_length_le (by omega)] at hst
    have hss : streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s =
        ⟨some entry, 1, fun i => if i = jR then FinTM.bufferTape s else fun _ => none,
          fun _ => 0, []⟩ :=
      Cfg.ext (streamStartCfg_state _ _ _ _) (streamStartCfg_inputPos _ _ _ _)
        (funext fun i => funext fun a => streamStartCfg_workTapes _ _ _ _ i a)
        (funext fun i => streamStartCfg_workTapePos _ _ _ _ i) (streamStartCfg_output _ _ _ _)
    rw [hss]
    exact ⟨T, hT, hst, hno⟩
  have hR' : ∀ s : List Bool, s.length = t → ∃ TR ≤ CR * (t + 1),
      ((R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some acc ∨
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some rej) ∧
      ∀ u < TR,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, hT, hst, hno⟩ := hcore s hs
    refine ⟨T, hT, ?_, hno⟩
    rw [hst]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hspec := guessRunTM_silent_spec ι cap hcap jR R entry acc rej P pexit TP t blk hblk hrun
    hfirst (CR * (t + 1)) hR'
  have hbud : TP + 2 * t + CR * (t + 1) + 11 ≤ (CP + CR + 13) * (t + 1) := by
    have e : (CP + CR + 13) * (t + 1) = CP * (t + 1) + CR * (t + 1) + 13 * (t + 1) := by
      rw [Nat.add_mul, Nat.add_mul]
    rw [e]
    generalize CP * (t + 1) = a at hTP ⊢
    generalize CR * (t + 1) = b
    omega
  refine ⟨hspec.1.mono hbud, FinNDTM.acceptsWithin_iff.trans ((hspec.2 _ hbud).trans ?_)⟩
  rw [FinNDTM.acceptsWithin_iff]
  constructor
  · rintro ⟨s, hs, TR, hacc, hf⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    have hTR : TR = T := by
      by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact (hno TR h).1 hacc
      · have h' := hf T h
        rw [hst] at h'
        split_ifs at h' with hc
        · exact h'.1 rfl
        · exact h'.2 rfl
    subst hTR
    rw [hst] at hacc
    split_ifs at hacc with hcond
    · exact ⟨s, hs, hcond.1, hcond.2⟩
    · exact absurd (Option.some.inj hacc).symm hne
  · rintro ⟨s, hs, hhalt, hout⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    exact ⟨s, hs, T, by rw [hst, if_pos ⟨hhalt, hout⟩], hno⟩

/-! ### The setup machine's pieces

`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup
hypothesis. The setup built below is a seam chain over `K + kC + 1` tapes — the core's `K`, the
embedded header composite's `kC`, and the capture/counter tape last — whose phases are the
embedded header pass, the code buffer's rewind and clear, a guided erase of the extractor scratch
bank, the expansion of the captured budget word into the unary block, the block rewind, the
counter clear, and the input rewind (`Turing.inputRewindTM`, imported). The pieces here are the
guided bank-erase leaf with its framed run, the seam-step composer, the header composite's exact
first halt, and two small word facts. -/

/-- Flattening `t` copies of the one-symbol pattern gives the length-`t` unary block. -/
private lemma un_flatten (t : ℕ) :
    (List.replicate t [true]).flatten = List.replicate t true := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, ih]

/-- A buffered word is blank at and beyond its length. -/
private lemma un_buffer_ge (w : List Bool) (q : ℤ) (hq : (w.length : ℤ) ≤ q) :
    FinTM.bufferTape w q = none := by
  have h0 : 0 ≤ q := le_trans (Int.natCast_nonneg _) hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [FinTM.bufferTape_nat]
  exact List.getElem?_eq_none (by exact_mod_cast hq)

/-- **The header composite's exact first halt**, uniformly in the input suffix: the buffered
composite of the prefix parser and the first-component extractor, on
`pairEncode (pairEncode a b) x`, halts at exactly `3·|pairEncode a b| + 4 + (4·|a| + 5)` and is
live before.

**Proof sketch.** `Turing.prefixCanon_run` at the extractor's halting time, read through
`Turing.prefixCanonTM_eq` and `Turing.FinTM.pairExtractTM_fst_run`, gives the halt. Before the
parser's `3·|pairEncode a b| + 4` steps the run is live by `Turing.prefixCanon_start`; after
them it is the extractor's run, live before its own halt. -/
private theorem un_canon_halt (a b x : List Bool) :
    ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
          (pairEncode (pairEncode a b) x))
        (3 * (pairEncode a b).length + 4 + (4 * a.length + 5))).state = none ∧
      ∀ v < 3 * (pairEncode a b).length + 4 + (4 * a.length + 5),
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
            (pairEncode (pairEncode a b) x)) v).state ≠ none := by
  obtain ⟨hrun, hlive⟩ := FinTM.pairExtractTM_fst_run a b
  constructor
  · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
      (4 * a.length + 5)
    simp only [prefixCanonTM_eq] at hb
    rw [hb, FinTM.bufferedSecondCfg_state, hrun]
    rfl
  · intro v hv
    by_cases hpre : v < 3 * (pairEncode a b).length + 4
    · have hs := prefixCanon_start (FinTM.pairExtractTM true false) (pairEncode a b) x
      simp only [prefixCanonTM_eq] at hs
      refine MultiTapeTM.runFrom_state_ne_none_of_le _ _
        (3 * (pairEncode a b).length + 4) ?_ v (by omega)
      rw [hs, FinTM.bufferedSecondCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact fun h => Option.noConfusion h
    · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
        (v - (3 * (pairEncode a b).length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * (pairEncode a b).length + 4 ≤ v)] at hb
      rw [hb, FinTM.bufferedSecondCfg_state]
      intro h
      refine hlive (v - (3 * (pairEncode a b).length + 4)) (by omega) ?_
      cases hstv : ((FinTM.pairExtractTM true false).tm.runFrom
          ((FinTM.pairExtractTM true false).tm.initCfg (pairEncode a b))
          (v - (3 * (pairEncode a b).length + 4))).state with
      | none => rfl
      | some q =>
        rw [hstv] at h
        exact Option.noConfusion h

/-- The bank erase's one action: blank the selected tapes and move them with the guide. -/
private def un_bankAct (k : ℕ) (S : Finset (Fin k)) (g : Fin k) (m : SignType) (q' : Fin 3) :
    Action k Bool (Fin 3) :=
  ⟨0, fun i => if i ∈ S then (some none, m) else if i = g then (none, m) else (none, 0),
    none, some q'⟩

private lemma un_bankAct_eq {k : ℕ} (S : Finset (Fin k)) (g : Fin k) (m : SignType)
    (q' : Fin 3) (i : Fin k) :
    ((un_bankAct k S g m q').workTapes i).1 = (if i ∈ S then some none else none) ∧
      (((un_bankAct k S g m q').workTapes i).2 : ℤ) =
        if i ∈ S ∨ i = g then (m : ℤ) else 0 := by
  by_cases hiS : i ∈ S
  · simp [un_bankAct, hiS]
  · by_cases hig : i = g
    · subst hig; simp [un_bankAct, hiS]
    · simp [un_bankAct, hiS, hig]

/-- **The guided bank erase**: one unconditional left step, a left sweep that blanks every
selected tape while the guide tape still shows a symbol under the travelling head, and one
step right into the live park. The guide's head travels with the bank, and when the guide is not
one of the selected tapes its word is kept; every other tape, every other head, the input head and
the output are untouched. -/
private def un_bankTM (k : ℕ) (S : Finset (Fin k)) (g : Fin k) :
    MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr := fun q _ w =>
    if q = 0 then un_bankAct k S g .neg 1
    else if q = 1 then
      match w g with
      | some _ => un_bankAct k S g .neg 1
      | none => un_bankAct k S g .pos 2
    else ⟨0, fun _ => (none, 0), none, some 2⟩

/-- **The guided bank erase, framed.** Take a guide outside the selected bank, and start with
every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks at exactly `L + 2` and not earlier, with the bank blank, the bank and guide heads at the
origin, the guide's word and everything else unchanged.

**Proof sketch.** After `r ≤ L + 1` steps the selected cells right of `L − r` are blank and the
bank and guide heads are at `L − r`, by induction on `r`: the first step is unconditional, and
for `1 ≤ r ≤ L` the guide still reads a symbol of its word. At `L + 1` the guide reads the blank
left of its word, so the last step moves right into the park; before it the state is `0` or
`1`. -/
private theorem un_bank_run {k : ℕ} {z : List Bool} (S : Finset (Fin k)) (g : Fin k)
    (hg : g ∉ S) (L : ℕ) (w : Fin k → List Bool)
    (hw : ∀ i, i ∈ S ∨ i = g → (w i).length = L)
    (d : Cfg k Bool (Fin 3) z) (hstate : d.state = some 0)
    (htape : ∀ i, i ∈ S ∨ i = g → d.workTapes i = FinTM.bufferTape (w i))
    (hpos : ∀ i, i ∈ S ∨ i = g → d.workTapePos i = (L : ℤ)) :
    (un_bankTM k S g).runFrom d (L + 2) =
        { d with
          state := some 2
          workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
          workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } ∧
      ∀ t < L + 2, ((un_bankTM k S g).runFrom d t).state ≠ some 2 := by
  classical
  -- the sweep's trajectory
  let T : ℕ → Cfg k Bool (Fin 3) z := fun r =>
    { d with
      state := some (if r = 0 then 0 else 1)
      workTapes := fun i =>
        if i ∈ S then (fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q)
        else d.workTapes i
      workTapePos := fun i => if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i }
  have hT0 : T 0 = d := by
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · show some (if 0 = 0 then (0 : Fin 3) else 1) = d.state
      rw [if_pos rfl, hstate]
    · funext i q
      show (if i ∈ S then (fun q => if (L : ℤ) - (0 : ℕ) < q then none
          else FinTM.bufferTape (w i) q) else d.workTapes i) q = d.workTapes i q
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, htape i (Or.inl hiS)]
        by_cases hq : (L : ℤ) - (0 : ℕ) < q
        · rw [if_pos hq, eq_comm]
          exact un_buffer_ge _ _ (by rw [hw i (Or.inl hiS)]; push_cast at hq ⊢; omega)
        · rw [if_neg hq]
      · rw [if_neg hiS]
    · funext i
      show (if i ∈ S ∨ i = g then (L : ℤ) - (0 : ℕ) else d.workTapePos i) = d.workTapePos i
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, hpos i hig]
        omega
      · rw [if_neg hig]
  -- one erasing step of the sweep
  have happly : ∀ r : ℕ, r ≤ L →
      (un_bankAct k S g .neg 1).apply (T r) = T (r + 1) := by
    intro r hr
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      show some 1 = some (if r + 1 = 0 then (0 : Fin 3) else 1)
      rw [if_neg (Nat.succ_ne_zero r)]
    · rw [Action.apply_inputPos]
      show moveInputPos (T r).inputPos (un_bankAct k S g .neg 1).inputTape = (T (r + 1)).inputPos
      rw [show (un_bankAct k S g .neg 1).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .neg 1 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        funext q
        rw [Function.update_apply]
        have hps : (T r).workTapePos i = (L : ℤ) - r := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        have htp : (T r).workTapes i =
            fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have htp' : (T (r + 1)).workTapes i =
            fun q => if (L : ℤ) - (r + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        rw [hps, htp, htp']
        dsimp only
        by_cases hq : q = (L : ℤ) - r
        · rw [if_pos hq, eq_comm,
            if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast; omega)]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - r < q
          · rw [if_pos hql,
              if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast at hql ⊢; omega)]
          · rw [if_neg hql, if_neg (show ¬((L : ℤ) - (r + 1 : ℕ) < q) by
              push_cast at hq hql ⊢; omega)]
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T r).workTapes i = (T (r + 1)).workTapes i
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .neg 1 i).2
      show (T r).workTapePos i + (((un_bankAct k S g .neg 1).workTapes i).2 : ℤ) =
        (T (r + 1)).workTapePos i
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) + _ =
        (if i ∈ S ∨ i = g then (L : ℤ) - (r + 1 : ℕ) else d.workTapePos i)
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.neg_eq_neg_one, SignType.coe_neg_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T r).output ++ (none : Option Bool).toList = (T (r + 1)).output
      rw [Option.toList_none, List.append_nil]
  have hstep : ∀ r : ℕ, r ≤ L → (un_bankTM k S g).step (T r) = T (r + 1) := by
    intro r hr
    have hs : (T r).state = some (if r = 0 then 0 else 1) := rfl
    rw [MultiTapeTM.step_of_some hs]
    have htr : (un_bankTM k S g).tr (if r = 0 then 0 else 1) (T r).inputSymbol
        (T r).workTapeSymbols = un_bankAct k S g .neg 1 := by
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        simp only [un_bankTM, ↓reduceIte]
      · rw [if_neg hr0]
        have hread : (T r).workTapeSymbols g =
            FinTM.bufferTape (w g) ((L : ℤ) - r) := by
          rw [Cfg.workTapeSymbols_eq]
          have h1 : (T r).workTapes g = FinTM.bufferTape (w g) := by
            show (if g ∈ S then _ else d.workTapes g) = _
            rw [if_neg hg, htape g (Or.inr rfl)]
          have h2 : (T r).workTapePos g = (L : ℤ) - r := by
            show (if g ∈ S ∨ g = g then (L : ℤ) - r else d.workTapePos g) = _
            rw [if_pos (Or.inr rfl)]
          rw [h1, h2]
        have hsome : ∃ b, FinTM.bufferTape (w g) ((L : ℤ) - r) = some b := by
          have hlt : L - r < (w g).length := by rw [hw g (Or.inr rfl)]; omega
          refine ⟨(w g)[L - r], ?_⟩
          rw [show (L : ℤ) - r = ((L - r : ℕ) : ℤ) by omega,
            FinTM.bufferTape_nat, List.getElem?_eq_getElem hlt]
        obtain ⟨b, hb⟩ := hsome
        simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
        rw [hread, hb]
    rw [htr]
    exact happly r hr
  have hrun : ∀ r : ℕ, r ≤ L + 1 → (un_bankTM k S g).runFrom d r = T r := by
    intro r hr
    induction r with
    | zero => rw [MultiTapeTM.runFrom_zero, hT0]
    | succ r ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep r (by omega)]
  -- the final turning step
  have hfinal : (un_bankTM k S g).step (T (L + 1)) =
      { d with
        state := some 2
        workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
        workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } := by
    have hs : (T (L + 1)).state = some 1 := by
      show some (if L + 1 = 0 then (0 : Fin 3) else 1) = some 1
      rw [if_neg (Nat.succ_ne_zero L)]
    rw [MultiTapeTM.step_of_some hs]
    have hread : (T (L + 1)).workTapeSymbols g = none := by
      rw [Cfg.workTapeSymbols_eq]
      have h1 : (T (L + 1)).workTapes g = FinTM.bufferTape (w g) := by
        show (if g ∈ S then _ else d.workTapes g) = _
        rw [if_neg hg, htape g (Or.inr rfl)]
      have h2 : (T (L + 1)).workTapePos g = (L : ℤ) - (L + 1 : ℕ) := by
        show (if g ∈ S ∨ g = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos g) = _
        rw [if_pos (Or.inr rfl)]
      rw [h1, h2]
      exact FinTM.bufferTape_of_neg _ (by push_cast; omega)
    have htr : (un_bankTM k S g).tr 1 (T (L + 1)).inputSymbol (T (L + 1)).workTapeSymbols =
        un_bankAct k S g .pos 2 := by
      simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
      rw [hread]
    rw [htr]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      rfl
    · rw [Action.apply_inputPos]
      rw [show (un_bankAct k S g .pos 2).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .pos 2 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        show Function.update ((T (L + 1)).workTapes i) ((T (L + 1)).workTapePos i) none =
          (if i ∈ S then (fun _ => none) else d.workTapes i)
        rw [if_pos hiS]
        have htp : (T (L + 1)).workTapes i =
            fun q => if (L : ℤ) - (L + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have hps : (T (L + 1)).workTapePos i = (L : ℤ) - (L + 1 : ℕ) := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        rw [htp, hps]
        funext q
        rw [Function.update_apply]
        try dsimp only
        by_cases hq : q = (L : ℤ) - (L + 1 : ℕ)
        · rw [if_pos hq]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - (L + 1 : ℕ) < q
          · rw [if_pos hql]
          · rw [if_neg hql]
            exact FinTM.bufferTape_of_neg _ (by push_cast at hql ⊢; omega)
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T (L + 1)).workTapes i = (if i ∈ S then _ else d.workTapes i)
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .pos 2 i).2
      show (T (L + 1)).workTapePos i + (((un_bankAct k S g .pos 2).workTapes i).2 : ℤ) =
        (if i ∈ S ∨ i = g then 0 else d.workTapePos i)
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) + _ = _
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.pos_eq_one, SignType.coe_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T (L + 1)).output ++ (none : Option Bool).toList = d.output
      rw [Option.toList_none, List.append_nil]
  constructor
  · rw [show L + 2 = (L + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      hrun (L + 1) le_rfl, hfinal]
  · intro t ht
    rw [hrun t (by omega)]
    show some (if t = 0 then (0 : Fin 3) else 1) ≠ some 2
    by_cases ht0 : t = 0
    · rw [if_pos ht0]; decide
    · rw [if_neg ht0]; decide

/-- One seam step whose previous endpoint arrives as a right-tagged configuration: the
handover's constant relabeling collapses the tag, so the next phase's framed run applies
verbatim. -/
private theorem un_step' {k : ℕ} {S₀ S₁ S₂ : Type} [DecidableEq S₁] {z : List Bool}
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (q₂ : S₂) (g : S₀ → S₁) {c₀ : Cfg k Bool S₁ z} {c₂ : Cfg k Bool S₀ z}
    {c₃ : Cfg k Bool S₂ z} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₂.mapState g) (hexit : (c₂.mapState g).state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₂.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂, (M₂.runFrom (c₂.mapState fun _ => entry) t).state ≠ some q₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₃.mapState Sum.inr ∧
      (c₃.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr q₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr q₂) := by
  have hcomp : (c₂.mapState g).mapState (fun _ => entry) = c₂.mapState fun _ => entry := by
    rw [Cfg.mapState_mapState]; rfl
  exact seamCompTM_step M₁ exit M₂ entry q₂ h₁ hexit hcut (by rw [hcomp]; exact h₂) hq
    (fun t ht => by rw [hcomp] at *; exact hcut₂ t ht)

/-- **The setup machine.** For the interpreter core's tape count `K` and stream tape `jR`,
the seam chain over `K + kC + 1` tapes — the embedded header pass, the code buffer's rewind
and clear, the guided bank erase, the expansion, the block rewind, the counter clear, and the
input rewind — first reaches its park at the setup hypothesis's exit configuration, within a
per-code linear budget.

**Proof sketch.** The header composite halts at `3|u| + 4 + (4|bits t| + 5)` with the code
buffer `u`, the extractor scratch `bits t` and the captured budget word `bits t` on `cap`
(`Turing.prefixCanon_run`, `Turing.FinTM.pairExtractTM_fst_run`, the cast pair and the
tape-block projections, through `Turing.embedSilentRetTM_run`). The buffer rewind and clear
blank the code buffer; the guided bank erase blanks the extractor scratch while rewinding the
capture head; the expansion writes the `t`-cell block on `ι jR` (`Turing.expandTM_run_ofCfg`,
`Turing.counterValue_bits`); the block rewind, the counter clear and the input rewind reach
the exit configuration. Each seam inherits the first-visit cut, and the ledger is linear by
`Turing.counterOverhead_le` and `Turing.length_bits_le_self`. -/
private theorem un_setup :
    ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
    cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
      (P : MultiTapeTM k Bool SP) (pexit : SP),
      ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
        ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
          (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
          P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
            ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
          ∀ u < TP,
            (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
              some pexit := by
  classical
  intro K jR
  set F : FinTM Bool := FinTM.pairExtractTM true false with hF
  set MC : FinTM Bool := FinTM.bufferedCompTM universalPrefixTM F with hMC
  have hkC : MC.k = universalPrefixTM.k + (1 + F.k) := FinTM.bufferedCompTM_k universalPrefixTM F
  have hup : universalPrefixTM.k = 0 := universalPrefixTM_k
  -- the tape layout: the core's `K`, the composite's `MC.k`, the capture/counter tape last
  let ι : Fin K ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.castAdd MC.k j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_castAdd] at hv
      exact Fin.ext hv⟩
  let ιC : Fin MC.k ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.natAdd K j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_natAdd] at hv
      exact Fin.ext (by omega)⟩
  let cap : Fin (K + MC.k + 1) := Fin.last (K + MC.k)
  have hvι : ∀ j : Fin K, (ι j).val = j.val := fun j => by
    simp [ι, Fin.coe_castSucc, Fin.coe_castAdd]
  have hvιC : ∀ j : Fin MC.k, (ιC j).val = K + j.val := fun j => by
    simp [ιC, Fin.coe_castSucc, Fin.coe_natAdd]
  have hvcap : cap.val = K + MC.k := Fin.val_last _
  have hcapr : cap ∉ Set.range ι := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvι j, hvcap] at hv
    have := j.isLt
    omega
  have hcaprC : cap ∉ Set.range ιC := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvιC j, hvcap] at hv
    have := j.isLt
    omega
  -- the composite's buffer and extractor coordinates, and their images
  let jBuf : Fin MC.k := Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0))
  let jEx : Fin F.k → Fin MC.k := fun e =>
    Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e))
  let iBuf : Fin (K + MC.k + 1) := ιC jBuf
  let iEx : Fin F.k → Fin (K + MC.k + 1) := fun e => ιC (jEx e)
  let Sx : Finset (Fin (K + MC.k + 1)) := Finset.univ.image iEx
  have hvjBuf : jBuf.val = 0 := by
    simp only [jBuf, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, hup, Fin.val_eq_zero, add_zero]
  have hvjEx : ∀ e : Fin F.k, (jEx e).val = 1 + e.val := fun e => by
    simp only [jEx, Fin.coe_cast, Fin.coe_natAdd, hup, zero_add]
  have hviBuf : iBuf.val = K := by rw [hvιC, hvjBuf]; omega
  have hviEx : ∀ e : Fin F.k, (iEx e).val = K + 1 + e.val := fun e => by
    rw [hvιC, hvjEx]
    omega
  have hSx : ∀ i, i ∈ Sx ↔ ∃ e : Fin F.k, iEx e = i := fun i => by
    constructor
    · intro hi
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp hi
      exact ⟨e, he⟩
    · rintro ⟨e, he⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩
  have hSxval : ∀ i ∈ Sx, ∃ e : Fin F.k, i.val = K + 1 + e.val := by
    intro i hi
    obtain ⟨e, he⟩ := (hSx i).mp hi
    exact ⟨e, by rw [← he, hviEx]⟩
  have hBufSx : iBuf ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval iBuf hi
    rw [hviBuf] at he
    omega
  have hcapSx : cap ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval cap hi
    rw [hvcap] at he
    have := e.isLt
    omega
  have hBufcap : iBuf ≠ cap := by
    intro h
    have hv := congrArg Fin.val h
    rw [hviBuf, hvcap] at hv
    omega
  have hιBuf : ∀ j : Fin K, ι j ≠ iBuf := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hviBuf] at hv
    have := j.isLt
    omega
  have hιcap : ∀ j : Fin K, ι j ≠ cap := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hvcap] at hv
    have := j.isLt
    omega
  have hιSx : ∀ j : Fin K, ι j ∉ Sx := by
    intro j hi
    obtain ⟨e, he⟩ := hSxval (ι j) hi
    rw [hvι] at he
    have := j.isLt
    omega
  -- the block coordinate inside the expansion's body bank
  let iBlkb : Fin (K + MC.k) := Fin.castAdd MC.k jR
  have hblk_eq : ι jR = iBlkb.castSucc := rfl
  -- the phase machines
  let A1 : MultiTapeTM (K + MC.k + 1) Bool (MC.State ⊕ Unit) := embedSilentRetTM ιC cap MC.tm
  let A2 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) iBuf
  let A3 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) iBuf
  let A4 : MultiTapeTM (K + MC.k + 1) Bool (Fin 3) := un_bankTM (K + MC.k + 1) Sx cap
  let A5 : MultiTapeTM (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) :=
    expandTM (K + MC.k) iBlkb [true]
  let A6 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) (ι jR)
  let A7 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) cap
  let A8 : MultiTapeTM (K + MC.k + 1) Bool InputRewindPhase := inputRewindTM (K + MC.k + 1)
  -- the seam chain and its start override
  let R2 := seamCompTM A1 (Sum.inr ()) A2 RewindPhase.start
  let R3 := seamCompTM R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep
  let R4 := seamCompTM R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3)
  let R5 := seamCompTM R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
  let R6 := seamCompTM R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
  let R7 := seamCompTM R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep
  let R8 := seamCompTM R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
  let P := { R8 with q₀ := (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl
    (Sum.inl MC.tm.q₀))))))))}
  refine ⟨K + MC.k + 1, ι, cap, hcapr, _, inferInstance, inferInstance, P,
    Sum.inr InputRewindPhase.done, fun α => ?_⟩
  refine ⟨7 * α.length + 130, fun x t => ?_⟩
  set bt : List Bool := Nat.bits t with hbt
  set u : List Bool := pairEncode bt α with hu
  set z : List Bool := pairEncode u x with hz
  have hul : u.length = 2 * bt.length + 2 + α.length := by rw [hu, length_pairEncode]
  have hzl : z.length = 2 * u.length + 2 + x.length := by rw [hz, length_pairEncode]
  have hbtt : bt.length ≤ t := length_bits_le_self t
  -- the junction ledgers
  let ip23 : Fin (z.length + 2) := ⟨2 * u.length + 3, by omega⟩
  let tp1 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = iBuf then FinTM.bufferTape u
    else if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let hd1 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = iBuf then (2 * bt.length + 2 : ℤ)
    else if i = cap then (bt.length : ℤ)
    else if i ∈ Sx then (bt.length : ℤ)
    else 0
  let hd2 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0
  let tp3 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let tp4 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt else fun _ => none
  let capW : ℤ → Option Bool := fun q =>
    if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q
  let blk : ℤ → Option Bool := FinTM.bufferTape (List.replicate t true)
  let tp5 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then capW else if i = ι jR then blk else fun _ => none
  let hd5 : Fin (K + MC.k + 1) → ℤ := fun i => if i = ι jR then (t : ℤ) else 0
  let tp7 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = ι jR then blk else fun _ => none
  -- the junction configurations
  let E1 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    ⟨some (Sum.inr ()), ip23, tp1, hd1, []⟩
  let E2 : Cfg (K + MC.k + 1) Bool RewindPhase z := ⟨some RewindPhase.done, ip23, tp1, hd2, []⟩
  let E3 : Cfg (K + MC.k + 1) Bool SweepPhase z := ⟨some SweepPhase.done, ip23, tp3, hd2, []⟩
  let E4 : Cfg (K + MC.k + 1) Bool (Fin 3) z := ⟨some 2, ip23, tp4, fun _ => 0, []⟩
  let E5 : Cfg (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) z :=
    ⟨some CounterLoopState.done, ip23, tp5, hd5, []⟩
  let E6 : Cfg (K + MC.k + 1) Bool RewindPhase z :=
    ⟨some RewindPhase.done, ip23, tp5, fun _ => 0, []⟩
  let E7 : Cfg (K + MC.k + 1) Bool SweepPhase z :=
    ⟨some SweepPhase.done, ip23, tp7, fun _ => 0, []⟩
  let E8 : Cfg (K + MC.k + 1) Bool InputRewindPhase z := ⟨some .done, 1, tp7, fun _ => 0, []⟩
  -- the phase times
  let T1 : ℕ := 3 * u.length + 4 + (4 * bt.length + 5)
  let T2 : ℕ := 2 * bt.length + 2 + 2
  let T3 : ℕ := 2 * u.length + 2
  let T4 : ℕ := bt.length + 2
  let T5 : ℕ := t * ([true].length + 1) + counterOverhead bt (t + 1)
  let T6 : ℕ := t + 2
  let T7 : ℕ := 2 * bt.length + 2
  let T8 : ℕ := 2 * u.length + 3 + 1
  -- phase 1: the embedded header pass with its capture
  let c0 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)).mapState
      Sum.inl
  have hs1 : A1.runFrom c0 T1 = E1 ∧ E1.state = some (Sum.inr ()) ∧
      ∀ v < T1, (A1.runFrom c0 v).state ≠ some (Sum.inr ()) := by
    obtain ⟨hhalt, hlive⟩ := un_canon_halt bt α x
    rw [← hF, ← hMC, ← hu, ← hz] at hhalt hlive
    have hc0' : (MC.tm.initCfg z).state ≠ none := by
      rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact Option.some_ne_none _
    obtain ⟨hlock, hend, hcut1⟩ := embedSilentRetTM_run ιC cap hcaprC MC.tm
      (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)
      (3 * u.length + 4 + (4 * bt.length + 5)) hc0' hlive hhalt
    -- the composite's halting configuration, read through the cast pair
    obtain ⟨b', hb⟩ := prefixCanon_run F u x (4 * bt.length + 5)
    simp only [prefixCanonTM_eq] at hb
    have hextr2 : F.tm.runFrom (F.tm.initCfg u) (4 * bt.length + 5) =
        (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
          fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) :=
      (FinTM.pairExtractTM_fst_run bt α).1
    rw [hextr2] at hb
    obtain ⟨fr1, fr2, hbM⟩ : ∃ fr1 fr2,
        MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) =
          FinTM.bufferedSecondCfg universalPrefixTM F
            (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
              fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) b'
            ⟨2 * u.length + 3, by omega⟩ fr1 fr2 := ⟨_, _, hb⟩
    set CC : Cfg MC.k Bool MC.State z :=
      MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) with hCC
    -- the embedded endpoint's fields
    have hip : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).inputPos =
        ip23 := by
      rw [embedSilentCfg_inputPos, hbM, FinTM.bufferedSecondCfg_inputPos]
    have hout : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).output = [] :=
      embedSilentCfg_output ιC cap _ _ [] [] CC
    have hcBuf : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) jBuf =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0) := by
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjBuf]
      simp [Fin.coe_natAdd, Fin.coe_castAdd, hup]
    have hcEx : ∀ e : Fin F.k, Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) (jEx e) =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e) := by
      intro e
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjEx]
      simp only [Fin.coe_natAdd, hup, zero_add]
    have hnr : ∀ i : Fin (K + MC.k + 1), i ≠ iBuf → i ∉ Sx → i ∉ Set.range ιC := by
      intro i hib hiS
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      rw [hvιC] at hv
      have hjlt : j.val < 1 + F.k := by
        have h := j.isLt
        omega
      by_cases hj0 : j.val = 0
      · exact hib (by rw [← hj, show j = jBuf from Fin.ext (by rw [hvjBuf]; exact hj0)])
      · refine hiS ((hSx i).mpr ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩)
        rw [hviEx]
        show K + 1 + (j.val - 1) = i.val
        omega
    have htap : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapes i
        = tp1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapes jBuf = FinTM.bufferTape u := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcBuf, FinTM.tapeBlocks_buffer]
        refine h1.trans (h2.trans ?_)
        show _ = tp1 iBuf
        show _ = (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).1
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then FinTM.bufferTape u else if cap = cap then
            FinTM.bufferTape bt else if cap ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapes (jEx e) = FinTM.bufferTape bt := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then FinTM.bufferTape u else if iEx e = cap then
              FinTM.bufferTape bt else if iEx e ∈ Sx then FinTM.bufferTape bt
              else fun _ => none)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).1
            refine h1.trans ?_
            show _ = (if i = iBuf then FinTM.bufferTape u else if i = cap then
              FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    have hhd : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapePos i
        = hd1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapePos jBuf = (2 * bt.length + 2 : ℤ) := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcBuf, FinTM.tapeBlocks_buffer]
          push_cast
          ring
        refine h1.trans (h2.trans ?_)
        show _ = (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
          (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).2
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then (2 * bt.length + 2 : ℤ) else if cap = cap then
            (bt.length : ℤ) else if cap ∈ Sx then (bt.length : ℤ) else 0)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapePos (jEx e) = (bt.length : ℤ) := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then (2 * bt.length + 2 : ℤ) else if iEx e = cap then
              (bt.length : ℤ) else if iEx e ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).2
            refine h1.trans ?_
            show _ = (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
              (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    exact ⟨hend.trans (Cfg.ext rfl hip (funext htap) (funext hhd) hout), rfl, hcut1⟩
  -- phase 2: rewind the code buffer's head to the word start
  have hs2 : A2.runFrom (E1.mapState fun _ => RewindPhase.start) T2 = E2 ∧
      E2.state = some RewindPhase.done ∧
      ∀ v < T2, (A2.runFrom (E1.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E1.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((2 * bt.length + 2 : ℕ) : ℤ) →
        (E1.mapState fun _ => RewindPhase.start).workTapes iBuf
          ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
            (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      show tp1 iBuf (hd1 iBuf - (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          ((if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
              (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      rw [if_pos rfl, if_pos rfl]
      congr 1
      push_cast
      ring
    obtain ⟨hrun2, hcut2, -⟩ := rewindTM_run_ofCfg iBuf u (2 * bt.length + 2)
      (by omega) (E1.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun2.trans ?_, rfl, hcut2⟩
    refine Cfg.ext rfl ?_ ?_ ?_ ?_
    · exact Cfg.mapState_inputPos (fun _ => RewindPhase.start) E1
    · funext i q
      exact Cfg.mapState_workTapes (fun _ => RewindPhase.start) E1 i q
    · funext i
      show Function.update (E1.mapState fun _ => RewindPhase.start).workTapePos iBuf
        ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
          ((2 * bt.length + 2 : ℕ) : ℤ)) i = E2.workTapePos i
      rw [Function.update_apply]
      by_cases hib : i = iBuf
      · rw [if_pos hib, hib, Cfg.mapState_workTapePos]
        show hd1 iBuf - (2 * bt.length + 2 : ℕ) = hd2 iBuf
        show (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
            (2 * bt.length + 2 : ℕ) =
          (if iBuf = cap then (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl, if_neg hBufcap, if_neg hBufSx]
        push_cast
        ring
      · rw [if_neg hib, Cfg.mapState_workTapePos]
        show hd1 i = hd2 i
        show (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
            (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
          (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_neg hib]
    · exact Cfg.mapState_output (fun _ => RewindPhase.start) E1
  -- phase 3: clear the code buffer
  have hs3 : A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) T3 = E3 ∧
      E3.state = some SweepPhase.done ∧
      ∀ v < T3, (A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E2.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf = 0 := by
      rw [Cfg.mapState_workTapePos]
      show (if iBuf = cap then (bt.length : ℤ)
        else if iBuf ∈ Sx then (bt.length : ℤ) else 0) = 0
      rw [if_neg hBufcap, if_neg hBufSx]
    have htp : ∀ q', (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf q' =
        FinTM.bufferTape u q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then FinTM.bufferTape bt
        else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none) q' =
        FinTM.bufferTape u q'
      rw [if_pos rfl]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
        (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf
          ((E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf + p) =
          FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add]
    obtain ⟨hrun3, hcut3, -⟩ := clearTM_run_ofCfg iBuf u (E2.mapState fun _ => SweepPhase.sweep)
      hst hhw
    refine ⟨hrun3.trans ?_, rfl, hcut3⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E2) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E2 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E2)
    funext i q
    show (if i = iBuf ∧ (E2.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E2.mapState fun _ => SweepPhase.sweep).workTapePos i + (u.length : ℤ) then none
      else (E2.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp3 i q
    by_cases hib : i = iBuf
    · rw [hib, hps, htp]
      have htp3 : tp3 iBuf q = none := by
        show (if iBuf = cap then FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q = none
        rw [if_neg hBufcap, if_neg hBufSx]
      rw [htp3]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (u.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hib hcon.1), Cfg.mapState_workTapes]
      show (if i = iBuf then FinTM.bufferTape u else if i = cap then FinTM.bufferTape bt
        else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none) q =
        (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q
      rw [if_neg hib]
  -- phase 4: the guided bank erase, which also rewinds the capture head
  have hs4 : A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) T4 = E4 ∧
      E4.state = some 2 ∧
      ∀ v < T4, (A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) v).state ≠ some 2 := by
    have htape4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i = FinTM.bufferTape bt := by
      intro i hi
      funext q
      rw [Cfg.mapState_workTapes]
      show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
        else fun _ => none) q = FinTM.bufferTape bt q
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    have hpos4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i = (bt.length : ℤ) := by
      intro i hi
      rw [Cfg.mapState_workTapePos]
      show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
        (bt.length : ℤ)
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    obtain ⟨hrun4, hcut4⟩ := un_bank_run Sx cap hcapSx bt.length (fun _ => bt)
      (fun _ _ => rfl) (E3.mapState fun _ => (0 : Fin 3))
      (by rw [Cfg.mapState_state]; rfl) htape4 hpos4
    refine ⟨hrun4.trans ?_, rfl, hcut4⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => (0 : Fin 3)) E3) ?_ ?_
      (Cfg.mapState_output (fun _ => (0 : Fin 3)) E3)
    · funext i q
      show (if i ∈ Sx then (fun _ => none) else
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i) q = tp4 i q
      by_cases hiS : i ∈ Sx
      · rw [if_pos hiS]
        have hic : i ≠ cap := fun h => hcapSx (h ▸ hiS)
        show (none : Option Bool) =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        rw [if_neg hic]
      · rw [if_neg hiS, Cfg.mapState_workTapes]
        show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        by_cases hic : i = cap
        · rw [if_pos hic, if_pos hic]
        · rw [if_neg hic, if_neg hic, if_neg hiS]
    · funext i
      show (if i ∈ Sx ∨ i = cap then 0 else
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i) = (0 : ℤ)
      by_cases hig : i ∈ Sx ∨ i = cap
      · rw [if_pos hig]
      · rw [if_neg hig, Cfg.mapState_workTapePos]
        show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) = 0
        rw [if_neg (fun h => hig (Or.inr h)), if_neg (fun h => hig (Or.inl h))]
  -- phase 5: the expansion of the captured budget word into the unary block
  have hd5' : Nat.ofDigits 2 (bt.map Bool.toNat) = t :=
    (counterValue_eq bt).symm.trans (counterValue_bits t)
  have hs5 : A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) T5 = E5 ∧
      E5.state = some CounterLoopState.done ∧
      ∀ v < T5, (A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) v).state ≠
        some CounterLoopState.done := by
    -- the junction into the counter host's layout
    have hJ5 : (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) =
        counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
          (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
            Cfg (K + MC.k) Bool (Fin 2) z) (FinTM.bufferTape bt) 0 := by
      rw [counter_cfg_eq]
      refine Cfg.ext ?_
        (Cfg.mapState_inputPos (fun _ => CounterLoopState.dec FlagPhase.run) E4) ?_ ?_
        (Cfg.mapState_output (fun _ => CounterLoopState.dec FlagPhase.run) E4)
      · rw [Cfg.mapState_state]
        rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          rw [Cfg.mapState_workTapes]
          show (if cap = cap then FinTM.bufferTape bt else fun _ => none) q =
            FinTM.bufferTape bt q
          rw [if_pos rfl]
        · rw [Fin.lastCases_castSucc]
          funext q
          rw [Cfg.mapState_workTapes]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          rw [Cfg.mapState_workTapePos]
        · rw [Fin.lastCases_castSucc]
          rw [Cfg.mapState_workTapePos]
    have hrow := expandTM_run_ofCfg (x := z) iBlkb [true]
      (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
        Cfg (K + MC.k) Bool (Fin 2) z) rfl bt (FinTM.bufferTape bt) 0
      (fun p _ _ => by rw [zero_add]) t hd5'
    have hlen1 : ([true] : List Bool).length = 1 := rfl
    refine ⟨?_, rfl, ?_⟩
    · rw [hJ5]
      refine hrow.1.trans ?_
      rw [counter_cfg_eq]
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) = tp5 (Fin.last (K + MC.k)) q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) =
            (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q
          rw [if_pos rfl, zero_add]
        · rw [Fin.lastCases_castSucc]
          funext q
          show (if j' = iBlkb ∧ (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ) then
              FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
            else tp4 (Fin.castSucc j') q) = tp5 (Fin.castSucc j') q
          have hne : Fin.castSucc j' ≠ cap := by
            intro h
            have hv := congrArg Fin.val h
            rw [Fin.coe_castSucc, hvcap] at hv
            have := j'.isLt
            omega
          by_cases hjb : j' = iBlkb
          · rw [hjb]
            show (if iBlkb = iBlkb ∧ (0 : ℤ) ≤ q ∧
                  q < 0 + ((t * [true].length : ℕ) : ℤ) then
                FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
              else tp4 (Fin.castSucc iBlkb) q) = tp5 (Fin.castSucc iBlkb) q
            have htp5v : tp5 (Fin.castSucc iBlkb) q = blk q := by
              show (if Fin.castSucc iBlkb = cap then capW else if Fin.castSucc iBlkb = ι jR
                then blk else fun _ => none) q = blk q
              rw [if_neg (hjb ▸ hne),
                if_pos (show Fin.castSucc iBlkb = ι jR from rfl)]
            rw [htp5v]
            by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ)
            · rw [if_pos ⟨rfl, hq.1, hq.2⟩, un_flatten, sub_zero]
            · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
              show tp4 (Fin.castSucc iBlkb) q = blk q
              show (if Fin.castSucc iBlkb = cap then FinTM.bufferTape bt else fun _ => none) q =
                blk q
              rw [if_neg (hjb ▸ hne)]
              rw [eq_comm]
              rcases lt_or_ge q 0 with h0 | h0
              · exact FinTM.bufferTape_of_neg _ h0
              · refine un_buffer_ge _ _ ?_
                rw [List.length_replicate]
                rw [hlen1] at hq
                push_cast at hq ⊢
                omega
          · rw [if_neg (fun hcon => hjb hcon.1)]
            have hnj : Fin.castSucc j' ≠ ι jR := by
              intro h
              exact hjb (Fin.castSucc_injective _ h)
            show (if Fin.castSucc j' = cap then FinTM.bufferTape bt else fun _ => none) q =
              (if Fin.castSucc j' = cap then capW else if Fin.castSucc j' = ι jR then blk
                else fun _ => none) q
            rw [if_neg hne, if_neg hne, if_neg hnj]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          show (0 : ℤ) = hd5 (Fin.last (K + MC.k))
          show (0 : ℤ) = (if cap = ι jR then (t : ℤ) else 0)
          rw [if_neg (Ne.symm (hιcap jR))]
        · rw [Fin.lastCases_castSucc]
          rw [Function.update_apply]
          by_cases hjb : j' = iBlkb
          · rw [if_pos hjb, hjb]
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) = hd5 (Fin.castSucc iBlkb)
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) =
              (if Fin.castSucc iBlkb = ι jR then (t : ℤ) else 0)
            rw [if_pos (show Fin.castSucc iBlkb = ι jR from rfl), hlen1]
            push_cast
            ring
          · rw [if_neg hjb]
            have hnj : Fin.castSucc j' ≠ ι jR := fun h => hjb (Fin.castSucc_injective _ h)
            show (0 : ℤ) = (if Fin.castSucc j' = ι jR then (t : ℤ) else 0)
            rw [if_neg hnj]
    · intro v hv
      rw [hJ5]
      exact (hrow.2.1 v hv).1
  -- phase 6: rewind the block head
  have hs6 : A6.runFrom (E5.mapState fun _ => RewindPhase.start) T6 = E6 ∧
      E6.state = some RewindPhase.done ∧
      ∀ v < T6, (A6.runFrom (E5.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E5.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) = (t : ℤ) := by
      rw [Cfg.mapState_workTapePos]
      show (if ι jR = ι jR then (t : ℤ) else 0) = (t : ℤ)
      rw [if_pos rfl]
    have htp : ∀ q', (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR) q' =
        blk q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if ι jR = cap then capW else if ι jR = ι jR then blk else fun _ => none) q' = blk q'
      rw [if_neg (hιcap jR), if_pos rfl]
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((t : ℕ) : ℤ) →
        (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR)
          ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - (t : ℕ) + p) =
          FinTM.bufferTape (List.replicate t true) p := by
      intro p hp1 hp2
      rw [hps, htp]
      show FinTM.bufferTape (List.replicate t true) ((t : ℤ) - (t : ℕ) + p) = _
      congr 1
      ring
    obtain ⟨hrun6, hcut6, -⟩ := rewindTM_run_ofCfg (ι jR) (List.replicate t true) t
      (by simp) (E5.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun6.trans ?_, rfl, hcut6⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => RewindPhase.start) E5) ?_ ?_
      (Cfg.mapState_output (fun _ => RewindPhase.start) E5)
    · funext i q
      show (E5.mapState fun _ => RewindPhase.start).workTapes i q = tp5 i q
      rw [Cfg.mapState_workTapes]
    · funext i
      show Function.update (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR)
        ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - ((t : ℕ) : ℤ)) i =
        (0 : ℤ)
      rw [Function.update_apply]
      by_cases hij : i = ι jR
      · rw [if_pos hij, hps]
        ring
      · rw [if_neg hij, Cfg.mapState_workTapePos]
        show (if i = ι jR then (t : ℤ) else 0) = 0
        rw [if_neg hij]
  -- phase 7: clear the counter word
  have hs7 : A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) T7 = E7 ∧
      E7.state = some SweepPhase.done ∧
      ∀ v < T7, (A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E6.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E6.mapState fun _ => SweepPhase.sweep).workTapePos cap = 0 :=
      Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 cap
    have htp : ∀ q', (E6.mapState fun _ => SweepPhase.sweep).workTapes cap q' = capW q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q' = capW q'
      rw [if_pos rfl]
    have hcapN : ∀ p : ℤ, capW p = FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p
      show (if 0 ≤ p ∧ p < (bt.length : ℤ) then some true else FinTM.bufferTape bt p) = _
      by_cases hp : 0 ≤ p ∧ p < (bt.length : ℤ)
      · rw [if_pos hp]
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
          ⟨p.toNat, (Int.toNat_of_nonneg hp.1).symm⟩
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
          rw [List.length_replicate]
          exact_mod_cast hp.2)]
        rw [List.getElem_replicate]
      · rw [if_neg hp]
        have h1 : FinTM.bufferTape bt p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · exact un_buffer_ge _ _ (by omega)
        have h2 : FinTM.bufferTape (List.replicate bt.length true) p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · refine un_buffer_ge _ _ ?_
            rw [List.length_replicate]
            omega
        rw [h1, h2]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate bt.length true).length : ℤ) →
        (E6.mapState fun _ => SweepPhase.sweep).workTapes cap
          ((E6.mapState fun _ => SweepPhase.sweep).workTapePos cap + p) =
          FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add, hcapN]
    obtain ⟨hrun7, hcut7, -⟩ := clearTM_run_ofCfg cap (List.replicate bt.length true)
      (E6.mapState fun _ => SweepPhase.sweep) hst hhw
    rw [List.length_replicate] at hrun7 hcut7
    refine ⟨hrun7.trans ?_, rfl, hcut7⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E6) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E6)
    funext i q
    show (if i = cap ∧ (E6.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E6.mapState fun _ => SweepPhase.sweep).workTapePos i + (bt.length : ℤ) then none
      else (E6.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp7 i q
    by_cases hic : i = cap
    · rw [hic, hps, htp]
      have htp7 : tp7 cap q = none := by
        show (if cap = ι jR then blk else fun _ => none) q = none
        rw [if_neg (Ne.symm (hιcap jR))]
      rw [htp7]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (bt.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        show capW q = none
        show (if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q) = none
        rw [if_neg (by omega)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hic hcon.1), Cfg.mapState_workTapes]
      show (if i = cap then capW else if i = ι jR then blk else fun _ => none) q =
        (if i = ι jR then blk else fun _ => none) q
      rw [if_neg hic]
  -- phase 8: the input rewind
  have hs8 : A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) T8 = E8 ∧
      E8.state = some .done ∧
      ∀ v < T8, (A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) v).state ≠
        some .done := by
    have hip8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos = ip23 :=
      Cfg.mapState_inputPos _ _
    obtain ⟨hrun8, hcut8, -⟩ := inputRewindTM_run (E7.mapState fun _ => InputRewindPhase.start)
      (by rw [Cfg.mapState_state]; rfl)
      (by rw [hip8]; show 1 ≤ 2 * u.length + 3; omega)
    have hT8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos.val + 1 = T8 := by
      rw [hip8]
    rw [hT8] at hrun8 hcut8
    refine ⟨hrun8.trans ?_, rfl, hcut8⟩
    refine Cfg.ext rfl rfl ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => InputRewindPhase.start) E7 i)
      (Cfg.mapState_output (fun _ => InputRewindPhase.start) E7)
    funext i q
    exact Cfg.mapState_workTapes (fun _ => InputRewindPhase.start) E7 i q
  -- the chain: every seam inherits the run, the exit state and the first-visit cut
  have hch2 := seamCompTM_step A1 (Sum.inr ()) A2 RewindPhase.start RewindPhase.done
    hs1.1 hs1.2.1 hs1.2.2 hs2.1 hs2.2.1 hs2.2.2
  have hch3 := un_step' R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep SweepPhase.done
    Sum.inr hch2.1 hch2.2.1 hch2.2.2 hs3.1 rfl hs3.2.2
  have hch4 := un_step' R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3) (2 : Fin 3)
    Sum.inr hch3.1 hch3.2.1 hch3.2.2 hs4.1 rfl hs4.2.2
  have hch5 := un_step' R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
    CounterLoopState.done Sum.inr hch4.1 hch4.2.1 hch4.2.2 hs5.1 rfl hs5.2.2
  have hch6 := un_step' R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
    RewindPhase.done Sum.inr hch5.1 hch5.2.1 hch5.2.2 hs6.1 rfl hs6.2.2
  have hch7 := un_step' R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep SweepPhase.done
    Sum.inr hch6.1 hch6.2.1 hch6.2.2 hs7.1 rfl hs7.2.2
  have hch8 := un_step' R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
    InputRewindPhase.done Sum.inr hch7.1 hch7.2.1 hch7.2.2 hs8.1 rfl hs8.2.2
  -- the start: the machine's initial configuration is the chain's left seam
  have hstart : P.initCfg z =
      ((((((c0.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState
        Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_with_q₀]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      rfl
    · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    · funext i q
      rw [Cfg.init_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_tape, MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).1,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).1]
    · funext i
      rw [Cfg.init_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_pos, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).2,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, List.length_nil]
          rfl
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).2]
    · rw [Cfg.init_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, embedSilentCfg_output]
  -- the exit configuration and the block property
  have hblk : ∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t := by
    intro p
    constructor
    · intro h
      by_contra hcon
      apply h
      rcases lt_or_ge p 0 with h0 | h0
      · exact FinTM.bufferTape_of_neg _ h0
      · refine un_buffer_ge _ _ ?_
        rw [List.length_replicate]
        push_cast at hcon ⊢
        omega
    · rintro ⟨h0, hlt⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
        ⟨p.toNat, (Int.toNat_of_nonneg h0).symm⟩
      show FinTM.bufferTape (List.replicate t true) ((n : ℕ) : ℤ) ≠ none
      rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
        rw [List.length_replicate]
        exact_mod_cast hlt)]
      simp
  have hfin : (E8.mapState (Sum.inr : InputRewindPhase → _)) =
      (⟨some (Sum.inr InputRewindPhase.done), 1, Function.update (fun _ _ => none) (ι jR) blk,
        fun _ => 0, []⟩ :
        Cfg (K + MC.k + 1) Bool ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          Fin 3) ⊕ CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          InputRewindPhase) z) := by
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · exact (Cfg.mapState_state (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · exact (Cfg.mapState_inputPos (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · funext i q
      refine (Cfg.mapState_workTapes (Sum.inr : InputRewindPhase → _) E8 i q).trans ?_
      show tp7 i q = Function.update (fun _ _ => none) (ι jR) blk i q
      rw [Function.update_apply]
    · funext i
      exact (Cfg.mapState_workTapePos (Sum.inr : InputRewindPhase → _) E8 i).trans rfl
    · exact (Cfg.mapState_output (Sum.inr : InputRewindPhase → _) E8).trans rfl
  -- the budget
  have hco : counterOverhead bt (t + 1) ≤ 4 * t + 2 * bt.length + 2 := by
    have h := counterOverhead_le bt
    rw [hd5'] at h
    exact h
  refine ⟨T1 + 1 + T2 + 1 + T3 + 1 + T4 + 1 + T5 + 1 + T6 + 1 + T7 + 1 + T8, ?_, blk, hblk,
    ?_, ?_⟩
  · show 3 * u.length + 4 + (4 * bt.length + 5) + 1 + (2 * bt.length + 2 + 2) + 1 +
      (2 * u.length + 2) + 1 + (bt.length + 2) + 1 +
      (t * ([true].length + 1) + counterOverhead bt (t + 1)) + 1 + (t + 2) + 1 +
      (2 * bt.length + 2) + 1 + (2 * u.length + 3 + 1) ≤ (7 * α.length + 130) * (t + 1)
    rw [show ([true] : List Bool).length = 1 from rfl]
    have hexp : (7 * α.length + 130) * (t + 1) =
        7 * (α.length * t) + 7 * α.length + 130 * t + 130 := by ring
    rw [hexp]
    have hA : α.length * t ≥ 0 := Nat.zero_le _
    omega
  · have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    show P.runFrom (P.initCfg z) _ = _
    rw [hstart, hPrun]
    exact hch8.1.trans hfin
  · intro v hv
    have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    rw [hstart, hPrun]
    exact hch8.2.2 v hv

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`.

**Implementation.** The setup before the guess is one seam chain of eight phases: the prefix
canonizer `Turing.prefixCanonTM` with the first-component extractor, embedded silently with its
output `bits t` captured on a scratch tape; the code buffer's rewind and clear; an erase of the
extractor's scratch tapes that also rewinds the capture; the expansion of `bits t` into the
unary block (`Turing.expandTM`); the block's rewind; the counter's clear; and the input rewind.
It first reaches its exit within `(7·|α| + 130)·(t + 1)` steps, with no `|x|` term, so the
constant is `C = C_P + C_R + 13` with `C_P = 7·|α| + 130` and `C_R` the core's. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  exact un_universal_of_setup c un_setup

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. `E` itself is
`Turing.FinNDTM.exists_exhaustiveDecider`, proved (iterative deepening over the
choice words of the fixed `UN`, each replayed by its replay machine under the
step-clocked runner, with a window clear between replays; no `|x|` term), so the
decider's only open dependency is the universal NDTM's interpreter core
`Turing.exists_ndInterpreterCore`. The proof applies
`Turing.ndAcceptsWithin_decider_of_universal` to `Turing.exists_timed_universal_NDTM`. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  exact ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)

end Turing

namespace Complexity

open Turing

/-- The chain's induction: `P n ↔ P (n + 1)` for `a ≤ n < b` gives `P a ↔ P b`.

**Proof sketch.** Induction on `b` from `a`, composing the step at `b`. -/
private theorem nh_chain (P : ℕ → Prop) {a b : ℕ} (hab : a ≤ b)
    (step : ∀ n, a ≤ n → n < b → (P n ↔ P (n + 1))) : P a ↔ P b := by
  induction b, hab using Nat.le_induction with
  | base => exact Iff.rfl
  | succ b hab ih =>
    exact (ih fun n h1 h2 => step n h1 (by omega)).trans (step b hab (by omega))

/-- Finite absorption: a function eventually below `g` is below `F · (g + 1)`.

**Proof sketch.** Take `F` one more than the sum of `f` below `N₀`: beyond `N₀` the first summand
pays, below it the sum does. -/
private theorem nh_absorb (f g : ℕ → ℕ) (N₀ : ℕ) (h : ∀ n ≥ N₀, f n ≤ g n) :
    ∃ F : ℕ, ∀ n, f n ≤ F * (g n + 1) := by
  refine ⟨1 + ∑ m ∈ Finset.range N₀, f m, fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · have h1 := h n hn
    nlinarith [Nat.zero_le (∑ m ∈ Finset.range N₀, f m)]
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have h2 := Finset.single_le_sum (fun m _ => Nat.zero_le (f m)) hmem
    nlinarith [Nat.zero_le (g n)]

/-- A constant factor folds into the membership constant: `NTIME (F · T) ⊆ NTIME T`.

**Proof sketch.** A decider within `a · (F · T n)` decides within `(a F) · T n`
(`Complexity.mem_NTIME_iff`, `Turing.FinNDTM.decidesInTime_iff`). -/
private theorem nh_fold {T : ℕ → ℕ} (F : ℕ) : NTIME (fun n => F * T n) ⊆ NTIME T := by
  intro L hL
  obtain ⟨a, N, hN⟩ := mem_NTIME_iff.mp hL
  apply mem_NTIME_iff.mpr
  refine ⟨a * F, N, FinNDTM.decidesInTime_iff.mpr ?_⟩
  intro x
  simpa only [Nat.mul_assoc] using (FinNDTM.decidesInTime_iff.mp hN x)

/-- The inclusion `NTIME f ⊆ NTIME (g + 1)` under the domination hypothesis.

**Proof sketch.** The hypothesis at `A = 1` gives `f n ≤ g n` eventually; absorb the finitely many
smaller lengths (`nh_absorb`), apply `NTIME.mono`, and fold the factor `F` into the membership
constant (`nh_fold`). -/
private theorem nh_inclusion {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊆ NTIME (fun n => g n + 1) := by
  obtain ⟨N₀, hN₀⟩ := hfg 1
  obtain ⟨F, hF⟩ := nh_absorb f g N₀ (fun n hn => by have := hN₀ n hn; omega)
  intro L hL
  have h1 : L ∈ NTIME (fun n => F * (g n + 1)) := NTIME.mono hF hL
  exact nh_fold F h1

/-- The top's threshold: `C · 2^{C (T + 1)} ≤ 2^{T²}` for every large `T`.

**Proof sketch.** `C < 2^C`, so the left side is below `2^{C + C (T + 1)}`, and
`C + C (T + 1) ≤ T²` once `T ≥ 2C + 2`. -/
private theorem nh_top (C : ℕ) : ∃ T₀, ∀ T ≥ T₀, C * 2 ^ (C * (T + 1)) ≤ 2 ^ (T ^ 2) := by
  refine ⟨2 * C + 2, fun T hT => ?_⟩
  have hC : C < 2 ^ C := Nat.lt_two_pow_self
  calc C * 2 ^ (C * (T + 1)) ≤ 2 ^ C * 2 ^ (C * (T + 1)) := Nat.mul_le_mul_right _ hC.le
    _ = 2 ^ (C + C * (T + 1)) := by rw [← pow_add]
    _ ≤ 2 ^ (T ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul_right T hT])

/-- The bottom's threshold: `C₁ (c₀ · fa + 1) ≤ (fa + a + 1)²` once `a ≥ C₁ (c₀ + 1)`.

**Proof sketch.** Then `C₁ c₀ ≤ a` and `C₁ ≤ a`, and the square's cross terms pay for both. -/
private theorem nh_bottom (C₁ c₀ fa a : ℕ) (ha : C₁ * (c₀ + 1) ≤ a) :
    C₁ * (c₀ * fa + 1) ≤ (fa + a + 1) ^ 2 := by
  have h1 : C₁ * c₀ ≤ a := by nlinarith
  have h2 : C₁ ≤ a := by nlinarith
  nlinarith [Nat.mul_le_mul_right fa h1]

/-- The middle's threshold: `C (C₁ (c₀ · f (n + 1) + 1) + 1) ≤ g n` for every large `n`.

**Proof sketch.** The left side is at most `(C C₁ (c₀ + 1) + C) · (f (n + 1) + 1)`, a ring
identity; the domination hypothesis at that constant bounds it by `g n`. -/
private theorem nh_middle {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) (C C₁ c₀ : ℕ) :
    ∃ N, ∀ n ≥ N, C * (C₁ * (c₀ * f (n + 1) + 1) + 1) ≤ g n := by
  obtain ⟨N, hN⟩ := hfg (C * C₁ * (c₀ + 1) + C)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have hid : C * (C₁ * (c₀ * f (n + 1) + 1) + 1) +
      (C * C₁ * f (n + 1) + C * f (n + 1) + C * C₁ * c₀) =
      (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := by ring
  calc C * (C₁ * (c₀ * f (n + 1) + 1) + 1)
      ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := Nat.le.intro hid
    _ ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + f n + n + 1) :=
        Nat.mul_le_mul_left _ (by omega)

/-- A late stage of a code: some stage of `α` has its bottom rung beyond `N`.

**Proof sketch.** Every code recurs at stages beyond any bound
(`Turing.NTimeDiag.stageCode_frequently`), and the ladder dominates the index
(`Turing.NTimeDiag.le_ladder`). -/
private theorem nh_stage (f : ℕ → ℕ) (α : List Bool) (N : ℕ) :
    ∃ i, N ≤ Turing.NTimeDiag.ladder f i ∧ Turing.NTimeDiag.stageCode i = α := by
  obtain ⟨i, hi, hα⟩ := Turing.NTimeDiag.stageCode_frequently α N
  exact ⟨i, by have := Turing.NTimeDiag.le_ladder f i; omega, hα⟩

/-- **Truncation at the all-branch budget.** If every branch of `N` on `x` halts within `T`, an
acceptance of `x` at any length is an acceptance within `T`.

**Proof sketch.** At a length `t ≤ T`, pad (`Turing.FinNDTM.AcceptsWithin.mono`). At `t > T`, the
accepting word runs as its length-`T` prefix, which has halted (`Turing.run_take_of_halted`, with
absorption by `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`), so it accepts. -/
private theorem nh_accepts_of_halts {N : FinNDTM Bool} {x : List Bool} {T t : ℕ}
    (hT : N.tm.HaltsWithin x T) (ht : N.AcceptsWithin x t) : N.AcceptsWithin x T := by
  rcases le_or_gt t T with hle | hlt
  · exact ht.mono hle
  · obtain ⟨w, hw, -, hout⟩ := FinNDTM.acceptsWithin_iff.mp ht
    obtain ⟨hlen, hp, hr⟩ := run_take_of_halted (fun w => N.tm.runWith w (N.tm.initCfg x))
      (fun c => c.state = none)
      (fun w w' h => by simp only [NDTM.runWith_append w w' (N.tm.initCfg x),
        NDTM.runWith_of_halt _ h])
      (NDTM.haltsWithin_iff.mp hT) (w := w) (by omega)
    exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take T, hlen, hp, hr ▸ hout⟩

/-- **A decider's language from an unbounded acceptance.** If `N` decides `L` within `T`, any
acceptance of `x`, at any length, puts `x` in `L`.

**Proof sketch.** Truncate the acceptance at `N`'s all-branch budget on `x`
(`nh_accepts_of_halts`); the decider's clause reads membership off it. -/
private theorem nh_mem_of_accepts {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (hN : N.DecidesInTime L T) {x : List Bool} (ht : ∃ t, N.AcceptsWithin x t) : x ∈ L := by
  obtain ⟨t, ht⟩ := ht
  exact ((FinNDTM.decidesInTime_iff.mp hN x).2).mpr
    (nh_accepts_of_halts (FinNDTM.decidesInTime_iff.mp hN x).1 ht)

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2]; [Coo72]): for
time-constructible `f` and `g`, if every constant multiple of `f(n+1) + f(n) + n + 1` is eventually
below `g(n)` — the book's `f(n+1) = o(g(n))` with the two addends of the module docstring — then
`NTIME f ⊊ NTIME (g + 1)`. The overhead on `f` is linear, as in the book, in contrast to the
received deterministic hierarchy's square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives `f n ≤ g n` eventually, and the
finitely many smaller lengths are absorbed into the constant (no monotonicity of `f` is needed).

*Strictness* is lazy diagonalization [AB09, proof of Theorem 3.2 and Figure 3.1]. Fix an effective
scheme `c` (`Turing.exists_effectiveNDMachineCode`) and take the diagonalizer `D` of
`Turing.NTimeDiag.exists_diagonalizer`, given the exponential decider
`Turing.exists_ndAcceptsWithin_decider`. Its language `L`, acceptance of `x` within
`K · (g |x| + 1)`, is in `NTIME (g + 1)` (`Turing.NTimeDiag.acceptLang_mem_NTIME`). Suppose `N`
decides `L` within `c₀ · f`. The linear coded normal form
(`Turing.FinNDTM.exists_codeNDTM_accepts_linear`) gives a coded machine `M'` and a constant `C₁`:
an acceptance by `N` within `t` is one by `M'` within `C₁ (t + 1)`, and an acceptance by `M'` is
one by `N` at some length. Let `C` be the diagonalizer's constant for `M'`'s code, and take a
stage `i` of that code whose bottom rung `ℓᵢ` lies beyond the three thresholds below
(`Turing.NTimeDiag.stageCode_frequently`). On unary words:
- **the middle**, for `ℓᵢ < n < ℓᵢ₊₁`: `1ⁿ ∈ L ↔ 1ⁿ⁺¹ ∈ L`. Forward, `D`'s acceptance gives
  `M'`'s within `g n`, hence `N`'s at some length; an acceptance at any length is one within
  `N`'s all-branch budget, so `1ⁿ⁺¹ ∈ L`. Backward, `N`'s acceptance within `c₀ · f (n + 1)`
  gives `M'`'s within `t' = C₁ (c₀ · f (n + 1) + 1)`, and the hypothesis puts `C (t' + 1)` below
  `g n`;
- **the chain** of these steps: `1^{ℓᵢ + 1} ∈ L ↔ 1^{ℓᵢ₊₁} ∈ L`;
- **the top**, at `n = ℓᵢ₊₁ = 2^{T*²}` with `T* = budget f ℓᵢ`: `1ⁿ ∈ L` iff `M'` does not accept
  `1^{ℓᵢ + 1}` within `T*`, since `C · 2^{C (T* + 1)} ≤ 2^{T*²}` once `T*` is large;
- **the bottom**, at `a = ℓᵢ + 1`: `M'` accepts `1ᵃ` within `T*` iff `1ᵃ ∈ L`, since
  `T* = (f a + a + 1)² ≥ C₁ (c₀ · f a + 1)` once `a ≥ C₁ (c₀ + 1)`.

Together they give `1ᵃ ∈ L ↔ 1ᵃ ∉ L`.

**Implementation.** The private lemmas before this theorem:
- the chain's induction (`nh_chain`);
- the absorption, the constant fold and the inclusion (`nh_absorb`, `nh_fold`, `nh_inclusion`);
- the three thresholds (`nh_top`, `nh_bottom`, `nh_middle`);
- a late stage of a code (`nh_stage`);
- the truncation of an acceptance at an all-branch budget (`nh_accepts_of_halts`, through
  `Turing.run_take_of_halted`), and its reading for a decider (`nh_mem_of_accepts`).

The diagonalizer and the linear coded normal form are cited as contracts. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  obtain ⟨c⟩ := exists_effectiveNDMachineCode
  obtain ⟨D, K, hhalt, hD⟩ :=
    NTimeDiag.exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)
  refine (Set.ssubset_iff_of_subset (nh_inclusion hfg)).mpr
    ⟨_, NTimeDiag.acceptLang_mem_NTIME D K g hhalt, fun hLf => ?_⟩
  set L : Language Bool := {x | D.AcceptsWithin x (K * (g x.length + 1))} with hL
  have hmemL : ∀ m, List.replicate m true ∈ L ↔
      D.AcceptsWithin (List.replicate m true) (K * (g m + 1)) := by
    intro m
    change D.AcceptsWithin (List.replicate m true)
      (K * (g (List.replicate m true).length + 1)) ↔ _
    rw [List.length_replicate]
  obtain ⟨c₀, N, hN⟩ := mem_NTIME_iff.mp hLf
  have hdec : ∀ m, List.replicate m true ∈ L →
      N.AcceptsWithin (List.replicate m true) (c₀ * f m) := by
    intro m hm
    have h := ((FinNDTM.decidesInTime_iff.mp hN (List.replicate m true)).2).mp hm
    rwa [List.length_replicate] at h
  obtain ⟨M', C₁, hfwd, hbwd⟩ := FinNDTM.exists_codeNDTM_accepts_linear N
  obtain ⟨C, hC⟩ := hD (c.encode M')
  rw [c.toNDMachineCode.decode_encode M'] at hC
  obtain ⟨N₁, hN₁⟩ := nh_middle hfg C C₁ c₀
  obtain ⟨T₀, hT₀⟩ := nh_top C
  obtain ⟨i, hi, hiα⟩ := nh_stage f (c.encode M') (N₁ + T₀ + C₁ * (c₀ + 1))
  have hℓ2 : 2 ≤ NTimeDiag.ladder f i := by have := NTimeDiag.le_ladder f i; omega
  have hlt : NTimeDiag.ladder f i < NTimeDiag.ladder f (i + 1) :=
    NTimeDiag.ladder_strictMono f (Nat.lt_succ_self i)
  -- the middle step, at every `n` with `ℓᵢ < n < ℓᵢ₊₁`
  have hmid : ∀ n, NTimeDiag.ladder f i + 1 ≤ n → n < NTimeDiag.ladder f (i + 1) →
      (List.replicate n true ∈ L ↔ List.replicate (n + 1) true ∈ L) := by
    intro n h1 h2
    have hs : NTimeDiag.stage f n = i := NTimeDiag.stage_eq f (by omega) h2.le
    obtain ⟨hmidC, -⟩ := hC n (by omega) (by rw [hs]; exact hiα)
    obtain ⟨hsound, hcompl⟩ := hmidC (by rw [hs]; omega)
    constructor
    · intro hn
      exact nh_mem_of_accepts hN (hbwd _ _ (hsound ((hmemL n).mp hn)))
    · intro hn1
      exact (hmemL n).mpr (hcompl _ (hfwd _ _ (hdec (n + 1) hn1)) (hN₁ n (by omega)))
  have hchain := nh_chain (fun m => List.replicate m true ∈ L)
    (show NTimeDiag.ladder f i + 1 ≤ NTimeDiag.ladder f (i + 1) by omega) hmid
  -- the top's flip, at `n = ℓᵢ₊₁`
  have htop : List.replicate (NTimeDiag.ladder f (i + 1)) true ∈ L ↔
      ¬M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
        (NTimeDiag.budget f (NTimeDiag.ladder f i)) := by
    have hs : NTimeDiag.stage f (NTimeDiag.ladder f (i + 1)) = i :=
      NTimeDiag.stage_eq f hlt le_rfl
    obtain ⟨-, htopC⟩ := hC (NTimeDiag.ladder f (i + 1)) (by omega) (by rw [hs]; exact hiα)
    rw [hs] at htopC
    have hTle : T₀ ≤ NTimeDiag.budget f (NTimeDiag.ladder f i) := by
      rw [NTimeDiag.budget_eq]
      calc T₀ ≤ f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1 := by omega
        _ ≤ (f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1) ^ 2 :=
          Nat.le_self_pow (by norm_num) _
    have hthr : C * 2 ^ (C * (NTimeDiag.budget f (NTimeDiag.ladder f i) + 1)) ≤
        NTimeDiag.ladder f (i + 1) := by
      rw [NTimeDiag.ladder_succ f i]
      exact hT₀ _ hTle
    rw [hmemL]
    exact htopC rfl hthr
  -- the bottom's transfer, at `a = ℓᵢ + 1` within `T*`
  have hbot : M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
      (NTimeDiag.budget f (NTimeDiag.ladder f i)) ↔
      List.replicate (NTimeDiag.ladder f i + 1) true ∈ L := by
    constructor
    · intro hM
      exact nh_mem_of_accepts hN (hbwd _ _ hM)
    · intro hx
      refine (hfwd _ _ (hdec _ hx)).mono ?_
      rw [NTimeDiag.budget_eq]
      exact nh_bottom C₁ c₀ _ _ (by omega)
  exact iff_not_self (hchain.trans (htop.trans (not_congr hbot)))

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`.

Formally, the factor `2` is absorbed into the membership witness's constant by the private
`nh_fold`, which the inclusion half of `Complexity.ntime_hierarchy` also uses. -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  have hback : NTIME (fun n => g n + 1) ⊆ NTIME g := by
    intro L hL
    have hscale : L ∈ NTIME (fun n => 2 * g n) :=
      NTIME.mono (fun n => by have := hpos n; omega) hL
    exact nh_fold 2 hscale
  have heq : NTIME (fun n => g n + 1) = NTIME g :=
    Set.Subset.antisymm hback (NTIME.mono (fun n => Nat.le_succ (g n)))
  simpa only [heq] using ntime_hierarchy hf hg hfg

/-- **The showcase separation**:
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
The two constructibility witnesses are `Complexity.timeConstructible_poly` at
`(C, c) = (1, 0)` and `(1, 1)`; domination takes `N = 3A + 4` and multiplies `N ≤ n` by `n`. -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  have hf : TimeConstructible (fun n => n + 1) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (0 + 1)) = (fun n => n + 1) := by
      funext n
      simp only [Nat.zero_add, pow_one, one_mul]
    rw [← h]
    exact timeConstructible_poly 1 0 (by decide)
  have hg : TimeConstructible (fun n => (n + 1) ^ 2) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (1 + 1)) = (fun n => (n + 1) ^ 2) := by
      funext n
      simp only [one_mul]
    rw [← h]
    exact timeConstructible_poly 1 1 (by decide)
  apply ntime_hierarchy_of_pos hf hg
  · intro n
    exact pow_pos (Nat.succ_pos n) _
  · intro A
    refine ⟨3 * A + 4, fun n hn => ?_⟩
    nlinarith [Nat.mul_le_mul_right n hn]

end Complexity

## ===== campaign/gates/100-nth-status/evidence/freeze/declfreeze.txt =====

public before/after: 5 5 private before/after: 20 20
public added: []
public removed: []
private removed: []
private added: []
private changed: []

## ===== campaign/gates/100-nth-status/evidence/lint/policy-base.txt =====


4 findings in 1 files
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean: module docstring missing `## Main definitions`
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean: 1941 lines (> 1000, must split)
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:32: public `theorem at` has no docstring
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:32: `at` proof is 83 lines, no **Proof sketch.**

## ===== campaign/gates/100-nth-status/evidence/lint/policy-head.txt =====


4 findings in 1 files
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean: module docstring missing `## Main definitions`
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean: 1941 lines (> 1000, must split)
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:32: public `theorem at` has no docstring
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:32: `at` proof is 83 lines, no **Proof sketch.**

## ===== campaign/gates/100-nth-status/evidence/merged-tree/down-lnth.txt =====

TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization

## ===== campaign/gates/100-nth-status/evidence/merged-tree/replay-lnth-static.txt =====

modules 2, mismatches 0, static total 0

## ===== campaign/gates/100-nth-status/evidence/merged-tree/replay-lnth.log =====

# replay-lnth at 0b05cc3a: #209, NTimeHierarchy's Status paragraph (2 modules), fresh .oleans into oleans-lnth
TCSlib/Complexity/Diagonalization/NTimeHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization exit=0 errors=0 sorry=0
# modules=2 failed=0

## ===== campaign/gates/100-nth-status/evidence/merged-tree/replay-lnth.sh =====

#!/usr/bin/env bash
# Replay lnth (#209, NTimeHierarchy's Status paragraph; branch lean/nth-status, stacked on the campaign after #207): its downstream closure (2 modules),
# fresh .oleans into oleans-lnth, a copy of oleans-lcamp1, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-si"
LIST="/home/user/tcslib-scratch/fills/replay/down-lnth.txt"
LOG="$S/fills/replay/replay-lnth.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:99dada9de8b3417c4bffb87060bf02ef7ada02d8"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/nth-status 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 12320b41db5641cf5d68186331b771c6be94f1d3 HEAD || { echo "precheck: the head must contain the campaign after #207; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 12320b41db5641cf5d68186331b771c6be94f1d3 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #207 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp1.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lnth" ] && { echo "precheck: $S/oleans-lnth already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp1" ] || { echo "precheck: oleans-lcamp1 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp1" "$S/oleans-lnth" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lnth at $(git rev-parse --short HEAD): #209, NTimeHierarchy's Status paragraph ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lnth"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lnth nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=2 failed=0" || { echo "replay: a module failed, or the count is not 2" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/100-nth-status/evidence/patches/0001-NTimeHierarchy-the-Status-paragraph-after-NF-and-E-D.patch =====

From 2029a1be49c6ba94c39a6b784890787592f464d4 Mon Sep 17 00:00:00 2001
From: Claude <noreply@anthropic.com>
Date: Fri, 6 Nov 2026 03:39:02 +0000
Subject: [PATCH] NTimeHierarchy: the Status paragraph after NF and E-D landed

Both contracts the hierarchy was proved from are now proved (E-D's
exists_diagonalizer, #188; NF's exists_codeNDTM_accepts_linear, #191), so
the module docstring no longer calls them sorry. Docstring only.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PqpVTk5MM3PtshNwvNBXBw
---
 TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean | 8 ++++----
 1 file changed, 4 insertions(+), 4 deletions(-)

diff --git a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
index 87f207da..99dada9d 100644
--- a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
+++ b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
@@ -38,10 +38,10 @@ Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
 **Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` is proved, from the
 interpreter core `Turing.exists_ndInterpreterCore`
 (`TCSlib.Complexity.TuringMachine.NDCodeSimulator`), and the exponential decider from it. The
-hierarchy `Complexity.ntime_hierarchy` is proved from two contracts that are still `sorry`: the
-diagonalizer `Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form
-`Turing.FinNDTM.exists_codeNDTM_accepts_linear`. The two corollaries are proved from the
-hierarchy.
+hierarchy `Complexity.ntime_hierarchy` is proved from the diagonalizer
+`Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form
+`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, both proved, and the two corollaries are proved
+from the hierarchy: all of them rest on the standard axioms alone.
 
 ## Design (declared deviations, each for the audit)
 
-- 
2.43.0


## ===== campaign/gates/95-nf-landing-fill/evidence/round5/axioms/NTHAx.lean.txt =====

import TCSlib.Complexity.Diagonalization.NTimeHierarchy

/-! Axiom prints at #191's merged tree (after `replay-lnf`): the normal form, the diagonalizer and
the nondeterministic time hierarchy's theorems. Re-run at round 5 on `oleans-lnf6` (after
`replay-lnf6`). A probe record, not library code. -/

#print axioms Turing.FinNDTM.exists_codeNDTM_accepts_linear
#print axioms Turing.NTimeDiag.exists_diagonalizer
#print axioms Turing.exists_timed_universal_NDTM
#print axioms Turing.exists_ndAcceptsWithin_decider
#print axioms Complexity.ntime_hierarchy
#print axioms Complexity.ntime_hierarchy_of_pos
#print axioms Complexity.NTIME_linear_ssubset_square

## ===== campaign/gates/95-nf-landing-fill/evidence/round5/axioms/NTHAx.out =====

'Turing.FinNDTM.exists_codeNDTM_accepts_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.NTimeDiag.exists_diagonalizer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_timed_universal_NDTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_ndAcceptsWithin_decider' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ntime_hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ntime_hierarchy_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NTIME_linear_ssubset_square' depends on axioms: [propext, Classical.choice, Quot.sound]
nthax exit 0

## ===== TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.NDNormalForm
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.ClassNP.ExhaustiveReplay
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer
import TCSlib.Complexity.TuringMachine.ChoiceWords

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` is proved, from the
interpreter core `Turing.exists_ndInterpreterCore`
(`TCSlib.Complexity.TuringMachine.NDCodeSimulator`), and the exponential decider from it. The
hierarchy `Complexity.ntime_hierarchy` is proved from the diagonalizer
`Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form
`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, both proved, and the two corollaries are proved
from the hierarchy: all of them rest on the standard axioms alone.

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`; the normal form is in
  `TCSlib.Complexity.ClassNP.NDNormalForm`.

## Main results

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style), stated in
  `TCSlib.Complexity.ClassNP.NDNormalForm` (moved there, user 2026-10-17).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The universal NDTM from a setup machine.** Given, for the interpreter core's tape count
`K` and stream tape `jR`, a deterministic setup `P` that on `⟨⟨bits t, α⟩, x⟩` first reaches its
exit within `C_P·(t + 1)` steps with a block of exactly `t` nonblank cells on the core's stream
tape from cell `0`, every other tape blank, every head at the origin, the input head at `1` and
empty output, the guess-then-run assembly over the interpreter core is a universal NDTM at
linear overhead.

**Proof sketch.** Take the core `R` of `Turing.exists_ndInterpreterCore` and the setup `P`; the
universal machine is `Turing.guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej`.
For each stream `s` of length `t`, the core reaches its verdict within `C_R·(t + 1)` from
`streamStartCfg` (assembled from its field equations), so `Turing.guessRunTM_silent_spec` gives
halting within `T_P + 2t + C_R·(t + 1) + 11 ≤ (C_P + C_R + 13)·(t + 1)` on every branch, and
acceptance iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.acceptsWithin_iff`). -/
private theorem un_universal_of_setup (c : EffectiveNDMachineCode)
    (hsetup : ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
      cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
        (P : MultiTapeTM k Bool SP) (pexit : SP),
        ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
          ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
            (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
            P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
              ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
            ∀ u < TP,
              (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
                some pexit) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  obtain ⟨K, SR, hfin, hdec, R, jR, entry, acc, rej, hne, hR⟩ := exists_ndInterpreterCore c
  obtain ⟨k, ι, cap, hcap, SP, hfinP, hdecP, P, pexit, hP⟩ := hsetup K jR
  refine ⟨⟨k, Σ i, GuessRunPhase.State SP SR i,
    guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej⟩, fun α => ?_⟩
  obtain ⟨CR, hCR⟩ := hR α
  obtain ⟨CP, hCP⟩ := hP α
  refine ⟨CP + CR + 13, fun x t => ?_⟩
  obtain ⟨TP, hTP, blk, hblk, hrun, hfirst⟩ := hCP x t
  -- the core's verdict on every stream of length `t`
  have hcore : ∀ s : List Bool, s.length = t → ∃ T, T ≤ CR * (t + 1) ∧
      (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s) T).state
        = some (if ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).state = none ∧
            ((c.decode α).toFinNDTM.tm.runWith s
              ((c.decode α).toFinNDTM.tm.initCfg x)).output = [true] then acc else rej) ∧
      ∀ u < T,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, -, hT, hst, hno⟩ := hCR x t s (by omega)
    rw [List.take_of_length_le (by omega)] at hst
    have hss : streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s =
        ⟨some entry, 1, fun i => if i = jR then FinTM.bufferTape s else fun _ => none,
          fun _ => 0, []⟩ :=
      Cfg.ext (streamStartCfg_state _ _ _ _) (streamStartCfg_inputPos _ _ _ _)
        (funext fun i => funext fun a => streamStartCfg_workTapes _ _ _ _ i a)
        (funext fun i => streamStartCfg_workTapePos _ _ _ _ i) (streamStartCfg_output _ _ _ _)
    rw [hss]
    exact ⟨T, hT, hst, hno⟩
  have hR' : ∀ s : List Bool, s.length = t → ∃ TR ≤ CR * (t + 1),
      ((R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some acc ∨
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          TR).state = some rej) ∧
      ∀ u < TR,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR entry s)
          u).state ≠ some rej := by
    intro s hs
    obtain ⟨T, hT, hst, hno⟩ := hcore s hs
    refine ⟨T, hT, ?_, hno⟩
    rw [hst]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hspec := guessRunTM_silent_spec ι cap hcap jR R entry acc rej P pexit TP t blk hblk hrun
    hfirst (CR * (t + 1)) hR'
  have hbud : TP + 2 * t + CR * (t + 1) + 11 ≤ (CP + CR + 13) * (t + 1) := by
    have e : (CP + CR + 13) * (t + 1) = CP * (t + 1) + CR * (t + 1) + 13 * (t + 1) := by
      rw [Nat.add_mul, Nat.add_mul]
    rw [e]
    generalize CP * (t + 1) = a at hTP ⊢
    generalize CR * (t + 1) = b
    omega
  refine ⟨hspec.1.mono hbud, FinNDTM.acceptsWithin_iff.trans ((hspec.2 _ hbud).trans ?_)⟩
  rw [FinNDTM.acceptsWithin_iff]
  constructor
  · rintro ⟨s, hs, TR, hacc, hf⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    have hTR : TR = T := by
      by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact (hno TR h).1 hacc
      · have h' := hf T h
        rw [hst] at h'
        split_ifs at h' with hc
        · exact h'.1 rfl
        · exact h'.2 rfl
    subst hTR
    rw [hst] at hacc
    split_ifs at hacc with hcond
    · exact ⟨s, hs, hcond.1, hcond.2⟩
    · exact absurd (Option.some.inj hacc).symm hne
  · rintro ⟨s, hs, hhalt, hout⟩
    obtain ⟨T, -, hst, hno⟩ := hcore s hs
    exact ⟨s, hs, T, by rw [hst, if_pos ⟨hhalt, hout⟩], hno⟩

/-! ### The setup machine's pieces

`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup
hypothesis. The setup built below is a seam chain over `K + kC + 1` tapes — the core's `K`, the
embedded header composite's `kC`, and the capture/counter tape last — whose phases are the
embedded header pass, the code buffer's rewind and clear, a guided erase of the extractor scratch
bank, the expansion of the captured budget word into the unary block, the block rewind, the
counter clear, and the input rewind (`Turing.inputRewindTM`, imported). The pieces here are the
guided bank-erase leaf with its framed run, the seam-step composer, the header composite's exact
first halt, and two small word facts. -/

/-- Flattening `t` copies of the one-symbol pattern gives the length-`t` unary block. -/
private lemma un_flatten (t : ℕ) :
    (List.replicate t [true]).flatten = List.replicate t true := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, ih]

/-- A buffered word is blank at and beyond its length. -/
private lemma un_buffer_ge (w : List Bool) (q : ℤ) (hq : (w.length : ℤ) ≤ q) :
    FinTM.bufferTape w q = none := by
  have h0 : 0 ≤ q := le_trans (Int.natCast_nonneg _) hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [FinTM.bufferTape_nat]
  exact List.getElem?_eq_none (by exact_mod_cast hq)

/-- **The header composite's exact first halt**, uniformly in the input suffix: the buffered
composite of the prefix parser and the first-component extractor, on
`pairEncode (pairEncode a b) x`, halts at exactly `3·|pairEncode a b| + 4 + (4·|a| + 5)` and is
live before.

**Proof sketch.** `Turing.prefixCanon_run` at the extractor's halting time, read through
`Turing.prefixCanonTM_eq` and `Turing.FinTM.pairExtractTM_fst_run`, gives the halt. Before the
parser's `3·|pairEncode a b| + 4` steps the run is live by `Turing.prefixCanon_start`; after
them it is the extractor's run, live before its own halt. -/
private theorem un_canon_halt (a b x : List Bool) :
    ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
          (pairEncode (pairEncode a b) x))
        (3 * (pairEncode a b).length + 4 + (4 * a.length + 5))).state = none ∧
      ∀ v < 3 * (pairEncode a b).length + 4 + (4 * a.length + 5),
        ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (FinTM.pairExtractTM true false)).tm.initCfg
            (pairEncode (pairEncode a b) x)) v).state ≠ none := by
  obtain ⟨hrun, hlive⟩ := FinTM.pairExtractTM_fst_run a b
  constructor
  · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
      (4 * a.length + 5)
    simp only [prefixCanonTM_eq] at hb
    rw [hb, FinTM.bufferedSecondCfg_state, hrun]
    rfl
  · intro v hv
    by_cases hpre : v < 3 * (pairEncode a b).length + 4
    · have hs := prefixCanon_start (FinTM.pairExtractTM true false) (pairEncode a b) x
      simp only [prefixCanonTM_eq] at hs
      refine MultiTapeTM.runFrom_state_ne_none_of_le _ _
        (3 * (pairEncode a b).length + 4) ?_ v (by omega)
      rw [hs, FinTM.bufferedSecondCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact fun h => Option.noConfusion h
    · obtain ⟨b', hb⟩ := prefixCanon_run (FinTM.pairExtractTM true false) (pairEncode a b) x
        (v - (3 * (pairEncode a b).length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * (pairEncode a b).length + 4 ≤ v)] at hb
      rw [hb, FinTM.bufferedSecondCfg_state]
      intro h
      refine hlive (v - (3 * (pairEncode a b).length + 4)) (by omega) ?_
      cases hstv : ((FinTM.pairExtractTM true false).tm.runFrom
          ((FinTM.pairExtractTM true false).tm.initCfg (pairEncode a b))
          (v - (3 * (pairEncode a b).length + 4))).state with
      | none => rfl
      | some q =>
        rw [hstv] at h
        exact Option.noConfusion h

/-- The bank erase's one action: blank the selected tapes and move them with the guide. -/
private def un_bankAct (k : ℕ) (S : Finset (Fin k)) (g : Fin k) (m : SignType) (q' : Fin 3) :
    Action k Bool (Fin 3) :=
  ⟨0, fun i => if i ∈ S then (some none, m) else if i = g then (none, m) else (none, 0),
    none, some q'⟩

private lemma un_bankAct_eq {k : ℕ} (S : Finset (Fin k)) (g : Fin k) (m : SignType)
    (q' : Fin 3) (i : Fin k) :
    ((un_bankAct k S g m q').workTapes i).1 = (if i ∈ S then some none else none) ∧
      (((un_bankAct k S g m q').workTapes i).2 : ℤ) =
        if i ∈ S ∨ i = g then (m : ℤ) else 0 := by
  by_cases hiS : i ∈ S
  · simp [un_bankAct, hiS]
  · by_cases hig : i = g
    · subst hig; simp [un_bankAct, hiS]
    · simp [un_bankAct, hiS, hig]

/-- **The guided bank erase**: one unconditional left step, a left sweep that blanks every
selected tape while the guide tape still shows a symbol under the travelling head, and one
step right into the live park. The guide's head travels with the bank, and when the guide is not
one of the selected tapes its word is kept; every other tape, every other head, the input head and
the output are untouched. -/
private def un_bankTM (k : ℕ) (S : Finset (Fin k)) (g : Fin k) :
    MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr := fun q _ w =>
    if q = 0 then un_bankAct k S g .neg 1
    else if q = 1 then
      match w g with
      | some _ => un_bankAct k S g .neg 1
      | none => un_bankAct k S g .pos 2
    else ⟨0, fun _ => (none, 0), none, some 2⟩

/-- **The guided bank erase, framed.** Take a guide outside the selected bank, and start with
every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks at exactly `L + 2` and not earlier, with the bank blank, the bank and guide heads at the
origin, the guide's word and everything else unchanged.

**Proof sketch.** After `r ≤ L + 1` steps the selected cells right of `L − r` are blank and the
bank and guide heads are at `L − r`, by induction on `r`: the first step is unconditional, and
for `1 ≤ r ≤ L` the guide still reads a symbol of its word. At `L + 1` the guide reads the blank
left of its word, so the last step moves right into the park; before it the state is `0` or
`1`. -/
private theorem un_bank_run {k : ℕ} {z : List Bool} (S : Finset (Fin k)) (g : Fin k)
    (hg : g ∉ S) (L : ℕ) (w : Fin k → List Bool)
    (hw : ∀ i, i ∈ S ∨ i = g → (w i).length = L)
    (d : Cfg k Bool (Fin 3) z) (hstate : d.state = some 0)
    (htape : ∀ i, i ∈ S ∨ i = g → d.workTapes i = FinTM.bufferTape (w i))
    (hpos : ∀ i, i ∈ S ∨ i = g → d.workTapePos i = (L : ℤ)) :
    (un_bankTM k S g).runFrom d (L + 2) =
        { d with
          state := some 2
          workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
          workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } ∧
      ∀ t < L + 2, ((un_bankTM k S g).runFrom d t).state ≠ some 2 := by
  classical
  -- the sweep's trajectory
  let T : ℕ → Cfg k Bool (Fin 3) z := fun r =>
    { d with
      state := some (if r = 0 then 0 else 1)
      workTapes := fun i =>
        if i ∈ S then (fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q)
        else d.workTapes i
      workTapePos := fun i => if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i }
  have hT0 : T 0 = d := by
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · show some (if 0 = 0 then (0 : Fin 3) else 1) = d.state
      rw [if_pos rfl, hstate]
    · funext i q
      show (if i ∈ S then (fun q => if (L : ℤ) - (0 : ℕ) < q then none
          else FinTM.bufferTape (w i) q) else d.workTapes i) q = d.workTapes i q
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, htape i (Or.inl hiS)]
        by_cases hq : (L : ℤ) - (0 : ℕ) < q
        · rw [if_pos hq, eq_comm]
          exact un_buffer_ge _ _ (by rw [hw i (Or.inl hiS)]; push_cast at hq ⊢; omega)
        · rw [if_neg hq]
      · rw [if_neg hiS]
    · funext i
      show (if i ∈ S ∨ i = g then (L : ℤ) - (0 : ℕ) else d.workTapePos i) = d.workTapePos i
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, hpos i hig]
        omega
      · rw [if_neg hig]
  -- one erasing step of the sweep
  have happly : ∀ r : ℕ, r ≤ L →
      (un_bankAct k S g .neg 1).apply (T r) = T (r + 1) := by
    intro r hr
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      show some 1 = some (if r + 1 = 0 then (0 : Fin 3) else 1)
      rw [if_neg (Nat.succ_ne_zero r)]
    · rw [Action.apply_inputPos]
      show moveInputPos (T r).inputPos (un_bankAct k S g .neg 1).inputTape = (T (r + 1)).inputPos
      rw [show (un_bankAct k S g .neg 1).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .neg 1 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        funext q
        rw [Function.update_apply]
        have hps : (T r).workTapePos i = (L : ℤ) - r := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        have htp : (T r).workTapes i =
            fun q => if (L : ℤ) - r < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have htp' : (T (r + 1)).workTapes i =
            fun q => if (L : ℤ) - (r + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        rw [hps, htp, htp']
        dsimp only
        by_cases hq : q = (L : ℤ) - r
        · rw [if_pos hq, eq_comm,
            if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast; omega)]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - r < q
          · rw [if_pos hql,
              if_pos (show (L : ℤ) - (r + 1 : ℕ) < q by push_cast at hql ⊢; omega)]
          · rw [if_neg hql, if_neg (show ¬((L : ℤ) - (r + 1 : ℕ) < q) by
              push_cast at hq hql ⊢; omega)]
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T r).workTapes i = (T (r + 1)).workTapes i
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .neg 1 i).2
      show (T r).workTapePos i + (((un_bankAct k S g .neg 1).workTapes i).2 : ℤ) =
        (T (r + 1)).workTapePos i
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - r else d.workTapePos i) + _ =
        (if i ∈ S ∨ i = g then (L : ℤ) - (r + 1 : ℕ) else d.workTapePos i)
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.neg_eq_neg_one, SignType.coe_neg_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T r).output ++ (none : Option Bool).toList = (T (r + 1)).output
      rw [Option.toList_none, List.append_nil]
  have hstep : ∀ r : ℕ, r ≤ L → (un_bankTM k S g).step (T r) = T (r + 1) := by
    intro r hr
    have hs : (T r).state = some (if r = 0 then 0 else 1) := rfl
    rw [MultiTapeTM.step_of_some hs]
    have htr : (un_bankTM k S g).tr (if r = 0 then 0 else 1) (T r).inputSymbol
        (T r).workTapeSymbols = un_bankAct k S g .neg 1 := by
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        simp only [un_bankTM, ↓reduceIte]
      · rw [if_neg hr0]
        have hread : (T r).workTapeSymbols g =
            FinTM.bufferTape (w g) ((L : ℤ) - r) := by
          rw [Cfg.workTapeSymbols_eq]
          have h1 : (T r).workTapes g = FinTM.bufferTape (w g) := by
            show (if g ∈ S then _ else d.workTapes g) = _
            rw [if_neg hg, htape g (Or.inr rfl)]
          have h2 : (T r).workTapePos g = (L : ℤ) - r := by
            show (if g ∈ S ∨ g = g then (L : ℤ) - r else d.workTapePos g) = _
            rw [if_pos (Or.inr rfl)]
          rw [h1, h2]
        have hsome : ∃ b, FinTM.bufferTape (w g) ((L : ℤ) - r) = some b := by
          have hlt : L - r < (w g).length := by rw [hw g (Or.inr rfl)]; omega
          refine ⟨(w g)[L - r], ?_⟩
          rw [show (L : ℤ) - r = ((L - r : ℕ) : ℤ) by omega,
            FinTM.bufferTape_nat, List.getElem?_eq_getElem hlt]
        obtain ⟨b, hb⟩ := hsome
        simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
        rw [hread, hb]
    rw [htr]
    exact happly r hr
  have hrun : ∀ r : ℕ, r ≤ L + 1 → (un_bankTM k S g).runFrom d r = T r := by
    intro r hr
    induction r with
    | zero => rw [MultiTapeTM.runFrom_zero, hT0]
    | succ r ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep r (by omega)]
  -- the final turning step
  have hfinal : (un_bankTM k S g).step (T (L + 1)) =
      { d with
        state := some 2
        workTapes := fun i => if i ∈ S then (fun _ => none) else d.workTapes i
        workTapePos := fun i => if i ∈ S ∨ i = g then 0 else d.workTapePos i } := by
    have hs : (T (L + 1)).state = some 1 := by
      show some (if L + 1 = 0 then (0 : Fin 3) else 1) = some 1
      rw [if_neg (Nat.succ_ne_zero L)]
    rw [MultiTapeTM.step_of_some hs]
    have hread : (T (L + 1)).workTapeSymbols g = none := by
      rw [Cfg.workTapeSymbols_eq]
      have h1 : (T (L + 1)).workTapes g = FinTM.bufferTape (w g) := by
        show (if g ∈ S then _ else d.workTapes g) = _
        rw [if_neg hg, htape g (Or.inr rfl)]
      have h2 : (T (L + 1)).workTapePos g = (L : ℤ) - (L + 1 : ℕ) := by
        show (if g ∈ S ∨ g = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos g) = _
        rw [if_pos (Or.inr rfl)]
      rw [h1, h2]
      exact FinTM.bufferTape_of_neg _ (by push_cast; omega)
    have htr : (un_bankTM k S g).tr 1 (T (L + 1)).inputSymbol (T (L + 1)).workTapeSymbols =
        un_bankAct k S g .pos 2 := by
      simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]
      rw [hread]
    rw [htr]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Action.apply_state]
      rfl
    · rw [Action.apply_inputPos]
      rw [show (un_bankAct k S g .pos 2).inputTape = 0 from rfl, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, (un_bankAct_eq S g .pos 2 i).1]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS, Option.getD_some]
        show Function.update ((T (L + 1)).workTapes i) ((T (L + 1)).workTapePos i) none =
          (if i ∈ S then (fun _ => none) else d.workTapes i)
        rw [if_pos hiS]
        have htp : (T (L + 1)).workTapes i =
            fun q => if (L : ℤ) - (L + 1 : ℕ) < q then none else FinTM.bufferTape (w i) q := by
          show (if i ∈ S then _ else d.workTapes i) = _
          rw [if_pos hiS]
        have hps : (T (L + 1)).workTapePos i = (L : ℤ) - (L + 1 : ℕ) := by
          show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) = _
          rw [if_pos (Or.inl hiS)]
        rw [htp, hps]
        funext q
        rw [Function.update_apply]
        try dsimp only
        by_cases hq : q = (L : ℤ) - (L + 1 : ℕ)
        · rw [if_pos hq]
        · rw [if_neg hq]
          by_cases hql : (L : ℤ) - (L + 1 : ℕ) < q
          · rw [if_pos hql]
          · rw [if_neg hql]
            exact FinTM.bufferTape_of_neg _ (by push_cast at hql ⊢; omega)
      · rw [if_neg hiS, Cfg.workTapeSymbols_eq, Option.getD_none, Function.update_eq_self]
        show (T (L + 1)).workTapes i = (if i ∈ S then _ else d.workTapes i)
        show (if i ∈ S then _ else d.workTapes i) = (if i ∈ S then _ else d.workTapes i)
        rw [if_neg hiS, if_neg hiS]
    · funext i
      rw [Action.apply_workTapePos]
      have hmv := (un_bankAct_eq S g .pos 2 i).2
      show (T (L + 1)).workTapePos i + (((un_bankAct k S g .pos 2).workTapes i).2 : ℤ) =
        (if i ∈ S ∨ i = g then 0 else d.workTapePos i)
      rw [hmv]
      show (if i ∈ S ∨ i = g then (L : ℤ) - (L + 1 : ℕ) else d.workTapePos i) + _ = _
      by_cases hig : i ∈ S ∨ i = g
      · rw [if_pos hig, if_pos hig, if_pos hig]
        rw [SignType.pos_eq_one, SignType.coe_one]
        omega
      · rw [if_neg hig, if_neg hig, if_neg hig, add_zero]
    · rw [Action.apply_output]
      show (T (L + 1)).output ++ (none : Option Bool).toList = d.output
      rw [Option.toList_none, List.append_nil]
  constructor
  · rw [show L + 2 = (L + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      hrun (L + 1) le_rfl, hfinal]
  · intro t ht
    rw [hrun t (by omega)]
    show some (if t = 0 then (0 : Fin 3) else 1) ≠ some 2
    by_cases ht0 : t = 0
    · rw [if_pos ht0]; decide
    · rw [if_neg ht0]; decide

/-- One seam step whose previous endpoint arrives as a right-tagged configuration: the
handover's constant relabeling collapses the tag, so the next phase's framed run applies
verbatim. -/
private theorem un_step' {k : ℕ} {S₀ S₁ S₂ : Type} [DecidableEq S₁] {z : List Bool}
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (q₂ : S₂) (g : S₀ → S₁) {c₀ : Cfg k Bool S₁ z} {c₂ : Cfg k Bool S₀ z}
    {c₃ : Cfg k Bool S₂ z} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₂.mapState g) (hexit : (c₂.mapState g).state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₂.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂, (M₂.runFrom (c₂.mapState fun _ => entry) t).state ≠ some q₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₃.mapState Sum.inr ∧
      (c₃.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr q₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr q₂) := by
  have hcomp : (c₂.mapState g).mapState (fun _ => entry) = c₂.mapState fun _ => entry := by
    rw [Cfg.mapState_mapState]; rfl
  exact seamCompTM_step M₁ exit M₂ entry q₂ h₁ hexit hcut (by rw [hcomp]; exact h₂) hq
    (fun t ht => by rw [hcomp] at *; exact hcut₂ t ht)

/-- **The setup machine.** For the interpreter core's tape count `K` and stream tape `jR`,
the seam chain over `K + kC + 1` tapes — the embedded header pass, the code buffer's rewind
and clear, the guided bank erase, the expansion, the block rewind, the counter clear, and the
input rewind — first reaches its park at the setup hypothesis's exit configuration, within a
per-code linear budget.

**Proof sketch.** The header composite halts at `3|u| + 4 + (4|bits t| + 5)` with the code
buffer `u`, the extractor scratch `bits t` and the captured budget word `bits t` on `cap`
(`Turing.prefixCanon_run`, `Turing.FinTM.pairExtractTM_fst_run`, the cast pair and the
tape-block projections, through `Turing.embedSilentRetTM_run`). The buffer rewind and clear
blank the code buffer; the guided bank erase blanks the extractor scratch while rewinding the
capture head; the expansion writes the `t`-cell block on `ι jR` (`Turing.expandTM_run_ofCfg`,
`Turing.counterValue_bits`); the block rewind, the counter clear and the input rewind reach
the exit configuration. Each seam inherits the first-visit cut, and the ledger is linear by
`Turing.counterOverhead_le` and `Turing.length_bits_le_self`. -/
private theorem un_setup :
    ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
    cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
      (P : MultiTapeTM k Bool SP) (pexit : SP),
      ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
        ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
          (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
          P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
            ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
          ∀ u < TP,
            (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
              some pexit := by
  classical
  intro K jR
  set F : FinTM Bool := FinTM.pairExtractTM true false with hF
  set MC : FinTM Bool := FinTM.bufferedCompTM universalPrefixTM F with hMC
  have hkC : MC.k = universalPrefixTM.k + (1 + F.k) := FinTM.bufferedCompTM_k universalPrefixTM F
  have hup : universalPrefixTM.k = 0 := universalPrefixTM_k
  -- the tape layout: the core's `K`, the composite's `MC.k`, the capture/counter tape last
  let ι : Fin K ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.castAdd MC.k j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_castAdd] at hv
      exact Fin.ext hv⟩
  let ιC : Fin MC.k ↪ Fin (K + MC.k + 1) :=
    ⟨fun j => (Fin.natAdd K j).castSucc, by
      intro a b h
      have hv := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.coe_natAdd] at hv
      exact Fin.ext (by omega)⟩
  let cap : Fin (K + MC.k + 1) := Fin.last (K + MC.k)
  have hvι : ∀ j : Fin K, (ι j).val = j.val := fun j => by
    simp [ι, Fin.coe_castSucc, Fin.coe_castAdd]
  have hvιC : ∀ j : Fin MC.k, (ιC j).val = K + j.val := fun j => by
    simp [ιC, Fin.coe_castSucc, Fin.coe_natAdd]
  have hvcap : cap.val = K + MC.k := Fin.val_last _
  have hcapr : cap ∉ Set.range ι := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvι j, hvcap] at hv
    have := j.isLt
    omega
  have hcaprC : cap ∉ Set.range ιC := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    rw [hvιC j, hvcap] at hv
    have := j.isLt
    omega
  -- the composite's buffer and extractor coordinates, and their images
  let jBuf : Fin MC.k := Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0))
  let jEx : Fin F.k → Fin MC.k := fun e =>
    Fin.cast hkC.symm (Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e))
  let iBuf : Fin (K + MC.k + 1) := ιC jBuf
  let iEx : Fin F.k → Fin (K + MC.k + 1) := fun e => ιC (jEx e)
  let Sx : Finset (Fin (K + MC.k + 1)) := Finset.univ.image iEx
  have hvjBuf : jBuf.val = 0 := by
    simp only [jBuf, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, hup, Fin.val_eq_zero, add_zero]
  have hvjEx : ∀ e : Fin F.k, (jEx e).val = 1 + e.val := fun e => by
    simp only [jEx, Fin.coe_cast, Fin.coe_natAdd, hup, zero_add]
  have hviBuf : iBuf.val = K := by rw [hvιC, hvjBuf]; omega
  have hviEx : ∀ e : Fin F.k, (iEx e).val = K + 1 + e.val := fun e => by
    rw [hvιC, hvjEx]
    omega
  have hSx : ∀ i, i ∈ Sx ↔ ∃ e : Fin F.k, iEx e = i := fun i => by
    constructor
    · intro hi
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp hi
      exact ⟨e, he⟩
    · rintro ⟨e, he⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩
  have hSxval : ∀ i ∈ Sx, ∃ e : Fin F.k, i.val = K + 1 + e.val := by
    intro i hi
    obtain ⟨e, he⟩ := (hSx i).mp hi
    exact ⟨e, by rw [← he, hviEx]⟩
  have hBufSx : iBuf ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval iBuf hi
    rw [hviBuf] at he
    omega
  have hcapSx : cap ∉ Sx := by
    intro hi
    obtain ⟨e, he⟩ := hSxval cap hi
    rw [hvcap] at he
    have := e.isLt
    omega
  have hBufcap : iBuf ≠ cap := by
    intro h
    have hv := congrArg Fin.val h
    rw [hviBuf, hvcap] at hv
    omega
  have hιBuf : ∀ j : Fin K, ι j ≠ iBuf := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hviBuf] at hv
    have := j.isLt
    omega
  have hιcap : ∀ j : Fin K, ι j ≠ cap := by
    intro j h
    have hv := congrArg Fin.val h
    rw [hvι, hvcap] at hv
    have := j.isLt
    omega
  have hιSx : ∀ j : Fin K, ι j ∉ Sx := by
    intro j hi
    obtain ⟨e, he⟩ := hSxval (ι j) hi
    rw [hvι] at he
    have := j.isLt
    omega
  -- the block coordinate inside the expansion's body bank
  let iBlkb : Fin (K + MC.k) := Fin.castAdd MC.k jR
  have hblk_eq : ι jR = iBlkb.castSucc := rfl
  -- the phase machines
  let A1 : MultiTapeTM (K + MC.k + 1) Bool (MC.State ⊕ Unit) := embedSilentRetTM ιC cap MC.tm
  let A2 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) iBuf
  let A3 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) iBuf
  let A4 : MultiTapeTM (K + MC.k + 1) Bool (Fin 3) := un_bankTM (K + MC.k + 1) Sx cap
  let A5 : MultiTapeTM (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) :=
    expandTM (K + MC.k) iBlkb [true]
  let A6 : MultiTapeTM (K + MC.k + 1) Bool RewindPhase := rewindTM (K + MC.k + 1) (ι jR)
  let A7 : MultiTapeTM (K + MC.k + 1) Bool SweepPhase := clearTM (K + MC.k + 1) cap
  let A8 : MultiTapeTM (K + MC.k + 1) Bool InputRewindPhase := inputRewindTM (K + MC.k + 1)
  -- the seam chain and its start override
  let R2 := seamCompTM A1 (Sum.inr ()) A2 RewindPhase.start
  let R3 := seamCompTM R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep
  let R4 := seamCompTM R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3)
  let R5 := seamCompTM R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
  let R6 := seamCompTM R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
  let R7 := seamCompTM R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep
  let R8 := seamCompTM R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
  let P := { R8 with q₀ := (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl
    (Sum.inl MC.tm.q₀))))))))}
  refine ⟨K + MC.k + 1, ι, cap, hcapr, _, inferInstance, inferInstance, P,
    Sum.inr InputRewindPhase.done, fun α => ?_⟩
  refine ⟨7 * α.length + 130, fun x t => ?_⟩
  set bt : List Bool := Nat.bits t with hbt
  set u : List Bool := pairEncode bt α with hu
  set z : List Bool := pairEncode u x with hz
  have hul : u.length = 2 * bt.length + 2 + α.length := by rw [hu, length_pairEncode]
  have hzl : z.length = 2 * u.length + 2 + x.length := by rw [hz, length_pairEncode]
  have hbtt : bt.length ≤ t := length_bits_le_self t
  -- the junction ledgers
  let ip23 : Fin (z.length + 2) := ⟨2 * u.length + 3, by omega⟩
  let tp1 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = iBuf then FinTM.bufferTape u
    else if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let hd1 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = iBuf then (2 * bt.length + 2 : ℤ)
    else if i = cap then (bt.length : ℤ)
    else if i ∈ Sx then (bt.length : ℤ)
    else 0
  let hd2 : Fin (K + MC.k + 1) → ℤ := fun i =>
    if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0
  let tp3 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt
    else if i ∈ Sx then FinTM.bufferTape bt
    else fun _ => none
  let tp4 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then FinTM.bufferTape bt else fun _ => none
  let capW : ℤ → Option Bool := fun q =>
    if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q
  let blk : ℤ → Option Bool := FinTM.bufferTape (List.replicate t true)
  let tp5 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = cap then capW else if i = ι jR then blk else fun _ => none
  let hd5 : Fin (K + MC.k + 1) → ℤ := fun i => if i = ι jR then (t : ℤ) else 0
  let tp7 : Fin (K + MC.k + 1) → ℤ → Option Bool := fun i =>
    if i = ι jR then blk else fun _ => none
  -- the junction configurations
  let E1 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    ⟨some (Sum.inr ()), ip23, tp1, hd1, []⟩
  let E2 : Cfg (K + MC.k + 1) Bool RewindPhase z := ⟨some RewindPhase.done, ip23, tp1, hd2, []⟩
  let E3 : Cfg (K + MC.k + 1) Bool SweepPhase z := ⟨some SweepPhase.done, ip23, tp3, hd2, []⟩
  let E4 : Cfg (K + MC.k + 1) Bool (Fin 3) z := ⟨some 2, ip23, tp4, fun _ => 0, []⟩
  let E5 : Cfg (K + MC.k + 1) Bool (CounterLoopState (Fin 2)) z :=
    ⟨some CounterLoopState.done, ip23, tp5, hd5, []⟩
  let E6 : Cfg (K + MC.k + 1) Bool RewindPhase z :=
    ⟨some RewindPhase.done, ip23, tp5, fun _ => 0, []⟩
  let E7 : Cfg (K + MC.k + 1) Bool SweepPhase z :=
    ⟨some SweepPhase.done, ip23, tp7, fun _ => 0, []⟩
  let E8 : Cfg (K + MC.k + 1) Bool InputRewindPhase z := ⟨some .done, 1, tp7, fun _ => 0, []⟩
  -- the phase times
  let T1 : ℕ := 3 * u.length + 4 + (4 * bt.length + 5)
  let T2 : ℕ := 2 * bt.length + 2 + 2
  let T3 : ℕ := 2 * u.length + 2
  let T4 : ℕ := bt.length + 2
  let T5 : ℕ := t * ([true].length + 1) + counterOverhead bt (t + 1)
  let T6 : ℕ := t + 2
  let T7 : ℕ := 2 * bt.length + 2
  let T8 : ℕ := 2 * u.length + 3 + 1
  -- phase 1: the embedded header pass with its capture
  let c0 : Cfg (K + MC.k + 1) Bool (MC.State ⊕ Unit) z :=
    (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)).mapState
      Sum.inl
  have hs1 : A1.runFrom c0 T1 = E1 ∧ E1.state = some (Sum.inr ()) ∧
      ∀ v < T1, (A1.runFrom c0 v).state ≠ some (Sum.inr ()) := by
    obtain ⟨hhalt, hlive⟩ := un_canon_halt bt α x
    rw [← hF, ← hMC, ← hu, ← hz] at hhalt hlive
    have hc0' : (MC.tm.initCfg z).state ≠ none := by
      rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
      exact Option.some_ne_none _
    obtain ⟨hlock, hend, hcut1⟩ := embedSilentRetTM_run ιC cap hcaprC MC.tm
      (fun _ _ => none) (fun _ => 0) [] [] (MC.tm.initCfg z)
      (3 * u.length + 4 + (4 * bt.length + 5)) hc0' hlive hhalt
    -- the composite's halting configuration, read through the cast pair
    obtain ⟨b', hb⟩ := prefixCanon_run F u x (4 * bt.length + 5)
    simp only [prefixCanonTM_eq] at hb
    have hextr2 : F.tm.runFrom (F.tm.initCfg u) (4 * bt.length + 5) =
        (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
          fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) :=
      (FinTM.pairExtractTM_fst_run bt α).1
    rw [hextr2] at hb
    obtain ⟨fr1, fr2, hbM⟩ : ∃ fr1 fr2,
        MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) =
          FinTM.bufferedSecondCfg universalPrefixTM F
            (⟨none, ⟨2 * bt.length + 3, by omega⟩, fun _ => FinTM.bufferTape bt,
              fun _ => (bt.length : ℤ), bt⟩ : Cfg F.k Bool F.State u) b'
            ⟨2 * u.length + 3, by omega⟩ fr1 fr2 := ⟨_, _, hb⟩
    set CC : Cfg MC.k Bool MC.State z :=
      MC.tm.runFrom (MC.tm.initCfg z) (3 * u.length + 4 + (4 * bt.length + 5)) with hCC
    -- the embedded endpoint's fields
    have hip : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).inputPos =
        ip23 := by
      rw [embedSilentCfg_inputPos, hbM, FinTM.bufferedSecondCfg_inputPos]
    have hout : (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).output = [] :=
      embedSilentCfg_output ιC cap _ _ [] [] CC
    have hcBuf : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) jBuf =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k 0) := by
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjBuf]
      simp [Fin.coe_natAdd, Fin.coe_castAdd, hup]
    have hcEx : ∀ e : Fin F.k, Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) (jEx e) =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 e) := by
      intro e
      refine Fin.ext ?_
      rw [Fin.coe_cast, hvjEx]
      simp only [Fin.coe_natAdd, hup, zero_add]
    have hnr : ∀ i : Fin (K + MC.k + 1), i ≠ iBuf → i ∉ Sx → i ∉ Set.range ιC := by
      intro i hib hiS
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      rw [hvιC] at hv
      have hjlt : j.val < 1 + F.k := by
        have h := j.isLt
        omega
      by_cases hj0 : j.val = 0
      · exact hib (by rw [← hj, show j = jBuf from Fin.ext (by rw [hvjBuf]; exact hj0)])
      · refine hiS ((hSx i).mpr ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩)
        rw [hviEx]
        show K + 1 + (j.val - 1) = i.val
        omega
    have htap : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapes i
        = tp1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapes jBuf = FinTM.bufferTape u := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcBuf, FinTM.tapeBlocks_buffer]
        refine h1.trans (h2.trans ?_)
        show _ = tp1 iBuf
        show _ = (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).1
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then FinTM.bufferTape u else if cap = cap then
            FinTM.bufferTape bt else if cap ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_tape ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapes (jEx e) = FinTM.bufferTape bt := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapes_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then FinTM.bufferTape u else if iEx e = cap then
              FinTM.bufferTape bt else if iEx e ∈ Sx then FinTM.bufferTape bt
              else fun _ => none)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).1
            refine h1.trans ?_
            show _ = (if i = iBuf then FinTM.bufferTape u else if i = cap then
              FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    have hhd : ∀ i, (embedSilentCfg ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC).workTapePos i
        = hd1 i := by
      intro i
      by_cases hib : i = iBuf
      · rw [hib]
        have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] [] CC jBuf
        have h2 : CC.workTapePos jBuf = (2 * bt.length + 2 : ℤ) := by
          rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcBuf, FinTM.tapeBlocks_buffer]
          push_cast
          ring
        refine h1.trans (h2.trans ?_)
        show _ = (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
          (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl]
      · by_cases hic : i = cap
        · rw [hic]
          have h1 := (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] [] CC).2
          have h2 : CC.output = bt := by
            rw [hbM, FinTM.bufferedSecondCfg_output]
          refine h1.trans ?_
          rw [h2, List.nil_append]
          show _ = (if cap = iBuf then (2 * bt.length + 2 : ℤ) else if cap = cap then
            (bt.length : ℤ) else if cap ∈ Sx then (bt.length : ℤ) else 0)
          rw [if_neg (Ne.symm hBufcap), if_pos rfl]
        · by_cases hiS : i ∈ Sx
          · obtain ⟨e, he⟩ := (hSx i).mp hiS
            rw [← he]
            have h1 := embedSilentCfg_selected_pos ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC (jEx e)
            have h2 : CC.workTapePos (jEx e) = (bt.length : ℤ) := by
              rw [hbM, FinTM.bufferedSecondCfg_workTapePos_cast, hcEx, FinTM.tapeBlocks_right]
            refine h1.trans (h2.trans ?_)
            have heS : iEx e ∈ Sx := (hSx (iEx e)).mpr ⟨e, rfl⟩
            have h3 : iEx e ≠ iBuf := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hviBuf] at hv
              omega
            have h4 : iEx e ≠ cap := by
              intro h
              have hv := congrArg Fin.val h
              rw [hviEx, hvcap] at hv
              have := e.isLt
              rw [hkC, hup] at hv
              omega
            show _ = (if iEx e = iBuf then (2 * bt.length + 2 : ℤ) else if iEx e = cap then
              (bt.length : ℤ) else if iEx e ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg h3, if_neg h4, if_pos heS]
          · have h1 := (embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
              CC i (hnr i hib hiS) hic).2
            refine h1.trans ?_
            show _ = (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
              (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
            rw [if_neg hib, if_neg hic, if_neg hiS]
    exact ⟨hend.trans (Cfg.ext rfl hip (funext htap) (funext hhd) hout), rfl, hcut1⟩
  -- phase 2: rewind the code buffer's head to the word start
  have hs2 : A2.runFrom (E1.mapState fun _ => RewindPhase.start) T2 = E2 ∧
      E2.state = some RewindPhase.done ∧
      ∀ v < T2, (A2.runFrom (E1.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E1.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((2 * bt.length + 2 : ℕ) : ℤ) →
        (E1.mapState fun _ => RewindPhase.start).workTapes iBuf
          ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
            (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      show tp1 iBuf (hd1 iBuf - (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then
          FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none)
          ((if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
              (2 * bt.length + 2 : ℕ) + p) = FinTM.bufferTape u p
      rw [if_pos rfl, if_pos rfl]
      congr 1
      push_cast
      ring
    obtain ⟨hrun2, hcut2, -⟩ := rewindTM_run_ofCfg iBuf u (2 * bt.length + 2)
      (by omega) (E1.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun2.trans ?_, rfl, hcut2⟩
    refine Cfg.ext rfl ?_ ?_ ?_ ?_
    · exact Cfg.mapState_inputPos (fun _ => RewindPhase.start) E1
    · funext i q
      exact Cfg.mapState_workTapes (fun _ => RewindPhase.start) E1 i q
    · funext i
      show Function.update (E1.mapState fun _ => RewindPhase.start).workTapePos iBuf
        ((E1.mapState fun _ => RewindPhase.start).workTapePos iBuf -
          ((2 * bt.length + 2 : ℕ) : ℤ)) i = E2.workTapePos i
      rw [Function.update_apply]
      by_cases hib : i = iBuf
      · rw [if_pos hib, hib, Cfg.mapState_workTapePos]
        show hd1 iBuf - (2 * bt.length + 2 : ℕ) = hd2 iBuf
        show (if iBuf = iBuf then (2 * bt.length + 2 : ℤ) else if iBuf = cap then
            (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0) -
            (2 * bt.length + 2 : ℕ) =
          (if iBuf = cap then (bt.length : ℤ) else if iBuf ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_pos rfl, if_neg hBufcap, if_neg hBufSx]
        push_cast
        ring
      · rw [if_neg hib, Cfg.mapState_workTapePos]
        show hd1 i = hd2 i
        show (if i = iBuf then (2 * bt.length + 2 : ℤ) else if i = cap then
            (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
          (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0)
        rw [if_neg hib]
    · exact Cfg.mapState_output (fun _ => RewindPhase.start) E1
  -- phase 3: clear the code buffer
  have hs3 : A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) T3 = E3 ∧
      E3.state = some SweepPhase.done ∧
      ∀ v < T3, (A3.runFrom (E2.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E2.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf = 0 := by
      rw [Cfg.mapState_workTapePos]
      show (if iBuf = cap then (bt.length : ℤ)
        else if iBuf ∈ Sx then (bt.length : ℤ) else 0) = 0
      rw [if_neg hBufcap, if_neg hBufSx]
    have htp : ∀ q', (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf q' =
        FinTM.bufferTape u q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if iBuf = iBuf then FinTM.bufferTape u else if iBuf = cap then FinTM.bufferTape bt
        else if iBuf ∈ Sx then FinTM.bufferTape bt else fun _ => none) q' =
        FinTM.bufferTape u q'
      rw [if_pos rfl]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
        (E2.mapState fun _ => SweepPhase.sweep).workTapes iBuf
          ((E2.mapState fun _ => SweepPhase.sweep).workTapePos iBuf + p) =
          FinTM.bufferTape u p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add]
    obtain ⟨hrun3, hcut3, -⟩ := clearTM_run_ofCfg iBuf u (E2.mapState fun _ => SweepPhase.sweep)
      hst hhw
    refine ⟨hrun3.trans ?_, rfl, hcut3⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E2) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E2 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E2)
    funext i q
    show (if i = iBuf ∧ (E2.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E2.mapState fun _ => SweepPhase.sweep).workTapePos i + (u.length : ℤ) then none
      else (E2.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp3 i q
    by_cases hib : i = iBuf
    · rw [hib, hps, htp]
      have htp3 : tp3 iBuf q = none := by
        show (if iBuf = cap then FinTM.bufferTape bt else if iBuf ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q = none
        rw [if_neg hBufcap, if_neg hBufSx]
      rw [htp3]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (u.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hib hcon.1), Cfg.mapState_workTapes]
      show (if i = iBuf then FinTM.bufferTape u else if i = cap then FinTM.bufferTape bt
        else if i ∈ Sx then FinTM.bufferTape bt else fun _ => none) q =
        (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q
      rw [if_neg hib]
  -- phase 4: the guided bank erase, which also rewinds the capture head
  have hs4 : A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) T4 = E4 ∧
      E4.state = some 2 ∧
      ∀ v < T4, (A4.runFrom (E3.mapState fun _ => (0 : Fin 3)) v).state ≠ some 2 := by
    have htape4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i = FinTM.bufferTape bt := by
      intro i hi
      funext q
      rw [Cfg.mapState_workTapes]
      show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
        else fun _ => none) q = FinTM.bufferTape bt q
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    have hpos4 : ∀ i, i ∈ Sx ∨ i = cap →
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i = (bt.length : ℤ) := by
      intro i hi
      rw [Cfg.mapState_workTapePos]
      show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) =
        (bt.length : ℤ)
      by_cases hic : i = cap
      · rw [if_pos hic]
      · rw [if_neg hic, if_pos (hi.resolve_right hic)]
    obtain ⟨hrun4, hcut4⟩ := un_bank_run Sx cap hcapSx bt.length (fun _ => bt)
      (fun _ _ => rfl) (E3.mapState fun _ => (0 : Fin 3))
      (by rw [Cfg.mapState_state]; rfl) htape4 hpos4
    refine ⟨hrun4.trans ?_, rfl, hcut4⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => (0 : Fin 3)) E3) ?_ ?_
      (Cfg.mapState_output (fun _ => (0 : Fin 3)) E3)
    · funext i q
      show (if i ∈ Sx then (fun _ => none) else
        (E3.mapState fun _ => (0 : Fin 3)).workTapes i) q = tp4 i q
      by_cases hiS : i ∈ Sx
      · rw [if_pos hiS]
        have hic : i ≠ cap := fun h => hcapSx (h ▸ hiS)
        show (none : Option Bool) =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        rw [if_neg hic]
      · rw [if_neg hiS, Cfg.mapState_workTapes]
        show (if i = cap then FinTM.bufferTape bt else if i ∈ Sx then FinTM.bufferTape bt
          else fun _ => none) q =
          (if i = cap then FinTM.bufferTape bt else fun _ => none) q
        by_cases hic : i = cap
        · rw [if_pos hic, if_pos hic]
        · rw [if_neg hic, if_neg hic, if_neg hiS]
    · funext i
      show (if i ∈ Sx ∨ i = cap then 0 else
        (E3.mapState fun _ => (0 : Fin 3)).workTapePos i) = (0 : ℤ)
      by_cases hig : i ∈ Sx ∨ i = cap
      · rw [if_pos hig]
      · rw [if_neg hig, Cfg.mapState_workTapePos]
        show (if i = cap then (bt.length : ℤ) else if i ∈ Sx then (bt.length : ℤ) else 0) = 0
        rw [if_neg (fun h => hig (Or.inr h)), if_neg (fun h => hig (Or.inl h))]
  -- phase 5: the expansion of the captured budget word into the unary block
  have hd5' : Nat.ofDigits 2 (bt.map Bool.toNat) = t :=
    (counterValue_eq bt).symm.trans (counterValue_bits t)
  have hs5 : A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) T5 = E5 ∧
      E5.state = some CounterLoopState.done ∧
      ∀ v < T5, (A5.runFrom (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) v).state ≠
        some CounterLoopState.done := by
    -- the junction into the counter host's layout
    have hJ5 : (E4.mapState fun _ => CounterLoopState.dec FlagPhase.run) =
        counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
          (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
            Cfg (K + MC.k) Bool (Fin 2) z) (FinTM.bufferTape bt) 0 := by
      rw [counter_cfg_eq]
      refine Cfg.ext ?_
        (Cfg.mapState_inputPos (fun _ => CounterLoopState.dec FlagPhase.run) E4) ?_ ?_
        (Cfg.mapState_output (fun _ => CounterLoopState.dec FlagPhase.run) E4)
      · rw [Cfg.mapState_state]
        rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          rw [Cfg.mapState_workTapes]
          show (if cap = cap then FinTM.bufferTape bt else fun _ => none) q =
            FinTM.bufferTape bt q
          rw [if_pos rfl]
        · rw [Fin.lastCases_castSucc]
          funext q
          rw [Cfg.mapState_workTapes]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          rw [Cfg.mapState_workTapePos]
        · rw [Fin.lastCases_castSucc]
          rw [Cfg.mapState_workTapePos]
    have hrow := expandTM_run_ofCfg (x := z) iBlkb [true]
      (⟨some 0, ip23, fun j => tp4 j.castSucc, fun _ => 0, []⟩ :
        Cfg (K + MC.k) Bool (Fin 2) z) rfl bt (FinTM.bufferTape bt) 0
      (fun p _ _ => by rw [zero_add]) t hd5'
    have hlen1 : ([true] : List Bool).length = 1 := rfl
    refine ⟨?_, rfl, ?_⟩
    · rw [hJ5]
      refine hrow.1.trans ?_
      rw [counter_cfg_eq]
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          funext q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) = tp5 (Fin.last (K + MC.k)) q
          show (if 0 ≤ q ∧ q < 0 + (bt.length : ℤ) then some true
            else FinTM.bufferTape bt q) =
            (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q
          rw [if_pos rfl, zero_add]
        · rw [Fin.lastCases_castSucc]
          funext q
          show (if j' = iBlkb ∧ (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ) then
              FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
            else tp4 (Fin.castSucc j') q) = tp5 (Fin.castSucc j') q
          have hne : Fin.castSucc j' ≠ cap := by
            intro h
            have hv := congrArg Fin.val h
            rw [Fin.coe_castSucc, hvcap] at hv
            have := j'.isLt
            omega
          by_cases hjb : j' = iBlkb
          · rw [hjb]
            show (if iBlkb = iBlkb ∧ (0 : ℤ) ≤ q ∧
                  q < 0 + ((t * [true].length : ℕ) : ℤ) then
                FinTM.bufferTape (List.replicate t [true]).flatten (q - 0)
              else tp4 (Fin.castSucc iBlkb) q) = tp5 (Fin.castSucc iBlkb) q
            have htp5v : tp5 (Fin.castSucc iBlkb) q = blk q := by
              show (if Fin.castSucc iBlkb = cap then capW else if Fin.castSucc iBlkb = ι jR
                then blk else fun _ => none) q = blk q
              rw [if_neg (hjb ▸ hne),
                if_pos (show Fin.castSucc iBlkb = ι jR from rfl)]
            rw [htp5v]
            by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + ((t * [true].length : ℕ) : ℤ)
            · rw [if_pos ⟨rfl, hq.1, hq.2⟩, un_flatten, sub_zero]
            · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
              show tp4 (Fin.castSucc iBlkb) q = blk q
              show (if Fin.castSucc iBlkb = cap then FinTM.bufferTape bt else fun _ => none) q =
                blk q
              rw [if_neg (hjb ▸ hne)]
              rw [eq_comm]
              rcases lt_or_ge q 0 with h0 | h0
              · exact FinTM.bufferTape_of_neg _ h0
              · refine un_buffer_ge _ _ ?_
                rw [List.length_replicate]
                rw [hlen1] at hq
                push_cast at hq ⊢
                omega
          · rw [if_neg (fun hcon => hjb hcon.1)]
            have hnj : Fin.castSucc j' ≠ ι jR := by
              intro h
              exact hjb (Fin.castSucc_injective _ h)
            show (if Fin.castSucc j' = cap then FinTM.bufferTape bt else fun _ => none) q =
              (if Fin.castSucc j' = cap then capW else if Fin.castSucc j' = ι jR then blk
                else fun _ => none) q
            rw [if_neg hne, if_neg hne, if_neg hnj]
      · funext j
        dsimp only
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · rw [Fin.lastCases_last]
          show (0 : ℤ) = hd5 (Fin.last (K + MC.k))
          show (0 : ℤ) = (if cap = ι jR then (t : ℤ) else 0)
          rw [if_neg (Ne.symm (hιcap jR))]
        · rw [Fin.lastCases_castSucc]
          rw [Function.update_apply]
          by_cases hjb : j' = iBlkb
          · rw [if_pos hjb, hjb]
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) = hd5 (Fin.castSucc iBlkb)
            show (0 : ℤ) + ((t * [true].length : ℕ) : ℤ) =
              (if Fin.castSucc iBlkb = ι jR then (t : ℤ) else 0)
            rw [if_pos (show Fin.castSucc iBlkb = ι jR from rfl), hlen1]
            push_cast
            ring
          · rw [if_neg hjb]
            have hnj : Fin.castSucc j' ≠ ι jR := fun h => hjb (Fin.castSucc_injective _ h)
            show (0 : ℤ) = (if Fin.castSucc j' = ι jR then (t : ℤ) else 0)
            rw [if_neg hnj]
    · intro v hv
      rw [hJ5]
      exact (hrow.2.1 v hv).1
  -- phase 6: rewind the block head
  have hs6 : A6.runFrom (E5.mapState fun _ => RewindPhase.start) T6 = E6 ∧
      E6.state = some RewindPhase.done ∧
      ∀ v < T6, (A6.runFrom (E5.mapState fun _ => RewindPhase.start) v).state ≠
        some RewindPhase.done := by
    have hst : (E5.mapState fun _ => RewindPhase.start).state = some RewindPhase.start := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) = (t : ℤ) := by
      rw [Cfg.mapState_workTapePos]
      show (if ι jR = ι jR then (t : ℤ) else 0) = (t : ℤ)
      rw [if_pos rfl]
    have htp : ∀ q', (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR) q' =
        blk q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if ι jR = cap then capW else if ι jR = ι jR then blk else fun _ => none) q' = blk q'
      rw [if_neg (hιcap jR), if_pos rfl]
    have hhu : ∀ p : ℤ, -1 ≤ p → p < ((t : ℕ) : ℤ) →
        (E5.mapState fun _ => RewindPhase.start).workTapes (ι jR)
          ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - (t : ℕ) + p) =
          FinTM.bufferTape (List.replicate t true) p := by
      intro p hp1 hp2
      rw [hps, htp]
      show FinTM.bufferTape (List.replicate t true) ((t : ℤ) - (t : ℕ) + p) = _
      congr 1
      ring
    obtain ⟨hrun6, hcut6, -⟩ := rewindTM_run_ofCfg (ι jR) (List.replicate t true) t
      (by simp) (E5.mapState fun _ => RewindPhase.start) hst hhu
    refine ⟨hrun6.trans ?_, rfl, hcut6⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => RewindPhase.start) E5) ?_ ?_
      (Cfg.mapState_output (fun _ => RewindPhase.start) E5)
    · funext i q
      show (E5.mapState fun _ => RewindPhase.start).workTapes i q = tp5 i q
      rw [Cfg.mapState_workTapes]
    · funext i
      show Function.update (E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR)
        ((E5.mapState fun _ => RewindPhase.start).workTapePos (ι jR) - ((t : ℕ) : ℤ)) i =
        (0 : ℤ)
      rw [Function.update_apply]
      by_cases hij : i = ι jR
      · rw [if_pos hij, hps]
        ring
      · rw [if_neg hij, Cfg.mapState_workTapePos]
        show (if i = ι jR then (t : ℤ) else 0) = 0
        rw [if_neg hij]
  -- phase 7: clear the counter word
  have hs7 : A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) T7 = E7 ∧
      E7.state = some SweepPhase.done ∧
      ∀ v < T7, (A7.runFrom (E6.mapState fun _ => SweepPhase.sweep) v).state ≠
        some SweepPhase.done := by
    have hst : (E6.mapState fun _ => SweepPhase.sweep).state = some SweepPhase.sweep := by
      rw [Cfg.mapState_state]
      rfl
    have hps : (E6.mapState fun _ => SweepPhase.sweep).workTapePos cap = 0 :=
      Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 cap
    have htp : ∀ q', (E6.mapState fun _ => SweepPhase.sweep).workTapes cap q' = capW q' := by
      intro q'
      rw [Cfg.mapState_workTapes]
      show (if cap = cap then capW else if cap = ι jR then blk else fun _ => none) q' = capW q'
      rw [if_pos rfl]
    have hcapN : ∀ p : ℤ, capW p = FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p
      show (if 0 ≤ p ∧ p < (bt.length : ℤ) then some true else FinTM.bufferTape bt p) = _
      by_cases hp : 0 ≤ p ∧ p < (bt.length : ℤ)
      · rw [if_pos hp]
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
          ⟨p.toNat, (Int.toNat_of_nonneg hp.1).symm⟩
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
          rw [List.length_replicate]
          exact_mod_cast hp.2)]
        rw [List.getElem_replicate]
      · rw [if_neg hp]
        have h1 : FinTM.bufferTape bt p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · exact un_buffer_ge _ _ (by omega)
        have h2 : FinTM.bufferTape (List.replicate bt.length true) p = none := by
          rcases lt_or_ge p 0 with h0 | h0
          · exact FinTM.bufferTape_of_neg _ h0
          · refine un_buffer_ge _ _ ?_
            rw [List.length_replicate]
            omega
        rw [h1, h2]
    have hhw : ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate bt.length true).length : ℤ) →
        (E6.mapState fun _ => SweepPhase.sweep).workTapes cap
          ((E6.mapState fun _ => SweepPhase.sweep).workTapePos cap + p) =
          FinTM.bufferTape (List.replicate bt.length true) p := by
      intro p hp1 hp2
      rw [hps, htp, zero_add, hcapN]
    obtain ⟨hrun7, hcut7, -⟩ := clearTM_run_ofCfg cap (List.replicate bt.length true)
      (E6.mapState fun _ => SweepPhase.sweep) hst hhw
    rw [List.length_replicate] at hrun7 hcut7
    refine ⟨hrun7.trans ?_, rfl, hcut7⟩
    refine Cfg.ext rfl (Cfg.mapState_inputPos (fun _ => SweepPhase.sweep) E6) ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => SweepPhase.sweep) E6 i)
      (Cfg.mapState_output (fun _ => SweepPhase.sweep) E6)
    funext i q
    show (if i = cap ∧ (E6.mapState fun _ => SweepPhase.sweep).workTapePos i ≤ q ∧
        q < (E6.mapState fun _ => SweepPhase.sweep).workTapePos i + (bt.length : ℤ) then none
      else (E6.mapState fun _ => SweepPhase.sweep).workTapes i q) = tp7 i q
    by_cases hic : i = cap
    · rw [hic, hps, htp]
      have htp7 : tp7 cap q = none := by
        show (if cap = ι jR then blk else fun _ => none) q = none
        rw [if_neg (Ne.symm (hιcap jR))]
      rw [htp7]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (bt.length : ℤ)
      · rw [if_pos ⟨rfl, hq.1, hq.2⟩]
      · rw [if_neg (fun hcon => hq ⟨hcon.2.1, hcon.2.2⟩)]
        show capW q = none
        show (if 0 ≤ q ∧ q < (bt.length : ℤ) then some true else FinTM.bufferTape bt q) = none
        rw [if_neg (by omega)]
        rcases lt_or_ge q 0 with h0 | h0
        · exact FinTM.bufferTape_of_neg _ h0
        · exact un_buffer_ge _ _ (by omega)
    · rw [if_neg (fun hcon => hic hcon.1), Cfg.mapState_workTapes]
      show (if i = cap then capW else if i = ι jR then blk else fun _ => none) q =
        (if i = ι jR then blk else fun _ => none) q
      rw [if_neg hic]
  -- phase 8: the input rewind
  have hs8 : A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) T8 = E8 ∧
      E8.state = some .done ∧
      ∀ v < T8, (A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) v).state ≠
        some .done := by
    have hip8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos = ip23 :=
      Cfg.mapState_inputPos _ _
    obtain ⟨hrun8, hcut8, -⟩ := inputRewindTM_run (E7.mapState fun _ => InputRewindPhase.start)
      (by rw [Cfg.mapState_state]; rfl)
      (by rw [hip8]; show 1 ≤ 2 * u.length + 3; omega)
    have hT8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos.val + 1 = T8 := by
      rw [hip8]
    rw [hT8] at hrun8 hcut8
    refine ⟨hrun8.trans ?_, rfl, hcut8⟩
    refine Cfg.ext rfl rfl ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => InputRewindPhase.start) E7 i)
      (Cfg.mapState_output (fun _ => InputRewindPhase.start) E7)
    funext i q
    exact Cfg.mapState_workTapes (fun _ => InputRewindPhase.start) E7 i q
  -- the chain: every seam inherits the run, the exit state and the first-visit cut
  have hch2 := seamCompTM_step A1 (Sum.inr ()) A2 RewindPhase.start RewindPhase.done
    hs1.1 hs1.2.1 hs1.2.2 hs2.1 hs2.2.1 hs2.2.2
  have hch3 := un_step' R2 (Sum.inr RewindPhase.done) A3 SweepPhase.sweep SweepPhase.done
    Sum.inr hch2.1 hch2.2.1 hch2.2.2 hs3.1 rfl hs3.2.2
  have hch4 := un_step' R3 (Sum.inr SweepPhase.done) A4 (0 : Fin 3) (2 : Fin 3)
    Sum.inr hch3.1 hch3.2.1 hch3.2.2 hs4.1 rfl hs4.2.2
  have hch5 := un_step' R4 (Sum.inr (2 : Fin 3)) A5 (CounterLoopState.dec FlagPhase.run)
    CounterLoopState.done Sum.inr hch4.1 hch4.2.1 hch4.2.2 hs5.1 rfl hs5.2.2
  have hch6 := un_step' R5 (Sum.inr CounterLoopState.done) A6 RewindPhase.start
    RewindPhase.done Sum.inr hch5.1 hch5.2.1 hch5.2.2 hs6.1 rfl hs6.2.2
  have hch7 := un_step' R6 (Sum.inr RewindPhase.done) A7 SweepPhase.sweep SweepPhase.done
    Sum.inr hch6.1 hch6.2.1 hch6.2.2 hs7.1 rfl hs7.2.2
  have hch8 := un_step' R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start
    InputRewindPhase.done Sum.inr hch7.1 hch7.2.1 hch7.2.2 hs8.1 rfl hs8.2.2
  -- the start: the machine's initial configuration is the chain's left seam
  have hstart : P.initCfg z =
      ((((((c0.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState
        Sum.inl).mapState Sum.inl).mapState Sum.inl).mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_with_q₀]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state,
        Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
      rfl
    · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    · funext i q
      rw [Cfg.init_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes,
        Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_tape, MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).1,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).1]
    · funext i
      rw [Cfg.init_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      by_cases hsel : ∃ j, ιC j = i
      · obtain ⟨j, rfl⟩ := hsel
        rw [embedSilentCfg_selected_pos, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hic : i = cap
        · rw [hic,
            (embedSilentCfg_cap ιC cap hcaprC (fun _ _ => none) (fun _ => 0) [] []
              (MC.tm.initCfg z)).2,
            MultiTapeTM.initCfg_eq, Cfg.init_output]
          rw [List.append_nil, List.length_nil]
          rfl
        · rw [(embedSilentCfg_unselected ιC cap (fun _ _ => none) (fun _ => 0) [] []
            (MC.tm.initCfg z) i (fun ⟨j, hj⟩ => hsel ⟨j, hj⟩) hic).2]
    · rw [Cfg.init_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, embedSilentCfg_output]
  -- the exit configuration and the block property
  have hblk : ∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t := by
    intro p
    constructor
    · intro h
      by_contra hcon
      apply h
      rcases lt_or_ge p 0 with h0 | h0
      · exact FinTM.bufferTape_of_neg _ h0
      · refine un_buffer_ge _ _ ?_
        rw [List.length_replicate]
        push_cast at hcon ⊢
        omega
    · rintro ⟨h0, hlt⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
        ⟨p.toNat, (Int.toNat_of_nonneg h0).symm⟩
      show FinTM.bufferTape (List.replicate t true) ((n : ℕ) : ℤ) ≠ none
      rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by
        rw [List.length_replicate]
        exact_mod_cast hlt)]
      simp
  have hfin : (E8.mapState (Sum.inr : InputRewindPhase → _)) =
      (⟨some (Sum.inr InputRewindPhase.done), 1, Function.update (fun _ _ => none) (ι jR) blk,
        fun _ => 0, []⟩ :
        Cfg (K + MC.k + 1) Bool ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          Fin 3) ⊕ CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕
          InputRewindPhase) z) := by
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · exact (Cfg.mapState_state (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · exact (Cfg.mapState_inputPos (Sum.inr : InputRewindPhase → _) E8).trans rfl
    · funext i q
      refine (Cfg.mapState_workTapes (Sum.inr : InputRewindPhase → _) E8 i q).trans ?_
      show tp7 i q = Function.update (fun _ _ => none) (ι jR) blk i q
      rw [Function.update_apply]
    · funext i
      exact (Cfg.mapState_workTapePos (Sum.inr : InputRewindPhase → _) E8 i).trans rfl
    · exact (Cfg.mapState_output (Sum.inr : InputRewindPhase → _) E8).trans rfl
  -- the budget
  have hco : counterOverhead bt (t + 1) ≤ 4 * t + 2 * bt.length + 2 := by
    have h := counterOverhead_le bt
    rw [hd5'] at h
    exact h
  refine ⟨T1 + 1 + T2 + 1 + T3 + 1 + T4 + 1 + T5 + 1 + T6 + 1 + T7 + 1 + T8, ?_, blk, hblk,
    ?_, ?_⟩
  · show 3 * u.length + 4 + (4 * bt.length + 5) + 1 + (2 * bt.length + 2 + 2) + 1 +
      (2 * u.length + 2) + 1 + (bt.length + 2) + 1 +
      (t * ([true].length + 1) + counterOverhead bt (t + 1)) + 1 + (t + 2) + 1 +
      (2 * bt.length + 2) + 1 + (2 * u.length + 3 + 1) ≤ (7 * α.length + 130) * (t + 1)
    rw [show ([true] : List Bool).length = 1 from rfl]
    have hexp : (7 * α.length + 130) * (t + 1) =
        7 * (α.length * t) + 7 * α.length + 130 * t + 130 := by ring
    rw [hexp]
    have hA : α.length * t ≥ 0 := Nat.zero_le _
    omega
  · have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    show P.runFrom (P.initCfg z) _ = _
    rw [hstart, hPrun]
    exact hch8.1.trans hfin
  · intro v hv
    have hPrun : ∀ (c : Cfg (K + MC.k + 1) Bool
        ((((((((MC.State ⊕ Unit) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ Fin 3) ⊕
          CounterLoopState (Fin 2)) ⊕ RewindPhase) ⊕ SweepPhase) ⊕ InputRewindPhase) z) (n : ℕ),
        P.runFrom c n = R8.runFrom c n :=
      fun c n => MultiTapeTM.runFrom_with_q₀ R8 _ c n
    rw [hstart, hPrun]
    exact hch8.2.2 v hv

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`.

**Implementation.** The setup before the guess is one seam chain of eight phases: the prefix
canonizer `Turing.prefixCanonTM` with the first-component extractor, embedded silently with its
output `bits t` captured on a scratch tape; the code buffer's rewind and clear; an erase of the
extractor's scratch tapes that also rewinds the capture; the expansion of `bits t` into the
unary block (`Turing.expandTM`); the block's rewind; the counter's clear; and the input rewind.
It first reaches its exit within `(7·|α| + 130)·(t + 1)` steps, with no `|x|` term, so the
constant is `C = C_P + C_R + 13` with `C_P = 7·|α| + 130` and `C_R` the core's. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  exact un_universal_of_setup c un_setup

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. `E` itself is
`Turing.FinNDTM.exists_exhaustiveDecider`, proved (iterative deepening over the
choice words of the fixed `UN`, each replayed by its replay machine under the
step-clocked runner, with a window clear between replays; no `|x|` term), so the
decider's only open dependency is the universal NDTM's interpreter core
`Turing.exists_ndInterpreterCore`. The proof applies
`Turing.ndAcceptsWithin_decider_of_universal` to `Turing.exists_timed_universal_NDTM`. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  exact ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)

end Turing

namespace Complexity

open Turing

/-- The chain's induction: `P n ↔ P (n + 1)` for `a ≤ n < b` gives `P a ↔ P b`.

**Proof sketch.** Induction on `b` from `a`, composing the step at `b`. -/
private theorem nh_chain (P : ℕ → Prop) {a b : ℕ} (hab : a ≤ b)
    (step : ∀ n, a ≤ n → n < b → (P n ↔ P (n + 1))) : P a ↔ P b := by
  induction b, hab using Nat.le_induction with
  | base => exact Iff.rfl
  | succ b hab ih =>
    exact (ih fun n h1 h2 => step n h1 (by omega)).trans (step b hab (by omega))

/-- Finite absorption: a function eventually below `g` is below `F · (g + 1)`.

**Proof sketch.** Take `F` one more than the sum of `f` below `N₀`: beyond `N₀` the first summand
pays, below it the sum does. -/
private theorem nh_absorb (f g : ℕ → ℕ) (N₀ : ℕ) (h : ∀ n ≥ N₀, f n ≤ g n) :
    ∃ F : ℕ, ∀ n, f n ≤ F * (g n + 1) := by
  refine ⟨1 + ∑ m ∈ Finset.range N₀, f m, fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · have h1 := h n hn
    nlinarith [Nat.zero_le (∑ m ∈ Finset.range N₀, f m)]
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have h2 := Finset.single_le_sum (fun m _ => Nat.zero_le (f m)) hmem
    nlinarith [Nat.zero_le (g n)]

/-- A constant factor folds into the membership constant: `NTIME (F · T) ⊆ NTIME T`.

**Proof sketch.** A decider within `a · (F · T n)` decides within `(a F) · T n`
(`Complexity.mem_NTIME_iff`, `Turing.FinNDTM.decidesInTime_iff`). -/
private theorem nh_fold {T : ℕ → ℕ} (F : ℕ) : NTIME (fun n => F * T n) ⊆ NTIME T := by
  intro L hL
  obtain ⟨a, N, hN⟩ := mem_NTIME_iff.mp hL
  apply mem_NTIME_iff.mpr
  refine ⟨a * F, N, FinNDTM.decidesInTime_iff.mpr ?_⟩
  intro x
  simpa only [Nat.mul_assoc] using (FinNDTM.decidesInTime_iff.mp hN x)

/-- The inclusion `NTIME f ⊆ NTIME (g + 1)` under the domination hypothesis.

**Proof sketch.** The hypothesis at `A = 1` gives `f n ≤ g n` eventually; absorb the finitely many
smaller lengths (`nh_absorb`), apply `NTIME.mono`, and fold the factor `F` into the membership
constant (`nh_fold`). -/
private theorem nh_inclusion {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊆ NTIME (fun n => g n + 1) := by
  obtain ⟨N₀, hN₀⟩ := hfg 1
  obtain ⟨F, hF⟩ := nh_absorb f g N₀ (fun n hn => by have := hN₀ n hn; omega)
  intro L hL
  have h1 : L ∈ NTIME (fun n => F * (g n + 1)) := NTIME.mono hF hL
  exact nh_fold F h1

/-- The top's threshold: `C · 2^{C (T + 1)} ≤ 2^{T²}` for every large `T`.

**Proof sketch.** `C < 2^C`, so the left side is below `2^{C + C (T + 1)}`, and
`C + C (T + 1) ≤ T²` once `T ≥ 2C + 2`. -/
private theorem nh_top (C : ℕ) : ∃ T₀, ∀ T ≥ T₀, C * 2 ^ (C * (T + 1)) ≤ 2 ^ (T ^ 2) := by
  refine ⟨2 * C + 2, fun T hT => ?_⟩
  have hC : C < 2 ^ C := Nat.lt_two_pow_self
  calc C * 2 ^ (C * (T + 1)) ≤ 2 ^ C * 2 ^ (C * (T + 1)) := Nat.mul_le_mul_right _ hC.le
    _ = 2 ^ (C + C * (T + 1)) := by rw [← pow_add]
    _ ≤ 2 ^ (T ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul_right T hT])

/-- The bottom's threshold: `C₁ (c₀ · fa + 1) ≤ (fa + a + 1)²` once `a ≥ C₁ (c₀ + 1)`.

**Proof sketch.** Then `C₁ c₀ ≤ a` and `C₁ ≤ a`, and the square's cross terms pay for both. -/
private theorem nh_bottom (C₁ c₀ fa a : ℕ) (ha : C₁ * (c₀ + 1) ≤ a) :
    C₁ * (c₀ * fa + 1) ≤ (fa + a + 1) ^ 2 := by
  have h1 : C₁ * c₀ ≤ a := by nlinarith
  have h2 : C₁ ≤ a := by nlinarith
  nlinarith [Nat.mul_le_mul_right fa h1]

/-- The middle's threshold: `C (C₁ (c₀ · f (n + 1) + 1) + 1) ≤ g n` for every large `n`.

**Proof sketch.** The left side is at most `(C C₁ (c₀ + 1) + C) · (f (n + 1) + 1)`, a ring
identity; the domination hypothesis at that constant bounds it by `g n`. -/
private theorem nh_middle {f g : ℕ → ℕ}
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) (C C₁ c₀ : ℕ) :
    ∃ N, ∀ n ≥ N, C * (C₁ * (c₀ * f (n + 1) + 1) + 1) ≤ g n := by
  obtain ⟨N, hN⟩ := hfg (C * C₁ * (c₀ + 1) + C)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have hid : C * (C₁ * (c₀ * f (n + 1) + 1) + 1) +
      (C * C₁ * f (n + 1) + C * f (n + 1) + C * C₁ * c₀) =
      (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := by ring
  calc C * (C₁ * (c₀ * f (n + 1) + 1) + 1)
      ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + 1) := Nat.le.intro hid
    _ ≤ (C * C₁ * (c₀ + 1) + C) * (f (n + 1) + f n + n + 1) :=
        Nat.mul_le_mul_left _ (by omega)

/-- A late stage of a code: some stage of `α` has its bottom rung beyond `N`.

**Proof sketch.** Every code recurs at stages beyond any bound
(`Turing.NTimeDiag.stageCode_frequently`), and the ladder dominates the index
(`Turing.NTimeDiag.le_ladder`). -/
private theorem nh_stage (f : ℕ → ℕ) (α : List Bool) (N : ℕ) :
    ∃ i, N ≤ Turing.NTimeDiag.ladder f i ∧ Turing.NTimeDiag.stageCode i = α := by
  obtain ⟨i, hi, hα⟩ := Turing.NTimeDiag.stageCode_frequently α N
  exact ⟨i, by have := Turing.NTimeDiag.le_ladder f i; omega, hα⟩

/-- **Truncation at the all-branch budget.** If every branch of `N` on `x` halts within `T`, an
acceptance of `x` at any length is an acceptance within `T`.

**Proof sketch.** At a length `t ≤ T`, pad (`Turing.FinNDTM.AcceptsWithin.mono`). At `t > T`, the
accepting word runs as its length-`T` prefix, which has halted (`Turing.run_take_of_halted`, with
absorption by `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`), so it accepts. -/
private theorem nh_accepts_of_halts {N : FinNDTM Bool} {x : List Bool} {T t : ℕ}
    (hT : N.tm.HaltsWithin x T) (ht : N.AcceptsWithin x t) : N.AcceptsWithin x T := by
  rcases le_or_gt t T with hle | hlt
  · exact ht.mono hle
  · obtain ⟨w, hw, -, hout⟩ := FinNDTM.acceptsWithin_iff.mp ht
    obtain ⟨hlen, hp, hr⟩ := run_take_of_halted (fun w => N.tm.runWith w (N.tm.initCfg x))
      (fun c => c.state = none)
      (fun w w' h => by simp only [NDTM.runWith_append w w' (N.tm.initCfg x),
        NDTM.runWith_of_halt _ h])
      (NDTM.haltsWithin_iff.mp hT) (w := w) (by omega)
    exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take T, hlen, hp, hr ▸ hout⟩

/-- **A decider's language from an unbounded acceptance.** If `N` decides `L` within `T`, any
acceptance of `x`, at any length, puts `x` in `L`.

**Proof sketch.** Truncate the acceptance at `N`'s all-branch budget on `x`
(`nh_accepts_of_halts`); the decider's clause reads membership off it. -/
private theorem nh_mem_of_accepts {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (hN : N.DecidesInTime L T) {x : List Bool} (ht : ∃ t, N.AcceptsWithin x t) : x ∈ L := by
  obtain ⟨t, ht⟩ := ht
  exact ((FinNDTM.decidesInTime_iff.mp hN x).2).mpr
    (nh_accepts_of_halts (FinNDTM.decidesInTime_iff.mp hN x).1 ht)

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2]; [Coo72]): for
time-constructible `f` and `g`, if every constant multiple of `f(n+1) + f(n) + n + 1` is eventually
below `g(n)` — the book's `f(n+1) = o(g(n))` with the two addends of the module docstring — then
`NTIME f ⊊ NTIME (g + 1)`. The overhead on `f` is linear, as in the book, in contrast to the
received deterministic hierarchy's square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives `f n ≤ g n` eventually, and the
finitely many smaller lengths are absorbed into the constant (no monotonicity of `f` is needed).

*Strictness* is lazy diagonalization [AB09, proof of Theorem 3.2 and Figure 3.1]. Fix an effective
scheme `c` (`Turing.exists_effectiveNDMachineCode`) and take the diagonalizer `D` of
`Turing.NTimeDiag.exists_diagonalizer`, given the exponential decider
`Turing.exists_ndAcceptsWithin_decider`. Its language `L`, acceptance of `x` within
`K · (g |x| + 1)`, is in `NTIME (g + 1)` (`Turing.NTimeDiag.acceptLang_mem_NTIME`). Suppose `N`
decides `L` within `c₀ · f`. The linear coded normal form
(`Turing.FinNDTM.exists_codeNDTM_accepts_linear`) gives a coded machine `M'` and a constant `C₁`:
an acceptance by `N` within `t` is one by `M'` within `C₁ (t + 1)`, and an acceptance by `M'` is
one by `N` at some length. Let `C` be the diagonalizer's constant for `M'`'s code, and take a
stage `i` of that code whose bottom rung `ℓᵢ` lies beyond the three thresholds below
(`Turing.NTimeDiag.stageCode_frequently`). On unary words:
- **the middle**, for `ℓᵢ < n < ℓᵢ₊₁`: `1ⁿ ∈ L ↔ 1ⁿ⁺¹ ∈ L`. Forward, `D`'s acceptance gives
  `M'`'s within `g n`, hence `N`'s at some length; an acceptance at any length is one within
  `N`'s all-branch budget, so `1ⁿ⁺¹ ∈ L`. Backward, `N`'s acceptance within `c₀ · f (n + 1)`
  gives `M'`'s within `t' = C₁ (c₀ · f (n + 1) + 1)`, and the hypothesis puts `C (t' + 1)` below
  `g n`;
- **the chain** of these steps: `1^{ℓᵢ + 1} ∈ L ↔ 1^{ℓᵢ₊₁} ∈ L`;
- **the top**, at `n = ℓᵢ₊₁ = 2^{T*²}` with `T* = budget f ℓᵢ`: `1ⁿ ∈ L` iff `M'` does not accept
  `1^{ℓᵢ + 1}` within `T*`, since `C · 2^{C (T* + 1)} ≤ 2^{T*²}` once `T*` is large;
- **the bottom**, at `a = ℓᵢ + 1`: `M'` accepts `1ᵃ` within `T*` iff `1ᵃ ∈ L`, since
  `T* = (f a + a + 1)² ≥ C₁ (c₀ · f a + 1)` once `a ≥ C₁ (c₀ + 1)`.

Together they give `1ᵃ ∈ L ↔ 1ᵃ ∉ L`.

**Implementation.** The private lemmas before this theorem:
- the chain's induction (`nh_chain`);
- the absorption, the constant fold and the inclusion (`nh_absorb`, `nh_fold`, `nh_inclusion`);
- the three thresholds (`nh_top`, `nh_bottom`, `nh_middle`);
- a late stage of a code (`nh_stage`);
- the truncation of an acceptance at an all-branch budget (`nh_accepts_of_halts`, through
  `Turing.run_take_of_halted`), and its reading for a decider (`nh_mem_of_accepts`).

The diagonalizer and the linear coded normal form are cited as contracts. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  obtain ⟨c⟩ := exists_effectiveNDMachineCode
  obtain ⟨D, K, hhalt, hD⟩ :=
    NTimeDiag.exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)
  refine (Set.ssubset_iff_of_subset (nh_inclusion hfg)).mpr
    ⟨_, NTimeDiag.acceptLang_mem_NTIME D K g hhalt, fun hLf => ?_⟩
  set L : Language Bool := {x | D.AcceptsWithin x (K * (g x.length + 1))} with hL
  have hmemL : ∀ m, List.replicate m true ∈ L ↔
      D.AcceptsWithin (List.replicate m true) (K * (g m + 1)) := by
    intro m
    change D.AcceptsWithin (List.replicate m true)
      (K * (g (List.replicate m true).length + 1)) ↔ _
    rw [List.length_replicate]
  obtain ⟨c₀, N, hN⟩ := mem_NTIME_iff.mp hLf
  have hdec : ∀ m, List.replicate m true ∈ L →
      N.AcceptsWithin (List.replicate m true) (c₀ * f m) := by
    intro m hm
    have h := ((FinNDTM.decidesInTime_iff.mp hN (List.replicate m true)).2).mp hm
    rwa [List.length_replicate] at h
  obtain ⟨M', C₁, hfwd, hbwd⟩ := FinNDTM.exists_codeNDTM_accepts_linear N
  obtain ⟨C, hC⟩ := hD (c.encode M')
  rw [c.toNDMachineCode.decode_encode M'] at hC
  obtain ⟨N₁, hN₁⟩ := nh_middle hfg C C₁ c₀
  obtain ⟨T₀, hT₀⟩ := nh_top C
  obtain ⟨i, hi, hiα⟩ := nh_stage f (c.encode M') (N₁ + T₀ + C₁ * (c₀ + 1))
  have hℓ2 : 2 ≤ NTimeDiag.ladder f i := by have := NTimeDiag.le_ladder f i; omega
  have hlt : NTimeDiag.ladder f i < NTimeDiag.ladder f (i + 1) :=
    NTimeDiag.ladder_strictMono f (Nat.lt_succ_self i)
  -- the middle step, at every `n` with `ℓᵢ < n < ℓᵢ₊₁`
  have hmid : ∀ n, NTimeDiag.ladder f i + 1 ≤ n → n < NTimeDiag.ladder f (i + 1) →
      (List.replicate n true ∈ L ↔ List.replicate (n + 1) true ∈ L) := by
    intro n h1 h2
    have hs : NTimeDiag.stage f n = i := NTimeDiag.stage_eq f (by omega) h2.le
    obtain ⟨hmidC, -⟩ := hC n (by omega) (by rw [hs]; exact hiα)
    obtain ⟨hsound, hcompl⟩ := hmidC (by rw [hs]; omega)
    constructor
    · intro hn
      exact nh_mem_of_accepts hN (hbwd _ _ (hsound ((hmemL n).mp hn)))
    · intro hn1
      exact (hmemL n).mpr (hcompl _ (hfwd _ _ (hdec (n + 1) hn1)) (hN₁ n (by omega)))
  have hchain := nh_chain (fun m => List.replicate m true ∈ L)
    (show NTimeDiag.ladder f i + 1 ≤ NTimeDiag.ladder f (i + 1) by omega) hmid
  -- the top's flip, at `n = ℓᵢ₊₁`
  have htop : List.replicate (NTimeDiag.ladder f (i + 1)) true ∈ L ↔
      ¬M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
        (NTimeDiag.budget f (NTimeDiag.ladder f i)) := by
    have hs : NTimeDiag.stage f (NTimeDiag.ladder f (i + 1)) = i :=
      NTimeDiag.stage_eq f hlt le_rfl
    obtain ⟨-, htopC⟩ := hC (NTimeDiag.ladder f (i + 1)) (by omega) (by rw [hs]; exact hiα)
    rw [hs] at htopC
    have hTle : T₀ ≤ NTimeDiag.budget f (NTimeDiag.ladder f i) := by
      rw [NTimeDiag.budget_eq]
      calc T₀ ≤ f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1 := by omega
        _ ≤ (f (NTimeDiag.ladder f i + 1) + (NTimeDiag.ladder f i + 1) + 1) ^ 2 :=
          Nat.le_self_pow (by norm_num) _
    have hthr : C * 2 ^ (C * (NTimeDiag.budget f (NTimeDiag.ladder f i) + 1)) ≤
        NTimeDiag.ladder f (i + 1) := by
      rw [NTimeDiag.ladder_succ f i]
      exact hT₀ _ hTle
    rw [hmemL]
    exact htopC rfl hthr
  -- the bottom's transfer, at `a = ℓᵢ + 1` within `T*`
  have hbot : M'.toFinNDTM.AcceptsWithin (List.replicate (NTimeDiag.ladder f i + 1) true)
      (NTimeDiag.budget f (NTimeDiag.ladder f i)) ↔
      List.replicate (NTimeDiag.ladder f i + 1) true ∈ L := by
    constructor
    · intro hM
      exact nh_mem_of_accepts hN (hbwd _ _ hM)
    · intro hx
      refine (hfwd _ _ (hdec _ hx)).mono ?_
      rw [NTimeDiag.budget_eq]
      exact nh_bottom C₁ c₀ _ _ (by omega)
  exact iff_not_self (hchain.trans (htop.trans (not_congr hbot)))

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`.

Formally, the factor `2` is absorbed into the membership witness's constant by the private
`nh_fold`, which the inclusion half of `Complexity.ntime_hierarchy` also uses. -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  have hback : NTIME (fun n => g n + 1) ⊆ NTIME g := by
    intro L hL
    have hscale : L ∈ NTIME (fun n => 2 * g n) :=
      NTIME.mono (fun n => by have := hpos n; omega) hL
    exact nh_fold 2 hscale
  have heq : NTIME (fun n => g n + 1) = NTIME g :=
    Set.Subset.antisymm hback (NTIME.mono (fun n => Nat.le_succ (g n)))
  simpa only [heq] using ntime_hierarchy hf hg hfg

/-- **The showcase separation**:
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
The two constructibility witnesses are `Complexity.timeConstructible_poly` at
`(C, c) = (1, 0)` and `(1, 1)`; domination takes `N = 3A + 4` and multiplies `N ≤ n` by `n`. -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  have hf : TimeConstructible (fun n => n + 1) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (0 + 1)) = (fun n => n + 1) := by
      funext n
      simp only [Nat.zero_add, pow_one, one_mul]
    rw [← h]
    exact timeConstructible_poly 1 0 (by decide)
  have hg : TimeConstructible (fun n => (n + 1) ^ 2) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (1 + 1)) = (fun n => (n + 1) ^ 2) := by
      funext n
      simp only [one_mul]
    rw [← h]
    exact timeConstructible_poly 1 1 (by decide)
  apply ntime_hierarchy_of_pos hf hg
  · intro n
    exact pow_pos (Nat.succ_pos n) _
  · intro A
    refine ⟨3 * A + 4, fun n hn => ?_⟩
    nlinarith [Nat.mul_le_mul_right n hn]

end Complexity
```
