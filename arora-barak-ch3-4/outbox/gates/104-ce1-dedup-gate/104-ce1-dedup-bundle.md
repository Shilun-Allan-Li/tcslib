## ===== campaign/gates/104-ce1-dedup/pack.md =====

# External audit pack: dedup CE-1, one equal-codes lemma (PR #213, a dedup gate)

## Why this PR

The dedup window (12.2c), opened on 2026-11-06 by the user, retires the ledger's acknowledged
families one PR at a time. **CE-1** (`campaign/duplication-ledger.md`): equal codes of window
configurations give equal vertices. The same statement had the same one-line proof through
`coreSum_eq_of_cfgWord_eq` in two places:
- `Complexity.ExpBFS.coreSum_eq_of_code_eq`, in `SpaceComplexity/ExpBFS/Radius`;
- `Randomized.BPLInP.coreSum_eq_of_code_eq`, in `Randomized/BPLInPCount`.

The recorded disposition was to keep `ExpBFS`'s and re-point the other's uses. Both files are
Hydroxyi's. The user allowed mechanical edits there, with an FYI.

**The PR:** #213 on `lean/dedup-ce1`, head `fdc0e425` (full hash in the bundle header). It
changes two files, `Randomized/BPLInPCount` and `Randomized/SpaceAmplifyPolyCode`.

## What changed (verify)

- **`Randomized.BPLInP.coreSum_eq_of_code_eq` is deleted.** This removes one public declaration;
  no other file used it.
- **Its five uses cite `Complexity.ExpBFS.coreSum_eq_of_code_eq`:**
  - in `BPLInPCount`: `stepRel_iff`, `acceptLang_iff` and `haltsWithin_of_codes`;
  - in `SpaceAmplifyPolyCode`: `mem_stepLang_iff` and `mem_acceptLang_iff`.
- **`haltsWithin_of_codes`'s proof sketch** now names the `ExpBFS` lemma.
- **No import changes:** `BPLInPCount` already reaches `ExpBFS/Radius`, through
  `Randomized.Space`.
- **No other copy:** the library search, by `coreSum_eq_of_cfgWord_eq` uses and by the statement's
  shape, finds no further declaration copy. The same one-line argument appears inline in
  `Codec/Bridge` (lines 113 and 120) and in `Codec/Word`'s `decodeCfg_cfgCode`. Both files sit
  upstream of `Radius`, and `Word` is the home of `coreSum_eq_of_cfgWord_eq`, so neither can cite
  the lemma. They are not members.

## Brief for the auditor

1. **Completeness:** is any copy of the statement, or any use of the deleted name, left in the
   library?
2. **The removal:** is deleting the public duplicate right, given the disposition, rather than
   keeping it as an alias?
3. **Scope:** does the change touch anything beyond the five uses and the deletion?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`):
  - `BPLInPCount` 12 → 11 public, with the duplicate removed and the three bodies above changed;
  - `SpaceAmplifyPolyCode` 18 → 18 public, with the two bodies above changed;
  - no statement changes.
- **Screen** (`evidence/screen/`): the two files and `ExpBFS/Radius`, at base and head. The base
  has 39 declarations and 4 pairs; the head has 38 and 2. The two pairs gone are the 100% copy
  in both directions. No pair is new.
- **Lint** (`evidence/lint/`):
  - the campaign lint on `Randomized`: 0 FAIL, 51 WARN over 65 files, as at the base;
  - the policy linter: the same single finding at base and head (`mem_stepLang_iff`, 21 lines
    with no sketch).
- **Replay** (`evidence/merged-tree/`): `replay-lce1` at `fdc0e425`, over the downstream closure
  of the two files, chained from the campaign's `oleans-lnth`: **7 modules, 0 failed,
  0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/104-ce1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `ce1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/104-ce1-dedup/STATUS.md =====

# Gate 104 (#213, the dedup window's CE-1)

- 2026-11-06: the change (a sub-agent's alias `32071598`, then the deletion `fdc0e425` following the
  disposition), #213 opened. `replay-lce1` passed (7 modules, 0 failed, 0 `sorry`); freeze, screen,
  lint in `evidence/`. Pack complete.

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
languages, which have no published reading; they are not members. Census after widening: one
declaration in each of the eight files, `PathWalkMachine` two. **Retired on #208's merge.**

**NZ-1, no NDTM branch halts in zero steps** (found 2026-11-06 in gate 102's round-1 search;
a promotion candidate, **awaiting the user's acknowledgment**). The deterministic fact is public
(`Turing.FinTM.not_computesInTime_zero`, `TuringMachine/Finite`) and cited where it applies. Its
nondeterministic analogue (`Cfg.init` is live, so `N.tm.HaltsWithin z 0` fails) has no public
lemma and is proved twice: `ClassNP/ExhaustiveReplay`'s private `xr_not_haltsWithin_zero` and an
inline step of `ClassNP/NDNormalForm` (`hpos`, through `runWith_nil`, `initCfg_eq` and
`Cfg.init_state`). One member in each file. **Proposed disposition:** the dedup window (12.2c):
publish `NDTM.not_haltsWithin_zero` beside the NDTM run equations and re-point both.

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
design that waits for him.

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
unfolding, and cite it from `ISCountMath`. Both files are Hydroxyi's.

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
Hydroxyi's: interface design in their files.

**RP-1, definitional reads that #196's equations can replace** (gate 96, the round-2 shape
search; recorded 2026-11-05; not duplication). #196 publishes `Iff.rfl` equations for `WalkLe`,
`StepRel`, `RCode`, `WinRun`, `Rel`, `InitO` and `AccO`. Colleagues' files read these definitions
by unfolding or by definitional equality: `WalkLe` in `Logspace/ISCountGenWalk` (83–105),
`PathWalkMachine` (429–439) and `ISCountMath` (124); `StepRel` in `ExpBFS/Radius` (167),
`Logspace/PathHard` (232) and `Randomized/BPLInPCount` (119); `RCode` in `ExpBFS/Main` (98–104)
and `ISCountGenRadius` (88–92); `Rel`, `InitO` and `AccO` in `SavitchARM/Correct` (55–71); lines
at the campaign tip. **Disposition:** the dedup window (12.2c): re-point them to the equations.
Not counted.

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

## ===== campaign/gates/104-ce1-dedup/evidence/freeze/declfreeze-BPLInPCount.txt =====

public before/after: 12 11 private before/after: 0 0
public added: []
public removed: ['Randomized.BPLInP.coreSum_eq_of_code_eq']
authorized body change: Randomized.BPLInP.acceptLang_iff
authorized body change: Randomized.BPLInP.haltsWithin_of_codes
authorized body change: Randomized.BPLInP.stepRel_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/104-ce1-dedup/evidence/freeze/declfreeze-SpaceAmplifyPolyCode.txt =====

public before/after: 18 18 private before/after: 0 0
public added: []
public removed: []
authorized body change: Randomized.PolyAmp.mem_acceptLang_iff
authorized body change: Randomized.PolyAmp.mem_stepLang_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/104-ce1-dedup/evidence/landing/ce1.diff =====

diff --git a/TCSlib/Complexity/Randomized/BPLInPCount.lean b/TCSlib/Complexity/Randomized/BPLInPCount.lean
index ca4c3ffd..f1170da3 100644
--- a/TCSlib/Complexity/Randomized/BPLInPCount.lean
+++ b/TCSlib/Complexity/Randomized/BPLInPCount.lean
@@ -102,11 +102,6 @@ theorem inWin_run {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤
     Cfg.InWindow s (run w) := by
   simpa using NDTM.runWith_take_inWindow N.tm w ((hN x w).trans hs) w.length
 
-/-- Equal codes of window-bounded configurations give equal vertices. -/
-theorem coreSum_eq_of_code_eq {C D : Cfg N.k Bool N.State x} (hC : Cfg.InWindow s C)
-    (hD : Cfg.InWindow s D) (h : cfgCode s C = cfgCode s D) : NDTM.coreSum C = NDTM.coreSum D :=
-  coreSum_eq_of_cfgWord_eq hC hD (by rw [← bits_cfgCode, ← bits_cfgCode, h])
-
 /-- From a reachable code, the coin-`b` step relation points exactly at the code of the
 coin-`b` successor. -/
 theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s) (v : List Bool)
@@ -118,7 +113,7 @@ theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length 
   · intro h
     obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ := (mem_stepLang (fixCoin N b) x _ _ s).mp h
     have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
-      coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
+      ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
     rw [← hcC', ← hb']
     change cfgCode s ((fixCoin N b).tm.stepWith b' C) = _
     rw [stepWith_fixCoin, hstep]
@@ -137,7 +132,7 @@ theorem acceptLang_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.lengt
   rw [mem_acceptLang]
   constructor
   · rintro ⟨C, hC, hcC, hst, hout⟩
-    have hcore := coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
+    have hcore := ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
     have h1 := congrArg (fun z => z.1.1) hcore
     have h2 := congrArg Prod.snd hcore
     simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at h1 h2
@@ -193,7 +188,7 @@ within some `T`, every branch halts within `V` steps. [AB09, §4.1.1, Claim 4.4(
 
 **Proof sketch.** Suppose a branch `w` of length `V` has not halted. The `V + 1` configurations
 after its prefixes have codes below `V`, so two prefixes `i < j` share a code, hence a vertex
-(`coreSum_eq_of_code_eq`). Repeating the segment between them keeps the vertex
+(`Complexity.ExpBFS.coreSum_eq_of_code_eq`). Repeating the segment between them keeps the vertex
 (`Turing.NDTM.coreSum_runWith`), so `w.take i` followed by `T` copies of the segment is a
 branch of length at least `T` whose state is that of `w.take i`, not halted (else `w` would
 have halted), contradicting halting within `T`. -/
@@ -217,7 +212,7 @@ theorem haltsWithin_of_codes {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x
     have hvlen : v.length = j - i := by simp [v, hw]; omega
     have hcore : NDTM.coreSum (run (u ++ v)) = NDTM.coreSum (run u) := by
       rw [huv]
-      exact (coreSum_eq_of_code_eq (inWin_run hN hs _) (inWin_run hN hs _) hcode).symm
+      exact (ExpBFS.coreSum_eq_of_code_eq (inWin_run hN hs _) (inWin_run hN hs _) hcode).symm
     have pump : ∀ m : ℕ, NDTM.coreSum (run (u ++ (List.replicate m v).flatten)) =
         NDTM.coreSum (run u) := by
       intro m
diff --git a/TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean b/TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean
index 853b30ac..fe88fe14 100644
--- a/TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean
+++ b/TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean
@@ -146,7 +146,7 @@ theorem mem_acceptLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (h
   rw [mem_acceptLang]
   constructor
   · rintro ⟨E, hE, hcE, hst, hout⟩
-    have h := BPLInP.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)
+    have h := ExpBFS.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)
     exact (accepting_congr (h.trans hDC)).mp ⟨hst, hout⟩
   · intro h
     exact ⟨D, hD, hcD, (accepting_congr hDC).mpr h⟩
@@ -163,7 +163,7 @@ theorem mem_stepLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs
   rw [mem_stepLang]
   constructor
   · rintro ⟨E, hE, hcE, E', ⟨b, rfl⟩, -, rfl⟩
-    have h := (BPLInP.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)).trans hDC
+    have h := (ExpBFS.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)).trans hDC
     refine ⟨b, ?_⟩
     rw [cfgCode, cfgWord_congr (NDTM.coreSum_stepWith _ b h)]
     rfl

## ===== campaign/gates/104-ce1-dedup/evidence/lint/campaign-head.txt =====

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
INFO  TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean         468 lines; 20 public / 0 private declarations
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

## ===== campaign/gates/104-ce1-dedup/evidence/lint/policy-base.txt =====


TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean:155: `mem_stepLang_iff` proof is 21 lines, no **Proof sketch.**

## ===== campaign/gates/104-ce1-dedup/evidence/lint/policy-head.txt =====


1 findings in 2 files

TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean:155: `mem_stepLang_iff` proof is 21 lines, no **Proof sketch.**

## ===== campaign/gates/104-ce1-dedup/evidence/merged-tree/down-lce1.txt =====

TCSlib/Complexity/Randomized/BPLInPCount
TCSlib/Complexity/Randomized/BPLInP
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun
TCSlib/Complexity/Randomized/SpaceAmplifyPoly
TCSlib/Complexity/Randomized

## ===== campaign/gates/104-ce1-dedup/evidence/merged-tree/replay-lce1-static.txt =====

modules 7, mismatches 0, static total 0

## ===== campaign/gates/104-ce1-dedup/evidence/merged-tree/replay-lce1.log =====

# replay-lce1 at fdc0e425: #213, CE-1 (7 modules), fresh .oleans into oleans-lce1
TCSlib/Complexity/Randomized/BPLInPCount exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPoly exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized exit=0 errors=0 sorry=0
# modules=7 failed=0

## ===== campaign/gates/104-ce1-dedup/evidence/merged-tree/replay-lce1.sh =====

#!/usr/bin/env bash
# Replay lce1 (#213, CE-1; branch lean/dedup-ce1, stacked on the campaign after #209): its downstream closure (7 modules),
# fresh .oleans into oleans-lce1, a copy of oleans-lnth, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-ce1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lce1.txt"
LOG="$S/fills/replay/replay-lce1.log"
PINS="TCSlib/Complexity/Randomized/BPLInPCount.lean:f1170da3b87823f0c1bd49ada3f9cab0e7662304
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean:fe88fe1488f3d5d3e3688b10f4ef5937b200f026"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-ce1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 4c7dffce6250f080ad294be1e08e649cc67cfe95 HEAD || { echo "precheck: the head must contain the campaign after #209; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 4c7dffce6250f080ad294be1e08e649cc67cfe95 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #209 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lnth.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "7" ] || { echo "precheck: the replay list must have 7 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lce1" ] && { echo "precheck: $S/oleans-lce1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lnth" ] || { echo "precheck: oleans-lnth is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lnth" "$S/oleans-lce1" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lce1 at $(git rev-parse --short HEAD): #213, CE-1 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lce1"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lce1 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=7 failed=0" || { echo "replay: a module failed, or the count is not 7" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/104-ce1-dedup/evidence/screen/pairdiff.txt =====

head pairs 2; union of earlier 4; new at head 0; earlier-only 2
  GONE  Radius.lean::coreSum_eq_of_code_eq  reproduces  BPLInPCount.lean::coreSum_eq_of_code_eq: 65/65 = 100%
  GONE  BPLInPCount.lean::coreSum_eq_of_code_eq  reproduces  Radius.lean::coreSum_eq_of_code_eq: 65/65 = 100%

## ===== campaign/gates/104-ce1-dedup/evidence/screen/population.txt =====

TCSlib/Complexity/Randomized/BPLInPCount.lean
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean

## ===== campaign/gates/104-ce1-dedup/evidence/screen/screen-base.txt =====

declarations screened: 39; copy pairs (target reproduces >= half of source): 4; reproduced text: 277 chars
   Radius.lean::coreSum_eq_of_code_eq  reproduces  BPLInPCount.lean::coreSum_eq_of_code_eq: 65/65 = 100%
   BPLInPCount.lean::coreSum_eq_of_code_eq  reproduces  Radius.lean::coreSum_eq_of_code_eq: 65/65 = 100%
   Radius.lean::rcode_iff  reproduces  SpaceAmplifyPolyCode.lean::Reach.step: 84/122 = 69%
   Radius.lean::winRun_of_card_eq  reproduces  SpaceAmplifyPolyCode.lean::Reach.step: 63/122 = 52%

## ===== campaign/gates/104-ce1-dedup/evidence/screen/screen-head.txt =====

declarations screened: 38; copy pairs (target reproduces >= half of source): 2; reproduced text: 147 chars
   Radius.lean::rcode_iff  reproduces  SpaceAmplifyPolyCode.lean::Reach.step: 84/122 = 69%
   Radius.lean::winRun_of_card_eq  reproduces  SpaceAmplifyPolyCode.lean::Reach.step: 63/122 = 52%

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
    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ := (mem_stepLang (fixCoin N b) x _ _ s).mp h
    have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
      ExpBFS.coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
    rw [← hcC', ← hb']
    change cfgCode s ((fixCoin N b).tm.stepWith b' C) = _
    rw [stepWith_fixCoin, hstep]
    exact congrArg bitsVal (cfgWord_congr (NDTM.coreSum_stepWith N.tm b hcore))
  · rintro rfl
    refine (mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v, inWin_run hN hs v, rfl,
      run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩
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

## ===== TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.Randomized.BPLInPCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded PTMs through configuration codes

The register-machine form of error reduction in logarithmic space [AB09, §7.7, p. 139] keeps
the configuration of the repeated PTM `N` as a code (`Complexity.Codec.cfgCode`) in a register
and moves it along the step pairs of `Complexity.Codec.stepLang N`. This file supplies the
facts about `N` that the simulation needs: a space-bounded PTM that halts on every branch
halts within the number `2 ^ (codeK N · (S + logSpace |x| + 1))` of codes (a branch repeating a
code could be pumped forever), its reachable configurations are coded, their two successors are
exactly the step partners of their code, and the probability of acceptance after `j` coins,
`Randomized.PolyAmp.accP`, averages over the two successors.

## Main definitions

* `Randomized.PolyAmp.codeBound` — the bound `2 ^ (codeK N · (S + logSpace |x| + 1))` on codes.
* `Randomized.PolyAmp.Accepting`, `Randomized.PolyAmp.accP` — acceptance and its probability
  after `j` coins.

## Main results

* `Randomized.PolyAmp.haltsWithin_codeBound` — halting within the code bound.
* `Randomized.PolyAmp.accP_succ` — the one-step recursion of `accP`.
* `Randomized.PolyAmp.mem_stepLang_iff` — the step partners of a reachable code.
* `Randomized.PolyAmp.mem_acceptLang_iff`, `Randomized.PolyAmp.mem_initLang_iff`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.PolyAmp

open Turing Complexity Complexity.Codec

variable {N : FinNDTM Bool} {x : List Bool}

/-- The bound `2 ^ (codeK N · (S + logSpace |x| + 1))` on the codes at radius `S`. -/
def codeBound (N : FinNDTM Bool) (n S : ℕ) : ℕ := 2 ^ (codeK N * (S + logSpace n + 1))

/-- A configuration is accepting: halted with output `[true]`. -/
def Accepting (C : Cfg N.k Bool N.State x) : Prop := C.state = none ∧ C.output = [true]

instance (C : Cfg N.k Bool N.State x) : Decidable (Accepting C) := by
  unfold Accepting; infer_instance

/-- The probability that `j` coins drive `N` from `C` to an accepting configuration. -/
noncomputable def accP (C : Cfg N.k Bool N.State x) (j : ℕ) : ℚ :=
  randProb j fun w => Accepting (N.tm.runWith w C)

/-- Acceptance depends only on the configuration-graph vertex. -/
theorem accepting_congr {C D : Cfg N.k Bool N.State x} (h : NDTM.coreSum C = NDTM.coreSum D) :
    Accepting C ↔ Accepting D := by
  have hs : C.state = D.state := by
    have := congrArg (fun z => z.1.1) h
    simpa [NDTM.coreSum, MultiTapeTM.ConfigCount.core] using this
  have ho : outSummary C.output = outSummary D.output := congrArg Prod.snd h
  unfold Accepting
  rw [hs, ← outSummary_eq_accept_iff, ← outSummary_eq_accept_iff, ho]

/-- `accP` depends only on the configuration-graph vertex. -/
theorem accP_congr {C D : Cfg N.k Bool N.State x} (h : NDTM.coreSum C = NDTM.coreSum D)
    (j : ℕ) : accP C j = accP D j :=
  randProb_congr fun _ => accepting_congr (NDTM.coreSum_runWith _ _ h)

/-- With no coin left, `accP` is the indicator of acceptance. -/
theorem accP_zero (C : Cfg N.k Bool N.State x) : accP C 0 = if Accepting C then 1 else 0 := by
  unfold accP
  rw [← randProb_const 0 (Accepting C)]
  exact randProb_congr fun r => by simp [List.ofFn_zero]

/-- **One coin**: `accP` averages over the two successors. -/
theorem accP_succ (C : Cfg N.k Bool N.State x) (j : ℕ) :
    accP C (j + 1) = (accP (N.tm.stepWith true C) j + accP (N.tm.stepWith false C) j) / 2 := by
  unfold accP
  rw [randProb_succ]
  rfl

/-- After the halting time, `accP` from the start is the probability of output `[true]`. -/
theorem accP_init {T : ℕ} (hT : N.tm.HaltsWithin x T) :
    accP (N.tm.initCfg x) T = N.outputProb x T [true] :=
  randProb_congr fun r => by
    simp only [Accepting, FinNDTM.outputWith, hT _ (List.length_ofFn), true_and]

/-! ### Halting within the code bound -/

/-- **A space-bounded PTM that halts halts within the code bound** [AB09, §4.1.1]: the code
form of `Randomized.BPLInP.haltsWithin_of_codes`. -/
theorem haltsWithin_codeBound {sp : ℕ → ℕ} {S T : ℕ} (hN : N.UsesSpace sp)
    (hs : sp x.length ≤ S) (hT : N.tm.HaltsWithin x T) :
    N.tm.HaltsWithin x (codeBound N x.length S) :=
  BPLInP.haltsWithin_of_codes hN hs le_rfl hT

/-! ### The code languages on reachable configurations -/

/-- A configuration is *reachable*: its vertex is that of some branch from the start. -/
def Reach (C : Cfg N.k Bool N.State x) : Prop :=
  ∃ u : List Bool, NDTM.coreSum (N.tm.runWith u (N.tm.initCfg x)) = NDTM.coreSum C

/-- The start is reachable. -/
theorem reach_init : Reach (N.tm.initCfg x) := ⟨[], rfl⟩

/-- A successor of a reachable configuration is reachable. -/
theorem Reach.step {C : Cfg N.k Bool N.State x} (h : Reach C) (b : Bool) :
    Reach (N.tm.stepWith b C) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u ++ [b], ?_⟩
  rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
  exact NDTM.coreSum_stepWith _ b hu

/-- Reachable configurations are in the window. -/
theorem Reach.inWin {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (h : Reach C) : ∃ D, Cfg.InWindow S D ∧
      NDTM.coreSum D = NDTM.coreSum C ∧ cfgCode S D = cfgCode S C := by
  obtain ⟨u, hu⟩ := h
  exact ⟨_, BPLInP.inWin_run hN hs u, hu, by rw [cfgCode, cfgWord_congr hu]; rfl⟩

/-- **The initial code**: `c` is the initial code iff it is the code of the start. -/
theorem mem_initLang_iff (S c : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits S)) ∈ initLang N ↔
      c = cfgCode S (N.tm.initCfg x) := by
  rw [mem_initLang]; exact eq_comm

/-- **The accepting codes**: the code of a reachable configuration is accepting iff the
configuration is. -/
theorem mem_acceptLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) :
    pairEncode x (pairEncode (Nat.bits (cfgCode S C)) (Nat.bits S)) ∈ acceptLang N ↔
      Accepting C := by
  obtain ⟨D, hD, hDC, hcD⟩ := hC.inWin hN hs
  rw [mem_acceptLang]
  constructor
  · rintro ⟨E, hE, hcE, hst, hout⟩
    have h := ExpBFS.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)
    exact (accepting_congr (h.trans hDC)).mp ⟨hst, hout⟩
  · intro h
    exact ⟨D, hD, hcD, (accepting_congr hDC).mpr h⟩

/-- **The step partners of a reachable code** are the codes of its two successors. -/
theorem mem_stepLang_iff {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) (c' : ℕ) :
    pairEncode x (pairEncode (Nat.bits (cfgCode S C)) (pairEncode (Nat.bits c') (Nat.bits S))) ∈
        stepLang N ↔ ∃ b, c' = cfgCode S (N.tm.stepWith b C) := by
  obtain ⟨u, hDC⟩ := hC
  set D := N.tm.runWith u (N.tm.initCfg x)
  have hD : Cfg.InWindow S D := BPLInP.inWin_run hN hs u
  have hcD : cfgCode S D = cfgCode S C := by rw [cfgCode, cfgWord_congr hDC]; rfl
  rw [mem_stepLang]
  constructor
  · rintro ⟨E, hE, hcE, E', ⟨b, rfl⟩, -, rfl⟩
    have h := (ExpBFS.coreSum_eq_of_code_eq hE hD (hcE.trans hcD.symm)).trans hDC
    refine ⟨b, ?_⟩
    rw [cfgCode, cfgWord_congr (NDTM.coreSum_stepWith _ b h)]
    rfl
  · rintro ⟨b, rfl⟩
    refine ⟨D, hD, hcD, N.tm.stepWith b D, ⟨b, rfl⟩, ?_, ?_⟩
    · have := BPLInP.inWin_run hN hs (u ++ [b])
      rwa [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil] at this
    · rw [cfgCode, cfgWord_congr (NDTM.coreSum_stepWith _ b hDC)]
      rfl

/-- The successor codes are below the code bound. -/
theorem cfgCode_lt_codeBound (S : ℕ) (C : Cfg N.k Bool N.State x) :
    cfgCode S C < codeBound N x.length S := cfgCode_lt S C

end Randomized.PolyAmp
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
      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
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
        rw [StepRel, mem_stepLang]
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
